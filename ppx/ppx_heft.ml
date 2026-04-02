open Ppxlib

type var_info = Annotated of core_type | Runtime of string * string option

let fresh_id =
  let counter = ref 0 in
  fun prefix ->
    incr counter;
    Printf.sprintf "_%s_%d" prefix !counter

let mk_bind ~loc expr var_name rest =
  let (module A) = Ast_builder.make loc in
  A.eapply (A.evar "Result.bind")
    [ expr; A.pexp_fun Nolabel None (A.pvar var_name) rest ]

let rec translate_type ~loc ct =
  let (module A) = Ast_builder.make loc in
  match ct.ptyp_desc with
  | Ptyp_constr ({ txt = Lident name; _ }, []) ->
      let v = fresh_id "ty" in
      (v, A.eapply (A.evar "make_type") [ A.estring name; A.elist [] ])
  | Ptyp_constr ({ txt = Lident name; _ }, args) ->
      let bindings, arg_vars = translate_type_args ~loc args in
      let v = fresh_id "ty" in
      let final =
        A.eapply (A.evar "make_type")
          [ A.estring name; A.elist (List.map A.evar arg_vars) ]
      in
      let wrapped =
        List.fold_right
          (fun (var, expr) acc -> mk_bind ~loc expr var acc)
          bindings final
      in
      (v, wrapped)
  | Ptyp_arrow (_, l, r) ->
      let lv, le = translate_type ~loc l in
      let rv, re = translate_type ~loc r in
      let v = fresh_id "ty" in
      let final =
        A.eapply (A.evar "Result.ok")
          [ A.eapply (A.evar "make_fun_ty") [ A.evar lv; A.evar rv ] ]
      in
      let wrapped = mk_bind ~loc le lv (mk_bind ~loc re rv final) in
      (v, wrapped)
  | Ptyp_var name ->
      let v = fresh_id "ty" in
      ( v,
        A.eapply (A.evar "Result.ok")
          [ A.eapply (A.evar "make_vartype") [ A.estring name ] ] )
  | _ -> Location.raise_errorf ~loc:ct.ptyp_loc "unsupported type"

and translate_type_args ~loc args =
  let results = List.map (translate_type ~loc) args in
  let bindings = List.map (fun (v, e) -> (v, e)) results in
  let vars = List.map fst results in
  (bindings, vars)

let extract_fun_params_and_body (input : expression) =
  match input.pexp_desc with
  | Pexp_function (params, None, Pfunction_body body) ->
      let pats =
        List.filter_map
          (fun (p : function_param) ->
            match p.pparam_desc with
            | Pparam_val (Nolabel, None, pat) -> Some pat
            | _ -> None)
          params
      in
      if List.length pats = List.length params && pats <> [] then
        Some (pats, body)
      else None
  | _ -> None

let is_fun_expr (input : expression) =
  match extract_fun_params_and_body input with Some _ -> true | None -> false

let extract_pat_binding pat =
  match pat.ppat_desc with
  | Ppat_constraint ({ ppat_desc = Ppat_var { txt = name; _ }; _ }, ct) ->
      (name, ct)
  | _ ->
      Location.raise_errorf ~loc:pat.ppat_loc
        "parameter must have a type annotation: (x : ty)"

let rec translate_expr ~loc ~env (input : expression) =
  let (module A) = Ast_builder.make loc in
  match input.pexp_desc with
  (* Annotated identifier → HOL variable: (x : nat) *)
  | Pexp_constraint
      ({ pexp_desc = Pexp_ident { txt = Lident name; _ }; _ }, core_type) ->
      let ty_var, ty_expr = translate_type ~loc core_type in
      mk_bind ~loc ty_expr ty_var
        (A.eapply (A.evar "Result.ok")
           [ A.eapply (A.evar "make_var") [ A.estring name; A.evar ty_var ] ])
  (* Bare identifier → check env for variable, otherwise HOL constant *)
  | Pexp_ident { txt = Lident name; _ } -> (
      match List.assoc_opt name env with
      | Some (Annotated core_type) ->
          let ty_var, ty_expr = translate_type ~loc core_type in
          mk_bind ~loc ty_expr ty_var
            (A.eapply (A.evar "Result.ok")
               [
                 A.eapply (A.evar "make_var") [ A.estring name; A.evar ty_var ];
               ])
      | Some (Runtime (rt_var, _)) ->
          A.eapply (A.evar "Result.ok")
            [ A.eapply (A.evar "make_var") [ A.estring name; A.evar rt_var ] ]
      | None -> A.eapply (A.evar "make_const") [ A.estring name; A.elist [] ])
  (* Lambda: fun (x : ty) (y : ty) -> body *)
  | Pexp_function _ -> (
      match extract_fun_params_and_body input with
      | Some (pats, body) -> translate_lambda ~loc ~env pats body
      | None ->
          Location.raise_errorf ~loc
            "lambda parameters must be annotated: fun (x : ty) -> body")
  (* true/false → HOL constants T/F *)
  | Pexp_construct ({ txt = Lident "true"; _ }, None) ->
      A.eapply (A.evar "make_const") [ A.estring "T"; A.elist [] ]
  | Pexp_construct ({ txt = Lident "false"; _ }, None) ->
      A.eapply (A.evar "make_const") [ A.estring "F"; A.elist [] ]
  (* Nullary constructor → HOL constant *)
  | Pexp_construct ({ txt = Lident name; _ }, None) ->
      A.eapply (A.evar "make_const") [ A.estring name; A.elist [] ]
  (* Constructor with arguments → HOL constant applied to args *)
  | Pexp_construct ({ txt = Lident name; _ }, Some arg) ->
      let args =
        match arg.pexp_desc with Pexp_tuple args -> args | _ -> [ arg ]
      in
      let const_expr =
        A.eapply (A.evar "make_const") [ A.estring name; A.elist [] ]
      in
      let func_var = fresh_id "app" in
      List.fold_left
        (fun (acc_expr, acc_var) arg_expr ->
          let translated = translate_expr ~loc ~env arg_expr in
          let arg_var = fresh_id "arg" in
          let app_var = fresh_id "app" in
          let expr =
            mk_bind ~loc acc_expr acc_var
              (mk_bind ~loc translated arg_var
                 (A.eapply
                    (A.evar "Heft.Rewrite.smart_make_app")
                    [ A.evar acc_var; A.evar arg_var ]))
          in
          (expr, app_var))
        (const_expr, func_var) args
      |> fst
  (* Nat literals: 0n, 1n, 2n, ... → zero, suc zero, suc (suc zero), ... *)
  | Pexp_constant (Pconst_integer (s, Some 'n')) ->
      let n =
        match int_of_string_opt s with
        | Some n when n >= 0 -> n
        | _ ->
            Location.raise_errorf ~loc
              "nat literal must be a non-negative integer"
      in
      let zero =
        A.eapply (A.evar "make_const") [ A.estring "Zero"; A.elist [] ]
      in
      let rec wrap k acc =
        if k = 0 then acc
        else
          let acc_var = fresh_id "nat" in
          let suc_var = fresh_id "nat" in
          wrap (k - 1)
            (mk_bind ~loc acc acc_var
               (mk_bind ~loc
                  (A.eapply (A.evar "make_const")
                     [ A.estring "Suc"; A.elist [] ])
                  suc_var
                  (A.eapply
                     (A.evar "Heft.Rewrite.smart_make_app")
                     [ A.evar suc_var; A.evar acc_var ])))
      in
      wrap n zero
  (* if/then/else → COND cond then_branch else_branch *)
  | Pexp_ifthenelse (cond, then_br, Some else_br) ->
      let cond_const =
        A.eapply (A.evar "make_const") [ A.estring "COND"; A.elist [] ]
      in
      let all_args = [ cond; then_br; else_br ] in
      let func_var = fresh_id "app" in
      List.fold_left
        (fun (acc_expr, acc_var) arg ->
          let arg_expr = translate_expr ~loc ~env arg in
          let arg_var = fresh_id "arg" in
          let app_var = fresh_id "app" in
          let expr =
            mk_bind ~loc acc_expr acc_var
              (mk_bind ~loc arg_expr arg_var
                 (A.eapply
                    (A.evar "Heft.Rewrite.smart_make_app")
                    [ A.evar acc_var; A.evar arg_var ]))
          in
          (expr, app_var))
        (cond_const, func_var) all_args
      |> fst
  (* Match expression → match_<type> scrutinee handler1 handler2 ... *)
  | Pexp_match (scrutinee, cases) -> translate_match ~loc ~env scrutinee cases
  (* Application *)
  | Pexp_apply (func, args) -> translate_apply ~loc ~env func args
  | _ -> Location.raise_errorf ~loc "unsupported expression in [%%term]"

and translate_lambda ~loc ~env pats body =
  let (module A) = Ast_builder.make loc in
  match pats with
  | [] -> translate_expr ~loc ~env body
  | pat :: rest ->
      let name, core_type = extract_pat_binding pat in
      let env = (name, Annotated core_type) :: env in
      let ty_var, ty_expr = translate_type ~loc core_type in
      let var_expr =
        A.eapply (A.evar "make_var") [ A.estring name; A.evar ty_var ]
      in
      let inner = translate_lambda ~loc ~env rest body in
      let body_var = fresh_id "body" in
      let lam_var = fresh_id "lam" in
      mk_bind ~loc ty_expr ty_var
        (mk_bind ~loc inner body_var
           (mk_bind ~loc
              (A.eapply (A.evar "make_lam") [ var_expr; A.evar body_var ])
              lam_var
              (A.eapply (A.evar "Result.ok") [ A.evar lam_var ])))

and translate_apply ~loc ~env func args =
  let (module A) = Ast_builder.make loc in
  (* Check for special forms based on the function name *)
  match (func.pexp_desc, args) with
  (* forall (fun (x : ty) -> body) → make_forall var body *)
  | Pexp_ident { txt = Lident "forall"; _ }, [ (Nolabel, lam) ]
    when is_fun_expr lam ->
      translate_quantifier ~loc ~env ~quant:"make_forall" lam
  (* exists (fun (x : ty) -> body) → make_exists var body *)
  | Pexp_ident { txt = Lident "exists"; _ }, [ (Nolabel, lam) ]
    when is_fun_expr lam ->
      translate_quantifier ~loc ~env ~quant:"make_exists" lam
  (* not p → make_neg p *)
  | Pexp_ident { txt = Lident "not"; _ }, [ (Nolabel, p) ] ->
      let p_expr = translate_expr ~loc ~env p in
      let p_var = fresh_id "arg" in
      mk_bind ~loc p_expr p_var
        (A.eapply (A.evar "Result.ok")
           [ A.eapply (A.evar "make_neg") [ A.evar p_var ] ])
  (* p = q → safe_make_eq p q *)
  | Pexp_ident { txt = Lident "="; _ }, [ (Nolabel, lhs); (Nolabel, rhs) ] ->
      translate_binary_result ~loc ~env ~fn:"Heft.Rewrite.smart_make_eq" lhs rhs
  (* p ==> q → make_imp p q (pure) *)
  | Pexp_ident { txt = Lident "==>"; _ }, [ (Nolabel, lhs); (Nolabel, rhs) ] ->
      translate_binary_pure ~loc ~env ~fn:"make_imp" lhs rhs
  (* p && q → make_conj p q (pure) *)
  | Pexp_ident { txt = Lident "&&"; _ }, [ (Nolabel, lhs); (Nolabel, rhs) ] ->
      translate_binary_pure ~loc ~env ~fn:"make_conj" lhs rhs
  (* p || q → make_disj p q (pure) *)
  | Pexp_ident { txt = Lident "||"; _ }, [ (Nolabel, lhs); (Nolabel, rhs) ] ->
      translate_binary_pure ~loc ~env ~fn:"make_disj" lhs rhs
  (* General application: f x y → make_app (make_app f x) y *)
  | _ ->
      let all_args = List.map (fun (_, arg) -> arg) args in
      let func_expr = translate_expr ~loc ~env func in
      let func_var = fresh_id "app" in
      List.fold_left
        (fun (acc_expr, acc_var) arg ->
          let arg_expr = translate_expr ~loc ~env arg in
          let arg_var = fresh_id "arg" in
          let app_var = fresh_id "app" in
          let expr =
            mk_bind ~loc acc_expr acc_var
              (mk_bind ~loc arg_expr arg_var
                 (A.eapply
                    (A.evar "Heft.Rewrite.smart_make_app")
                    [ A.evar acc_var; A.evar arg_var ]))
          in
          (expr, app_var))
        (func_expr, func_var) all_args
      |> fst

(* forall/exists applied to a lambda: quantifier (fun (x : ty) (y : ty) -> body) *)
and translate_quantifier ~loc ~env ~quant lam =
  match extract_fun_params_and_body lam with
  | Some (pats, body) -> translate_quantifier_params ~loc ~env ~quant pats body
  | None ->
      Location.raise_errorf ~loc:lam.pexp_loc
        "forall/exists expects a lambda argument"

and translate_quantifier_params ~loc ~env ~quant pats body =
  let (module A) = Ast_builder.make loc in
  match pats with
  | [] -> translate_expr ~loc ~env body
  | pat :: rest ->
      let name, core_type = extract_pat_binding pat in
      let env = (name, Annotated core_type) :: env in
      let ty_var, ty_expr = translate_type ~loc core_type in
      let var_expr =
        A.eapply (A.evar "make_var") [ A.estring name; A.evar ty_var ]
      in
      let inner = translate_quantifier_params ~loc ~env ~quant rest body in
      let body_var = fresh_id "body" in
      mk_bind ~loc ty_expr ty_var
        (mk_bind ~loc inner body_var
           (A.eapply (A.evar "Result.ok")
              [ A.eapply (A.evar quant) [ var_expr; A.evar body_var ] ]))

(* Binary operator where the kernel function returns a result *)
and translate_binary_result ~loc ~env ~fn lhs rhs =
  let (module A) = Ast_builder.make loc in
  let l_expr = translate_expr ~loc ~env lhs in
  let r_expr = translate_expr ~loc ~env rhs in
  let l_var = fresh_id "arg" in
  let r_var = fresh_id "arg" in
  mk_bind ~loc l_expr l_var
    (mk_bind ~loc r_expr r_var
       (A.eapply (A.evar fn) [ A.evar l_var; A.evar r_var ]))

(* Binary operator where the kernel function is pure *)
and translate_binary_pure ~loc ~env ~fn lhs rhs =
  let (module A) = Ast_builder.make loc in
  let l_expr = translate_expr ~loc ~env lhs in
  let r_expr = translate_expr ~loc ~env rhs in
  let l_var = fresh_id "arg" in
  let r_var = fresh_id "arg" in
  mk_bind ~loc l_expr l_var
    (mk_bind ~loc r_expr r_var
       (A.eapply (A.evar "Result.ok")
          [ A.eapply (A.evar fn) [ A.evar l_var; A.evar r_var ] ]))

and translate_match ~loc ~env scrutinee cases =
  let (module A) = Ast_builder.make loc in
  let type_name = extract_match_type_name ~loc ~env scrutinee in
  let match_fn_name = "match_" ^ type_name in
  let match_expr =
    A.eapply (A.evar "make_const") [ A.estring match_fn_name; A.elist [] ]
  in
  let scr_expr = translate_expr ~loc ~env scrutinee in
  let handler_exprs = List.map (translate_match_case ~loc ~env) cases in
  let all_args = scr_expr :: handler_exprs in
  let func_var = fresh_id "mfn" in
  List.fold_left
    (fun (acc_expr, acc_var) arg_expr ->
      let arg_var = fresh_id "marg" in
      let app_var = fresh_id "mapp" in
      let expr =
        mk_bind ~loc acc_expr acc_var
          (mk_bind ~loc arg_expr arg_var
             (A.eapply
                (A.evar "Heft.Rewrite.smart_make_app")
                [ A.evar acc_var; A.evar arg_var ]))
      in
      (expr, app_var))
    (match_expr, func_var) all_args
  |> fst

and extract_match_type_name ~loc:_ ~env scrutinee =
  let extract_from_core_type ct =
    match ct.ptyp_desc with
    | Ptyp_constr ({ txt = Lident name; _ }, _) -> name
    | _ ->
        Location.raise_errorf ~loc:ct.ptyp_loc
          "cannot determine inductive type from this type"
  in
  match scrutinee.pexp_desc with
  | Pexp_constraint (_, ct) -> extract_from_core_type ct
  | Pexp_ident { txt = Lident name; _ } -> (
      match List.assoc_opt name env with
      | Some (Annotated ct) -> extract_from_core_type ct
      | Some (Runtime (_, Some tyname)) -> tyname
      | _ ->
          Location.raise_errorf ~loc:scrutinee.pexp_loc
            "match scrutinee type unknown; add a type annotation or use a \
             bound variable")
  | _ ->
      Location.raise_errorf ~loc:scrutinee.pexp_loc
        "match scrutinee must have a type annotation or be a bound variable"

and translate_match_case ~loc ~env case =
  let (module A) = Ast_builder.make loc in
  match case.pc_lhs.ppat_desc with
  | Ppat_construct ({ txt = Lident _con_name; _ }, None) ->
      translate_expr ~loc ~env case.pc_rhs
  | Ppat_construct ({ txt = Lident con_name; _ }, Some (_, pat_arg)) ->
      let pat_vars = extract_match_pattern_vars pat_arg in
      if pat_vars = [] then translate_expr ~loc ~env case.pc_rhs
      else
        let atys_var = fresh_id "atys" in
        let var_data =
          List.mapi
            (fun i name ->
              let ty_v = fresh_id "pty" in
              let pv = fresh_id "pv" in
              (name, i, ty_v, pv))
            pat_vars
        in
        let env' =
          List.fold_left
            (fun env (name, _, ty_v, _) -> (name, Runtime (ty_v, None)) :: env)
            env var_data
        in
        let body_expr = translate_expr ~loc ~env:env' case.pc_rhs in
        let body_v = fresh_id "mbody" in
        let lambda_chain, _ =
          List.fold_right
            (fun (_, _, _, pv) (inner_expr, inner_var) ->
              let lam_v = fresh_id "mlam" in
              let expr =
                mk_bind ~loc inner_expr inner_var
                  (A.eapply (A.evar "make_lam") [ A.evar pv; A.evar inner_var ])
              in
              (expr, lam_v))
            var_data (body_expr, body_v)
        in
        let with_pvs =
          List.fold_right
            (fun (name, _, ty_v, pv) acc ->
              A.pexp_let Nonrecursive
                [
                  A.value_binding ~pat:(A.pvar pv)
                    ~expr:
                      (A.eapply (A.evar "make_var")
                         [ A.estring name; A.evar ty_v ]);
                ]
                acc)
            var_data lambda_chain
        in
        let with_tys =
          List.fold_right
            (fun (_, i, ty_v, _) acc ->
              A.pexp_let Nonrecursive
                [
                  A.value_binding ~pat:(A.pvar ty_v)
                    ~expr:
                      (A.eapply (A.evar "List.nth")
                         [ A.evar atys_var; A.eint i ]);
                ]
                acc)
            var_data with_pvs
        in
        A.pexp_let Nonrecursive
          [
            A.value_binding ~pat:(A.pvar atys_var)
              ~expr:
                (A.eapply
                   (A.evar "Heft.Printing.constructor_arg_types")
                   [ A.estring con_name ]);
          ]
          with_tys
  | _ ->
      Location.raise_errorf ~loc:case.pc_lhs.ppat_loc
        "unsupported pattern in match"

and extract_match_pattern_vars pat =
  match pat.ppat_desc with
  | Ppat_var { txt = name; _ } -> [ name ]
  | Ppat_any -> [ fresh_id "wild" ]
  | Ppat_tuple pats -> List.concat_map extract_match_pattern_vars pats
  | Ppat_constraint (inner, _) -> extract_match_pattern_vars inner
  | _ ->
      Location.raise_errorf ~loc:pat.ppat_loc
        "unsupported pattern variable in match"

let translate ~(loc : location) ~(path : label) (input : expression) =
  let (module A) = Ast_builder.make loc in
  let _ = path in
  let inner = translate_expr ~loc ~env:[] input in
  A.eapply (A.evar "Heft.Printing.unwrap_term") [ inner ]

let rec translate_type_raw ~loc ct =
  let (module A) = Ast_builder.make loc in
  match ct.ptyp_desc with
  | Ptyp_constr ({ txt = Lident name; _ }, []) ->
      A.pexp_construct
        { txt = Lident "TyCon"; loc }
        (Some (A.pexp_tuple [ A.estring name; A.elist [] ]))
  | Ptyp_constr ({ txt = Lident name; _ }, args) ->
      let arg_exprs = List.map (translate_type_raw ~loc) args in
      A.pexp_construct
        { txt = Lident "TyCon"; loc }
        (Some (A.pexp_tuple [ A.estring name; A.elist arg_exprs ]))
  | Ptyp_arrow (_, l, r) ->
      let le = translate_type_raw ~loc l in
      let re = translate_type_raw ~loc r in
      A.pexp_construct
        { txt = Lident "TyCon"; loc }
        (Some (A.pexp_tuple [ A.estring "fun"; A.elist [ le; re ] ]))
  | Ptyp_var name ->
      A.pexp_construct { txt = Lident "TyVar"; loc } (Some (A.estring name))
  | _ ->
      Location.raise_errorf ~loc:ct.ptyp_loc
        "unsupported type in [%%%%inductive]"

let translate_inductive ~(loc : location) ~(path : label)
    (payload : structure_item list) =
  let (module A) = Ast_builder.make loc in
  let _ = path in
  let type_decl =
    match payload with
    | [ { pstr_desc = Pstr_type (_, [ td ]); _ } ] -> td
    | _ ->
        Location.raise_errorf ~loc
          "[%%%%inductive] expects a single type declaration"
  in
  let type_name = type_decl.ptype_name.txt in
  let type_params =
    List.map
      (fun (ct, _) ->
        match ct.ptyp_desc with
        | Ptyp_var name -> A.estring name
        | _ ->
            Location.raise_errorf ~loc:ct.ptyp_loc
              "type parameter must be a type variable")
      type_decl.ptype_params
  in
  let constructors =
    match type_decl.ptype_kind with
    | Ptype_variant cds -> cds
    | _ -> Location.raise_errorf ~loc "[%%%%inductive] expects a variant type"
  in
  let spec_exprs =
    List.map
      (fun (cd : constructor_declaration) ->
        let name = cd.pcd_name.txt in
        let arg_types =
          match cd.pcd_args with
          | Pcstr_tuple cts -> List.map (translate_type_raw ~loc) cts
          | _ ->
              Location.raise_errorf ~loc:cd.pcd_name.loc
                "unsupported constructor argument form"
        in
        A.pexp_record
          [
            ({ txt = Ldot (Lident "Kernel", "name"); loc }, A.estring name);
            ( { txt = Ldot (Lident "Kernel", "arg_types"); loc },
              A.elist arg_types );
          ]
          None)
      constructors
  in
  let define_expr =
    A.eapply
      (A.evar "Heft.Inductive.define_inductive")
      [ A.estring type_name; A.elist type_params; A.elist spec_exprs ]
  in
  let body =
    A.pexp_match define_expr
      [
        A.case
          ~lhs:(A.ppat_construct { txt = Lident "Ok"; loc } (Some (A.pvar "_")))
          ~guard:None
          ~rhs:(A.pexp_construct { txt = Lident "()"; loc } None);
        A.case
          ~lhs:
            (A.ppat_construct { txt = Lident "Error"; loc } (Some (A.pvar "e")))
          ~guard:None
          ~rhs:
            (A.eapply (A.evar "failwith")
               [ A.eapply (A.evar "Heft.Printing.print_error") [ A.evar "e" ] ]);
      ]
  in
  A.pstr_eval body []

let term_extension =
  Extension.declare "term" Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    translate

let inductive_extension =
  Extension.declare "inductive" Extension.Context.structure_item
    Ast_pattern.(pstr __)
    translate_inductive

let () =
  Driver.register_transformation "heft_ppx"
    ~rules:
      [
        Context_free.Rule.extension term_extension;
        Context_free.Rule.extension inductive_extension;
      ]
