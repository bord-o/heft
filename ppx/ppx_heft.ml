open Ppxlib

type var_info =
  | Annotated of core_type
  | Runtime of string * string option
  | Prebuilt of string

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
  | _ -> Location.raise_errorf ~loc:ct.ptyp_loc "unsupported type in [%%%%term]"

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
  (* General type annotation on arbitrary expression: (expr : ty) *)
  | Pexp_constraint (inner_expr, _core_type) ->
      translate_expr ~loc ~env inner_expr
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
      | Some (Prebuilt ocaml_var) ->
          A.eapply (A.evar "Result.ok") [ A.evar ocaml_var ]
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
  (* [] → Nil *)
  | Pexp_construct ({ txt = Lident "[]"; _ }, None) ->
      A.eapply (A.evar "make_const") [ A.estring "Nil"; A.elist [] ]
  (* x :: xs → Cons x xs *)
  | Pexp_construct ({ txt = Lident "::"; _ }, Some arg) ->
      let hd, tl =
        match arg.pexp_desc with
        | Pexp_tuple [ hd; tl ] -> (hd, tl)
        | _ -> Location.raise_errorf ~loc "malformed :: expression"
      in
      let const_expr =
        A.eapply (A.evar "make_const") [ A.estring "Cons"; A.elist [] ]
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
        (const_expr, func_var) [ hd; tl ]
      |> fst
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
  (* choose (fun (x : ty) -> body) → make_select var body *)
  | Pexp_ident { txt = Lident "choose"; _ }, [ (Nolabel, lam) ]
    when is_fun_expr lam ->
      translate_quantifier ~loc ~env ~quant:"make_select" ~pure:false lam
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

(* forall/exists/choose applied to a lambda: quantifier (fun (x : ty) (y : ty) -> body) *)
and translate_quantifier ~loc ~env ~quant ?(pure = true) lam =
  match extract_fun_params_and_body lam with
  | Some (pats, body) ->
      translate_quantifier_params ~loc ~env ~quant ~pure pats body
  | None ->
      Location.raise_errorf ~loc:lam.pexp_loc
        "forall/exists/choose expects a lambda argument"

and translate_quantifier_params ~loc ~env ~quant ~pure pats body =
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
      let inner =
        translate_quantifier_params ~loc ~env ~quant ~pure rest body
      in
      let body_var = fresh_id "body" in
      let quant_call = A.eapply (A.evar quant) [ var_expr; A.evar body_var ] in
      mk_bind ~loc ty_expr ty_var
        (mk_bind ~loc inner body_var
           (if pure then A.eapply (A.evar "Result.ok") [ quant_call ]
            else quant_call))

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
  let type_name, scr_ct_opt = extract_match_type_info ~loc ~env scrutinee in
  let match_fn_name = "match_" ^ type_name in
  let match_expr =
    A.eapply (A.evar "make_const") [ A.estring match_fn_name; A.elist [] ]
  in
  let scr_expr = translate_expr ~loc ~env scrutinee in
  (* Compute tysub at runtime for polymorphic types *)
  let tysub_var = fresh_id "mtsub" in
  let tysub_expr =
    match scr_ct_opt with
    | Some ct ->
        let scr_ty_expr = translate_type_raw ~loc ct in
        A.pexp_match
          (A.eapply
             (A.evar "Heft.Rewrite.type_match")
             [
               A.elist [];
               A.pexp_field
                 (A.eapply (A.evar "Hashtbl.find")
                    [ A.evar "Kernel.the_inductives"; A.estring type_name ])
                 { txt = Lident "ty"; loc };
               scr_ty_expr;
             ])
          [
            A.case
              ~lhs:
                (A.ppat_construct
                   { txt = Lident "Some"; loc }
                   (Some (A.pvar "_msub")))
              ~guard:None ~rhs:(A.evar "_msub");
            A.case
              ~lhs:(A.ppat_construct { txt = Lident "None"; loc } None)
              ~guard:None ~rhs:(A.elist []);
          ]
    | None -> A.elist []
  in
  let handler_exprs =
    List.map (translate_match_case ~loc ~env ~tysub_var) cases
  in
  let all_args = scr_expr :: handler_exprs in
  let func_var = fresh_id "mfn" in
  let app_chain =
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
  in
  A.pexp_let Nonrecursive
    [ A.value_binding ~pat:(A.pvar tysub_var) ~expr:tysub_expr ]
    app_chain

and extract_match_type_info ~loc:_ ~env scrutinee =
  let extract_from_core_type ct =
    match ct.ptyp_desc with
    | Ptyp_constr ({ txt = Lident name; _ }, _) -> (name, Some ct)
    | _ ->
        Location.raise_errorf ~loc:ct.ptyp_loc
          "cannot determine inductive type from this type"
  in
  match scrutinee.pexp_desc with
  | Pexp_constraint (_, ct) -> extract_from_core_type ct
  | Pexp_ident { txt = Lident name; _ } -> (
      match List.assoc_opt name env with
      | Some (Annotated ct) -> extract_from_core_type ct
      | Some (Runtime (_, Some tyname)) -> (tyname, None)
      | _ ->
          Location.raise_errorf ~loc:scrutinee.pexp_loc
            "match scrutinee type unknown; add a type annotation or use a \
             bound variable")
  | _ ->
      Location.raise_errorf ~loc:scrutinee.pexp_loc
        "match scrutinee must have a type annotation or be a bound variable"

and normalize_con_name = function
  | "[]" -> "Nil"
  | "::" -> "Cons"
  | name -> name

and translate_match_case ~loc ~env ~tysub_var case =
  let (module A) = Ast_builder.make loc in
  match case.pc_lhs.ppat_desc with
  | Ppat_construct ({ txt = Lident name; _ }, None) ->
      ignore (normalize_con_name name);
      translate_expr ~loc ~env case.pc_rhs
  | Ppat_construct ({ txt = Lident name; _ }, Some (_, pat_arg)) ->
      let con_name = normalize_con_name name in
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
                {
                  pexp_desc =
                    Pexp_apply
                      ( A.evar "Heft.Printing.constructor_arg_types",
                        [
                          (Labelled "tysub", A.evar tysub_var);
                          (Nolabel, A.estring con_name);
                        ] );
                  pexp_loc = loc;
                  pexp_loc_stack = [];
                  pexp_attributes = [];
                };
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

let extract_def_parts expr =
  let rec go acc expr =
    match expr.pexp_desc with
    | Pexp_function (params, constraint_opt, Pfunction_body body) ->
        let pats =
          List.filter_map
            (fun (p : function_param) ->
              match p.pparam_desc with
              | Pparam_val (Nolabel, None, pat) -> Some pat
              | _ -> None)
            params
        in
        let ret_ct =
          match constraint_opt with
          | Some (Pconstraint ct) -> Some ct
          | _ -> None
        in
        if List.length pats = List.length params && pats <> [] then
          match ret_ct with
          | Some _ -> (acc @ pats, ret_ct, body)
          | None -> go (acc @ pats) body
        else (acc, ret_ct, expr)
    | _ -> (acc, None, expr)
  in
  go [] expr

let translate_def ~(loc : location) ~(path : label)
    (payload : structure_item list) =
  let (module A) = Ast_builder.make loc in
  let _ = path in
  let vb =
    match payload with
    | [ { pstr_desc = Pstr_value (Nonrecursive, [ vb ]); _ } ] -> vb
    | _ ->
        Location.raise_errorf ~loc
          "[%%%%def] expects a single non-recursive let binding"
  in
  let fn_name =
    match vb.pvb_pat.ppat_desc with
    | Ppat_var { txt = name; _ } -> name
    | _ ->
        Location.raise_errorf ~loc:vb.pvb_pat.ppat_loc
          "[%%%%def] expects a simple name"
  in
  let constraint_type =
    match vb.pvb_constraint with
    | Some (Pvc_constraint { locally_abstract_univars = _; typ }) -> Some typ
    | _ -> None
  in
  let params, ret_type_opt, body = extract_def_parts vb.pvb_expr in
  let ret_type =
    match (ret_type_opt, constraint_type) with
    | Some ct, _ -> ct
    | None, Some ct -> ct
    | None, None ->
        Location.raise_errorf ~loc "[%%%%def] requires a type annotation"
  in
  let param_bindings =
    List.map
      (fun pat ->
        match pat.ppat_desc with
        | Ppat_constraint ({ ppat_desc = Ppat_var { txt = name; _ }; _ }, ct) ->
            (name, ct)
        | _ ->
            Location.raise_errorf ~loc:pat.ppat_loc
              "[%%%%def] parameters must be annotated: (x : ty)")
      params
  in
  (* Build the full type: arg1 -> arg2 -> ... -> ret *)
  let full_type_expr =
    List.fold_right
      (fun (_, ct) acc ->
        let arg_e = translate_type_raw ~loc ct in
        let acc_e = acc in
        A.eapply (A.evar "make_fun_ty") [ arg_e; acc_e ])
      param_bindings
      (translate_type_raw ~loc ret_type)
  in
  (* Build the env for body translation *)
  let env = List.map (fun (name, ct) -> (name, Annotated ct)) param_bindings in
  (* Translate body *)
  let body_expr = translate_expr ~loc ~env body in
  (* Build the RHS term: either lambda-wrapped (function) or bare (constant) *)
  let rhs_chain, rhs_v =
    if param_bindings = [] then (body_expr, fresh_id "defbody")
    else
      let body_v = fresh_id "defbody" in
      let chain, _ =
        List.fold_right
          (fun (name, ct) (inner_expr, inner_var) ->
            let ty_v, ty_e = translate_type ~loc ct in
            let lam_v = fresh_id "deflam" in
            let var_expr =
              A.eapply (A.evar "make_var") [ A.estring name; A.evar ty_v ]
            in
            let expr =
              mk_bind ~loc ty_e ty_v
                (mk_bind ~loc inner_expr inner_var
                   (A.eapply (A.evar "make_lam") [ var_expr; A.evar inner_var ]))
            in
            (expr, lam_v))
          param_bindings (body_expr, body_v)
      in
      (chain, fresh_id "deflam")
  in
  (* Build: Var(fn_name, full_type) = rhs_term, then new_basic_definition *)
  let full_ty_v = fresh_id "defty" in
  let def_expr =
    A.pexp_let Nonrecursive
      [ A.value_binding ~pat:(A.pvar full_ty_v) ~expr:full_type_expr ]
      (mk_bind ~loc rhs_chain rhs_v
         (let def_var =
            A.eapply (A.evar "make_var") [ A.estring fn_name; A.evar full_ty_v ]
          in
          let eq_v = fresh_id "defeq" in
          let def_thm_v = fresh_id "defthm" in
          mk_bind ~loc
            (A.eapply (A.evar "safe_make_eq") [ def_var; A.evar rhs_v ])
            eq_v
            (mk_bind ~loc
               (A.eapply (A.evar "new_basic_definition") [ A.evar eq_v ])
               def_thm_v
               (A.pexp_sequence
                  (A.eapply
                     (A.evar "Heft.Rules.add_def")
                     [ A.estring fn_name; A.evar def_thm_v ])
                  (A.eapply (A.evar "Result.ok") [ A.evar def_thm_v ])))))
  in
  let unwrapped = A.eapply (A.evar "Heft.Printing.unwrap_thm") [ def_expr ] in
  A.pstr_value Nonrecursive
    [ A.value_binding ~pat:(A.pvar fn_name) ~expr:unwrapped ]

(* Replace recursive calls in body AST: fn_name arg rest... → r_arg rest...
   rec_map: (pattern_var_name, replacement_ident) list *)
let rec replace_rec_calls fn_name rec_map expr =
  let go = replace_rec_calls fn_name rec_map in
  match expr.pexp_desc with
  | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident fn; _ }; _ }, args)
    when fn = fn_name -> (
      match args with
      | (_, { pexp_desc = Pexp_ident { txt = Lident arg_name; _ }; _ }) :: rest
        -> (
          match List.assoc_opt arg_name rec_map with
          | Some r_name ->
              let r_ident =
                {
                  expr with
                  pexp_desc =
                    Pexp_ident { txt = Lident r_name; loc = expr.pexp_loc };
                }
              in
              if rest = [] then r_ident
              else
                {
                  expr with
                  pexp_desc =
                    Pexp_apply (r_ident, List.map (fun (l, e) -> (l, go e)) rest);
                }
          | None ->
              {
                expr with
                pexp_desc =
                  Pexp_apply
                    ( {
                        expr with
                        pexp_desc =
                          Pexp_ident { txt = Lident fn; loc = expr.pexp_loc };
                      },
                      List.map (fun (l, e) -> (l, go e)) args );
              })
      | _ ->
          {
            expr with
            pexp_desc =
              Pexp_apply
                ( {
                    expr with
                    pexp_desc =
                      Pexp_ident { txt = Lident fn; loc = expr.pexp_loc };
                  },
                  List.map (fun (l, e) -> (l, go e)) args );
          })
  | Pexp_apply (f, args) ->
      {
        expr with
        pexp_desc = Pexp_apply (go f, List.map (fun (l, e) -> (l, go e)) args);
      }
  | Pexp_construct (lid, Some arg) ->
      { expr with pexp_desc = Pexp_construct (lid, Some (go arg)) }
  | Pexp_tuple es -> { expr with pexp_desc = Pexp_tuple (List.map go es) }
  | Pexp_ifthenelse (c, t, Some e) ->
      { expr with pexp_desc = Pexp_ifthenelse (go c, go t, Some (go e)) }
  | Pexp_match (scr, cases) ->
      {
        expr with
        pexp_desc =
          Pexp_match
            (go scr, List.map (fun c -> { c with pc_rhs = go c.pc_rhs }) cases);
      }
  | Pexp_constraint (inner, ct) ->
      { expr with pexp_desc = Pexp_constraint (go inner, ct) }
  | Pexp_function (params, constr, Pfunction_body body) ->
      {
        expr with
        pexp_desc = Pexp_function (params, constr, Pfunction_body (go body));
      }
  | _ -> expr

let translate_primrec ~(loc : location) ~(path : label)
    (payload : structure_item list) =
  let (module A) = Ast_builder.make loc in
  let _ = path in
  let vb =
    match payload with
    | [ { pstr_desc = Pstr_value (Nonrecursive, [ vb ]); _ } ] -> vb
    | _ ->
        Location.raise_errorf ~loc "[%%%%primrec] expects a single let binding"
  in
  let fn_name =
    match vb.pvb_pat.ppat_desc with
    | Ppat_var { txt = name; _ } -> name
    | _ ->
        Location.raise_errorf ~loc:vb.pvb_pat.ppat_loc
          "[%%%%primrec] expects a simple function name"
  in
  let params, ret_type_opt, match_body = extract_def_parts vb.pvb_expr in
  let ret_type =
    match ret_type_opt with
    | Some ct -> ct
    | None ->
        Location.raise_errorf ~loc
          "[%%%%primrec] requires a return type annotation"
  in
  if params = [] then
    Location.raise_errorf ~loc "[%%%%primrec] requires at least one parameter";
  let param_bindings =
    List.map
      (fun pat ->
        match pat.ppat_desc with
        | Ppat_constraint ({ ppat_desc = Ppat_var { txt = name; _ }; _ }, ct) ->
            (name, ct)
        | _ ->
            Location.raise_errorf ~loc:pat.ppat_loc
              "[%%%%primrec] parameters must be annotated: (x : ty)")
      params
  in
  (* The body must be a match expression *)
  let scrutinee, cases =
    match match_body.pexp_desc with
    | Pexp_match (scr, cases) -> (scr, cases)
    | _ ->
        Location.raise_errorf ~loc:match_body.pexp_loc
          "[%%%%primrec] body must be a match expression"
  in
  (* The scrutinee must be a parameter (first param expected) *)
  let scr_name =
    match scrutinee.pexp_desc with
    | Pexp_ident { txt = Lident name; _ } -> name
    | _ ->
        Location.raise_errorf ~loc:scrutinee.pexp_loc
          "[%%%%primrec] match scrutinee must be a parameter name"
  in
  let scr_param_idx =
    match List.find_index (fun (name, _) -> name = scr_name) param_bindings with
    | Some i -> i
    | None ->
        Location.raise_errorf ~loc:scrutinee.pexp_loc
          "[%%%%primrec] match scrutinee must be one of the parameters"
  in
  if scr_param_idx <> 0 then
    Location.raise_errorf ~loc:scrutinee.pexp_loc
      "[%%%%primrec] recursion on non-first parameter not yet supported";
  let _scr_ct = snd (List.nth param_bindings 0) in
  let non_rec_params = List.filteri (fun i _ -> i <> 0) param_bindings in
  let ind_type_name, _ =
    extract_match_type_info ~loc:scrutinee.pexp_loc
      ~env:(List.map (fun (n, ct) -> (n, Annotated ct)) param_bindings)
      scrutinee
  in
  (* Build the inductive type expression (raw, for runtime comparison) *)
  let ind_ty_expr = translate_type_raw ~loc _scr_ct in
  (* Build the expanded return type: non_rec_param_types -> ret_type *)
  let expanded_ret_type_expr =
    List.fold_right
      (fun (_, ct) acc ->
        A.eapply (A.evar "make_fun_ty") [ translate_type_raw ~loc ct; acc ])
      non_rec_params
      (translate_type_raw ~loc ret_type)
  in
  (* Build the scrutinee type for tysub computation *)
  let scr_type_expr = translate_type_raw ~loc _scr_ct in
  (* Build non-rec param variables at runtime *)
  let nrp_data =
    List.mapi
      (fun i (name, ct) ->
        let ty_v = fresh_id "nrpty" in
        let pv = fresh_id "nrpv" in
        (name, ct, i, ty_v, pv))
      non_rec_params
  in
  let tysub_v = fresh_id "tysub" in
  (* For each case, build a case term expression *)
  let case_exprs =
    List.map
      (fun case ->
        let con_name, pat_vars =
          match case.pc_lhs.ppat_desc with
          | Ppat_construct ({ txt = Lident cn; _ }, None) ->
              (normalize_con_name cn, [])
          | Ppat_construct ({ txt = Lident cn; _ }, Some (_, pat_arg)) ->
              (normalize_con_name cn, extract_match_pattern_vars pat_arg)
          | _ ->
              Location.raise_errorf ~loc:case.pc_lhs.ppat_loc
                "[%%%%primrec] unsupported pattern"
        in
        let n_pvars = List.length pat_vars in
        (* Generate OCaml names for pattern var types, HOL vars, and r vars *)
        let pv_data =
          List.mapi
            (fun i name ->
              let pty = fresh_id "prpty" in
              let pv = fresh_id "prpv" in
              let rv = fresh_id "prrv" in
              let r_ident = "_r_" ^ name in
              (name, i, pty, pv, rv, r_ident))
            pat_vars
        in
        (* Build rec_map for AST preprocessing: pat_var_name → r_ident *)
        let rec_map =
          List.map (fun (name, _, _, _, _, r_ident) -> (name, r_ident)) pv_data
        in
        (* Preprocess body to replace recursive calls *)
        let preprocessed_body = replace_rec_calls fn_name rec_map case.pc_rhs in
        (* Build env for body translation *)
        let env =
          List.map
            (fun (name, _, pty, _, _, _) -> (name, Runtime (pty, None)))
            pv_data
          @ List.map
              (fun (_, _, _, _, rv, r_ident) -> (r_ident, Prebuilt rv))
              pv_data
          @ List.map
              (fun (name, ct, _, _ty_v, _pv) -> (name, Annotated ct))
              nrp_data
        in
        (* Translate preprocessed body *)
        let body_expr = translate_expr ~loc ~env preprocessed_body in
        let body_v = fresh_id "prbody" in
        (* Generate runtime code *)
        let ind_ty_v = fresh_id "indty" in
        let ret_ty_v = fresh_id "retty" in
        let atys_v = fresh_id "pratys" in
        (* Build the case term construction *)
        (* Instantiate type variables in body (e.g., None : a option → None : nat option) *)
        let body_inst_v = fresh_id "prbinst" in
        let body_inst_expr =
          A.pexp_match
            (A.eapply (A.evar "Kernel.type_of_term") [ A.evar body_v ])
            [
              A.case
                ~lhs:
                  (A.ppat_construct { txt = Lident "Ok"; loc }
                     (Some (A.pvar "_bty")))
                ~guard:None
                ~rhs:
                  (A.pexp_let Nonrecursive
                     [
                       A.value_binding ~pat:(A.pvar "_leaf")
                         ~expr:
                           (A.eapply
                              (A.evar "Heft.Printing.leaf_type")
                              [ A.evar "_bty" ]);
                     ]
                     (A.pexp_match
                        (A.eapply
                           (A.evar "Heft.Rewrite.type_match")
                           [
                             A.elist [];
                             A.evar "_leaf";
                             A.eapply
                               (A.evar "Heft.Printing.leaf_type")
                               [ A.evar ret_ty_v ];
                           ])
                        [
                          A.case
                            ~lhs:
                              (A.ppat_construct
                                 { txt = Lident "Some"; loc }
                                 (Some (A.pvar "_bsub")))
                            ~guard:None
                            ~rhs:
                              (A.eapply
                                 (A.evar "Heft.Rewrite.term_type_subst")
                                 [ A.evar "_bsub"; A.evar body_v ]);
                          A.case
                            ~lhs:
                              (A.ppat_construct
                                 { txt = Lident "None"; loc }
                                 None)
                            ~guard:None ~rhs:(A.evar body_v);
                        ]));
              A.case
                ~lhs:
                  (A.ppat_construct
                     { txt = Lident "Error"; loc }
                     (Some (A.pvar "_")))
                ~guard:None ~rhs:(A.evar body_v);
            ]
        in
        let inner =
          mk_bind ~loc body_expr body_v
            (A.pexp_let Nonrecursive
               [
                 A.value_binding ~pat:(A.pvar body_inst_v) ~expr:body_inst_expr;
               ]
               (A.eapply (A.evar "Result.ok")
                  [
                    A.eapply
                      (A.evar "Heft.Printing.wrap_case_lambdas")
                      [
                        A.elist
                          (List.map
                             (fun (_, _, _, pv, _, _) -> A.evar pv)
                             pv_data);
                        A.eapply (A.evar "List.map")
                          [
                            A.evar "snd";
                            {
                              pexp_desc =
                                Pexp_apply
                                  ( A.evar "Heft.Printing.primrec_rec_info",
                                    [
                                      (Labelled "tysub", A.evar tysub_v);
                                      (Nolabel, A.estring con_name);
                                      (Nolabel, A.evar ind_ty_v);
                                      (Nolabel, A.evar ret_ty_v);
                                      ( Nolabel,
                                        A.elist
                                          (List.map
                                             (fun (name, _, _, _, _, _) ->
                                               A.estring name)
                                             pv_data) );
                                    ] );
                              pexp_loc = loc;
                              pexp_loc_stack = [];
                              pexp_attributes = [];
                            };
                          ];
                        A.elist
                          (List.map
                             (fun (_, _, _, _, pv) -> A.evar pv)
                             nrp_data);
                        A.evar body_inst_v;
                      ];
                  ]))
        in
        (* Wrap with r var creation *)
        let with_rvs =
          if n_pvars = 0 then inner
          else
            A.pexp_let Nonrecursive
              (List.map
                 (fun (name, _, _, _, rv, _) ->
                   A.value_binding ~pat:(A.pvar rv)
                     ~expr:
                       (A.eapply (A.evar "make_var")
                          [ A.estring ("_r_" ^ name); A.evar ret_ty_v ]))
                 pv_data)
              inner
        in
        (* Wrap with pattern var creation *)
        let with_pvs =
          if n_pvars = 0 then with_rvs
          else
            A.pexp_let Nonrecursive
              (List.map
                 (fun (name, _, pty, pv, _, _) ->
                   A.value_binding ~pat:(A.pvar pv)
                     ~expr:
                       (A.eapply (A.evar "make_var")
                          [ A.estring name; A.evar pty ]))
                 pv_data)
              with_rvs
        in
        (* Wrap with type lookups *)
        let with_tys =
          if n_pvars = 0 then with_pvs
          else
            A.pexp_let Nonrecursive
              (List.mapi
                 (fun i (_, _, pty, _, _, _) ->
                   A.value_binding ~pat:(A.pvar pty)
                     ~expr:
                       (A.eapply (A.evar "List.nth")
                          [ A.evar atys_v; A.eint i ]))
                 pv_data)
              with_pvs
        in
        let with_atys =
          if n_pvars = 0 then with_tys
          else
            A.pexp_let Nonrecursive
              [
                A.value_binding ~pat:(A.pvar atys_v)
                  ~expr:
                    {
                      pexp_desc =
                        Pexp_apply
                          ( A.evar "Heft.Printing.constructor_arg_types",
                            [
                              (Labelled "tysub", A.evar tysub_v);
                              (Nolabel, A.estring con_name);
                            ] );
                      pexp_loc = loc;
                      pexp_loc_stack = [];
                      pexp_attributes = [];
                    };
              ]
              with_tys
        in
        (* Wrap with ret_ty and ind_ty *)
        A.pexp_let Nonrecursive
          [
            A.value_binding ~pat:(A.pvar ind_ty_v) ~expr:ind_ty_expr;
            A.value_binding ~pat:(A.pvar ret_ty_v) ~expr:expanded_ret_type_expr;
          ]
          with_atys)
      cases
  in
  (* Unwrap each case term from Result *)
  let case_vars =
    List.mapi (fun i _ -> fresh_id (Printf.sprintf "case%d" i)) cases
  in
  (* nrp bindings are generated inline in the final expression *)
  (* Build the define_recursive_function call *)
  let ret_ty_outer = fresh_id "retty" in
  let define_call =
    A.eapply
      (A.evar "Heft.Inductive.define_recursive_function")
      [
        A.pexp_construct { txt = Lident "~tysub"; loc } (Some (A.evar tysub_v));
        A.estring fn_name;
        A.evar ret_ty_outer;
        A.estring ind_type_name;
        A.elist (List.map A.evar case_vars);
      ]
  in
  (* Hmm, labeled arguments don't work this way with eapply.
     Let me use a different approach for the optional tysub arg *)
  ignore define_call;
  let define_call =
    {
      pexp_desc =
        Pexp_apply
          ( A.evar "Heft.Inductive.define_recursive_function",
            [
              (Labelled "tysub", A.evar tysub_v);
              (Nolabel, A.estring fn_name);
              (Nolabel, A.evar ret_ty_outer);
              (Nolabel, A.estring ind_type_name);
              (Nolabel, A.elist (List.map A.evar case_vars));
            ] );
      pexp_loc = loc;
      pexp_loc_stack = [];
      pexp_attributes = [];
    }
  in
  (* Chain: non-rec param lets, then case term bindings, then define call *)
  let case_chain =
    List.fold_right
      (fun (cv, ce) acc -> mk_bind ~loc ce cv acc)
      (List.combine case_vars case_exprs)
      define_call
  in
  (* Wrap nrp bindings sequentially (each pv depends on its ty_v) *)
  let with_nrp =
    List.fold_right
      (fun (name, ct, _, ty_v, pv) acc ->
        A.pexp_let Nonrecursive
          [
            A.value_binding ~pat:(A.pvar ty_v)
              ~expr:(translate_type_raw ~loc ct);
          ]
          (A.pexp_let Nonrecursive
             [
               A.value_binding ~pat:(A.pvar pv)
                 ~expr:
                   (A.eapply (A.evar "make_var")
                      [ A.estring name; A.evar ty_v ]);
             ]
             acc))
      nrp_data case_chain
  in
  let inner =
    A.pexp_let Nonrecursive
      [
        A.value_binding ~pat:(A.pvar tysub_v)
          ~expr:
            (A.pexp_match
               (A.eapply
                  (A.evar "Heft.Rewrite.type_match")
                  [
                    A.elist [];
                    A.pexp_field
                      (A.eapply (A.evar "Hashtbl.find")
                         [
                           A.evar "Kernel.the_inductives";
                           A.estring ind_type_name;
                         ])
                      { txt = Lident "ty"; loc };
                    scr_type_expr;
                  ])
               [
                 A.case
                   ~lhs:
                     (A.ppat_construct
                        { txt = Lident "Some"; loc }
                        (Some (A.pvar "_sub")))
                   ~guard:None ~rhs:(A.evar "_sub");
                 A.case
                   ~lhs:(A.ppat_construct { txt = Lident "None"; loc } None)
                   ~guard:None ~rhs:(A.elist []);
               ]);
        A.value_binding ~pat:(A.pvar ret_ty_outer) ~expr:expanded_ret_type_expr;
      ]
      with_nrp
  in
  let unwrapped = A.eapply (A.evar "Heft.Printing.unwrap_thm") [ inner ] in
  A.pstr_value Nonrecursive
    [ A.value_binding ~pat:(A.pvar fn_name) ~expr:unwrapped ]

let thm_attrs = [ "simp"; "quiet"; "trace" ]

(* Shared core: given bindings, returns (thm_name, generated_expr).
   For goal-only, the expr is make_goal(...).
   For with-proof, the expr is let _goal = make_goal(...) in run_proof ...; _goal *)
let translate_thm_bindings ~loc bindings =
  let (module A) = Ast_builder.make loc in
  let goal_binding = List.hd bindings in
  let thm_name =
    match goal_binding.pvb_pat.ppat_desc with
    | Ppat_var { txt = name; _ } -> name
    | _ ->
        Location.raise_errorf ~loc:goal_binding.pvb_pat.ppat_loc
          "[%%%%thm] expects a simple name"
  in
  let params, body =
    match extract_fun_params_and_body goal_binding.pvb_expr with
    | Some (pats, body) -> (pats, body)
    | None -> ([], goal_binding.pvb_expr)
  in
  let param_bindings =
    List.map
      (fun pat ->
        match pat.ppat_desc with
        | Ppat_constraint ({ ppat_desc = Ppat_var { txt = name; _ }; _ }, ct) ->
            (name, ct)
        | _ ->
            Location.raise_errorf ~loc:pat.ppat_loc
              "[%%%%thm] parameters must have type annotations: (x : ty)")
      params
  in
  let env = List.map (fun (name, ct) -> (name, Annotated ct)) param_bindings in
  let body_expr = translate_expr ~loc ~env body in
  let goal_term =
    List.fold_right
      (fun (name, ct) inner_expr ->
        let ty_var, ty_expr = translate_type ~loc ct in
        let var_expr =
          A.eapply (A.evar "make_var") [ A.estring name; A.evar ty_var ]
        in
        let body_var = fresh_id "body" in
        mk_bind ~loc ty_expr ty_var
          (mk_bind ~loc inner_expr body_var
             (A.eapply (A.evar "Result.ok")
                [
                  A.eapply (A.evar "make_forall") [ var_expr; A.evar body_var ];
                ])))
      param_bindings body_expr
  in
  let unwrapped_goal =
    A.eapply (A.evar "Heft.Printing.unwrap_term") [ goal_term ]
  in
  let save_name = not (String.length thm_name > 0 && thm_name.[0] = '_') in
  let expr =
    match bindings with
    | [ _ ] -> A.eapply (A.evar "make_goal") [ unwrapped_goal ]
    | [ _; proof_binding ] ->
        let proof_name =
          match proof_binding.pvb_pat.ppat_desc with
          | Ppat_var { txt = name; _ } -> name
          | _ ->
              Location.raise_errorf ~loc:proof_binding.pvb_pat.ppat_loc
                "[%%%%thm] second binding must be named 'proof'"
        in
        if proof_name <> "proof" then
          Location.raise_errorf ~loc:proof_binding.pvb_pat.ppat_loc
            "[%%%%thm] second binding must be named 'proof', got '%s'"
            proof_name;
        let tactic_expr = proof_binding.pvb_expr in
        let has_attr name expr =
          List.exists
            (fun (attr : attribute) -> attr.attr_name.txt = name)
            expr.pexp_attributes
        in
        let has_simp = has_attr "simp" tactic_expr in
        let has_quiet = has_attr "quiet" tactic_expr in
        let has_trace = has_attr "trace" tactic_expr in
        let clean_tactic =
          {
            tactic_expr with
            pexp_attributes =
              List.filter
                (fun (attr : attribute) ->
                  not (List.mem attr.attr_name.txt thm_attrs))
                tactic_expr.pexp_attributes;
          }
        in
        let goal_var = fresh_id "goal" in
        let bool_true = A.pexp_construct { txt = Lident "true"; loc } None in
        let args =
          (if save_name then [ (Labelled "name", A.estring thm_name) ] else [])
          @ (if has_simp then [ (Labelled "simp", bool_true) ] else [])
          @ (if has_quiet then [ (Labelled "quiet", bool_true) ] else [])
          @ (if has_trace then
               [
                 ( Labelled "notrace",
                   A.pexp_construct { txt = Lident "false"; loc } None );
               ]
             else [])
          @ [ (Nolabel, A.evar goal_var); (Nolabel, clean_tactic) ]
        in
        let run_proof_expr = A.pexp_apply (A.evar "run_proof") args in
        A.pexp_let Nonrecursive
          [
            A.value_binding ~pat:(A.pvar goal_var)
              ~expr:(A.eapply (A.evar "make_goal") [ unwrapped_goal ]);
          ]
          (A.pexp_sequence run_proof_expr (A.evar goal_var))
    | _ ->
        Location.raise_errorf ~loc
          "[%%%%thm] expects one or two bindings (goal, and optionally 'proof')"
  in
  (thm_name, expr)

let translate_thm ~(loc : location) ~(path : label)
    (payload : structure_item list) =
  let (module A) = Ast_builder.make loc in
  let _ = path in
  let bindings =
    match payload with
    | [ { pstr_desc = Pstr_value (_, bindings); _ } ] -> bindings
    | _ -> Location.raise_errorf ~loc "[%%%%thm] expects let bindings"
  in
  let thm_name, expr = translate_thm_bindings ~loc bindings in
  A.pstr_value Nonrecursive [ A.value_binding ~pat:(A.pvar thm_name) ~expr ]

let translate_thm_expr ~(loc : location) ~(path : label) (input : expression) =
  let (module A) = Ast_builder.make loc in
  let _ = path in
  match input.pexp_desc with
  | Pexp_let (_, bindings, body) ->
      let thm_name, expr = translate_thm_bindings ~loc bindings in
      A.pexp_let Nonrecursive
        [ A.value_binding ~pat:(A.pvar thm_name) ~expr ]
        body
  | _ -> Location.raise_errorf ~loc "[%%%%thm] expects a let binding"

let term_extension =
  Extension.declare "term" Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    translate

let inductive_extension =
  Extension.declare "inductive" Extension.Context.structure_item
    Ast_pattern.(pstr __)
    translate_inductive

let def_extension =
  Extension.declare "def" Extension.Context.structure_item
    Ast_pattern.(pstr __)
    translate_def

let primrec_extension =
  Extension.declare "primrec" Extension.Context.structure_item
    Ast_pattern.(pstr __)
    translate_primrec

let thm_extension =
  Extension.declare "thm" Extension.Context.structure_item
    Ast_pattern.(pstr __)
    translate_thm

let thm_expr_extension =
  Extension.declare "thm" Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    translate_thm_expr

let () =
  Driver.register_transformation "heft_ppx"
    ~rules:
      [
        Context_free.Rule.extension term_extension;
        Context_free.Rule.extension inductive_extension;
        Context_free.Rule.extension def_extension;
        Context_free.Rule.extension primrec_extension;
        Context_free.Rule.extension thm_extension;
        Context_free.Rule.extension thm_expr_extension;
      ]
