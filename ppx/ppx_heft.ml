open Ppxlib

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
      | Some core_type ->
          let ty_var, ty_expr = translate_type ~loc core_type in
          mk_bind ~loc ty_expr ty_var
            (A.eapply (A.evar "Result.ok")
               [
                 A.eapply (A.evar "make_var") [ A.estring name; A.evar ty_var ];
               ])
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
  (* Application *)
  | Pexp_apply (func, args) -> translate_apply ~loc ~env func args
  | _ -> Location.raise_errorf ~loc "unsupported expression in [%%term]"

and translate_lambda ~loc ~env pats body =
  let (module A) = Ast_builder.make loc in
  match pats with
  | [] -> translate_expr ~loc ~env body
  | pat :: rest ->
      let name, core_type = extract_pat_binding pat in
      let env = (name, core_type) :: env in
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
      let env = (name, core_type) :: env in
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

let translate ~(loc : location) ~(path : label) (input : expression) =
  let (module A) = Ast_builder.make loc in
  let _ = path in
  let inner = translate_expr ~loc ~env:[] input in
  A.eapply (A.evar "Heft.Printing.unwrap_term") [ inner ]

let extension =
  Extension.declare "term" Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    translate

let () =
  Driver.register_transformation "term"
    ~rules:[ Context_free.Rule.extension extension ]
