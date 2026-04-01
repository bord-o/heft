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
      let final = A.eapply (A.evar "make_type") [ A.estring name; A.elist (List.map A.evar arg_vars) ] in
      let wrapped = List.fold_right (fun (var, expr) acc -> mk_bind ~loc expr var acc) bindings final in
      (v, wrapped)
  | Ptyp_arrow (_, l, r) ->
      let lv, le = translate_type ~loc l in
      let rv, re = translate_type ~loc r in
      let v = fresh_id "ty" in
      let final = A.eapply (A.evar "make_fun_ty") [ A.evar lv; A.evar rv ] in
      let wrapped = mk_bind ~loc le lv (mk_bind ~loc re rv final) in
      (v, wrapped)
  | Ptyp_var name ->
      let v = fresh_id "ty" in
      (v, A.eapply (A.evar "Result.ok") [ A.eapply (A.evar "make_vartype") [ A.estring name ] ])
  | _ -> Location.raise_errorf ~loc:(ct.ptyp_loc) "unsupported type"

and translate_type_args ~loc args =
  let results = List.map (translate_type ~loc) args in
  let bindings = List.map (fun (v, e) -> (v, e)) results in
  let vars = List.map fst results in
  (bindings, vars)

let translate ~(loc : location) ~(path : label) (input : expression) =
  let (module A) = Ast_builder.make loc in
  let _ = path in
  let inner = match input.pexp_desc with
    | Pexp_constraint
        ({ pexp_desc = Pexp_ident { txt = Lident name; _ }; _ }, core_type) ->
        let ty_var, ty_expr = translate_type ~loc core_type in
        mk_bind ~loc ty_expr ty_var
          (A.eapply (A.evar "Result.ok")
            [ A.eapply (A.evar "make_var") [ A.estring name; A.evar ty_var ] ])
    | Pexp_ident { txt = Lident name; _ } ->
        A.eapply (A.evar "make_const") [ A.estring name; A.elist [] ]
    | _ -> Location.raise_errorf ~loc "expected an identifier"
  in
  A.eapply (A.evar "Heft.Printing.unwrap_term") [ inner ]

let extension =
  Extension.declare "term" Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    translate

let () =
  Driver.register_transformation "term"
    ~rules:[ Context_free.Rule.extension extension ]
