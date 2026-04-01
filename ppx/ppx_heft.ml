open Ppxlib

let convert ~(loc : location) ~(path : label) (input : expression) =
  let (module A) = Ast_builder.make loc in
  let _ = path in
  match input.pexp_desc with
  | Pexp_ident { txt = Lident name; _ } ->
      A.eapply (A.evar "String.length") [ A.estring name ]
  | _ -> Location.raise_errorf ~loc "expected an identifier"

let extension =
  Extension.declare "heft" Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    convert

let () =
  Driver.register_transformation "heft"
    ~rules:[ Context_free.Rule.extension extension ]
