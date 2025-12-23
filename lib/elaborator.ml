(* take an AST produce some HOL *)
open Ast
open Kernel
open Result.Syntax

let rec hol_of_typ (t : typ) : hol_type =
  match t with
  | TyVar n -> Kernel.TyVar n
  | TyCon (name, args) -> Kernel.TyCon (name, List.map hol_of_typ args)
  | TyArr (l, r) -> Kernel.make_fun_ty (hol_of_typ l) (hol_of_typ r)

let hol_of_constructor (c : constructor) : constructor_spec =
  let name, typs = c in
  { name; arg_types = typs |> List.map hol_of_typ }

let hol_of_type_def (td : type_def) =
  let* def =
    Inductive.define_inductive td.name td.params
      (td.constructors |> List.map hol_of_constructor)
  in
  Ok def.ty

let hol_of_term t = failwith "TODO"
let hol_of_def d = failwith "TODO"
let hol_of_fun_def fd = failwith "TODO"
let hol_of_theorem t = failwith "TODO"
let elaborate (defs : toplevel list) = defs
