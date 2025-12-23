(* take an AST produce some HOL *)
open Ast
open Kernel
open Result.Syntax
open Inductive_theorems

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

(*create a hol term from this*)
let rec hol_of_term ?(type_env = []) (t : Ast.term) :
    (Kernel.term, Kernel.kernel_error) result =
  match t with
  | Var name -> (
      match List.assoc_opt name type_env with
      | Some ty -> Ok (Kernel.make_var name ty)
      | None -> Error Kernel.NotAVar)
  | Con name -> (
      match Kernel.get_const_term_type name with
      | Some _ty -> Kernel.make_const name (Hashtbl.create 0)
      | None -> Error (Kernel.NotAConstantName name))
  | App (f, a) ->
      let* f_term = hol_of_term ~type_env f in
      let* a_term = hol_of_term ~type_env a in
      Kernel.make_app f_term a_term
  | Lam (var, body) ->
      (* Need to infer type - for now use a placeholder *)
      let var_ty = Kernel.TyVar ("'a" ^ string_of_int (Random.int 1000)) in
      let var_term = Kernel.make_var var var_ty in
      let new_env = (var, var_ty) :: type_env in
      let* body_term = hol_of_term ~type_env:new_env body in
      Kernel.make_lam var_term body_term
  | Let (var, value, body) ->
      (* Let x = e1 in e2 becomes (\x. e2) e1 *)
      let* value_term = hol_of_term ~type_env value in
      let* value_ty = Kernel.type_of_term value_term in
      let var_term = Kernel.make_var var value_ty in
      let new_env = (var, value_ty) :: type_env in
      let* body_term = hol_of_term ~type_env:new_env body in
      let* lambda = Kernel.make_lam var_term body_term in
      Kernel.make_app lambda value_term
  | If (cond, then_branch, else_branch) ->
      let* _cond_term = hol_of_term ~type_env cond in
      let* then_term = hol_of_term ~type_env then_branch in
      let* _else_term = hol_of_term ~type_env else_branch in
      (* For now, just return the then_branch - proper conditional needs more setup *)
      Ok then_term
  | Forall (var, body) ->
      let var_ty = Kernel.TyVar ("'a" ^ string_of_int (Random.int 1000)) in
      let var_term = Kernel.make_var var var_ty in
      let new_env = (var, var_ty) :: type_env in
      let* body_term = hol_of_term ~type_env:new_env body in
      let* lambda = Kernel.make_lam var_term body_term in
      (* For now, just return the lambda - proper forall needs more setup *)
      Ok lambda
  | Ann (term, typ) ->
      let* term_hol = hol_of_term ~type_env term in
      let expected_ty = hol_of_typ typ in
      let* actual_ty = Kernel.type_of_term term_hol in
      if compare actual_ty expected_ty = 0 then Ok term_hol
      else Error (Kernel.MakeAppTypesDontAgree (actual_ty, expected_ty))

(*define a constant from this*)
let hol_of_def d =
  let* _term_hol = hol_of_term d.body in
  let ty_hol = hol_of_typ d.typ in
  let* _ = Kernel.new_constant d.name ty_hol in
  Ok ()

let rec result_type_of_fun_ty = function
    | TyCon ("fun", [_; ret]) -> (result_type_of_fun_ty ret)
    | TyCon _ as t -> t
    | TyVar _ as t -> t


(*define a recursive function from this*)
(* type fun_def = { name : string; typ : typ; equations : equation list } *)
let hol_of_fun_def (fd : fun_def) =
  let ty_hol = hol_of_typ fd.typ in
  let res_ty = result_type_of_fun_ty ty_hol in
  print_endline @@ show_hol_type  res_ty;

  let branches = [] in

  let* _d = define_recursive_function fd.name res_ty branches in
  
  Ok ()

(* this just wraps hol_of_term for now, I'll add handling later *)
let hol_of_theorem t =
  let* statement = hol_of_term t.statement in
  Ok statement

(*This iterates through and calls the above functions*)
let rec elaborate = function
  | [] -> Ok ()
  | TypeDef td :: defs ->
      let* _ = hol_of_type_def td in
      elaborate defs
  | Def d :: defs ->
      let* _ = hol_of_def d in
      elaborate defs
  | Fun fd :: defs ->
      let* _ = hol_of_fun_def fd in
      elaborate defs
  | Theorem t :: defs ->
      let* _ = hol_of_theorem t in
      elaborate defs
