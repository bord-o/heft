(*

A HOL kernel, closely following the approach of HOL light.

Where possible the code will follow a more modern OCaml approach.

Explicit inductive definitions are the only kernel extension, in order to avoid lots of manual derivation

*)

type hol_type = TyVar of string | TyCon of string * hol_type list

type term =
  | Var of string * hol_type
  | Const of string * hol_type
  | App of term * term
  | Lam of term * term

type thm = Sequent of term list * term

type inductive_def = {
  name : string;
  ty_params : string list;
  constructors : string list;
  induction : thm;
  recursion : thm;
  distinct : thm list;
  injective : thm list;
}

let the_type_constants : (string, int) Hashtbl.t = Hashtbl.create 512
let the_term_constants : (string, hol_type) Hashtbl.t = Hashtbl.create 512
let the_inductives : (string, inductive_def list) Hashtbl.t = Hashtbl.create 512
let the_axioms : thm list ref = ref []
let the_definitions : thm list ref = ref []
let bool_ty = TyCon ("bool", [])
let aty = TyVar "A"

let () =
  Hashtbl.add the_term_constants "="
    (TyCon ("fun", [ aty; TyCon ("fun", [ aty; bool_ty ]) ]))

let get_type_arity typ = Hashtbl.find_opt the_type_constants typ

(* add a type to the type constants table *)
let new_type name arity =
  match get_type_arity name with
  | Some _ -> Error (`TypeAlreadyDeclared (name, [%here]))
  | None -> Ok (Hashtbl.add the_type_constants name arity)

(* for constructing types *)
let make_type name args =
  match Hashtbl.find_opt the_type_constants name with
  | None -> Error (`TypeNotDeclared name)
  | Some arity when arity = List.length args -> Ok (TyCon (name, args))
  | Some other_arity ->
      Error
        (`WrongNumberOfTypeArgs
           (Format.sprintf "%s: expected %i args, found %i" name
              (List.length args) other_arity))

let make_vartype name = TyVar name

let destruct_type = function
  | TyCon (s, ty) -> Ok (s, ty)
  | TyVar name -> Error (`TypeVariableNotAConstructor (name, [%here]))

let destruct_vartype = function
  | TyCon (name, _) -> Error (`TypeConstructorNotAVariable (name, [%here]))
  | TyVar name -> Ok name

let is_type = function TyCon _ -> true | _ -> false
let is_vartype = function TyVar _ -> true | _ -> false

(*TODO: check equivalence *)
let rec type_vars = function
  | TyCon (_, args) ->
      List.fold_left (fun acc a -> acc @ type_vars a) [] args
      |> List.sort_uniq compare
  | TyVar _ as tv -> [ tv ]

let rec type_substitution type_consts typ =
  match typ with
  | TyCon (tycon, args) ->
      let args' = List.map (type_substitution type_consts) args in
      if args' == args then typ else TyCon (tycon, args')
  | _ -> Hashtbl.find_opt type_consts typ |> Option.value ~default:typ

let get_const_term_type name = Hashtbl.find_opt the_term_constants name

let new_constant name typ =
  match get_const_term_type name with
  | Some name -> Error (`ConstantTermAlreadyDeclared (name, [%here]))
  | None -> Ok (Hashtbl.add the_term_constants name typ)

open Result.Syntax

let rec type_of_term = function
  | Var (_, ty) -> Ok ty
  | Const (_, ty) -> Ok ty
  | App (s, _) -> (
      let* sty = type_of_term s in
      match sty with
      | TyCon ("fun", [ _dty; rty ]) -> Ok rty
      | _ -> Error (`CantApplyNonFunctionType (s, [%here])))
  | Lam (Var (_, ty), t) ->
      let* rty = type_of_term t in
      Ok (TyCon ("fun", [ ty; rty ]))
  | _ -> failwith "inv"

let is_var = function Var (_, _) -> true | _ -> false
let is_const = function Const (_, _) -> true | _ -> false
let is_abs = function Lam (_, _) -> true | _ -> false
let is_comb = function App (_, _) -> true | _ -> false
let make_var (v, ty) = Var (v, ty)

let make_const name theta =
  let* uty =
    get_const_term_type name
    |> Option.to_result ~none:(`NotAConstantName (name, [%here]))
  in
  Ok (Const (name, type_substitution theta uty))

let make_lam bvar body =
  match bvar with
  | Var (_, _) -> Ok (Lam (bvar, body))
  | _ -> Error (`MakeLamNotAVariable (bvar, [%here]))

let make_app f a =
  let* fty = type_of_term f in
  let* aty = type_of_term a in
  match fty with
  | TyCon ("fun", [ ty; _ ]) when compare ty aty = 0 -> Ok (App (f, a))
  | _ -> Error (`MkAppTypesDontAgree (fty, aty, [%here]))

let destruct_var = function
  | Var (s, ty) -> Ok (s, ty)
  | _ -> Error (`NotAVar [%here])

let destruct_const = function
  | Const (s, ty) -> Ok (s, ty)
  | _ -> Error (`NotAConst [%here])

let destruct_app = function
  | App (f, x) -> Ok (f, x)
  | _ -> Error (`NotAnApp [%here])

let destruct_lam = function
  | Lam (v, b) -> Ok (v, b)
  | _ -> Error (`NotALam [%here])

let rec frees = function
  | Var (_, _) as tm -> [ tm ]
  | Const (_, _) -> []
  | Lam (bv, bod) ->
      let body_frees = frees bod in
      List.filter (( <> ) bv) body_frees
  | App (s, t) ->
      let t_frees = frees t in
      let s_frees = frees s in
      List.append s_frees t_frees |> List.sort_uniq compare

let frees_in_list terms =
  let rec aux acc = function [] -> acc | x :: xs -> aux (acc @ frees x) xs in
  aux [] terms |> List.sort_uniq compare

let rec all_frees_within acc = function
  | Var (_, _) as tm -> List.mem tm acc
  | Const (_, _) -> true
  | Lam (bv, bod) -> all_frees_within (bv :: acc) bod
  | App (s, t) -> all_frees_within acc s && all_frees_within acc t

let rec var_free_in v tm =
  match tm with
  | Lam (bv, bod) -> v <> bv && var_free_in v bod
  | App (s, t) -> var_free_in v s || var_free_in v t
  | _ -> compare tm v = 0

let rec type_vars_in_term tm =
  match tm with
  | Var (_, ty) -> Ok (type_vars ty)
  | Const (_, ty) -> Ok (type_vars ty)
  | App (s, t) ->
      let* sty = type_vars_in_term s in
      let* tty = type_vars_in_term t in
      Ok (sty @ tty |> List.sort_uniq compare)
  | Lam (Var (_, ty), t) ->
      let* tty = type_vars_in_term t in
      Ok (type_vars ty @ tty |> List.sort_uniq compare)
  | Lam (_, _) -> Error (`UnexpectedLambdaForm [%here])

let rec variant avoid v =
  if not (List.exists (var_free_in v) avoid) then Ok v
  else
    match v with
    | Var (s, ty) -> variant avoid (Var (s ^ "'", ty))
    | _ -> Error (`CantCreateVariantForNonVariable (v, [%here]))

(* Helpers *)
let rev_assoc_default key alist ~default =
  let flipped = List.map (fun (a, b) -> (b, a)) alist in
  List.assoc_opt key flipped |> Option.value ~default

let is_valid_subst_pair (replacement, target) =
  match target with
  | Var (_, target_ty) -> (
      match type_of_term replacement with
      | Ok replacement_ty -> compare replacement_ty target_ty = 0
      | Error _ -> false)
  | _ -> false

let is_valid_substitution theta = List.for_all is_valid_subst_pair theta

let map_results f lst =
  List.fold_right
    (fun x acc ->
      match (acc, f x) with
      | Ok xs, Ok x' -> Ok (x' :: xs)
      | Error e, _ -> Error e
      | _, Error e -> Error e)
    lst (Ok [])

(* Variable substitution *)
let rec vsubst theta tm =
  let rec aux subst_list term =
    match term with
    | Var _ -> Ok (rev_assoc_default term subst_list ~default:term)
    | Const _ -> Ok term
    | App (func, arg) ->
        let* func' = aux subst_list func and* arg' = aux subst_list arg in
        if func' == func && arg' == arg then Ok term else Ok (App (func', arg'))
    | Lam (bound_var, body) ->
        let subst_list' =
          List.filter (fun (_, target) -> target <> bound_var) subst_list
        in
        if subst_list' = [] then Ok term
        else
          let* body' = aux subst_list' body in
          if body' == body then Ok term
          else if needs_renaming bound_var body subst_list' then
            let* renamed_var = variant [ body' ] bound_var in
            let* renamed_body =
              aux ((renamed_var, bound_var) :: subst_list') body
            in
            Ok (Lam (renamed_var, renamed_body))
          else Ok (Lam (bound_var, body'))
  in
  if theta = [] then Ok tm
  else if is_valid_substitution theta then aux theta tm
  else Error (`BadSubstitutionList [%here])

and needs_renaming bound_var body subst_list =
  List.exists
    (fun (replacement, target) ->
      var_free_in bound_var replacement && var_free_in target body)
    subst_list

(* Type instantiation *)
let inst tyin tm =
  let rec go env term =
    match term with
    | Var (name, ty) ->
        let ty' = type_substitution tyin ty in
        let term' = if ty' == ty then term else Var (name, ty') in
        let lookup_result = rev_assoc_default term' env ~default:term in
        if compare lookup_result term = 0 then Ok term'
        else Error (`Clash (term', [%here]))
    | Const (name, ty) ->
        let ty' = type_substitution tyin ty in
        if ty' == ty then Ok term else Ok (Const (name, ty'))
    | App (func, arg) ->
        let* func' = go env func and* arg' = go env arg in
        if func' == func && arg' == arg then Ok term else Ok (App (func', arg'))
    | Lam (bound_var, body) -> (
        let* bound_var' = go [] bound_var in
        let env' = (bound_var, bound_var') :: env in
        match go env' body with
        | Ok body' ->
            if bound_var' == bound_var && body' == body then Ok term
            else Ok (Lam (bound_var', body'))
        | Error (`Clash (clashing_var, _)) when clashing_var = bound_var' ->
            handle_lam_clash env bound_var bound_var' body
        | Error e -> Error e)
  and handle_lam_clash env original_var instantiated_var body =
    let* free_vars_instantiated = map_results (go []) (frees body) in
    let* renamed_var = variant free_vars_instantiated instantiated_var in
    let* renamed_name, _ = destruct_var renamed_var in
    let* _, original_ty = destruct_var original_var in
    let fresh_var = Var (renamed_name, original_ty) in
    let* substituted_body = vsubst [ (fresh_var, original_var) ] body in
    go env (Lam (fresh_var, substituted_body))
  in
  if Hashtbl.length tyin = 0 then Ok tm else go [] tm

let rator tm =
  match tm with
  | App (l, _) -> Ok l
  | _ -> Error (`NotAnApplication (tm, [%here]))

let rand tm =
  match tm with
  | App (_, r) -> Ok r
  | _ -> Error (`NotAnApplication (tm, [%here]))

let safe_make_eq l r =
  let* ty = type_of_term l in
  Ok
    (App
       ( App
           ( Const ("=", TyCon ("fun", [ ty; TyCon ("fun", [ ty; bool_ty ]) ])),
             l ),
         r ))

let destruct_eq tm =
  match tm with
  | App (App (Const ("=", _), l), r) -> Ok (l, r)
  | _ -> Error (`CantDestructEquality [%here])
