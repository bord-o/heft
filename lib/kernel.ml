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

let (vsubst : (term * term) list ->
term ->
(term,
 [> `BadSubstitutionList of Lexing.position
  | `CantCreateVariantForNonVariable of term * Lexing.position ])
result) =
  let rec vsubst ilist tm =
    match tm with
    | Var (_, _) ->
        Ok
          (ilist
          |> List.map (fun (a, b) -> (b, a))
          |> List.assoc_opt tm |> Option.value ~default:tm)
    | Const (_, _) -> Ok tm
    | App (s, t) ->
        let* s' = vsubst ilist s and* t' = vsubst ilist t in
        if s' == s && t' == t then Ok tm else Ok (App (s', t'))
    | Lam (v, s) ->
        let ilist' = List.filter (fun (t, x) -> x <> v) ilist in
        if ilist' = [] then Ok tm
        else
          let* s' = vsubst ilist' s in
          if s' == s then Ok tm
          else if
            List.exists
              (fun (t, x) -> var_free_in v t && var_free_in x s)
              ilist'
          then
            let* v' = variant [ s' ] v in
            let* substitued = vsubst ((v', v) :: ilist') s in

            Ok (Lam (v', substitued))
          else Ok (Lam (v, s'))
  in
  fun theta ->
    if theta = [] then fun tm -> Ok tm
    else if
      let univ arg =
        Result.value
          ((function
             | t, Var (_, y) ->
                 let* tty = type_of_term t in
                 Ok (compare tty y = 0)
             | _ -> Ok false)
             arg)
          ~default:false
      in
      List.for_all univ theta
    then vsubst theta
    else fun _ -> Error (`BadSubstitutionList [%here])

let (inst : (hol_type, hol_type) Hashtbl.t ->
term ->
(term,
 [> `Bad
  | `BadSubstitutionList of Lexing.position
  | `CantCreateVariantForNonVariable of term * Lexing.position
  | `Clash of term * Lexing.position
  | `NotAVar of Lexing.position ])
result) =
  let rec inst env tyin tm =
    match tm with
    | Var (n, ty) ->
        let ty' = type_substitution tyin ty in
        let tm' = if ty' == ty then tm else Var (n, ty') in
        if
          compare
            (env
            |> List.map (fun (a, b) -> (b, a))
            |> List.assoc_opt tm |> Option.value ~default:tm)
            tm
          = 0
        then Ok tm'
        else Error (`Clash (tm', [%here]))
    | Const (c, ty) ->
        let ty' = type_substitution tyin ty in
        if ty' == ty then Ok tm else Ok (Const (c, ty'))
    | App (f, x) ->
        let* f' = inst env tyin f and* x' = inst env tyin x in
        if f' == f && x' == x then Ok tm else Ok (App (f', x'))
    | Lam (y, t) -> (
        let* y' = inst [] tyin y in
        let env' = (y, y') :: env in
        match inst env' tyin t with
        | Ok t' ->
            let* t' = inst env' tyin t in
            if y' == y && t' == t then Ok tm else Ok (Lam (y', t'))
        | Error (`Clash (w', _)) as err ->
            if w' <> y' then err
            else
              let* ifrees =
                List.fold_left
                  (fun acc a ->
                    match (acc, inst [] tyin a) with
                    | Ok nacc, Ok na -> Ok (na :: nacc)
                    | _ -> Error `Bad)
                  (Ok []) (frees t)
              in
              let* y'' = variant ifrees y' in
              let* dyy = destruct_var y'' in
              let* dy = destruct_var y in
              let z = Var (fst dyy, snd dy) in
              let* subst = vsubst [ (z, y) ] t in
              inst env tyin (Lam (z, subst))
        | Error e -> Error e)
  in
  fun tyin -> if Hashtbl.length tyin = 0 then fun tm -> Ok tm else inst [] tyin

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
