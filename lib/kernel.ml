(*

Where possible the code will follow a more modern OCaml approach.

Explicit inductive definitions are the only kernel extension, in order to avoid lots of manual derivation
*)

type hol_type = TyVar of string | TyCon of string * hol_type list
[@@deriving show { with_path = false }]

type term =
  | Var of string * hol_type
  | Const of string * hol_type
  | App of term * term
  | Lam of term * term
[@@deriving show { with_path = false }]

type thm = Sequent of term list * term [@@deriving show { with_path = false }]

type constructor_spec = { name : string; arg_types : hol_type list }
[@@deriving show { with_path = false }]

type inductive_def = {
  ty : hol_type;
  constructors : (string * term) list; (* name, constant *)
  induction : thm;
  recursion : thm;
  distinct : thm list;
  injective : thm list;
}
[@@deriving show { with_path = false }]

type kernel_error =
  | NewAxiomNotAProp
  | NoBaseCase
  | NotPositive
  | TypeAlreadyExists
  | ConstructorsAlreadyExist
  | TypeAlreadyDeclared of
      string * (Lexing.position[@printer fun _fmt _pos -> ()])
  | TypeNotDeclared of string
  | WrongNumberOfTypeArgs of string
  | TypeVariableNotAConstructor of
      string * (Lexing.position[@printer fun _fmt _pos -> ()])
  | TypeConstructorNotAVariable of
      string * (Lexing.position[@printer fun _fmt _pos -> ()])
  | ConstantTermAlreadyDeclared of
      string * (Lexing.position[@printer fun _fmt _pos -> ()])
  | CantApplyNonFunctionType of
      term * (Lexing.position[@printer fun _fmt _pos -> ()])
  | NotAConstantName of string * (Lexing.position[@printer fun _fmt _pos -> ()])
  | MakeLamNotAVariable of
      term * (Lexing.position[@printer fun _fmt _pos -> ()])
  | MakeAppTypesDontAgree of
      hol_type * hol_type * (Lexing.position[@printer fun _fmt _pos -> ()])
  | NotAVar of (Lexing.position[@printer fun _fmt _pos -> ()])
  | NotAConst of (Lexing.position[@printer fun _fmt _pos -> ()])
  | NotAnApp of (Lexing.position[@printer fun _fmt _pos -> ()])
  | NotALam of (Lexing.position[@printer fun _fmt _pos -> ()])
  | UnexpectedLambdaForm of (Lexing.position[@printer fun _fmt _pos -> ()])
  | CantCreateVariantForNonVariable of
      term * (Lexing.position[@printer fun _fmt _pos -> ()])
  | BadSubstitutionList of (Lexing.position[@printer fun _fmt _pos -> ()])
  | Clash of term * (Lexing.position[@printer fun _fmt _pos -> ()])
  | NotAnApplication of term * (Lexing.position[@printer fun _fmt _pos -> ()])
  | CantDestructEquality of (Lexing.position[@printer fun _fmt _pos -> ()])
  | RuleTrans of (Lexing.position[@printer fun _fmt _pos -> ()])
  | TypesDontAgree of (Lexing.position[@printer fun _fmt _pos -> ()])
  | NotBothEquations of (Lexing.position[@printer fun _fmt _pos -> ()])
  | LamRuleCantApply of (Lexing.position[@printer fun _fmt _pos -> ()])
  | NotTrivialBetaRedex of (Lexing.position[@printer fun _fmt _pos -> ()])
  | NotAProposition of (Lexing.position[@printer fun _fmt _pos -> ()])
  | Eq_MP
  | NewBasicDefinitionAlreadyDefined of
      string * (Lexing.position[@printer fun _fmt _pos -> ()])
  | NewBasicDefinition
  | NotFreshConstructor
  | InvariantViolation of string
  | TypeEquivalenceNotImplemented
  | NameMappingError of string
  | DefinitionError of string
  | TypeDefinitionError of string
[@@deriving show { with_path = false }]

let the_type_constants : (string, int) Hashtbl.t = Hashtbl.create 512
let the_term_constants : (string, hol_type) Hashtbl.t = Hashtbl.create 512
let the_inductives : (string, inductive_def) Hashtbl.t = Hashtbl.create 512
let _the_axioms : thm list ref = ref []
let _the_definitions : thm list ref = ref []
let bool_ty = TyCon ("bool", [])
let aty = TyVar "A"

let () =
  Hashtbl.add the_term_constants "="
    (TyCon ("fun", [ aty; TyCon ("fun", [ aty; bool_ty ]) ]))

let get_type_arity typ = Hashtbl.find_opt the_type_constants typ

let new_type name arity =
  match get_type_arity name with
  | Some _ -> Error (TypeAlreadyDeclared (name, [%here]))
  | None -> Ok (Hashtbl.add the_type_constants name arity)

let make_type name args =
  match Hashtbl.find_opt the_type_constants name with
  | None -> Error (TypeNotDeclared name)
  | Some arity when arity = List.length args -> Ok (TyCon (name, args))
  | Some other_arity ->
      Error
        (WrongNumberOfTypeArgs
           (Format.sprintf "%s: expected %i args, found %i" name
              (List.length args) other_arity))

let make_vartype name = TyVar name

let destruct_type = function
  | TyCon (s, ty) -> Ok (s, ty)
  | TyVar name -> Error (TypeVariableNotAConstructor (name, [%here]))

let destruct_vartype = function
  | TyCon (name, _) -> Error (TypeConstructorNotAVariable (name, [%here]))
  | TyVar name -> Ok name

let is_type = function TyCon _ -> true | _ -> false
let is_vartype = function TyVar _ -> true | _ -> false

(* Extract type variables from a type *)
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
  | Some _ -> Error (ConstantTermAlreadyDeclared (name, [%here]))
  | None -> Ok (Hashtbl.add the_term_constants name typ)

open Result.Syntax

let rec type_of_term = function
  | Var (_, ty) -> Ok ty
  | Const (_, ty) -> Ok ty
  | App (s, _) -> (
      let* sty = type_of_term s in
      match sty with
      | TyCon ("fun", [ _dty; rty ]) -> Ok rty
      | _ -> Error (CantApplyNonFunctionType (s, [%here])))
  | Lam (Var (_, ty), t) ->
      let* rty = type_of_term t in
      Ok (TyCon ("fun", [ ty; rty ]))
  | Lam (_, _) -> Error (UnexpectedLambdaForm [%here])

let is_var = function Var (_, _) -> true | _ -> false
let is_const = function Const (_, _) -> true | _ -> false
let is_abs = function Lam (_, _) -> true | _ -> false
let is_comb = function App (_, _) -> true | _ -> false
let make_var v ty = Var (v, ty)

let make_const name theta =
  let* uty =
    get_const_term_type name
    |> Option.to_result ~none:(NotAConstantName (name, [%here]))
  in
  Ok (Const (name, type_substitution theta uty))

let make_lam bvar body =
  match bvar with
  | Var (_, _) -> Ok (Lam (bvar, body))
  | _ -> Error (MakeLamNotAVariable (bvar, [%here]))

let make_app f a =
  let* fty = type_of_term f in
  let* aty = type_of_term a in
  match fty with
  | TyCon ("fun", [ ty; _ ]) when compare ty aty = 0 -> Ok (App (f, a))
  | _ -> Error (MakeAppTypesDontAgree (fty, aty, [%here]))

let destruct_var = function
  | Var (s, ty) -> Ok (s, ty)
  | _ -> Error (NotAVar [%here])

let destruct_const = function
  | Const (s, ty) -> Ok (s, ty)
  | _ -> Error (NotAConst [%here])

let destruct_app = function
  | App (f, x) -> Ok (f, x)
  | _ -> Error (NotAnApp [%here])

let destruct_lam = function
  | Lam (v, b) -> Ok (v, b)
  | _ -> Error (NotALam [%here])

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
  | Lam (_, _) -> Error (UnexpectedLambdaForm [%here])

let rec variant avoid v =
  if not (List.exists (var_free_in v) avoid) then Ok v
  else
    match v with
    | Var (s, ty) -> variant avoid (Var (s ^ "'", ty))
    | _ -> Error (CantCreateVariantForNonVariable (v, [%here]))

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
  else Error (BadSubstitutionList [%here])

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
        else Error (Clash (term', [%here]))
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
        | Error (Clash (clashing_var, _)) when clashing_var = bound_var' ->
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
  | _ -> Error (NotAnApplication (tm, [%here]))

let rand tm =
  match tm with
  | App (_, r) -> Ok r
  | _ -> Error (NotAnApplication (tm, [%here]))

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
  | _ -> Error (CantDestructEquality [%here])

let rec alpha_compare_var env x1 x2 =
  match env with
  | [] -> compare x1 x2
  | (t1, t2) :: oenv ->
      if compare x1 t1 = 0 then if compare x2 t2 = 0 then 0 else -1
      else if compare x2 t2 = 0 then 1
      else alpha_compare_var oenv x1 x2

let rec alpha_compare env tm1 tm2 =
  if tm1 == tm2 && List.for_all (fun (x, y) -> x = y) env then 0
  else
    match (tm1, tm2) with
    | Var (_x1, _ty1), Var (_x2, _ty2) -> alpha_compare_var env tm1 tm2
    | Const (_x1, _ty1), Const (_x2, _ty2) -> compare tm1 tm2
    | App (s1, t1), App (s2, t2) ->
        let c = alpha_compare env s1 s2 in
        if c <> 0 then c else alpha_compare env t1 t2
    | Lam ((Var (_, ty1) as x1), t1), Lam ((Var (_, ty2) as x2), t2) ->
        let c = compare ty1 ty2 in
        if c <> 0 then c else alpha_compare ((x1, x2) :: env) t1 t2
    | Const (_, _), _ -> -1
    | _, Const (_, _) -> 1
    | Var (_, _), _ -> -1
    | _, Var (_, _) -> 1
    | App (_, _), _ -> -1
    | _, App (_, _) -> 1
    | _ -> failwith "alpha_compare: unexpected term combination"

let alphaorder = alpha_compare []

let rec term_union l1 l2 =
  match (l1, l2) with
  | [], l2 -> l2
  | l1, [] -> l1
  | h1 :: t1, h2 :: t2 ->
      let c = alphaorder h1 h2 in
      if c = 0 then h1 :: term_union t1 t2
      else if c < 0 then h1 :: term_union t1 l2
      else h2 :: term_union l1 t2

let rec term_remove t l =
  match l with
  | s :: ss ->
      let c = alphaorder t s in
      if c > 0 then
        let ss' = term_remove t ss in
        if ss' == ss then l else s :: ss'
      else if c = 0 then ss
      else l
  | [] -> l

let rec term_map f l =
  match l with
  | h :: t ->
      let h' = f h and t' = term_map f t in
      if h' == h && t' == t then l else term_union [ h' ] t'
  | [] -> l

let destruct_thm (Sequent (asl, c)) = (asl, c)
let hyp (Sequent (asl, _)) = asl
let concl (Sequent (_, c)) = c

let refl tm =
  let* tm_eq = safe_make_eq tm tm in
  Ok (Sequent ([], tm_eq))

let trans (Sequent (asl1, c1)) (Sequent (asl2, c2)) =
  match (c1, c2) with
  | App ((App (Const ("=", _), _) as eql), m1), App (App (Const ("=", _), m2), r)
    when alphaorder m1 m2 = 0 ->
      Ok (Sequent (term_union asl1 asl2, App (eql, r)))
  | _ -> Error (RuleTrans [%here])

let mk_comb (Sequent (asl1, c1)) (Sequent (asl2, c2)) =
  match (c1, c2) with
  | App (App (Const ("=", _), l1), r1), App (App (Const ("=", _), l2), r2) -> (
      let* tr1 = type_of_term r1 in
      match tr1 with
      | TyCon ("fun", [ ty; _ ]) ->
          let* tr2 = type_of_term r2 in
          if compare ty tr2 = 0 then
            let* lr_eq = safe_make_eq (App (l1, l2)) (App (r1, r2)) in
            Ok (Sequent (term_union asl1 asl2, lr_eq))
          else Error (TypesDontAgree [%here])
      | _ -> Error (TypesDontAgree [%here]))
  | _ -> Error (NotBothEquations [%here])

let lam v (Sequent (asl, c)) =
  match (v, c) with
  | Var (_, _), App (App (Const ("=", _), l), r)
    when not (List.exists (var_free_in v) asl) ->
      let* lr_eq = safe_make_eq (Lam (v, l)) (Lam (v, r)) in
      Ok (Sequent (asl, lr_eq))
  | _ -> Error (LamRuleCantApply [%here])

let beta = function
  | App (Lam (v, bod), arg) as tm when compare arg v = 0 ->
      let* b = safe_make_eq tm bod in
      Ok (Sequent ([], b))
  | _ -> Error (NotTrivialBetaRedex [%here])

let assume tm =
  let* tty = type_of_term tm in
  if compare tty bool_ty = 0 then Ok (Sequent ([ tm ], tm))
  else Error (NotAProposition [%here])

let eq_mp (Sequent (asl1, eq)) (Sequent (asl2, c)) =
  match eq with
  | App (App (Const ("=", _), l), r) when alphaorder l c = 0 ->
      Ok (Sequent (term_union asl1 asl2, r))
  | _ -> Error Eq_MP

let deduct_antisym_rule (Sequent (asl1, c1)) (Sequent (asl2, c2)) =
  let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
  let* cc_eq = safe_make_eq c1 c2 in
  Ok (Sequent (term_union asl1' asl2', cc_eq))

let inst_type theta (Sequent (asl, c)) =
  let inst_fn = inst theta in
  let* inst_asl =
    List.fold_left
      (fun acc a ->
        match (acc, a) with
        | Ok nacc, a ->
            let* inst_a = inst_fn a in
            Ok (inst_a :: nacc)
        | e, _ -> e)
      (Ok []) asl
  in
  let* inst_c = inst_fn c in
  Ok (Sequent (inst_asl, inst_c))

let inst theta (Sequent (asl, c)) =
  let inst_fn = vsubst theta in
  let* inst_asl =
    List.fold_left
      (fun acc a ->
        match (acc, a) with
        | Ok nacc, a ->
            let* inst_a = inst_fn a in
            Ok (inst_a :: nacc)
        | e, _ -> e)
      (Ok []) asl
  in
  let* inst_c = inst_fn c in
  Ok (Sequent (inst_asl, inst_c))

let the_axioms = ref ([] : thm list)
let axioms () = !the_axioms

let new_axiom tm =
  let* tty = type_of_term tm in
  if compare tty bool_ty = 0 then (
    let th = Sequent ([], tm) in
    the_axioms := th :: !the_axioms;
    Ok th)
  else Error NewAxiomNotAProp

let the_definitions = ref ([] : thm list)
let definitions () = !the_definitions

let subset l1 l2 =
  l1 |> List.for_all @@ fun elem -> l2 |> List.exists (( = ) elem)

let new_basic_definition tm =
  match tm with
  | App (App (Const ("=", _), Var (cname, ty)), r) ->
      if not (all_frees_within [] r) then
        Error
          (DefinitionError
             ("new_definition: term not closed: "
             ^ String.concat ", "
                 (List.map
                    (fun a ->
                      match a with Var (name, _) -> name | _ -> "<non-var>")
                    (frees r))))
      else
        let* r_tys = type_vars_in_term r in
        if not (subset r_tys (type_vars ty)) then
          Error
            (DefinitionError
               "new_definition: Type variables not reflected in constant")
        else
          let* () = new_constant cname ty in
          let c = Const (cname, ty) in
          let* cr_eq = safe_make_eq c r in
          let dth = Sequent ([], cr_eq) in
          the_definitions := dth :: !the_definitions;
          Ok dth
  | App (App (Const ("=", _), Const (cname, _ty)), _r) ->
      Error (NewBasicDefinitionAlreadyDefined (cname, [%here]))
  | _ -> Error NewBasicDefinition

let new_basic_type_definition tyname (absname, repname) (Sequent (asl, c)) =
  if
    List.exists
      (fun t -> get_const_term_type t |> Option.is_some)
      [ absname; repname ]
  then
    Error
      (TypeDefinitionError
         "new_basic_type_definition: Constant(s) already in use")
  else if not (asl = []) then
    Error
      (TypeDefinitionError "new_basic_type_definition: Assumptions in theorem")
  else
    let* p, x = destruct_app c in
    if not (all_frees_within [] p) then
      Error
        (TypeDefinitionError
           "new_basic_type_definition: Predicate is not closed")
    else
      let* p_tyvars = type_vars_in_term p in
      let tyvars = List.sort compare p_tyvars in
      let* () = new_type tyname (List.length tyvars) in
      let aty = TyCon (tyname, tyvars) in
      let* rty = type_of_term x in
      let absty = TyCon ("fun", [ rty; aty ])
      and repty = TyCon ("fun", [ aty; rty ]) in
      let* () = new_constant absname absty in
      let abs = Const (absname, absty) in
      let* () = new_constant repname repty in
      let rep = Const (repname, repty) in
      let a = Var ("a", aty) and r = Var ("r", rty) in
      let* eq1 = safe_make_eq (App (abs, App (rep, a))) a
      and* inner_eq = safe_make_eq (App (rep, App (abs, r))) r in
      let* eq2 = safe_make_eq (App (p, r)) inner_eq in
      Ok (Sequent ([], eq1), Sequent ([], eq2))

(* helpful *)

let make_fun_ty a b = TyCon ("fun", [ a; b ])

let type_of_var = function
  | Var (_, ty) -> ty
  | _ -> failwith "type_of_var: not a variable"

let init_types () =
  let* () = new_type "bool" 0 in
  let* () = new_type "fun" 2 in
  Ok ()

(* T = ((λp:bool. p) = (λp. p)) *)
let init_true () =
  let p = Var ("p", bool_ty) in
  let id = Lam (p, p) in
  let* id_eq_id = safe_make_eq id id in
  let t_var = Var ("T", bool_ty) in
  let* def_eq = safe_make_eq t_var id_eq_id in
  new_basic_definition def_eq

let make_true () = Const ("T", bool_ty)

(* ∀ = (λP. P = (λx. T)) *)
let init_forall () =
  let a = TyVar "a" in
  let pred_ty = make_fun_ty a bool_ty in
  let forall_ty = make_fun_ty pred_ty bool_ty in
  let forall_var = Var ("!", forall_ty) in
  let p_var = Var ("P", pred_ty) in
  let x_var = Var ("x", a) in
  let t = make_true () in
  let lam_x_t = Lam (x_var, t) in
  let* p_eq_lam = safe_make_eq p_var lam_x_t in
  let rhs = Lam (p_var, p_eq_lam) in
  let* def_eq = safe_make_eq forall_var rhs in
  new_basic_definition def_eq

let make_forall_const var_ty =
  let pred_ty = make_fun_ty var_ty bool_ty in
  let forall_ty = make_fun_ty pred_ty bool_ty in
  Const ("!", forall_ty)

let make_forall var body =
  let var_ty = type_of_var var in
  App (make_forall_const var_ty, Lam (var, body))

let make_foralls vars body = List.fold_right make_forall vars body

(* ∧ = (λp q. (λf. f p q) = (λf. f T T)) *)
let init_conj () =
  let p = Var ("p", bool_ty) in
  let q = Var ("q", bool_ty) in
  let conj_var =
    Var ("/\\", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))
  in
  let f_ty = make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty) in
  let f = Var ("f", f_ty) in
  let t = make_true () in
  let f_p_q = App (App (f, p), q) in
  let f_t_t = App (App (f, t), t) in
  let lam_f_p_q = Lam (f, f_p_q) in
  let lam_f_t_t = Lam (f, f_t_t) in
  let* eq_lams = safe_make_eq lam_f_p_q lam_f_t_t in
  let rhs = Lam (p, Lam (q, eq_lams)) in
  let* def_eq = safe_make_eq conj_var rhs in
  new_basic_definition def_eq

let make_conj_const () =
  Const ("/\\", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))

let make_conj p q = App (App (make_conj_const (), p), q)

let make_conjs = function
  | [] -> make_true ()
  | [ p ] -> p
  | p :: ps -> List.fold_left make_conj p ps

(* ==> = (λp q. p ∧ q ⟺ p) *)
let init_imp () =
  let p = Var ("p", bool_ty) in
  let q = Var ("q", bool_ty) in
  let imp_var =
    Var ("==>", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))
  in
  let p_and_q = make_conj p q in
  let* p_and_q_eq_p = safe_make_eq p_and_q p in
  let rhs = Lam (p, Lam (q, p_and_q_eq_p)) in
  let* def_eq = safe_make_eq imp_var rhs in
  new_basic_definition def_eq

let make_imp_const () =
  Const ("==>", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))

let make_imp p q = App (App (make_imp_const (), p), q)

let make_imps antecedents consequent =
  List.fold_right make_imp antecedents consequent

(* F = (∀p. p) *)
let init_false () =
  let p = Var ("p", bool_ty) in
  let f_var = Var ("F", bool_ty) in
  let forall_p_p = make_forall p p in
  let* def_eq = safe_make_eq f_var forall_p_p in
  new_basic_definition def_eq

let make_false () = Const ("F", bool_ty)

(* ¬ = (λp. p ==> F) *)
let init_neg () =
  let p = Var ("p", bool_ty) in
  let neg_var = Var ("~", make_fun_ty bool_ty bool_ty) in
  let f = make_false () in
  let p_imp_f = make_imp p f in
  let rhs = Lam (p, p_imp_f) in
  let* def_eq = safe_make_eq neg_var rhs in
  new_basic_definition def_eq

let make_neg_const () = Const ("~", make_fun_ty bool_ty bool_ty)
let make_neg p = App (make_neg_const (), p)

(* ∃ = (λP. ¬(∀x. ¬(P x))) *)
let init_exists () =
  let a = TyVar "a" in
  let pred_ty = make_fun_ty a bool_ty in
  let exists_ty = make_fun_ty pred_ty bool_ty in
  let exists_var = Var ("?", exists_ty) in
  let p_var = Var ("P", pred_ty) in
  let x_var = Var ("x", a) in
  let p_x = App (p_var, x_var) in
  let not_p_x = make_neg p_x in
  let forall_not_p = make_forall x_var not_p_x in
  let not_forall_not_p = make_neg forall_not_p in
  let rhs = Lam (p_var, not_forall_not_p) in
  let* def_eq = safe_make_eq exists_var rhs in
  new_basic_definition def_eq

let make_exists_const var_ty =
  let pred_ty = make_fun_ty var_ty bool_ty in
  let exists_ty = make_fun_ty pred_ty bool_ty in
  Const ("?", exists_ty)

let make_exists var body =
  let var_ty = type_of_var var in
  App (make_exists_const var_ty, Lam (var, body))

(* ∨ = (λp q. ∀r. (p ==> r) ==> (q ==> r) ==> r) *)
let init_disj () =
  let p = Var ("p", bool_ty) in
  let q = Var ("q", bool_ty) in
  let r = Var ("r", bool_ty) in
  let disj_var =
    Var ("\\/", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))
  in
  let p_imp_r = make_imp p r in
  let q_imp_r = make_imp q r in
  let body = make_imp p_imp_r (make_imp q_imp_r r) in
  let forall_r = make_forall r body in
  let rhs = Lam (p, Lam (q, forall_r)) in
  let* def_eq = safe_make_eq disj_var rhs in
  new_basic_definition def_eq

let make_disj_const () =
  Const ("\\/", make_fun_ty bool_ty (make_fun_ty bool_ty bool_ty))

let make_disj p q = App (App (make_disj_const (), p), q)

let make_neq l r =
  match safe_make_eq l r with Ok eq -> Ok (make_neg eq) | Error e -> Error e

let init_classical () =
  let p = Var ("p", bool_ty) in
  let excl_middle = make_forall p (make_disj p (make_neg p)) in
  new_axiom excl_middle

let init () =
  let* () = init_types () in
  let* _ = init_true () in
  let* _ = init_forall () in
  let* _ = init_conj () in
  let* _ = init_imp () in
  let* _ = init_false () in
  let* _ = init_neg () in
  let* _ = init_exists () in
  let* _ = init_disj () in
  let* _ = init_classical () in
  Ok ()

(* --- *)

(*
(* Theorem generation *)
val make_induction_thm : hol_type -> constructor_spec list -> thm
val make_recursion_thm : hol_type -> constructor_spec list -> thm
val make_distinct_thms : (string * term) list -> thm list
val make_injective_thms : hol_type -> constructor_spec list -> thm list
*)

let rec mentions_type tyname ty =
  match ty with
  | TyVar _ -> false
  | TyCon (name, args) ->
      name = tyname || List.exists (mentions_type tyname) args

let is_base_case tyname c = not (List.exists (mentions_type tyname) c.arg_types)

let check_base_case tyname constructors =
  Ok (List.exists (is_base_case tyname) constructors)

let make_constructor_type arg_types result_type =
  List.fold_right
    (fun arg acc -> TyCon ("fun", [ arg; acc ]))
    arg_types result_type

let rec appears_left_of_arrow tyname ty =
  match ty with
  | TyVar _ -> false
  | TyCon ("fun", [ arg; result ]) ->
      mentions_type tyname arg || appears_left_of_arrow tyname result
  | TyCon (_, args) -> List.exists (appears_left_of_arrow tyname) args

let check_positivity tyname constructors =
  let ok =
    constructors
    |> List.for_all (fun c ->
        c.arg_types
        |> List.for_all (fun ty -> not (appears_left_of_arrow tyname ty)))
  in
  Ok ok

(* forall P. P base_constructor -> (forall n.  P n -> P other_constructor n) -> (forall n. P n)*)
let make_induction_thm (ty : hol_type) (constructors : constructor_spec list) =
  (* Setup our abitrary predicate*)
  let pred_ty = make_fun_ty ty bool_ty in
  let pred_var = Var ("P", pred_ty) in

  (* filter on the recursive types of a constructor (i.e. xs in Cons x xs) and ensure we have P xs for each of them*)
  let quantify_recursive (c : constructor_spec) =
    let arg_tys = c.arg_types in
    let args =
      arg_tys
      |> List.mapi @@ fun idx aty ->
         let is_recursive = aty = ty in
         (is_recursive, Var ("n" ^ string_of_int idx, aty))
    in
    let recursive_hypotheses =
      args
      |> List.filter_map (fun (recur, arg) -> if recur then Some arg else None)
      |> List.map @@ fun arg -> App (pred_var, arg)
    in
    let make_app_exn l r = Result.get_ok (make_app l r) in

    (* Build `P (Constructor a b c...)*)
    let concl =
      make_app_exn pred_var
        (List.fold_left
           (fun acc a -> make_app_exn acc a)
           (Const (c.name, make_constructor_type arg_tys ty))
           (List.map snd args))
    in

    let implications = make_imps recursive_hypotheses concl in
    make_foralls (List.map snd args) implications
  in

  let bases, recursives =
    constructors |> List.partition (fun c -> c.arg_types = [])
  in
  let base_holds =
    bases |> List.map @@ fun c -> App (pred_var, Const (c.name, ty))
  in
  let recursive_holds =
    recursives |> List.map @@ fun c -> quantify_recursive c
  in
  let all_premises = base_holds @ recursive_holds in

  let x = Var ("x", ty) in
  let conclusion = make_forall x (App (pred_var, x)) in

  let theorem_body = make_imps all_premises conclusion in
  let theorem = make_forall pred_var theorem_body in

  new_axiom theorem

(*
  ∀ok_case err_case pend_case. 
  ∃g. 
    (∀x. g (Ok x) = ok_case x) ∧ 
    (g Err = err_case) ∧
    (∀r. g (Pending r) = pend_case r (g r))
*)
let make_recursion_thm (ty : hol_type) (constructors : constructor_spec list) =
  let ret_ty = TyVar "r" in
  let g_ty = make_fun_ty ty ret_ty in
  let g_var = Var ("g", g_ty) in

  (* Build case function types: args + (r for each recursive arg) -> r *)
  let case_tys =
    constructors
    |> List.map @@ fun c ->
       let args = c.arg_types in
       let rec_results =
         args
         |> List.filter (fun arg_ty -> arg_ty = ty)
         |> List.map (fun _ -> ret_ty)
       in
       (c.name, make_constructor_type (args @ rec_results) ret_ty)
  in

  let case_vars =
    case_tys |> List.mapi @@ fun idx (name, t) -> (name, Var (name ^ "_case", t))
  in

  (* Build equation for each constructor *)
  let construct_case (cons : constructor_spec) =
    let case_var = List.assoc cons.name case_vars in

    match cons.arg_types with
    | [] ->
        (* Nullary constructor: g Constructor = case_var *)
        let* g_app = make_app g_var (Const (cons.name, ty)) in
        safe_make_eq g_app case_var
    | arg_tys ->
        (* Create variables for constructor arguments *)
        let arg_vars =
          arg_tys
          |> List.mapi (fun i arg_ty -> Var ("x" ^ string_of_int i, arg_ty))
        in

        (* Build: Constructor x0 x1 x2 ... *)
        let constructor_ty = make_constructor_type arg_tys ty in
        let constructor = Const (cons.name, constructor_ty) in
        let constructor_applied =
          List.fold_left
            (fun acc arg -> Result.get_ok (make_app acc arg))
            constructor arg_vars
        in

        (* Build: g (Constructor x0 x1 x2 ...) *)
        let* g_applied = make_app g_var constructor_applied in

        (* Find recursive arguments and build g applications *)
        let recursive_calls =
          arg_vars
          |> List.filter (fun v -> type_of_var v = ty)
          |> List.map (fun v -> Result.get_ok (make_app g_var v))
        in

        (* Build RHS: case_var x0 x1 ... (g x_rec0) (g x_rec1) ... *)
        let all_case_args = arg_vars @ recursive_calls in
        let case_applied =
          List.fold_left
            (fun acc arg -> Result.get_ok (make_app acc arg))
            case_var all_case_args
        in

        (* Build equation: g (Constructor ...) = case_var ... *)
        let* equation = safe_make_eq g_applied case_applied in

        (* Quantify over all constructor arguments: ∀x0 x1 x2. ... *)
        Ok (make_foralls arg_vars equation)
  in

  (* Build all equations *)
  let* equations =
    constructors |> List.map construct_case
    |> List.fold_left
         (fun acc eq ->
           match (acc, eq) with
           | Ok eqs, Ok e -> Ok (e :: eqs)
           | Error e, _ -> Error e
           | _, Error e -> Error e)
         (Ok [])
    |> Result.map List.rev
  in

  let conjoined = make_conjs equations in

  let body = make_exists g_var conjoined in

  let all_case_vars = List.map snd case_vars in
  let theorem = make_foralls all_case_vars body in

  new_axiom theorem

(* let make_distinct_thms constructor_terms = failwith "TODO: make_distinct_thms" *)
(* let make_injective_thms ty constructors = failwith "TODO: make_injective_thms" *)

let make_distinct_thms constructor_terms = refl (Var ("r", bool_ty))
let make_injective_thms ty constructors = refl (Var ("r", bool_ty))

let define_inductive tyname params (constructors : constructor_spec list) =
  let* () =
    match Hashtbl.find_opt the_type_constants tyname with
    | Some _ -> Error TypeAlreadyExists
    | None -> Ok ()
  in

  let* () =
    let not_fresh =
      constructors
      |> List.filter (fun c -> Hashtbl.mem the_term_constants c.name)
      |> List.map (fun c -> c.name)
    in
    match not_fresh with
    | [] -> Ok ()
    | _names -> Error ConstructorsAlreadyExist
  in

  let* positive = check_positivity tyname constructors in
  let* () = if not positive then Error NotPositive else Ok () in

  let* base_case_exists = check_base_case tyname constructors in
  let* () = if not base_case_exists then Error NoBaseCase else Ok () in

  let* () = new_type tyname (List.length params) in
  let ty_params = List.map (fun p -> TyVar p) params in
  let ty = TyCon (tyname, ty_params) in

  let* constructor_terms =
    constructors
    |> List.map (fun c ->
        let con_ty = make_constructor_type c.arg_types ty in
        let* () = new_constant c.name con_ty in
        Ok (c.name, Const (c.name, con_ty)))
    |> List.fold_left
         (fun acc r ->
           let* lst = acc in
           let* item = r in
           Ok (item :: lst))
         (Ok [])
    |> Result.map List.rev
  in

  let* induction = make_induction_thm ty constructors in

  let* recursion = make_recursion_thm ty constructors in

  let* distinct = make_distinct_thms constructor_terms in

  let* injective = make_injective_thms ty constructors in

  let def =
    {
      ty;
      constructors = constructor_terms;
      induction;
      recursion;
      distinct = [ distinct ];
      injective = [ injective ];
    }
  in
  Hashtbl.add the_inductives tyname def;
  Ok def
