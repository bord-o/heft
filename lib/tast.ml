open Ast

type tty = Ast.ty [@@deriving show]

type ttm =
  | TVar of name * tty
  | TConst of name * tty
  | TApp of ttm * ttm * tty
  | TLam of name * tty * ttm * tty
  | TLet of name * tty * ttm * ttm * tty
  | TIf of ttm * ttm * ttm * tty
  | TEq of ttm * ttm * tty
  | TForall of (name * tty) list * ttm * tty
  | TExists of (name * tty) list * ttm * tty
  | TFix of (name * tty) list * ttm * tty
[@@deriving show]

type tclause = ttm list * ttm [@@deriving show]

type tdecl =
  | TDType of name * name list * constr list
  | TDDef of name * tty * ttm
  | TDFun of name * tty * tclause list
  | TDTheorem of name * ttm
[@@deriving show]

type tprogram = tdecl list [@@deriving show]

let type_of_tm = function
  | TVar (_, ty) -> ty
  | TConst (_, ty) -> ty
  | TApp (_, _, ty) -> ty
  | TLam (_, _, _, ty) -> ty
  | TLet (_, _, _, _, ty) -> ty
  | TIf (_, _, _, ty) -> ty
  | TEq (_, _, ty) -> ty
  | TForall (_, _, ty) -> ty
  | TExists (_, _, ty) -> ty
  | TFix (_, _, ty) -> ty

type env = {
  types : (name * int) list;
  constants : (name * tty) list;
  locals : (name * tty) list;
}
[@@deriving show]

let ty_bool = TyApp ("bool", [])
let ty_fun a b = TyApp ("fun", [ a; b ])

(* Built-in HOL constants from derived.ml *)
let builtin_constants =
  let a = TyVar "'a" in
  let bool = ty_bool in
  let bool_to_bool = ty_fun bool bool in
  let bool_to_bool_to_bool = ty_fun bool bool_to_bool in
  let pred_a = ty_fun a bool in
  [
    (* equality: A -> A -> bool *)
    ("=", ty_fun a (ty_fun a bool));
    (* T : bool *)
    ("T", bool);
    (* F : bool *)
    ("F", bool);
    (* forall: (a -> bool) -> bool *)
    ("!", ty_fun pred_a bool);
    (* exists: (a -> bool) -> bool *)
    ("?", ty_fun pred_a bool);
    (* conjunction: bool -> bool -> bool *)
    ("/\\", bool_to_bool_to_bool);
    (* disjunction: bool -> bool -> bool *)
    ("\\/", bool_to_bool_to_bool);
    (* implication: bool -> bool -> bool *)
    ("==>", bool_to_bool_to_bool);
    (* negation: bool -> bool *)
    ("~", bool_to_bool);
    (* choice/select: (a -> bool) -> a *)
    ("@", ty_fun pred_a a);
  ]

let empty_env =
  {
    types = [ ("bool", 0); ("fun", 2) ];
    constants = builtin_constants;
    locals = [];
  }

let add_type name arity env = { env with types = (name, arity) :: env.types }

let add_constant name ty env =
  { env with constants = (name, ty) :: env.constants }

let add_local name ty env = { env with locals = (name, ty) :: env.locals }

let rec ty_equal t1 t2 =
  match (t1, t2) with
  | TyVar a, TyVar b -> a = b
  | TyApp (n1, args1), TyApp (n2, args2) ->
      n1 = n2
      && List.length args1 = List.length args2
      && List.for_all2 ty_equal args1 args2
  | _ -> false

let rec subst_ty subst = function
  | TyVar n -> (
      match List.assoc_opt n subst with Some t -> t | None -> TyVar n)
  | TyApp (n, args) -> TyApp (n, List.map (subst_ty subst) args)

let rec collect_tyvars acc = function
  | TyVar n -> if List.mem n acc then acc else n :: acc
  | TyApp (_, args) -> List.fold_left collect_tyvars acc args

(* Fresh type variable generation for instantiating polymorphic constants *)
let fresh_counter = ref 0

let fresh_tyvar () =
  incr fresh_counter;
  "'_t" ^ string_of_int !fresh_counter

let freshen_ty ty =
  let tyvars = collect_tyvars [] ty in
  if tyvars = [] then ty
  else
    let subst = List.map (fun v -> (v, TyVar (fresh_tyvar ()))) tyvars in
    subst_ty subst ty

let rec subst_tm subst tm =
  let sty = subst_ty subst in
  match tm with
  | TVar (n, ty) -> TVar (n, sty ty)
  | TConst (n, ty) -> TConst (n, sty ty)
  | TApp (f, x, ty) -> TApp (subst_tm subst f, subst_tm subst x, sty ty)
  | TLam (n, ty, body, full_ty) ->
      TLam (n, sty ty, subst_tm subst body, sty full_ty)
  | TLet (n, ty, bound, body, full_ty) ->
      TLet (n, sty ty, subst_tm subst bound, subst_tm subst body, sty full_ty)
  | TIf (c, t, e, ty) ->
      TIf (subst_tm subst c, subst_tm subst t, subst_tm subst e, sty ty)
  | TEq (l, r, ty) -> TEq (subst_tm subst l, subst_tm subst r, sty ty)
  | TForall (bindings, body, ty) ->
      let bindings' = List.map (fun (n, t) -> (n, sty t)) bindings in
      TForall (bindings', subst_tm subst body, sty ty)
  | TExists (bindings, body, ty) ->
      let bindings' = List.map (fun (n, t) -> (n, sty t)) bindings in
      TExists (bindings', subst_tm subst body, sty ty)
  | TFix (bindings, body, ty) ->
      let bindings' = List.map (fun (n, t) -> (n, sty t)) bindings in
      TFix (bindings', subst_tm subst body, sty ty)

let instantiate ty ty_args =
  let tyvars = collect_tyvars [] ty in
  if List.length tyvars <> List.length ty_args then
    failwith "wrong number of type arguments for instantiation"
  else
    let subst = List.combine tyvars ty_args in
    subst_ty subst ty

let rec unify_types subst t1 t2 =
  match (t1, t2) with
  | TyVar n, t | t, TyVar n -> (
      match List.assoc_opt n subst with
      | Some t' ->
          if ty_equal t t' then subst else failwith ("type mismatch: " ^ n)
      | None -> (n, t) :: subst)
  | TyApp (n1, args1), TyApp (n2, args2)
    when n1 = n2 && List.length args1 = List.length args2 ->
      List.fold_left2 unify_types subst args1 args2
  | _ -> failwith "type mismatch in unification"

let rec result_type = function
  | TyApp ("fun", [ _; ret ]) -> result_type ret
  | ty -> ty

let lookup_var env name =
  match List.assoc_opt name env.locals with
  | Some ty -> `Local ty
  | None -> (
      match List.assoc_opt name env.constants with
      | Some ty -> `Const (freshen_ty ty)  (* Freshen type variables for each use *)
      | None -> failwith ("unbound variable: " ^ name))

let rec infer env tm =
  match tm with
  | Var n -> (
      match lookup_var env n with
      | `Local ty -> TVar (n, ty)
      | `Const ty -> TConst (n, ty))
  | App (f, x) -> (
      let f' = infer env f in
      let tf = type_of_tm f' in
      match tf with
      | TyApp ("fun", [ arg_ty; ret_ty ]) ->
          let x' = infer env x in
          let actual_arg_ty = type_of_tm x' in
          (* Unify arg_ty with actual_arg_ty to instantiate type variables *)
          let subst =
            try unify_types [] arg_ty actual_arg_ty
            with _ ->
              failwith
                ("argument type mismatch: expected " ^ show_ty arg_ty
               ^ " but got " ^ show_ty actual_arg_ty)
          in
          let ret_ty' = subst_ty subst ret_ty in
          let f'' = subst_tm subst f' in
          let x'' = subst_tm subst x' in
          TApp (f'', x'', ret_ty')
      | _ -> failwith "expected function type in application")
  | Lam (x, ty, body) ->
      let env' = add_local x ty env in
      let body' = infer env' body in
      let body_ty = type_of_tm body' in
      TLam (x, ty, body', ty_fun ty body_ty)
  | Let (x, bound, body) ->
      let bound' = infer env bound in
      let bound_ty = type_of_tm bound' in
      let env' = add_local x bound_ty env in
      let body' = infer env' body in
      let body_ty = type_of_tm body' in
      TLet (x, bound_ty, bound', body', body_ty)
  | If (cond, then_, else_) ->
      let cond' = check env cond ty_bool in
      let then_' = infer env then_ in
      let then_ty = type_of_tm then_' in
      let else_' = check env else_ then_ty in
      TIf (cond', then_', else_', then_ty)
  | Eq (lhs, rhs) ->
      let lhs' = infer env lhs in
      let lhs_ty = type_of_tm lhs' in
      let rhs' = check env rhs lhs_ty in
      TEq (lhs', rhs', ty_bool)
  | Forall (bindings, body) ->
      let env' =
        List.fold_left (fun e (n, ty) -> add_local n ty e) env bindings
      in
      let body' = check env' body ty_bool in
      TForall (bindings, body', ty_bool)
  | Exists (bindings, body) ->
      let env' =
        List.fold_left (fun e (n, ty) -> add_local n ty e) env bindings
      in
      let body' = check env' body ty_bool in
      TExists (bindings, body', ty_bool)
  | Fix (bindings, body) ->
      let env' =
        List.fold_left (fun e (n, ty) -> add_local n ty e) env bindings
      in
      let body' = infer env' body in
      let body_ty = type_of_tm body' in
      TFix (bindings, body', body_ty)

and check env tm expected =
  match (tm, expected) with
  | Lam (x, ty, body), TyApp ("fun", [ arg_ty; ret_ty ]) ->
      if not (ty_equal ty arg_ty) then failwith "lambda argument type mismatch"
      else
        let env' = add_local x ty env in
        let body' = check env' body ret_ty in
        TLam (x, ty, body', expected)
  | Var n, _ -> (
      match List.assoc_opt n env.constants with
      | Some const_ty ->
          let const_ty = freshen_ty const_ty in  (* Freshen type variables *)
          let subst = unify_types [] const_ty expected in
          let const_ty' = subst_ty subst const_ty in
          TConst (n, const_ty')
      | None -> (
          match List.assoc_opt n env.locals with
          | Some ty ->
              if ty_equal ty expected then TVar (n, ty)
              else failwith ("type mismatch for local " ^ n)
          | None -> failwith ("unbound variable: " ^ n)))
  | _ -> (
      let tm' = infer env tm in
      let actual = type_of_tm tm' in
      if ty_equal actual expected then tm'
      else
        let subst =
          try Some (unify_types [] actual expected) with _ -> None
        in
        match subst with
        | Some s ->
            let actual' = subst_ty s actual in
            if ty_equal actual' expected then subst_tm s tm'
            else
              failwith
                ("type mismatch: expected " ^ show_ty expected ^ " but got "
               ^ show_ty actual)
        | None ->
            failwith
              ("type mismatch: expected " ^ show_ty expected ^ " but got "
             ^ show_ty actual))

let rec check_pattern env tm expected =
  match tm with
  | Var n -> (
      match List.assoc_opt n env.constants with
      | Some const_ty ->
          let const_ty = freshen_ty const_ty in
          let subst = unify_types [] (result_type const_ty) expected in
          let const_ty' = subst_ty subst const_ty in
          (TConst (n, const_ty'), [])
      | None -> (TVar (n, expected), [ (n, expected) ]))
  | App (_f, _x) -> (
      let rec get_ctor_and_args tm =
        match tm with
        | Var n -> (n, [])
        | App (f, x) ->
            let ctor, args = get_ctor_and_args f in
            (ctor, args @ [ x ])
        | _ -> failwith "invalid pattern"
      in
      let ctor_name, ctor_args = get_ctor_and_args tm in
      match List.assoc_opt ctor_name env.constants with
      | Some const_ty ->
          let const_ty = freshen_ty const_ty in
          let subst = unify_types [] (result_type const_ty) expected in
          let const_ty' = subst_ty subst const_ty in
          let rec check_args ty args =
            match (ty, args) with
            | _, [] -> []
            | TyApp ("fun", [ arg_ty; ret_ty ]), arg :: rest ->
                let arg', bindings = check_pattern env arg arg_ty in
                (arg', bindings) :: check_args ret_ty rest
            | _ -> failwith "too many arguments to constructor"
          in
          let checked_args = check_args const_ty' ctor_args in
          let targs = List.map fst checked_args in
          let bindings = List.concat_map snd checked_args in
          let result =
            List.fold_left
              (fun acc arg -> TApp (acc, arg, expected))
              (TConst (ctor_name, const_ty'))
              targs
          in
          (result, bindings)
      | None -> failwith ("unknown constructor: " ^ ctor_name))
  | _ -> failwith "invalid pattern"

let check_clause env func_ty clause =
  let args, body = clause in
  let rec go ty args env bindings =
    match (ty, args) with
    | _, [] -> (List.rev bindings, env, ty)
    | TyApp ("fun", [ arg_ty; ret_ty ]), arg :: rest ->
        let arg', new_bindings = check_pattern env arg arg_ty in
        let env' =
          List.fold_left (fun e (n, t) -> add_local n t e) env new_bindings
        in
        go ret_ty rest env' (arg' :: bindings)
    | _ -> failwith "too many arguments in clause"
  in
  let targs, env', ret_ty = go func_ty args env [] in
  let body' = check env' body ret_ty in
  (targs, body')

let make_constructor_type arg_types result_type =
  List.fold_right ty_fun arg_types result_type

let check_decl env decl =
  match decl with
  | DType (name, params, constrs) ->
      let env = add_type name (List.length params) env in
      let ty_params = List.map (fun p -> TyVar p) params in
      let result_ty = TyApp (name, ty_params) in
      let env =
        List.fold_left
          (fun e (cname, arg_tys) ->
            let full_ty = make_constructor_type arg_tys result_ty in
            add_constant cname full_ty e)
          env constrs
      in
      (TDType (name, params, constrs), env)
  | DDef (name, ty, body) ->
      let body' = check env body ty in
      let env = add_constant name ty env in
      (TDDef (name, ty, body'), env)
  | DFun (name, ty, clauses) ->
      let env' = add_constant name ty env in
      let tclauses = List.map (check_clause env' ty) clauses in
      let env = add_constant name ty env in
      (TDFun (name, ty, tclauses), env)
  | DTheorem (name, body) ->
      let body' = check env body ty_bool in
      (TDTheorem (name, body'), env)

let check_program prog =
  let rec go env = function
    | [] -> []
    | d :: ds ->
        let td, env' = check_decl env d in
        td :: go env' ds
  in
  go empty_env prog
