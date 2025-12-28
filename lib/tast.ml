(* typechecker.ml *)

open Ast

(* --- Types with unification variables --- *)

type tyvar = Unbound of int | Link of ty
and ty = TyVar of tyvar ref | TyApp of name * ty list
[@@deriving show]

let ty_counter = ref 0

let fresh_tyvar () =
  let n = !ty_counter in
  ty_counter := n + 1;
  TyVar (ref (Unbound n))

(* --- TAST --- *)

type tpattern =
  | TPVar of name * ty
  | TPApp of name * tpattern list * ty
[@@deriving show]

type ttm =
  | TVar of name * ty
  | TConst of name * ty
  | TApp of ttm * ttm * ty
  | TLam of name * ty * ttm * ty
  | TLet of name * ty * ttm * ttm * ty
  | TIf of ttm * ttm * ttm * ty
  | TForall of name * ty * ttm * ty
  | TExists of name * ty * ttm * ty
  | TEq of ttm * ttm * ty
[@@deriving show]

type tconstructor = name * ty list
[@@deriving show]

type tclause = tpattern list * ttm
[@@deriving show]

type tdecl =
  | TDType of name * name list * tconstructor list
  | TDDef of name * ty * ttm
  | TDFun of name * ty * tclause list
  | TDTheorem of name * ttm
[@@deriving show]

type tprogram = tdecl list
[@@deriving show]


(* --- Environment --- *)

type env = {
  types : (name * int) list;
  constants : (name * ty) list;
  locals : (name * ty) list;
}

let empty_env = {
  types = [("bool", 0); ("fun", 2)];
  constants = [];
  locals = [];
}

let add_type name arity env =
  { env with types = (name, arity) :: env.types }

let add_constant name ty env =
  { env with constants = (name, ty) :: env.constants }

let add_local name ty env =
  { env with locals = (name, ty) :: env.locals }

let add_locals bindings env =
  List.fold_left (fun e (n, t) -> add_local n t e) env bindings

(* --- Type utilities --- *)

let rec occurs (r : tyvar ref) (t : ty) : bool =
  match t with
  | TyVar r' ->
      if r == r' then true
      else (match !r' with Link t' -> occurs r t' | Unbound _ -> false)
  | TyApp (_, args) -> List.exists (occurs r) args

let rec unify (t1 : ty) (t2 : ty) : unit =
  match (t1, t2) with
  | TyVar r1, TyVar r2 when r1 == r2 -> ()
  | TyVar { contents = Link t1' }, t2 -> unify t1' t2
  | t1, TyVar { contents = Link t2' } -> unify t1 t2'
  | TyVar ({ contents = Unbound _ } as r), t ->
      if occurs r t then failwith "occurs check failed";
      r := Link t
  | t, TyVar ({ contents = Unbound _ } as r) ->
      if occurs r t then failwith "occurs check failed";
      r := Link t
  | TyApp (n1, args1), TyApp (n2, args2) ->
      if n1 <> n2 then failwith ("type mismatch: " ^ n1 ^ " vs " ^ n2);
      if List.length args1 <> List.length args2 then
        failwith ("arity mismatch for type " ^ n1);
      List.iter2 unify args1 args2

let rec resolve (t : ty) : ty =
  match t with
  | TyVar { contents = Link t' } -> resolve t'
  | TyVar { contents = Unbound _ } -> t
  | TyApp (n, args) -> TyApp (n, List.map resolve args)

let ty_bool = TyApp ("bool", [])
let ty_arrow a b = TyApp ("fun", [a; b])

let rec instantiate_surf_ty (subst : (name * ty) list) (sty : surf_ty) : ty =
  match sty with
  | STyVar n ->
      (match List.assoc_opt n subst with
       | Some t -> t
       | None -> failwith ("unbound type variable: " ^ n))
  | STyApp (n, args) ->
      TyApp (n, List.map (instantiate_surf_ty subst) args)

let instantiate (t : ty) : ty =
  let rec collect_tyvars acc t =
    match t with
    | TyVar { contents = Unbound n } ->
        if List.mem n acc then acc else n :: acc
    | TyVar { contents = Link t' } -> collect_tyvars acc t'
    | TyApp (_, args) -> List.fold_left collect_tyvars acc args
  in
  let vars = collect_tyvars [] t in
  if vars = [] then t
  else
    let subst = List.map (fun v -> (v, fresh_tyvar ())) vars in
    let rec go t =
      match t with
      | TyVar { contents = Unbound n } ->
          (match List.assoc_opt n subst with Some t' -> t' | None -> t)
      | TyVar { contents = Link t' } -> go t'
      | TyApp (n, args) -> TyApp (n, List.map go args)
    in
    go t

(* --- Checking types --- *)

let rec check_surf_ty (env : env) (sty : surf_ty) : ty =
  match sty with
  | STyVar n -> TyVar (ref (Unbound (Hashtbl.hash n)))
  | STyApp (n, args) ->
      (match List.assoc_opt n env.types with
       | None -> failwith ("unknown type: " ^ n)
       | Some arity ->
           if List.length args <> arity then
             failwith ("type " ^ n ^ " expects " ^ string_of_int arity ^ " arguments");
           TyApp (n, List.map (check_surf_ty env) args))

(* --- Checking terms --- *)

let lookup_var (env : env) (name : name) : [ `Local of ty | `Const of ty ] =
  match List.assoc_opt name env.locals with
  | Some t -> `Local t
  | None ->
      (match List.assoc_opt name env.constants with
       | Some t -> `Const t
       | None -> failwith ("unbound variable: " ^ name))

let rec check_term (env : env) (tm : surf_tm) : ttm * ty =
  match tm with
  | SVar n ->
      (match lookup_var env n with
       | `Local t -> (TVar (n, t), t)
       | `Const t ->
           let t' = instantiate t in
           (TConst (n, t'), t'))

  | SApp (f, x) ->
      let f', tf = check_term env f in
      let x', tx = check_term env x in
      let tr = fresh_tyvar () in
      unify tf (ty_arrow tx tr);
      let tr' = resolve tr in
      (TApp (f', x', tr'), tr')

  | SLam (x, body) ->
      let tx = fresh_tyvar () in
      let env' = add_local x tx env in
      let body', tbody = check_term env' body in
      let tx' = resolve tx in
      let tfull = ty_arrow tx' tbody in
      (TLam (x, tx', body', tfull), tfull)

  | SLet (x, bound, body) ->
      let bound', tbound = check_term env bound in
      let env' = add_local x tbound env in
      let body', tbody = check_term env' body in
      (TLet (x, tbound, bound', body', tbody), tbody)

  | SIf (cond, then_, else_) ->
      let cond', tcond = check_term env cond in
      unify tcond ty_bool;
      let then_', tthen = check_term env then_ in
      let else_', telse = check_term env else_ in
      unify tthen telse;
      let t = resolve tthen in
      (TIf (cond', then_', else_', t), t)

  | SForall (bindings, body) ->
      let typed_bindings = List.map (fun (n, sty) -> (n, check_surf_ty env sty)) bindings in
      let env' = add_locals typed_bindings env in
      let body', tbody = check_term env' body in
      unify tbody ty_bool;
      let result = List.fold_right
        (fun (n, t) acc -> TForall (n, t, acc, ty_bool))
        typed_bindings body'
      in
      (result, ty_bool)

  | SExists (bindings, body) ->
      let typed_bindings = List.map (fun (n, sty) -> (n, check_surf_ty env sty)) bindings in
      let env' = add_locals typed_bindings env in
      let body', tbody = check_term env' body in
      unify tbody ty_bool;
      let result = List.fold_right
        (fun (n, t) acc -> TExists (n, t, acc, ty_bool))
        typed_bindings body'
      in
      (result, ty_bool)

  | SEq (lhs, rhs) ->
      let lhs', tlhs = check_term env lhs in
      let rhs', trhs = check_term env rhs in
      unify tlhs trhs;
      let t = resolve tlhs in
      (TEq (lhs', rhs', t), ty_bool)

(* --- Checking patterns --- *)

let rec check_pattern (env : env) (pat : pattern) (expected : ty) : tpattern * (name * ty) list =
  match pat with
  | PVar n -> (TPVar (n, expected), [(n, expected)])
  | PApp (ctor, args) ->
      (match List.assoc_opt ctor env.constants with
       | None -> failwith ("unknown constructor: " ^ ctor)
       | Some ctor_ty ->
           let ctor_ty' = instantiate ctor_ty in
           let rec go ty pats =
             match (ty, pats) with
             | t, [] ->
                 unify t expected;
                 ([], [])
             | TyApp ("fun", [arg_ty; rest_ty]), p :: ps ->
                 let tp, binds = check_pattern env p arg_ty in
                 let tps, binds' = go rest_ty ps in
                 (tp :: tps, binds @ binds')
             | _, _ :: _ -> failwith ("constructor " ^ ctor ^ " applied to too many arguments")
           in
           let tpats, bindings = go ctor_ty' args in
           (TPApp (ctor, tpats, expected), bindings))

(* --- Checking clauses --- *)

let check_clause (env : env) (clause : clause) (expected : ty) : tclause =
  let (pats, body) = clause in
  let rec go ty pats env =
    match (ty, pats) with
    | t, [] -> ([], env, t)
    | TyApp ("fun", [arg_ty; rest_ty]), p :: ps ->
        let tp, bindings = check_pattern env p arg_ty in
        let tps, env', result_ty = go rest_ty ps (add_locals bindings env) in
        (tp :: tps, env', result_ty)
    | _, _ :: _ -> failwith "too many patterns for function type"
  in
  let tpats, env', result_ty = go expected pats env in
  let body', tbody = check_term env' body in
  unify tbody result_ty;
  (tpats, body')

(* --- Checking declarations --- *)

let check_decl (env : env) (d : decl) : tdecl * env =
  match d with
  | DType (name, params, constrs) ->
      let env = add_type name (List.length params) env in
      let param_subst = List.map (fun p -> (p, fresh_tyvar ())) params in
      let result_ty = TyApp (name, List.map snd param_subst) in
      let check_constr (cname, arg_tys) =
        let targs = List.map (instantiate_surf_ty param_subst) arg_tys in
        let full_ty = List.fold_right ty_arrow targs result_ty in
        (cname, targs, full_ty)
      in
      let tconstrs = List.map check_constr constrs in
      let env = List.fold_left (fun e (cname, _, full_ty) -> add_constant cname full_ty e) env tconstrs in
      (TDType (name, params, List.map (fun (n, args, _) -> (n, args)) tconstrs), env)

  | DDef (name, sty, body) ->
      let ty = check_surf_ty env sty in
      let body', tbody = check_term env body in
      unify ty tbody;
      let ty' = resolve ty in
      let env = add_constant name ty' env in
      (TDDef (name, ty', body'), env)

  | DFun (name, sty, clauses) ->
      let ty = check_surf_ty env sty in
      (* Add function to env for recursive calls *)
      let env' = add_constant name ty env in
      let tclauses = List.map (fun c -> check_clause env' c ty) clauses in
      let ty' = resolve ty in
      let env = add_constant name ty' env in
      (TDFun (name, ty', tclauses), env)

  | DTheorem (name, body) ->
      let body', tbody = check_term env body in
      unify tbody ty_bool;
      (TDTheorem (name, body'), env)

(* --- Checking programs --- *)

let check_program (prog : program) : tprogram =
  let rec go env = function
    | [] -> []
    | d :: ds ->
        let td, env' = check_decl env d in
        td :: go env' ds
  in
  go empty_env prog
