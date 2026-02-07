open Kernel
open Derived
open Inductive
open Parser
open Rewrite
module K = Kernel
module P = Parser

type env = {
  tyvars : string list;
  vars : (string * hol_type) list;
  inductives : (string * inductive_def) list;
  defs : (string * thm) list;
}

let empty_env = { tyvars = []; vars = []; inductives = []; defs = [] }

(* Application with type instantiation - if types don't match exactly,
   try to instantiate type variables in f to make it work *)
let make_app_inst f x =
  match make_app f x with
  | Ok app -> Ok app
  | Error _ -> (
      (* Types didn't match - try to instantiate *)
      let fty =
        match type_of_term f with Ok t -> t | Error _ -> K.TyVar "?"
      in
      let xty =
        match type_of_term x with Ok t -> t | Error _ -> K.TyVar "?"
      in
      match fty with
      | K.TyCon ("fun", [ arg_ty; _ ]) -> (
          match type_match [] arg_ty xty with
          | Some tysub ->
              let f' = term_type_subst tysub f in
              make_app f' x
          | None -> Error (`MakeAppTypesDontAgree (fty, xty)))
      | _ -> Error (`MakeAppTypesDontAgree (fty, xty)))

let rec get_hol_arg_types hty =
  match hty with
  | K.TyCon ("fun", [ arg; rest ]) -> arg :: get_hol_arg_types rest
  | _ -> []

(* Type elaboration *)
let rec elab_ty env (ty : P.ty) : hol_type =
  match ty with
  | P.TyVar n ->
      if List.mem n env.tyvars then make_vartype n else K.TyCon (n, [])
  | P.TyCon (n, args) -> K.TyCon (n, List.map (elab_ty env) args)
  | P.TyFun (a, b) -> make_fun_ty (elab_ty env a) (elab_ty env b)

(* Find constructor info from inductive definitions *)
let find_constructor env name =
  env.inductives
  |> List.find_map (fun (_, def) ->
      List.assoc_opt name def.constructors
      |> Option.map (fun term -> (def, term)))

(* Helper for elaborating binary operations *)
let elab_binop env elab l r make_op =
  match elab env l with
  | Error e -> Error e
  | Ok l' -> (
      match elab env r with Error e -> Error e | Ok r' -> Ok (make_op l' r'))

(* Helper for elaborating quantifiers: forall x. body or exists x. body *)
let elab_quantifier env elab x body make_quant =
  match List.assoc_opt x env.vars with
  | Some ty -> (
      let var = K.Var (x, ty) in
      match elab env body with
      | Error e -> Error e
      | Ok body' -> Ok (make_quant var body'))
  | None ->
      Error
        (`InvariantViolation
           (Printf.sprintf "Quantifier variable %s not in scope" x))

(* Expression elaboration *)
let rec elab_expr env (e : P.expr) =
  match e with
  (* eq l r => safe_make_eq l r *)
  | P.App (P.App (P.Var "eq", l), r) -> (
      match elab_expr env l with
      | Error e -> Error e
      | Ok l' -> (
          match elab_expr env r with
          | Error e -> Error e
          | Ok r' -> safe_make_eq l' r'))
  (* imp p q => make_imp p q *)
  | P.App (P.App (P.Var "imp", l), r) -> elab_binop env elab_expr l r make_imp
  (* conj p q => make_conj p q *)
  | P.App (P.App (P.Var "conj", l), r) -> elab_binop env elab_expr l r make_conj
  (* disj p q => make_disj p q *)
  | P.App (P.App (P.Var "disj", l), r) -> elab_binop env elab_expr l r make_disj
  (* forall (λx. body) => make_forall x body *)
  | P.App (P.Var "forall", P.Lam (x, body)) ->
      elab_quantifier env elab_expr x body make_forall
  (* exists (λx. body) => make_exists x body *)
  | P.App (P.Var "exists", P.Lam (x, body)) ->
      elab_quantifier env elab_expr x body make_exists
  (* neg p => make_neg p *)
  | P.App (P.Var "neg", p) -> (
      match elab_expr env p with
      | Error e -> Error e
      | Ok p' -> Ok (make_neg p'))
  | P.Var "eq" -> make_const "=" []
  | P.Var name -> (
      match List.assoc_opt name env.vars with
      | Some ty -> Ok (K.Var (name, ty))
      | None -> (
          match find_constructor env name with
          | Some (_, term) -> Ok term
          | None -> make_const name []))
  | P.App (f, x) -> (
      match elab_expr env f with
      | Error e -> Error e
      | Ok f' -> (
          match elab_expr env x with
          | Error e -> Error e
          | Ok x' -> make_app_inst f' x'))
  | P.Lam (x, body) -> (
      match List.assoc_opt x env.vars with
      | Some ty -> (
          let var = K.Var (x, ty) in
          match elab_expr env body with
          | Error e -> Error e
          | Ok body' -> make_lam var body')
      | None ->
          Error
            (`InvariantViolation
               (Printf.sprintf "Lambda variable %s not in scope" x)))

(* Pattern elaboration - returns the pattern term and bindings introduced *)
let rec elab_pat env ind_ty (p : P.pat) : term * (string * hol_type) list =
  match p with
  | P.PVar name ->
      let var = K.Var (name, ind_ty) in
      (var, [ (name, ind_ty) ])
  | P.PCon (name, args) -> (
      match find_constructor env name with
      | Some (_, con_term) ->
          let con_ty =
            match con_term with K.Const (_, hty) -> hty | _ -> ind_ty
          in
          let arg_tys = get_hol_arg_types con_ty in
          let args_and_binds =
            List.map2
              (fun arg_p arg_ty ->
                match arg_p with
                | P.PVar n ->
                    let var = K.Var (n, arg_ty) in
                    (var, [ (n, arg_ty) ])
                | P.PCon _ -> elab_pat env arg_ty arg_p)
              args arg_tys
          in
          let arg_terms = List.map fst args_and_binds in
          let bindings = List.concat_map snd args_and_binds in
          let applied =
            List.fold_left (fun acc arg -> K.App (acc, arg)) con_term arg_terms
          in
          (applied, bindings)
      | None ->
          let var = K.Var (name, ind_ty) in
          (var, [ (name, ind_ty) ]))

(* Elaborate expression with recursive call substitution *)
(* rec_call_info: (func_name, [(rec_arg_name, r_var)]) *)
let rec elab_expr_with_rec env rec_call_info (e : P.expr) =
  let func_name, rec_arg_map = rec_call_info in
  match e with
  | P.App (P.App (P.Var fn, P.Var arg), rest) when fn = func_name -> (
      (* plus n m => r_i m where n maps to r_i *)
      match List.assoc_opt arg rec_arg_map with
      | Some r_var -> (
          match elab_expr_with_rec env rec_call_info rest with
          | Error e -> Error e
          | Ok rest' -> make_app r_var rest')
      | None -> (
          (* Not a recognized recursive arg, elaborate normally *)
          match
            elab_expr_with_rec env rec_call_info (P.App (P.Var fn, P.Var arg))
          with
          | Error e -> Error e
          | Ok f' -> (
              match elab_expr_with_rec env rec_call_info rest with
              | Error e -> Error e
              | Ok rest' -> make_app f' rest')))
  | P.App (P.Var fn, P.Var arg) when fn = func_name -> (
      (* plus n => r_i *)
      match List.assoc_opt arg rec_arg_map with
      | Some r_var -> Ok r_var
      | None ->
          (* Not a recursive call pattern we recognize *)
          Error
            (`InvariantViolation
               (Printf.sprintf "Recursive call %s %s not on bound recursive arg"
                  fn arg)))
  | P.Var "eq" -> make_const "=" []
  | P.Var name -> (
      match List.assoc_opt name env.vars with
      | Some ty -> Ok (K.Var (name, ty))
      | None -> (
          match find_constructor env name with
          | Some (_, term) -> Ok term
          | None -> make_const name []))
  | P.App (f, x) -> (
      match elab_expr_with_rec env rec_call_info f with
      | Error e -> Error e
      | Ok f' -> (
          match elab_expr_with_rec env rec_call_info x with
          | Error e -> Error e
          | Ok x' -> make_app_inst f' x'))
  | P.Lam (x, body) -> (
      match List.assoc_opt x env.vars with
      | Some ty -> (
          let var = K.Var (x, ty) in
          match elab_expr_with_rec env rec_call_info body with
          | Error e -> Error e
          | Ok body' -> make_lam var body')
      | None ->
          Error
            (`InvariantViolation
               (Printf.sprintf "Lambda variable %s not in scope" x)))

(* Elaborate a function definition clause for a recursive definition *)
let elab_def_clause env func_name ind_def ret_ty (pat, body) =
  (* Normalize pattern: PVar that matches a constructor becomes PCon with no args *)
  let con_name, args =
    match pat with
    | P.PCon (name, args) -> (name, args)
    | P.PVar name -> (name, [])
    (* Either a nullary constructor or variable *)
  in
  let con_term_opt = List.assoc_opt con_name ind_def.constructors in
  let arg_tys =
    match con_term_opt with
    | Some (K.Const (_, ty)) -> get_hol_arg_types ty
    | _ -> []
  in
  let arg_bindings =
    List.map2
      (fun p ty ->
        match p with P.PVar n -> K.Var (n, ty) | P.PCon _ -> K.Var ("_", ty))
      args arg_tys
  in
  let var_bindings =
    List.map2
      (fun p ty ->
        match p with P.PVar n -> (n, ty) | P.PCon (n, _) -> (n, ty))
      args arg_tys
  in
  (* For each recursive arg, create r_i variable and mapping *)
  let rec_info =
    List.filter_map
      (fun (i, (p, ty)) ->
        if ty = ind_def.ty then
          let arg_name = match p with P.PVar n -> n | P.PCon (n, _) -> n in
          let r_name = "r" ^ string_of_int i in
          Some (arg_name, r_name, ty)
        else None)
      (List.mapi (fun i (p, ty) -> (i, (p, ty))) (List.combine args arg_tys))
  in
  let rec_bindings = List.map (fun (_, r, _) -> (r, ret_ty)) rec_info in
  let rec_arg_map =
    List.map (fun (arg, r, _) -> (arg, K.Var (r, ret_ty))) rec_info
  in
  let env' = { env with vars = var_bindings @ rec_bindings @ env.vars } in
  match elab_expr_with_rec env' (func_name, rec_arg_map) body with
  | Error e -> Error e
  | Ok body' ->
      let rec_vars = List.map (fun (_, r, _) -> K.Var (r, ret_ty)) rec_info in
      let all_vars = arg_bindings @ rec_vars in
      let case_term =
        List.fold_right
          (fun v acc -> match make_lam v acc with Ok l -> l | Error _ -> acc)
          all_vars body'
      in
      Ok case_term

(* Elaborate a non-recursive definition with a single clause binding the first arg *)
let elab_simple_definition env name hol_ty (pat, body) =
  let arg_ty =
    match hol_ty with K.TyCon ("fun", [ arg; _ ]) -> arg | _ -> hol_ty
  in
  let var_name = match pat with P.PVar n -> n | P.PCon (n, _) -> n in
  let env' = { env with vars = (var_name, arg_ty) :: env.vars } in
  match elab_expr env' body with
  | Error e -> Error e
  | Ok body_term -> (
      let var = K.Var (var_name, arg_ty) in
      match make_lam var body_term with
      | Error e -> Error e
      | Ok lam_term -> (
          (* Create a simple definition: name = λvar. body
             Create constant, then axiom, then add to the_specifications *)
          match new_constant name hol_ty with
          | Error e -> Error e
          | Ok () -> (
              let def_const = K.Const (name, hol_ty) in
              let eq = Result.get_ok (safe_make_eq def_const lam_term) in
              match new_axiom eq with
              | Error e -> Error e
              | Ok thm ->
                  Hashtbl.add the_specifications name thm;
                  Ok thm)))

let elab_definition env name ty clauses =
  let hol_ty = elab_ty env ty in
  let rec_ty, ret_ty =
    match hol_ty with
    | K.TyCon ("fun", [ arg; rest ]) -> (arg, rest)
    | _ -> (hol_ty, hol_ty)
  in
  (* Find if there's an inductive type matching the first argument *)
  let ind_def_opt =
    env.inductives
    |> List.find_map (fun (_, def) ->
        if def.ty = rec_ty then Some def else None)
  in
  (* Check if clauses use constructor patterns (recursive) or variable patterns (simple)
     A PVar is a constructor if it matches a known constructor name *)
  let is_constructor_pattern pat ind_def =
    match pat with
    | P.PCon _ -> true
    | P.PVar name -> List.mem_assoc name ind_def.constructors
  in
  let is_recursive =
    match (clauses, ind_def_opt) with
    | [], _ -> false
    | (pat, _) :: _, Some ind_def -> is_constructor_pattern pat ind_def
    | (P.PCon _, _) :: _, None ->
        true (* PCon without inductive - will error later *)
    | (P.PVar _, _) :: _, None -> false
  in
  if not is_recursive then
    (* Non-recursive: single clause with variable pattern *)
    match clauses with
    | [ clause ] -> elab_simple_definition env name hol_ty clause
    | _ ->
        Error
          (`InvariantViolation
             "Non-recursive definition must have exactly one clause")
  else
    (* Recursive definition over an inductive type *)
    match ind_def_opt with
    | None ->
        Error (`InvariantViolation "No inductive type found for recursion")
    | Some ind_def -> (
        let rec build_cases acc = function
          | [] -> Ok (List.rev acc)
          | clause :: rest -> (
              match elab_def_clause env name ind_def ret_ty clause with
              | Error e -> Error e
              | Ok term -> build_cases (term :: acc) rest)
        in
        match build_cases [] clauses with
        | Error e -> Error e
        | Ok case_terms ->
            let ind_name = match rec_ty with K.TyCon (n, _) -> n | _ -> "" in
            define_recursive_function name ret_ty ind_name case_terms)

(* Elaborate a top-level definition and update environment *)
let elab_toplevel env (d : P.def) =
  match d with
  | P.Vartype names ->
      let env' = { env with tyvars = names @ env.tyvars } in
      Ok (env', None)
  | P.Variable (names, ty) ->
      let hol_ty = elab_ty env ty in
      let new_vars = List.map (fun n -> (n, hol_ty)) names in
      let env' = { env with vars = new_vars @ env.vars } in
      Ok (env', None)
  | P.Inductive (name, constrs) -> (
      let find_tyvars ty =
        let rec go acc = function
          | P.TyVar n -> if List.mem n acc then acc else n :: acc
          | P.TyCon (_, args) -> List.fold_left go acc args
          | P.TyFun (a, b) -> go (go acc a) b
        in
        go [] ty
      in
      let all_tyvars =
        constrs
        |> List.concat_map (fun (_, ty) -> find_tyvars ty)
        |> List.filter (fun tv -> List.mem tv env.tyvars)
        |> List.sort_uniq compare
      in
      let constr_specs =
        constrs
        |> List.map (fun (cname, cty) ->
            let rec get_args ty =
              match ty with
              | P.TyFun (arg, rest) -> elab_ty env arg :: get_args rest
              | _ -> []
            in
            { name = cname; arg_types = get_args cty })
      in
      match define_inductive name all_tyvars constr_specs with
      | Error e -> Error e
      | Ok ind_def ->
          let env' =
            { env with inductives = (name, ind_def) :: env.inductives }
          in
          Ok (env', None))
  | P.Def (name, ty, clauses) -> (
      match elab_definition env name ty clauses with
      | Error e -> Error e
      | Ok def_thm ->
          let env' = { env with defs = (name, def_thm) :: env.defs } in
          Ok (env', None))
  | P.Theorem (_name, expr) -> (
      match elab_expr env expr with
      | Error e -> Error e
      | Ok term -> Ok (env, Some term))

(* Elaborate a full program - returns (env, goals) where goals are terms to prove *)
let elaborate defs =
  let rec go env goals = function
    | [] -> Ok (env, List.rev goals)
    | d :: ds -> (
        match elab_toplevel env d with
        | Ok (env', None) -> go env' goals ds
        | Ok (env', Some goal) -> go env' (goal :: goals) ds
        | Error e -> Error e)
  in
  go empty_env [] defs

let elaborate_string s =
  let defs = parse_string s in
  elaborate defs

let goals_from_string s =
  match elaborate_string s with Ok (_, goals) -> goals | Error _ -> []
