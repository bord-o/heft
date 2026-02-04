open Kernel
open Inductive
open Parser
module K = Kernel
module P = Parser

type env = {
  tyvars : string list;
  vars : (string * hol_type) list;
  inductives : (string * inductive_def) list;
  defs : (string * thm) list;
}

let empty_env = { tyvars = []; vars = []; inductives = []; defs = [] }

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
          | Ok x' -> make_app f' x'))
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
          | Ok x' -> make_app f' x'))
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

(* Elaborate a function definition clause *)
let elab_def_clause env func_name ind_def ret_ty (pat, body) =
  match pat with
  | P.PVar _ -> elab_expr env body
  | P.PCon (con_name, args) -> (
      let con_term_opt = List.assoc_opt con_name ind_def.constructors in
      let arg_tys =
        match con_term_opt with
        | Some (K.Const (_, ty)) -> get_hol_arg_types ty
        | _ -> []
      in
      let arg_bindings =
        List.map2
          (fun p ty ->
            match p with
            | P.PVar n -> K.Var (n, ty)
            | P.PCon _ -> K.Var ("_", ty))
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
              let arg_name =
                match p with P.PVar n -> n | P.PCon (n, _) -> n
              in
              let r_name = "r" ^ string_of_int i in
              Some (arg_name, r_name, ty)
            else None)
          (List.mapi
             (fun i (p, ty) -> (i, (p, ty)))
             (List.combine args arg_tys))
      in
      let rec_bindings = List.map (fun (_, r, _) -> (r, ret_ty)) rec_info in
      let rec_arg_map =
        List.map (fun (arg, r, _) -> (arg, K.Var (r, ret_ty))) rec_info
      in
      let env' = { env with vars = var_bindings @ rec_bindings @ env.vars } in
      match elab_expr_with_rec env' (func_name, rec_arg_map) body with
      | Error e -> Error e
      | Ok body' ->
          let rec_vars =
            List.map (fun (_, r, _) -> K.Var (r, ret_ty)) rec_info
          in
          let all_vars = arg_bindings @ rec_vars in
          let case_term =
            List.fold_right
              (fun v acc ->
                match make_lam v acc with Ok l -> l | Error _ -> acc)
              all_vars body'
          in
          Ok case_term)

let elab_definition env name _over ty clauses =
  let hol_ty = elab_ty env ty in
  let rec_ty, ret_ty =
    match hol_ty with
    | K.TyCon ("fun", [ arg; rest ]) -> (arg, rest)
    | _ -> (hol_ty, hol_ty)
  in
  let ind_def_opt =
    env.inductives
    |> List.find_map (fun (_, def) ->
        if def.ty = rec_ty then Some def else None)
  in
  match ind_def_opt with
  | None -> Error (`InvariantViolation "No inductive type found for recursion")
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
  | P.Def (name, over, ty, clauses) -> (
      match elab_definition env name over ty clauses with
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
