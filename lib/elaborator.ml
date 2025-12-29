open Parse
open Inductive
open Ast

module Elab = struct
  open Tast
  module K = Kernel
  module I = Inductive

  let rec elab_ty = function
    | TyVar n -> K.TyVar n
    | TyApp (name, args) -> K.TyCon (name, List.map elab_ty args)

  let rec elab_tm = function
    | TVar (n, ty) -> K.Var (n, elab_ty ty)
    | TConst (n, ty) -> K.Const (n, elab_ty ty)
    | TApp (f, x, _) -> K.App (elab_tm f, elab_tm x)
    | TLam (n, ty, body, _) -> K.Lam (K.Var (n, elab_ty ty), elab_tm body)
    | TLet (n, ty, bound, body, _) ->
        let var = K.Var (n, elab_ty ty) in
        let lam = K.Lam (var, elab_tm body) in
        K.App (lam, elab_tm bound)
    | TIf (_, _, _, _) -> failwith "if not yet supported in elaboration"
    | TEq (l, r, _) -> (
        let l' = elab_tm l in
        let r' = elab_tm r in
        match K.safe_make_eq l' r' with
        | Ok eq -> eq
        | Error e -> failwith ("elab_tm eq: " ^ K.show_kernel_error e))
    | TForall (bindings, body, _) ->
        let body' = elab_tm body in
        List.fold_right
          (fun (n, ty) acc ->
            let var = K.Var (n, elab_ty ty) in
            Derived.make_forall var acc)
          bindings body'
    | TExists (bindings, body, _) ->
        let body' = elab_tm body in
        List.fold_right
          (fun (n, ty) acc ->
            let var = K.Var (n, elab_ty ty) in
            Derived.make_exists var acc)
          bindings body'

  let elab_constr_spec (name, arg_tys) : K.constructor_spec =
    { name; arg_types = List.map elab_ty arg_tys }

  let elab_type_decl name params constrs =
    let specs = List.map elab_constr_spec constrs in
    match I.define_inductive name params specs with
    | Ok def -> def
    | Error e -> failwith ("define_inductive: " ^ K.show_kernel_error e)

  let elab_def name ty body =
    let hol_ty = elab_ty ty in
    let hol_body = elab_tm body in
    let var = K.Var (name, hol_ty) in
    match K.safe_make_eq var hol_body with
    | Ok eq -> (
        match K.new_basic_definition eq with
        | Ok thm -> thm
        | Error e -> failwith ("new_basic_definition: " ^ K.show_kernel_error e)
        )
    | Error e -> failwith ("elab_def eq: " ^ K.show_kernel_error e)

  let find_inductive_for_type ty =
    let get_head = function
      | TyApp (name, _) -> name
      | _ -> failwith "expected type application"
    in
    let type_name = get_head ty in
    match Hashtbl.find_opt K.the_inductives type_name with
    | Some def -> def
    | None -> failwith ("no inductive definition for type: " ^ type_name)

  let rec extract_pattern_info tm =
    match tm with
    | TConst (name, ty) -> (name, [], elab_ty ty)
    | TApp (f, arg, _) ->
        let ctor_name, args, ctor_ty = extract_pattern_info f in
        (ctor_name, args @ [ arg ], ctor_ty)
    | TVar (name, ty) -> (name, [], elab_ty ty)
    | _ -> failwith "invalid pattern structure"

  let get_arg_types func_ty =
    let rec go acc = function
      | TyApp ("fun", [ arg; ret ]) -> go (arg :: acc) ret
      | ret -> (List.rev acc, ret)
    in
    go [] func_ty

  let elab_fun_clause func_name func_ty _inductive_def clause _env =
    let patterns, body = clause in
    let arg_tys, ret_ty = get_arg_types func_ty in

    if List.length patterns = 0 then
      failwith "function clause must have at least one pattern";

    let first_pattern = List.hd patterns in
    let rest_patterns = List.tl patterns in

    let ctor_name, ctor_args, _ = extract_pattern_info first_pattern in

    let ctor_arg_tms =
      List.map
        (fun a ->
          match a with
          | TVar (n, ty) -> (n, elab_ty ty)
          | _ -> failwith "constructor argument must be a variable")
        ctor_args
    in

    let inductive_ty = elab_ty (List.hd arg_tys) in
    let additional_arg_tys = List.tl arg_tys in

    (* The recursive result type is the full return type including additional args *)
    let full_ret_ty =
      List.fold_right
        (fun arg_ty acc -> K.make_fun_ty (elab_ty arg_ty) acc)
        additional_arg_tys (elab_ty ret_ty)
    in

    let recursive_args =
      List.filter (fun (_, ty) -> ty = inductive_ty) ctor_arg_tms
    in

    let recursive_result_vars =
      List.map
        (fun (name, _) ->
          let r_name = "r_" ^ name in
          (name, K.Var (r_name, full_ret_ty)))
        recursive_args
    in

    let additional_args =
      List.map2
        (fun pat ty ->
          match pat with
          | TVar (n, _) -> (n, elab_ty ty)
          | _ -> failwith "additional argument must be a variable")
        rest_patterns additional_arg_tys
    in

    let rec subst_recursive_calls tm =
      match tm with
      | TApp (TApp (TConst (fn, _), TVar (arg_name, _), _), rest, _)
        when fn = func_name && List.mem_assoc arg_name recursive_result_vars ->
          let r_var = List.assoc arg_name recursive_result_vars in
          let rest' = subst_recursive_calls rest in
          K.App (r_var, rest')
      | TApp (TConst (fn, _), TVar (arg_name, _), _)
        when fn = func_name && List.mem_assoc arg_name recursive_result_vars ->
          List.assoc arg_name recursive_result_vars
      | TApp (f, x, _) ->
          K.App (subst_recursive_calls f, subst_recursive_calls x)
      | TLam (n, ty, body, _) ->
          K.Lam (K.Var (n, elab_ty ty), subst_recursive_calls body)
      | TLet (n, ty, bound, body, _) ->
          let var = K.Var (n, elab_ty ty) in
          K.App
            ( K.Lam (var, subst_recursive_calls body),
              subst_recursive_calls bound )
      | TVar (n, ty) -> K.Var (n, elab_ty ty)
      | TConst (n, ty) -> K.Const (n, elab_ty ty)
      | TEq (l, r, _) -> (
          match
            K.safe_make_eq (subst_recursive_calls l) (subst_recursive_calls r)
          with
          | Ok eq -> eq
          | Error e -> failwith ("subst eq: " ^ K.show_kernel_error e))
      | TIf _ -> failwith "if not supported"
      | TForall (bindings, body, _) ->
          let body' = subst_recursive_calls body in
          List.fold_right
            (fun (n, ty) acc ->
              let var = K.Var (n, elab_ty ty) in
              Derived.make_forall var acc)
            bindings body'
      | TExists (bindings, body, _) ->
          let body' = subst_recursive_calls body in
          List.fold_right
            (fun (n, ty) acc ->
              let var = K.Var (n, elab_ty ty) in
              Derived.make_exists var acc)
            bindings body'
    in

    let body' = subst_recursive_calls body in

    let with_additional_args =
      List.fold_right
        (fun (n, ty) acc -> K.Lam (K.Var (n, ty), acc))
        additional_args body'
    in

    let with_recursive_results =
      List.fold_right
        (fun (_, r_var) acc -> K.Lam (r_var, acc))
        recursive_result_vars with_additional_args
    in

    let with_ctor_args =
      List.fold_right
        (fun (n, ty) acc -> K.Lam (K.Var (n, ty), acc))
        ctor_arg_tms with_recursive_results
    in

    (ctor_name, with_ctor_args)

  let get_inductive_type_name = function
    | TyApp (name, _) -> name
    | _ -> failwith "expected type application"

  let elab_fun name ty clauses env =
    let arg_tys, ret_ty = get_arg_types ty in
    if List.length arg_tys = 0 then
      failwith "recursive function must have at least one argument";

    let first_arg_ty = List.hd arg_tys in
    let inductive_type_name = get_inductive_type_name first_arg_ty in
    let inductive_def = find_inductive_for_type first_arg_ty in

    let ctor_names = List.map fst inductive_def.constructors in

    let branch_map =
      List.map
        (fun clause -> elab_fun_clause name ty inductive_def clause env)
        clauses
    in

    let branches =
      List.map
        (fun ctor_name ->
          match List.assoc_opt ctor_name branch_map with
          | Some branch -> branch
          | None -> failwith ("missing clause for constructor: " ^ ctor_name))
        ctor_names
    in

    let full_ret_ty =
      List.fold_right
        (fun arg_ty acc -> K.make_fun_ty (elab_ty arg_ty) acc)
        (List.tl arg_tys) (elab_ty ret_ty)
    in

    match
      define_recursive_function name full_ret_ty inductive_type_name branches
    with
    | Ok thm -> thm
    | Error e -> failwith ("define_recursive_function: " ^ K.show_kernel_error e)

  let elab_decl env decl =
    match decl with
    | TDType (name, params, constrs) ->
        let _ = elab_type_decl name params constrs in
        env
    | TDDef (name, ty, body) ->
        let _ = elab_def name ty body in
        env
    | TDFun (name, ty, clauses) ->
        let _ = elab_fun name ty clauses env in
        env
    | TDTheorem (name, body) ->
        let _ = name in
        let _ = elab_tm body in
        env

  let elab_program tprog =
    let _ = List.fold_left elab_decl Tast.empty_env tprog in
    ()
end

let elaborate prog =
  let tprog = Tast.check_program prog in
  Elab.elab_program tprog

let parse_and_elaborate s =
  let ast = parse_string s in
  let tast = Tast.check_program ast in
  Elab.elab_program tast
