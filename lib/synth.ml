(* AI Code Ahead.
   term enumeration is a straightforward problem for the most part
   when the language is STLC like in HOL. There are some facilities
   for setting up goals that enable program synthesis through backtracking
   search of existentials representing functions of each part of an 
   inductive type. By following the structure of the inductive type
   and structuring the specs as a conjunction of goals that should
   hold under an implementation we can solve a synthesis problem
   by providing a proof powerful enough to solve basic rewriting goals
   (auto_dfs_tac) and running the whole thing under a handler like
   with_best_first to try all of the enumerated terms under the spec.

 *)

(** Type-directed term enumeration.

    Enumerates well-typed, beta-normal terms of a given type up to a given
    depth.

    Five cases: 1. Variables from context matching the target type 2. Extra
    constants provided by the caller (e.g. defined functions, T, F) 3.
    Constructors of inductive types (looked up from the_inductives) 4. Lambda
    abstractions when target is a function type 5. Applications f e where f : A
    -> target and e : A

    After enumeration, terms are beta-normalized (via Derived.deep_beta) and
    deduplicated. Beta-redexes are not generated during enumeration to avoid
    redundant work.

    Extra constants can be curried functions. When an extra constant has a
    curried type like [A -> B -> C] and the target type is [C], the enumerator
    will try filling arguments recursively to produce fully applied terms.
    Partial applications are also produced when the partially applied type
    matches the target. *)

open Kernel
open Derived

type ctx = (string * hol_type) list

(** Extract argument types from a curried function type given a target return
    type. e.g. arg_types_of (A -> B -> T) T = Some [A; B] arg_types_of T T =
    Some [] arg_types_of (A -> B) T = None *)
let rec arg_types_of ty target =
  if ty = target then Some []
  else
    match ty with
    | TyCon ("fun", [ a; rest ]) ->
        Option.map (fun args -> a :: args) (arg_types_of rest target)
    | _ -> None

(** Collect all types that appear in the context, goal, and extra constant
    argument positions. These are the only types we consider as argument types
    for general applications. *)
let candidate_types (ctx : ctx) (extra : (string * hol_type) list)
    (goal_ty : hol_type) : hol_type list =
  let from_ctx = List.map snd ctx in
  let rec all_arg_types = function
    | TyCon ("fun", [ a; rest ]) -> a :: all_arg_types rest
    | _ -> []
  in
  let from_extra = extra |> List.concat_map (fun (_, ty) -> all_arg_types ty) in
  (goal_ty :: from_ctx) @ from_extra |> List.sort_uniq compare

let fresh_name (ctx : ctx) (base : string) =
  let names = List.map fst ctx in
  if not (List.mem base names) then base
  else
    let rec aux i =
      let s = base ^ string_of_int i in
      if List.mem s names then aux (i + 1) else s
    in
    aux 0

let name_hint = function
  | TyCon ("bool", []) -> "b"
  | TyCon ("num", []) | TyCon ("nat", []) -> "n"
  | TyVar s -> String.lowercase_ascii s
  | TyCon (s, _) ->
      if String.length s > 0 then String.make 1 (Char.lowercase_ascii s.[0])
      else "x"

let rec cartesian = function
  | [] -> [ [] ]
  | xs :: rest ->
      let rest' = cartesian rest in
      List.concat_map (fun x -> List.map (fun r -> x :: r) rest') xs

(** Beta-normalize a term using Derived.deep_beta. deep_beta returns a theorem
    [|- tm = tm'], we extract tm'. Returns the original term if normalization
    fails. *)
let normalize (tm : term) : term =
  match Derived.deep_beta tm with
  | Ok thm -> (
      match destruct_eq (concl thm) with Ok (_, rhs) -> rhs | Error _ -> tm)
  | Error _ -> tm

(** Build a curried application [f a1 a2 ... an], returning None if any
    application fails the type check. *)
let build_app (f : term) (args : term list) : term option =
  List.fold_left
    (fun acc arg ->
      match acc with
      | Some t -> (
          match make_app t arg with Ok t' -> Some t' | Error _ -> None)
      | None -> None)
    (Some f) args

(** Main entry point. Enumerates well-typed terms of type [ty] in context [ctx]
    up to the given [depth]. Provide [~extra] for additional constants to
    consider (e.g. defined functions like append, T, F).

    Terms are beta-normalized and deduplicated before returning. *)
let rec enumerate ?(extra : (string * hol_type) list = []) (ctx : ctx)
    (ty : hol_type) (depth : int) : term list =
  if depth <= 0 then []
  else
    let vars = enum_vars ctx ty in
    let consts = enum_extra_exact extra ty in
    let constrs = enum_constructors ~extra ctx ty depth in
    let lams = enum_lambdas ~extra ctx ty depth in
    let apps = enum_applications ~extra ctx ty depth in
    let raw = vars @ consts @ constrs @ lams @ apps in
    raw |> List.map normalize |> List.sort_uniq compare

(** Variables in context matching the type *)
and enum_vars (ctx : ctx) (ty : hol_type) : term list =
  List.filter_map
    (fun (name, vty) -> if vty = ty then Some (Var (name, ty)) else None)
    ctx

(** Extra constants whose type matches exactly (no application needed) *)
and enum_extra_exact extra ty : term list =
  extra
  |> List.filter_map (fun (name, cty) ->
      if cty = ty then Some (Const (name, cty)) else None)

(** Extra constants applied to fill arguments to reach the target type. For a
    constant [f : A -> B -> C] and target [B -> C], yields [f a] for each
    [a : A]. For target [C], yields [f a b] for each [a : A, b : B]. Also yields
    partial applications when the partial type matches. *)
and enum_extra_applied ~extra (ctx : ctx) (ty : hol_type) (depth : int) :
    term list =
  if depth <= 0 then []
  else
    extra
    |> List.concat_map (fun (name, cty) ->
        (* Skip if the type matches exactly — already handled by enum_extra_exact *)
        if cty = ty then []
        else
          let rec try_partial f fty remaining_depth =
            if fty = ty then [ f ]
            else
              match fty with
              | TyCon ("fun", [ arg_ty; ret_ty ]) ->
                  if remaining_depth <= 0 then []
                  else
                    let args =
                      enumerate ~extra ctx arg_ty (remaining_depth - 1)
                    in
                    args
                    |> List.concat_map (fun a ->
                        match make_app f a with
                        | Ok t -> try_partial t ret_ty (remaining_depth - 1)
                        | Error _ -> [])
              | _ -> []
          in
          try_partial (Const (name, cty)) cty depth)

(** Constructor applications for inductive types *)
and enum_constructors ~extra (ctx : ctx) (ty : hol_type) (depth : int) :
    term list =
  match ty with
  | TyCon (tyname, ty_args) -> (
      match Hashtbl.find_opt the_inductives tyname with
      | None -> []
      | Some idef ->
          let type_sub =
            match destruct_type idef.ty with
            | Ok (_, def_params) -> (
                try List.combine def_params ty_args
                with Invalid_argument _ -> [])
            | Error _ -> []
          in
          let target = type_substitution type_sub idef.ty in
          idef.constructors
          |> List.concat_map (fun (cname, cconst) ->
              let cty =
                match cconst with
                | Const (_, t) -> type_substitution type_sub t
                | _ -> (
                    match type_of_var cconst with
                    | Ok ty -> type_substitution type_sub ty
                    | Error _ -> type_substitution type_sub (TyVar "?"))
              in
              match arg_types_of cty target with
              | Some [] -> [ Const (cname, cty) ]
              | Some arg_tys ->
                  if depth <= 1 then []
                  else
                    let arg_enums =
                      List.map
                        (fun aty -> enumerate ~extra ctx aty (depth - 1))
                        arg_tys
                    in
                    cartesian arg_enums
                    |> List.filter_map (fun args ->
                        build_app (Const (cname, cty)) args)
              | None -> []))
  | _ -> []

(** Lambda abstractions when target is [A -> B] *)
and enum_lambdas ~extra (ctx : ctx) (ty : hol_type) (depth : int) : term list =
  match ty with
  | TyCon ("fun", [ arg_ty; ret_ty ]) ->
      if depth <= 1 then []
      else
        let vname = fresh_name ctx (name_hint arg_ty) in
        let bvar = Var (vname, arg_ty) in
        let ctx' = (vname, arg_ty) :: ctx in
        enumerate ~extra ctx' ret_ty (depth - 1)
        |> List.filter_map (fun body ->
            match make_lam bvar body with Ok t -> Some t | Error _ -> None)
  | _ -> []

(** Applications [f e] where [f : A -> ty] and [e : A]. Skips cases where [f] is
    a lambda to avoid generating beta-redexes. Also includes partially applied
    extra constants. *)
and enum_applications ~extra (ctx : ctx) (ty : hol_type) (depth : int) :
    term list =
  if depth <= 1 then []
  else
    let from_extra = enum_extra_applied ~extra ctx ty depth in
    let arg_tys = candidate_types ctx extra ty in
    let from_general =
      arg_tys
      |> List.concat_map (fun arg_ty ->
          let fun_ty = TyCon ("fun", [ arg_ty; ty ]) in
          let funcs = enumerate ~extra ctx fun_ty (depth - 1) in
          let args = enumerate ~extra ctx arg_ty (depth - 1) in
          funcs
          |> List.concat_map (fun f ->
              match f with
              | Lam _ -> []
              | _ ->
                  args
                  |> List.filter_map (fun a ->
                      match make_app f a with Ok t -> Some t | Error _ -> None)))
    in
    from_extra @ from_general

(** Automated synthesis goal generation.

    Given a function type, an inductive type to recurse on (always the first
    argument), and concrete test cases, generates a HOL goal term of the form:

    ∃nil_case. ∃cons_case. ... (equations for each constructor) ==> (conjunction
    of test cases)

    The generated goal can be solved by exists_tac with enumeration followed by
    intros and simplification. *)

(** Decompose a curried function type into argument types and return type. e.g.
    split_fun_type (A -> B -> C) = ([A; B], C) *)
let split_fun_type ty =
  let rec go acc = function
    | TyCon ("fun", [ arg; rest ]) -> go (arg :: acc) rest
    | ret -> (List.rev acc, ret)
  in
  go [] ty

(** Build a curried function type from arg types and return type. e.g.
    make_curried_type [A; B] C = A -> B -> C *)
let make_curried_type arg_tys ret_ty =
  List.fold_right make_fun_ty arg_tys ret_ty

(** For a constructor of an inductive type, determine which argument positions
    are recursive (i.e. same type as the inductive type) *)
let classify_constructor_args ind_ty con_ty =
  let rec go = function
    | TyCon ("fun", [ arg; rest ]) ->
        let is_rec = arg = ind_ty in
        (arg, is_rec) :: go rest
    | _ -> []
  in
  go con_ty

(** Generate fresh variable names for a list of types *)
let gen_vars prefix tys =
  List.mapi
    (fun i ty ->
      let name = prefix ^ string_of_int i in
      (name, Var (name, ty), ty))
    tys

(** Build the case function type for a constructor.

    For a function f : ind -> carry1 -> carry2 -> ... -> ret and a constructor C
    : arg1 -> arg2(rec) -> arg3 -> ind

    The case function takes:
    - non-recursive constructor args (arg1, arg3)
    - carried arguments (carry1, carry2, ...)
    - for each recursive arg: the recursive result fully applied (type: ret)
    - returns: ret

    For a nullary constructor (no args), the case is just:
    - carried arguments -> ret *)
let make_case_type ind_ty carry_tys ret_ty con_ty =
  let classified = classify_constructor_args ind_ty con_ty in
  let non_rec_tys =
    classified
    |> List.filter_map (fun (ty, is_rec) -> if is_rec then None else Some ty)
  in
  let rec_count =
    classified |> List.filter (fun (_, is_rec) -> is_rec) |> List.length
  in
  let rec_result_tys = List.init rec_count (fun _ -> ret_ty) in
  make_curried_type (non_rec_tys @ carry_tys @ rec_result_tys) ret_ty

(** Build the equation for a single constructor case.

    For constructor C : a -> ind -> b -> ind, carried args [y1, y2], function g,
    and case variable case_var:

    ∀a. ∀b. ∀y1. ∀y2. ∀x_rec0. ∀x_rec1. g (C a x_rec0 b x_rec1) y1 y2 = case_var
    a y1 y2 (g x_rec0 y1 y2) (g x_rec1 y1 y2) *)
let make_constructor_equation g_var ind_ty carry_vars case_var con_name con_ty =
  let classified = classify_constructor_args ind_ty con_ty in

  (* Generate variables for each constructor arg *)
  let con_arg_vars =
    List.mapi
      (fun i (ty, _is_rec) ->
        let name = "c" ^ string_of_int i in
        (Var (name, ty), ty, _is_rec))
      classified
  in

  (* Build the constructor application: C c0 c1 c2 ... *)
  let con_const = Const (con_name, con_ty) in
  let con_applied =
    List.fold_left
      (fun acc (v, _, _) -> Result.get_ok (make_app acc v))
      con_const con_arg_vars
  in

  (* Build LHS: g (C c0 c1 ...) y1 y2 ... *)
  let lhs =
    List.fold_left
      (fun acc (_, v, _) -> Result.get_ok (make_app acc v))
      (Result.get_ok (make_app g_var con_applied))
      carry_vars
  in

  (* Build RHS args: non-recursive con args, then carry args,
     then recursive results *)
  let non_rec_args =
    con_arg_vars
    |> List.filter_map (fun (v, _, is_rec) -> if is_rec then None else Some v)
  in
  let carry_arg_terms = List.map (fun (_, v, _) -> v) carry_vars in
  let rec_results =
    con_arg_vars
    |> List.filter_map (fun (v, _, is_rec) ->
        if not is_rec then None
        else
          (* g rec_var y1 y2 ... *)
          let applied =
            List.fold_left
              (fun acc (_, cv, _) -> Result.get_ok (make_app acc cv))
              (Result.get_ok (make_app g_var v))
              carry_vars
          in
          Some applied)
  in

  let rhs_args = non_rec_args @ carry_arg_terms @ rec_results in
  let rhs =
    List.fold_left
      (fun acc arg -> Result.get_ok (make_app acc arg))
      case_var rhs_args
  in

  (* Build equation: lhs = rhs *)
  let eq = Result.get_ok (safe_make_eq lhs rhs) in

  (* Quantify over constructor args and carry args *)
  let all_vars =
    List.map (fun (v, _, _) -> v) con_arg_vars
    @ List.map (fun (_, v, _) -> v) carry_vars
  in
  Result.get_ok (make_foralls all_vars eq)

(** Generate a complete synthesis goal.

    @param func_type
      The type of the function to synthesize (e.g. list nat -> nat)
    @param test_cases
      List of (input_terms, expected_output) pairs where input_terms is a list
      of argument terms
    @return A goal term: ∃case1. ∃case2. ... equations ==> tests *)
let make_synthesis_goal ~(func_type : hol_type)
    ~(test_cases : (term list * term) list) : term =
  let arg_tys, ret_ty = split_fun_type func_type in

  (* First arg is the one we recurse on *)
  let ind_ty = List.hd arg_tys in
  let carry_tys = List.tl arg_tys in

  (* Look up the inductive definition *)
  let ind_name =
    match ind_ty with TyCon (name, _) -> name | _ -> failwith "not inductive"
  in
  let ind_def =
    match Hashtbl.find_opt the_inductives ind_name with
    | Some d -> d
    | None -> failwith ("not an inductive type: " ^ ind_name)
  in

  (* Build type substitution from definition params to concrete params *)
  let type_sub =
    match (destruct_type ind_def.ty, destruct_type ind_ty) with
    | Ok (_, def_params), Ok (_, concrete_params) -> (
        try List.combine def_params concrete_params
        with Invalid_argument _ -> [])
    | _ -> []
  in

  (* Generate the g variable *)
  let g_var = Var ("g", func_type) in

  (* Generate carried argument variables *)
  let carry_vars =
    List.mapi
      (fun i ty ->
        let name = "y" ^ string_of_int i in
        (name, Var (name, ty), ty))
      carry_tys
  in

  (* For each constructor, build case variable and equation *)
  let constructor_info =
    ind_def.constructors
    |> List.map (fun (cname, cconst) ->
        let cty =
          match cconst with
          | Const (_, t) -> type_substitution type_sub t
          | _ -> (
              match type_of_var cconst with
              | Ok ty -> type_substitution type_sub ty
              | Error _ -> type_substitution type_sub (TyVar "?"))
        in
        let case_ty = make_case_type ind_ty carry_tys ret_ty cty in
        let case_name = cname ^ "_case" in
        let case_var = Var (case_name, case_ty) in
        (cname, cty, case_name, case_var, case_ty))
  in

  (* Build equations *)
  let equations =
    constructor_info
    |> List.map (fun (cname, cty, _, case_var, _) ->
        make_constructor_equation g_var ind_ty carry_vars case_var cname cty)
  in

  (* Build test conjunction *)
  let test_eqs =
    test_cases
    |> List.map (fun (inputs, expected) ->
        let applied =
          List.fold_left
            (fun acc arg -> Result.get_ok (make_app acc arg))
            g_var inputs
        in
        Result.get_ok (safe_make_eq applied expected))
  in
  let tests = make_conjs test_eqs in

  (* Build: equations ==> tests *)
  let body = make_imps equations tests in

  (* Wrap in existentials: ∃case1. ∃case2. ... body *)
  let case_vars =
    constructor_info |> List.map (fun (_, _, _, case_var, _) -> case_var)
  in
  Result.get_ok (make_existss case_vars body)
