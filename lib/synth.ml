(* AI Code Ahead *)

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
                | _ -> type_substitution type_sub (type_of_var cconst)
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
