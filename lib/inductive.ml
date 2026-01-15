open Kernel
open Derived
open Result.Syntax

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
  List.exists (is_base_case tyname) constructors

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
  constructors
  |> List.for_all (fun c ->
      c.arg_types
      |> List.for_all (fun ty -> not (appears_left_of_arrow tyname ty)))

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
    case_tys |> List.map @@ fun (name, t) -> (name, Var (name ^ "_case", t))
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

let all_constructor_pairs constructors =
  let rec pairs = function
    | [] -> []
    | x :: xs ->
        let pairs_with_x = List.map (fun y -> (x, y)) xs in
        pairs_with_x @ pairs xs
  in
  pairs constructors

(* Distinctness Theorems *)
let make_distinct_thms (ty : hol_type) (constructors : constructor_spec list) =
  let pairs = all_constructor_pairs constructors in

  pairs
  |> List.map (fun (c1, c2) ->
      (* Create variables for c1's arguments *)
      let c1_vars =
        c1.arg_types
        |> List.mapi (fun i arg_ty -> Var ("x" ^ string_of_int i, arg_ty))
      in

      (* Create variables for c2's arguments *)
      let c2_vars =
        c2.arg_types
        |> List.mapi (fun i arg_ty -> Var ("y" ^ string_of_int i, arg_ty))
      in

      (* Build: Constructor1 x0 x1 ... *)
      let c1_ty = make_constructor_type c1.arg_types ty in
      let c1_const = Const (c1.name, c1_ty) in
      let lhs =
        List.fold_left
          (fun acc var -> Result.get_ok (make_app acc var))
          c1_const c1_vars
      in

      (* Build: Constructor2 y0 y1 ... *)
      let c2_ty = make_constructor_type c2.arg_types ty in
      let c2_const = Const (c2.name, c2_ty) in
      let rhs =
        List.fold_left
          (fun acc var -> Result.get_ok (make_app acc var))
          c2_const c2_vars
      in

      (* Build: ¬(lhs = rhs) *)
      let* eq = safe_make_eq lhs rhs in
      let neq = make_neg eq in

      (* Quantify over all variables *)
      let all_vars = c1_vars @ c2_vars in
      let theorem = make_foralls all_vars neq in

      (* Assert as axiom *)
      new_axiom theorem)

(* Injectivity Theorems *)
let make_injective_thms (ty : hol_type) (constructors : constructor_spec list) =
  constructors
  |> List.filter (fun c -> c.arg_types <> [])
  |> List.map (fun c ->
      (* Create two sets of variables *)
      let vars1 =
        c.arg_types
        |> List.mapi (fun i arg_ty -> Var ("x" ^ string_of_int i, arg_ty))
      in
      let vars2 =
        c.arg_types
        |> List.mapi (fun i arg_ty -> Var ("y" ^ string_of_int i, arg_ty))
      in

      (* Build: Constructor x0 x1 ... *)
      let c_ty = make_constructor_type c.arg_types ty in
      let c_const = Const (c.name, c_ty) in
      let lhs =
        List.fold_left
          (fun acc var -> Result.get_ok (make_app acc var))
          c_const vars1
      in

      (* Build: Constructor y0 y1 ... *)
      let rhs =
        List.fold_left
          (fun acc var -> Result.get_ok (make_app acc var))
          c_const vars2
      in

      (* Build premise: lhs = rhs *)
      let* premise = safe_make_eq lhs rhs in

      (* Build conclusion: x0 = y0 ∧ x1 = y1 ∧ ... *)
      let* equalities =
        List.map2 (fun v1 v2 -> safe_make_eq v1 v2) vars1 vars2
        |> List.fold_left
             (fun acc eq ->
               match (acc, eq) with
               | Ok eqs, Ok e -> Ok (e :: eqs)
               | Error e, _ -> Error e
               | _, Error e -> Error e)
             (Ok [])
        |> Result.map List.rev
      in
      let conclusion = make_conjs equalities in

      (* Build: premise → conclusion *)
      let body = make_imp premise conclusion in

      (* Quantify over all variables *)
      let all_vars = vars1 @ vars2 in
      let theorem = make_foralls all_vars body in

      (* Assert as axiom *)
      new_axiom theorem)

let define_inductive tyname params (constructors : constructor_spec list) =
  let* () =
    match Hashtbl.find_opt the_type_constants tyname with
    | Some _ -> Error `TypeAlreadyExists
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
    | _names -> Error `ConstructorsAlreadyExist
  in

  let positive = check_positivity tyname constructors in
  let* () = if not positive then Error `NotPositive else Ok () in

  let base_case_exists = check_base_case tyname constructors in
  let* () = if not base_case_exists then Error `NoBaseCase else Ok () in

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

  let* distinct =
    make_distinct_thms ty constructors |> Util.result_of_results []
  in

  let* injective =
    make_injective_thms ty constructors |> Util.result_of_results []
  in

  let def =
    {
      ty;
      constructors = constructor_terms;
      induction;
      recursion;
      distinct;
      injective;
    }
  in
  Hashtbl.add the_inductives tyname def;
  Ok def

(*function definition*)

let pp_thm th = print_newline @@ print_endline @@ Printing.pretty_print_thm th

let pp_term trm =
  print_newline @@ print_endline @@ Printing.pretty_print_hol_term trm

let new_specification name ex_thm =
  let concl_tm = concl ex_thm in
  let* exists_var, body = destruct_exists concl_tm in
  let var_type = type_of_var exists_var in
  let* () = new_constant name var_type in
  let new_const = Const (name, var_type) in
  let* defining_property = vsubst [ (new_const, exists_var) ] body in
  let* thm = new_axiom defining_property in
  Hashtbl.add the_specifications name thm;
  Ok thm

(* Extract the inductive type being recursed on from branch terms *)
let rec find_inductive_type_in_term = function
  | Const (name, _) ->
      let find_containing_type () =
        Hashtbl.fold
          (fun type_name def acc ->
            match acc with
            | Some _ -> acc
            | None ->
                if
                  List.exists
                    (fun (ctor_name, _) -> ctor_name = name)
                    def.constructors
                then Some (type_name, def)
                else None)
          the_inductives None
      in
      find_containing_type ()
  | App (f, arg) -> (
      match find_inductive_type_in_term f with
      | Some result -> Some result
      | None -> find_inductive_type_in_term arg)
  | Lam (_, body) -> find_inductive_type_in_term body
  | _ -> None

let find_recursed_inductive_type branches =
  let rec search = function
    | [] ->
        Error
          (`InvariantViolation
             "Could not determine inductive type from branches")
    | branch :: rest -> (
        match find_inductive_type_in_term branch with
        | Some result -> Ok result
        | None -> search rest)
  in
  search branches

(* Define a recursive function on an inductive type *)
let define_recursive_function func_name return_type inductive_type_name branches
    =
  let inductive_def =
    match Hashtbl.find_opt the_inductives inductive_type_name with
    | Some def -> def
    | None -> failwith ("Unknown inductive type: " ^ inductive_type_name)
  in

  let type_inst =
    [ (make_vartype "r", return_type) ] |> List.to_seq |> Hashtbl.of_seq
  in
  let* typed_recursion_thm = inst_type type_inst inductive_def.recursion in
  let* instantiated_thm = specs branches typed_recursion_thm in
  new_specification func_name instantiated_thm

(* Examples *)
(* let nat_def = *)
(*   let nat_ty = TyCon ("nat", []) in *)
(*   define_inductive "nat" [] *)
(*     [ *)
(*       { name = "Zero"; arg_types = [] }; *)
(*       { name = "Suc"; arg_types = [ nat_ty ] }; *)
(*     ] *)

(* let plus_def = *)
(*   let _ = init_types () in *)
(*   let nat_ty = TyCon ("nat", []) in *)
(*   let* nat_def = nat_def in *)
(*   let suc = nat_def.constructors |> List.assoc_opt "Suc" |> Option.get in *)
(*   let z = nat_def.constructors |> List.assoc_opt "Zero" |> Option.get in *)
(*   print_endline @@ show_term z; *)
(**)
(*   let n = make_var "n" nat_ty in *)
(*   let m' = make_var "m'" nat_ty in *)
(*   let r = make_var "r" (make_fun_ty nat_ty nat_ty) in *)
(**)
(*   let* zero_case = make_lam n n in *)
(*   (* λn. n *) *)
(*   let* suc_case = *)
(*     let* r_n = make_app r n in *)
(*     let* suc_rn = make_app suc r_n in *)
(*     let* lam_n_suc_rn = make_lam n suc_rn in *)
(*     let* lam_r = make_lam r lam_n_suc_rn in *)
(*     make_lam m' lam_r (* λm'. λr. λn. Suc (r n) *) *)
(*   in *)
(**)
(*   let return_type = make_fun_ty nat_ty nat_ty in *)
(*   define_recursive_function "plus" return_type "nat" [ zero_case; suc_case ] *)
