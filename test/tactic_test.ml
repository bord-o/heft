open Heft
open Derived
open Inductive
open Tactic
open Effect
open Printing

type dfs_res = Success | Failure

let test_dfs () =
  let print_choice = function
    | `A -> print_endline "A"
    | `B -> print_endline "B"
    | `C -> print_endline "C"
    | `D -> print_endline "D"
    | `E -> print_endline "E"
    | `F -> print_endline "F"
    | `G -> print_endline "G"
    | `H -> print_endline "H"
    | `I -> print_endline "I"
  in
  let choice = perform @@ Choose [ `A; `B; `C ] in
  let choice2 = perform @@ Choose [ `D; `E; `F ] in
  let choice3 = perform @@ Choose [ `G; `H; `I ] in
  List.iter print_choice [ choice; choice2; choice3 ];

  match (choice, choice2, choice3) with `C, `F, `G -> Success | _ -> Failure

let choice_dfs () =
  match test_dfs () with
  | effect Choose cs, k ->
      let r = Multicont.Deep.promote k in
      let rec try' = function
        | [] -> Failure
        | this :: rest -> (
            print_endline "trying next";
            match Multicont.Deep.resume r this with
            | Success -> Success
            | Failure -> try' rest)
      in
      try' cs
  | v ->
      print_endline
        (match v with
        | Success -> "computation returned Success"
        | Failure -> "computation returned Failure");
      v

let%expect_test "choice test" =
  (match choice_dfs () with
  | Success -> print_endline "success"
  | Failure -> print_endline "failure");
  [%expect
    {|
    trying next
    trying next
    trying next
    A
    D
    G
    computation returned Failure
    trying next
    A
    D
    H
    computation returned Failure
    trying next
    A
    D
    I
    computation returned Failure
    trying next
    trying next
    A
    E
    G
    computation returned Failure
    trying next
    A
    E
    H
    computation returned Failure
    trying next
    A
    E
    I
    computation returned Failure
    trying next
    trying next
    A
    F
    G
    computation returned Failure
    trying next
    A
    F
    H
    computation returned Failure
    trying next
    A
    F
    I
    computation returned Failure
    trying next
    trying next
    trying next
    B
    D
    G
    computation returned Failure
    trying next
    B
    D
    H
    computation returned Failure
    trying next
    B
    D
    I
    computation returned Failure
    trying next
    trying next
    B
    E
    G
    computation returned Failure
    trying next
    B
    E
    H
    computation returned Failure
    trying next
    B
    E
    I
    computation returned Failure
    trying next
    trying next
    B
    F
    G
    computation returned Failure
    trying next
    B
    F
    H
    computation returned Failure
    trying next
    B
    F
    I
    computation returned Failure
    trying next
    trying next
    trying next
    C
    D
    G
    computation returned Failure
    trying next
    C
    D
    H
    computation returned Failure
    trying next
    C
    D
    I
    computation returned Failure
    trying next
    trying next
    C
    E
    G
    computation returned Failure
    trying next
    C
    E
    H
    computation returned Failure
    trying next
    C
    E
    I
    computation returned Failure
    trying next
    trying next
    C
    F
    G
    computation returned Success
    success
    |}]
(* let nat_def = *)
(*   let nat_ty = TyCon ("nat", []) in *)
(*   define_inductive "nat" [] *)
(*     [ *)
(*       { name = "Zero"; arg_types = [] }; *)
(*       { name = "Suc"; arg_types = [ nat_ty ] }; *)
(*     ] in *)
(* let plus_def = *)
(*   let _ = init_types () in *)
(*   let nat_ty = TyCon ("nat", []) in *)
(*   let* nat_def = nat_def in *)
(*   let suc = nat_def.constructors |> List.assoc_opt "Suc" |> Option.get in *)
(*   let z = nat_def.constructors |> List.assoc_opt "Zero" |> Option.get in *)
(*   print_endline @@ show_term z; *)
(*   let n = make_var "n" nat_ty in *)
(*   let m' = make_var "m'" nat_ty in *)
(*   let r = make_var "r" (make_fun_ty nat_ty nat_ty) in *)
(*   let* zero_case = make_lam n n in *)
(*   (* λn. n *) *)
(*   let* suc_case = *)
(*     let* r_n = make_app r n in *)
(*     let* suc_rn = make_app suc r_n in *)
(*     let* lam_n_suc_rn = make_lam n suc_rn in *)
(*     let* lam_r = make_lam r lam_n_suc_rn in *)
(*     make_lam m' lam_r (* λm'. λr. λn. Suc (r n) *) *)
(*   in *)
(*   let return_type = make_fun_ty nat_ty nat_ty in *)
(*   define_recursive_function "plus" return_type "nat" [ zero_case; suc_case ] in *)

let%expect_test "basic" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = make_conj a b in

  let next_tactic =
    next_tactic_of_list
      [
        with_skip_fail conj_tac;
        with_first_success assumption_tac;
        with_first_success assumption_tac;
      ]
  in
  (match prove ([ a; b ], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);

  [%expect
    {|
    Destruct succeeded
    0: A
    1: B
    Found matching assumption
    Assumption succeeded
    0: B
    assumption doesn't match the goal
    Found matching assumption
    Assumption succeeded
    conj success
    Proof Complete!
    A
    B
    ========================================
    A ∧ B
    |}]

let%expect_test "basic2" =
  let a = make_var "A" bool_ty in
  let goal = safe_make_eq a a |> Result.get_ok in

  let next_tactic = next_tactic_of_list [ refl_tac ] in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);

  [%expect
    {|
      destruct success
      refl success
      Proof Complete!
      ========================================
      A = A
      |}]

let%expect_test "basic3" =
  let a = make_var "A" bool_ty in
  let goal = make_imp a a in

  let next_tactic = next_tactic_of_list [ intro_tac; assumption_tac ] in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);

  [%expect
    {|
      destruct success
      Found matching assumption
      Assumption succeeded
      disch success
      Proof Complete!
      ========================================
      A ==> A
      |}]

let%expect_test "basic4" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in

  let goal = make_disj a b in

  let next_tactic = next_tactic_of_list [ left_tac; assumption_tac ] in
  (match prove ([ a ], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);

  [%expect
    {|
      Found matching assumption
      Assumption succeeded
      disj_left success
      Proof Complete!
      A
      ========================================
      A ∨ B
      |}]

let%expect_test "basic5" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in

  let goal = make_disj a b in

  let next_tactic =
    next_tactic_of_list
    @@ wrap_all with_first_success [ right_tac; assumption_tac ]
  in
  (match prove ([ a; b ], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);

  [%expect
    {|
    assumption doesn't match the goal
    Found matching assumption
    Assumption succeeded
    disj_right success
    Proof Complete!
    B
    ========================================
    A ∨ B
    |}]

let%expect_test "basic6" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in

  let imp_ab = make_imp a b in
  let imp_abc = make_imp (make_imp c a) b in

  let goal = b in

  let next_tactic = next_tactic_of_list [ apply_tac; assumption_tac ] in
  (match prove_dfs ([ imp_abc; imp_ab; a ], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);

  [%expect
    {|
    assume chosen h success
    assumption doesn't match the goal
    assumption doesn't match the goal
    assumption doesn't match the goal
    assume chosen h success
    assumption doesn't match the goal
    assumption doesn't match the goal
    Found matching assumption
    Assumption succeeded
    mp success
    Proof Complete!
    A
    A ==> B
    ========================================
    B
    |}]

let%expect_test "basic7" =
  let a = make_var "A" bool_ty in

  let goal = a in

  let next_tactic = next_tactic_of_list [ contr_tac; assumption_tac ] in
  (match prove_dfs ([ make_false () ], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);

  [%expect
    {|
    Found matching assumption
    Assumption succeeded
    Proof Complete!
    F
    ========================================
    A
    |}]

let%expect_test "basic8" =
  let a = make_var "A" bool_ty in

  let goal = a in

  let next_tactic = next_tactic_of_list [ contr_tac; assumption_tac ] in
  (match prove ([ make_false () ], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);

  [%expect
    {|
    Found matching assumption
    Assumption succeeded
    Proof Complete!
    F
    ========================================
    A
    |}]

let err = Result.get_ok

let%expect_test "basic9" =
  let a = make_var "A" bool_ty in
  let x = make_var "x" bool_ty in

  let goal = make_forall x (make_imp a a) in

  let next_tactic =
    next_tactic_of_list [ gen_tac; intro_tac; assumption_tac ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);

  [%expect
    {|
    destruct success
    Found matching assumption
    Assumption succeeded
    disch success
    Proof Complete!
    ========================================
    ∀x. A ==> A
    |}]

let%expect_test "basic10" =
  let a = make_var "A" bool_ty in
  let nat_def =
    let nat_ty = TyCon ("nat", []) in
    define_inductive "nat" []
      [
        { name = "Zero"; arg_types = [] };
        { name = "Suc"; arg_types = [ nat_ty ] };
      ]
    |> err
  in
  let x = make_var "x" nat_def.ty in

  let goal = make_forall x (make_imp a a) in

  let next_tactic =
    next_tactic_of_list
      [
        induct_tac;
        intro_tac;
        assumption_tac;
        gen_tac;
        intro_tac;
        assumption_tac;
      ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);

  [%expect
    {|
    0: A ==> A
    1: ∀n0. (A ==> A) ==> A ==> A
    destruct success
    Found matching assumption
    Assumption succeeded
    disch success
    0: ∀n0. (A ==> A) ==> A ==> A
    destruct success
    Found matching assumption
    Assumption succeeded
    disch success
    Proof Complete!
    ========================================
    ∀x. A ==> A
    |}]

let%expect_test "dfs_backtrack" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let d = make_var "D" bool_ty in
  let e = make_var "E" bool_ty in
  let f = make_var "F" bool_ty in
  (* Goal: A ∨ B, but only B is available *)

  let goal =
    make_disj (make_disj e (make_disj (make_disj c d) (make_disj a b))) f
  in
  print_term goal;
  let next_tactic =
    next_tactic_of_list [ with_repeat or_tac; assumption_tac ]
  in
  (match prove_dfs ([ f ], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);
  [%expect
    {|
    E ∨ C ∨ D ∨ A ∨ B ∨ F

    OperationDoesntMatch
    assumption doesn't match the goal
    OperationDoesntMatch
    assumption doesn't match the goal
    OperationDoesntMatch
    assumption doesn't match the goal
    OperationDoesntMatch
    assumption doesn't match the goal
    OperationDoesntMatch
    assumption doesn't match the goal
    OperationDoesntMatch
    assumption doesn't match the goal
    OperationDoesntMatch
    assumption doesn't match the goal
    OperationDoesntMatch
    assumption doesn't match the goal
    OperationDoesntMatch
    assumption doesn't match the goal
    OperationDoesntMatch
    assumption doesn't match the goal
    OperationDoesntMatch
    Found matching assumption
    Assumption succeeded
    disj_right success
    Proof Complete!
    F
    ========================================
    E ∨ C ∨ D ∨ A ∨ B ∨ F
    |}]

let%expect_test "dfs_conj_backtrack" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  (* Goal: (A ∨ B) ∧ C, only have [B; C] *)
  let left = make_disj a b in
  let goal = make_conj left c in
  let next_tactic =
    next_tactic_of_list [ conj_tac; with_skip_fail or_tac; assumption_tac ]
  in
  (match prove_dfs ([ b; c ], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");

  [%expect
    {|
    Destruct succeeded
    0: A ∨ B
    1: C
    assumption doesn't match the goal
    assumption doesn't match the goal
    Found matching assumption
    Assumption succeeded
    disj_right success
    0: C
    OperationDoesntMatch
    assumption doesn't match the goal
    Found matching assumption
    Assumption succeeded
    conj success
    Proof Complete!
    B
    C
    ========================================
    A ∨ B ∧ C
    |}]
