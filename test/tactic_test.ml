open Heft
open Derived
open Tactic

(* open Effect *)
open Printing

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
    assumption_tac
    0: B
    assumption doesn't match the goal
    Found matching assumption
    Assumption succeeded
    assumption_tac
    conj success
    conj_tac
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
    refl_tac
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
    assumption_tac
    disch success
    intro_tac
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
    assumption_tac
    disj_left success
    left_tac
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
    assumption_tac
    disj_right success
    right_tac
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
  let imp_cab = make_imp (make_imp c a) b in

  let goal = b in

  let next_tactic =
    next_tactic_of_list
      [ apply_asm_tac |> with_term imp_ab; with_first_success assumption_tac ]
  in
  (match prove ([ imp_cab; imp_ab; a ], goal) next_tactic with
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
    Found matching assumption
    Assumption succeeded
    assumption_tac
    mp success
    apply_asm_tac
    Proof Complete!
    A
    A ==> B
    ========================================
    B
    |}]

let%expect_test "basic7" =
  let a = make_var "A" bool_ty in

  let goal = a in

  let next_tactic = next_tactic_of_list [ ccontr_tac; assumption_tac ] in
  (match prove_dfs ([ make_false () ], goal) next_tactic with
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
    Proof Complete!
    F
    ========================================
    A
    |}]

let%expect_test "basic8" =
  let a = make_var "A" bool_ty in

  let goal = a in

  let next_tactic = next_tactic_of_list [ false_elim_tac; assumption_tac ] in
  (match prove ([ make_false () ], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g);

  [%expect
    {|
    false_elim_tac
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
    assumption_tac
    disch success
    intro_tac
    gen_tac
    Proof Complete!
    ========================================
    ∀x. A ==> A
    |}]

let%expect_test "basic10" =
  let a = make_var "A" bool_ty in
  let nat_def = Theorems.Nat.nat_def in
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
    assumption_tac
    disch success
    intro_tac
    0: ∀n0. (A ==> A) ==> A ==> A
    destruct success
    Found matching assumption
    Assumption succeeded
    assumption_tac
    disch success
    intro_tac
    gen_tac
    induction_tac
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

let%expect_test "dfs_conj_assumptions" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in

  let p_imp_q = make_imp p q in
  let q_imp_r = make_imp q r in
  let p_imp_r = make_imp p r in
  let goal = make_imp (make_conj p_imp_q q_imp_r) p_imp_r in

  let next_tactic =
    next_tactic_of_list
      [
        intro_tac;
        elim_conj_asm_tac;
        intro_tac;
        apply_asm_tac;
        apply_asm_tac;
        assumption_tac;
      ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, conc) ->
      print_endline "Proof Failed";
      List.iter
        (fun t ->
          print_endline "assumption: ";
          print_term t)
        asms;
      print_term conc);

  [%expect
    {|
    destruct success
    destruct success
    assume chosen h success
    assume chosen h success
    Found matching assumption
    Assumption succeeded
    mp success
    mp success
    disch success
    disch success
    Proof Complete!
    ========================================
    (P ==> Q) ∧ (Q ==> R) ==> P ==> R
    |}]

let%expect_test "complete_prop_automation" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in

  let p_imp_q = make_imp p q in
  let q_imp_r = make_imp q r in
  let p_imp_r = make_imp p r in
  let goal = make_imp (make_conj p_imp_q q_imp_r) p_imp_r in

  let next_tactic =
    next_tactic_of_list [ with_dfs @@ with_repeat ctauto_tac ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, conc) ->
      print_endline "Proof Failed";
      List.iter
        (fun t ->
          print_endline "assumption: ";
          print_term t)
        asms;
      print_term conc);

  [%expect
    {|
    destruct success
    assumption doesn't match the goal
    destruct success
    assumption doesn't match the goal
    assumption doesn't match the goal
    OperationDoesntMatch
    NotANegation
    NotAForall
    NotAConj
    assumption doesn't match the goal
    assumption doesn't match the goal
    assumption doesn't match the goal
    OperationDoesntMatch
    NotANegation
    NotAForall
    NotAConj
    assume chosen h success
    assumption doesn't match the goal
    assumption doesn't match the goal
    assumption doesn't match the goal
    OperationDoesntMatch
    NotANegation
    NotAForall
    NotAConj
    assume chosen h success
    assumption doesn't match the goal
    assumption doesn't match the goal
    Found matching assumption
    Assumption succeeded
    mp success
    mp success
    disch success
    disch success
    Proof Complete!
    ========================================
    (P ==> Q) ∧ (Q ==> R) ==> P ==> R
    |}]

let%expect_test "dfs_disj_assumptions" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let p_or_q = make_disj p q in
  let p_imp_r = make_imp p r in
  let q_imp_r = make_imp q r in
  let goal = make_imp p_or_q (make_imp p_imp_r (make_imp q_imp_r r)) in
  let next_tactic =
    next_tactic_of_list
      [
        intro_tac;
        intro_tac;
        intro_tac;
        elim_disj_asm_tac;
        apply_asm_tac;
        assumption_tac;
        apply_asm_tac;
        assumption_tac;
      ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, conc) ->
      print_endline "Proof Failed";
      List.iter
        (fun t ->
          print_endline "assumption: ";
          print_term t)
        asms;
      print_term conc);
  [%expect
    {|
    destruct success
    destruct success
    destruct success
    0: R
    1: R
    assume chosen h success
    assumption doesn't match the goal
    assumption doesn't match the goal
    assumption doesn't match the goal
    assume chosen h success
    Found matching assumption
    Assumption succeeded
    mp success
    0: R
    assume chosen h success
    Found matching assumption
    Assumption succeeded
    mp success
    disch success
    disch success
    disch success
    Proof Complete!
    ========================================
    P ∨ Q ==> (P ==> R) ==> (Q ==> R) ==> R
    |}]

let%expect_test "pauto_disj_elimination" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let p_or_q = make_disj p q in
  let p_imp_r = make_imp p r in
  let q_imp_r = make_imp q r in
  let goal = make_imp p_or_q (make_imp p_imp_r (make_imp q_imp_r r)) in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, conc) ->
      print_endline "Proof Failed";
      List.iter
        (fun t ->
          print_endline "assumption: ";
          print_term t)
        asms;
      print_term conc);
  [%expect
    {|
    Proof Complete!
    ========================================
    P ∨ Q ==> (P ==> R) ==> (Q ==> R) ==> R
    |}]

let%expect_test "false_elim_tac_test" =
  (* ⊥ in assumptions, prove anything *)
  let p = make_var "P" bool_ty in
  let false_tm = make_false () in
  let goal = make_imp false_tm p in
  let next_tactic = next_tactic_of_list [ intro_tac; false_elim_tac ] in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    destruct success
    disch success
    Proof Complete!
    ========================================
    F ==> P
    |}]

let%expect_test "neg_elim_tac_test" =
  (* P and ¬P in assumptions, prove anything *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = make_imp p (make_imp (make_neg p) q) in
  let next_tactic =
    next_tactic_of_list [ intro_tac; intro_tac; neg_elim_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    destruct success
    destruct success
    disch success
    disch success
    Proof Complete!
    ========================================
    P ==> ¬P ==> Q
    |}]

let%expect_test "neg_intro_tac_test" =
  (* Goal is ¬P, reduce to [P] ⊢ ⊥ *)
  (* Prove: P ⟹ ¬¬P *)
  let p = make_var "P" bool_ty in
  let goal = make_imp p (make_neg (make_neg p)) in
  let next_tactic =
    next_tactic_of_list [ intro_tac; neg_intro_tac; neg_elim_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    destruct success
    disch success
    Proof Complete!
    ========================================
    P ==> ¬¬P
    |}]

let%expect_test "ccontr_tac_test" =
  (* Classical: assume ¬P, derive ⊥, conclude P *)
  (* Prove: ¬¬P ⟹ P (requires classical logic) *)
  let p = make_var "P" bool_ty in
  let goal = make_imp (make_neg (make_neg p)) p in
  let next_tactic =
    next_tactic_of_list [ intro_tac; ccontr_tac; neg_elim_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    destruct success
    disch success
    Proof Complete!
    ========================================
    ¬¬P ==> P
    |}]

let%expect_test "modus_tollens" =
  (* (P ⟹ Q) ⟹ ¬Q ⟹ ¬P *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = make_imp (make_imp p q) (make_imp (make_neg q) (make_neg p)) in
  let next_tactic =
    next_tactic_of_list
      [ intro_tac; intro_tac; neg_intro_tac; mp_asm_tac; neg_elim_tac ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      List.iter
        (fun t ->
          print_endline "assumption: ";
          print_term t)
        asms;
      print_term g);
  [%expect
    {|
    destruct success
    destruct success
    neg_elim_tac
    mp_asm_tac
    neg_intro_tac
    disch success
    intro_tac
    disch success
    intro_tac
    Proof Complete!
    ========================================
    (P ==> Q) ==> ¬Q ==> ¬P
    |}]

let%expect_test "excluded_middle_pauto" =
  (* P ∨ ¬P (requires classical logic) *)
  let p = make_var "P" bool_ty in
  let goal = make_disj p (make_neg p) in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    P ∨ ¬P
    |}]

let%expect_test "contraposition" =
  (* (P ⟹ Q) ⟹ (¬Q ⟹ ¬P) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = make_imp (make_imp p q) (make_imp (make_neg q) (make_neg p)) in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    (P ==> Q) ==> ¬Q ==> ¬P
    |}]

let%expect_test "distribution_and_over_or" =
  (* P ∧ (Q ∨ R) ⟹ (P ∧ Q) ∨ (P ∧ R) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let goal =
    make_imp
      (make_conj p (make_disj q r))
      (make_disj (make_conj p q) (make_conj p r))
  in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    P ∧ Q ∨ R ==> P ∧ Q ∨ P ∧ R
    |}]

let%expect_test "distribution_or_over_and" =
  (* P ∨ (Q ∧ R) ⟹ (P ∨ Q) ∧ (P ∨ R) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let goal =
    make_imp
      (make_disj p (make_conj q r))
      (make_conj (make_disj p q) (make_disj p r))
  in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    P ∨ Q ∧ R ==> P ∨ Q ∧ P ∨ R
    |}]

let%expect_test "de_morgan_and" =
  (* ¬(P ∧ Q) ⟹ ¬P ∨ ¬Q - requires classical *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    make_imp (make_neg (make_conj p q)) (make_disj (make_neg p) (make_neg q))
  in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    ¬P ∧ Q ==> ¬P ∨ ¬Q
    |}]

let%expect_test "de_morgan_or" =
  (* ¬(P ∨ Q) ⟹ ¬P ∧ ¬Q - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    make_imp (make_neg (make_disj p q)) (make_conj (make_neg p) (make_neg q))
  in
  let next_tactic =
    next_tactic_of_list [ with_dfs @@ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q
    |}]

let%expect_test "de_morgan_or_converse" =
  (* ¬P ∧ ¬Q ⟹ ¬(P ∨ Q) - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    make_imp (make_conj (make_neg p) (make_neg q)) (make_neg (make_disj p q))
  in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    ¬P ∧ ¬Q ==> ¬P ∨ Q
    |}]

let%expect_test "implication_as_disjunction" =
  (* (P ⟹ Q) ⟹ ¬P ∨ Q - requires classical *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = make_imp (make_imp p q) (make_disj (make_neg p) q) in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    (P ==> Q) ==> ¬P ∨ Q
    |}]

let%expect_test "disjunction_as_implication" =
  (* ¬P ∨ Q ⟹ (P ⟹ Q) - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = make_imp (make_disj (make_neg p) q) (make_imp p q) in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    ¬P ∨ Q ==> P ==> Q
    |}]

let%expect_test "triple_negation" =
  (* ¬¬¬P ⟹ ¬P - intuitionistic *)
  let p = make_var "P" bool_ty in
  let goal = make_imp (make_neg (make_neg (make_neg p))) (make_neg p) in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    ¬¬¬P ==> ¬P
    |}]

let%expect_test "explosion" =
  (* P ⟹ ¬P ⟹ Q *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = make_imp p (make_imp (make_neg p) q) in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    P ==> ¬P ==> Q
    |}]

let%expect_test "complex_nested" =
  (* ((P ⟹ Q) ⟹ P) ⟹ P - Peirce's law, requires classical *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = make_imp (make_imp (make_imp p q) p) p in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    ((P ==> Q) ==> P) ==> P
    |}]

let%expect_test "four_variable_distribution" =
  (* (A ∨ B) ∧ (C ∨ D) ⟹ (A ∧ C) ∨ (A ∧ D) ∨ (B ∧ C) ∨ (B ∧ D) *)
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let d = make_var "D" bool_ty in
  let goal =
    make_imp
      (make_conj (make_disj a b) (make_disj c d))
      (make_disj (make_conj a c)
         (make_disj (make_conj a d) (make_disj (make_conj b c) (make_conj b d))))
  in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    A ∨ B ∧ C ∨ D ==> A ∧ C ∨ A ∧ D ∨ B ∧ C ∨ B ∧ D
    |}]

let%expect_test "implication_chain" =
  (* (A ⟹ B) ⟹ (B ⟹ C) ⟹ (C ⟹ D) ⟹ (A ⟹ D) *)
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let d = make_var "D" bool_ty in
  let goal =
    make_imp (make_imp a b)
      (make_imp (make_imp b c) (make_imp (make_imp c d) (make_imp a d)))
  in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    (A ==> B) ==> (B ==> C) ==> (C ==> D) ==> A ==> D
    |}]

let%expect_test "contraposition_chain" =
  (* (A ⟹ B) ⟹ (B ⟹ C) ⟹ (¬C ⟹ ¬A) *)
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let goal =
    make_imp (make_imp a b)
      (make_imp (make_imp b c) (make_imp (make_neg c) (make_neg a)))
  in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    (A ==> B) ==> (B ==> C) ==> ¬C ==> ¬A
    |}]

let%expect_test "absorption_law" =
  (* P ∧ (P ∨ Q) ⟺ P - just one direction here *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = make_imp (make_conj p (make_disj p q)) p in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    P ∧ P ∨ Q ==> P
    |}]

let%expect_test "absorption_law_converse" =
  (* P ⟹ P ∧ (P ∨ Q) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = make_imp p (make_conj p (make_disj p q)) in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    P ==> P ∧ P ∨ Q
    |}]

let%expect_test "not_false_is_true" =
  (* ¬⊥ *)
  let goal = make_neg (make_false ()) in
  let next_tactic =
    next_tactic_of_list [ with_repeat @@ with_no_trace ctauto_tac ]
  in
  (match prove_dfs ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    Proof Complete!
    ========================================
    ¬F
    |}]

let%expect_test "manual version " =
  (* ¬(P ∨ Q) ⟹ ¬P ∧ ¬Q - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    make_imp (make_neg (make_disj p q)) (make_conj (make_neg p) (make_neg q))
  in
  let next_tactic =
    next_tactic_of_list
    @@ wrap_all
         (with_no_trace ~show_proof:true)
         [
           intro_tac;
           conj_tac;
           neg_intro_tac;
           apply_neg_asm_tac;
           left_tac;
           assumption_tac;
           neg_intro_tac;
           apply_neg_asm_tac;
           right_tac;
           assumption_tac;
         ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      List.iter Printing.print_term asms;
      Printing.print_term g;
      print_endline "Proof Failed");
  [%expect
    {|
    assumption_tac
    left_tac
    apply_neg_asm_tac
    neg_intro_tac
    assumption_tac
    right_tac
    apply_neg_asm_tac
    neg_intro_tac
    conj_tac
    intro_tac
    Proof Complete!
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q
    |}]

let%expect_test "dfs demorgans" =
  (* ¬(P ∨ Q) ⟹ ¬P ∧ ¬Q - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    make_imp (make_neg (make_disj p q)) (make_conj (make_neg p) (make_neg q))
  in
  let fuel = ref 0 in
  let next_tactic =
    next_tactic_of_list
      [
        with_repeat
        @@ with_no_trace ~show_proof:true
        @@ (with_fuel_counter fuel) ctauto_tac;
      ]
  in
  (match prove_dfs_with_trace ([], goal) next_tactic with
  | t, Complete thm ->
      List.iter print_endline t;
      print_endline "Proof Complete!";
      Printf.printf "With fuel usage: %d\n" !fuel;
      Printing.print_thm thm
  | _t, Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    intro_tac
    conj_tac
    neg_intro_tac
    apply_neg_asm_tac
    left_tac
    ccontr_tac
    apply_neg_asm_tac
    right_tac
    assumption_tac
    neg_intro_tac
    apply_neg_asm_tac
    left_tac
    assumption_tac
    Proof Complete!
    With fuel usage: 270
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q
    |}]

let%expect_test "bfs demorgans" =
  (* ¬(P ∨ Q) ⟹ ¬P ∧ ¬Q - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    make_imp (make_neg (make_disj p q)) (make_conj (make_neg p) (make_neg q))
  in
  let fuel = ref 0 in
  let next_tactic =
    next_tactic_of_list
      [
        with_repeat
        @@ with_no_trace ~show_proof:true
        @@ (with_fuel_counter fuel) ctauto_tac;
      ]
  in
  (match prove_bfs_with_trace ([], goal) next_tactic with
  | t, Complete thm ->
      List.iter print_endline t;
      print_endline "Proof Complete!";
      Printf.printf "With fuel usage: %d\n" !fuel;
      Printing.print_thm thm
  | _t, Incomplete _ -> print_endline "Proof Failed");
  [%expect
    {|
    intro_tac
    conj_tac
    neg_intro_tac
    apply_neg_asm_tac
    right_tac
    assumption_tac
    neg_intro_tac
    apply_neg_asm_tac
    left_tac
    assumption_tac
    Proof Complete!
    With fuel usage: 29526
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q
    |}]

let%expect_test "another tautology" =
  let mkvar s = make_var s bool_ty in

  let a = mkvar "a" in
  let b = mkvar "b" in
  (* let c = mkvar "c" in *)

  let na = make_neg a in
  let nb = make_neg b in

  let na_imp_nb = make_imp na nb in
  let na_imp_b = make_imp na b in

  let conjd = make_conj na_imp_b na_imp_nb in

  let goal = make_imp conjd a in

  let initial_fuel = 900 in
  let fuel = ref initial_fuel in

  let next_tactic =
    next_tactic_of_list
      [
        with_repeat
        @@ with_no_trace ~show_proof:true
        @@ (with_fuel_limit fuel) ctauto_tac;
      ]
  in
  (match prove_bfs_with_trace ([], goal) next_tactic with
  | exception Out_of_fuel ->
      print_endline "out of fuel";
      Printf.printf "With fuel usage: %d\n" (initial_fuel - !fuel)
  | t, Complete thm ->
      List.iter print_endline t;
      print_endline "Proof Complete!";
      Printf.printf "With fuel usage: %d\n" !fuel;
      Printing.print_thm thm
  | _t, Incomplete _ ->
      Printf.printf "With fuel usage: %d\n" !fuel;
      print_endline "Proof Failed");
  [%expect {|
    out of fuel
    With fuel usage: 900
    |}]

let%expect_test "rewrite_basic" =
  let nat_ty = Theorems.Nat.nat_def.ty in
  let _ = new_constant "Zero" nat_ty in
  let _ = new_constant "One" nat_ty in
  let _ = new_constant "Two" nat_ty in
  let _ = new_constant "add" (make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)) in

  let zero = Const ("Zero", nat_ty) in
  let one = Const ("One", nat_ty) in
  let two = Const ("Two", nat_ty) in
  let add = Const ("add", make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)) in
  let n = make_var "n" nat_ty in

  (* Rewrite rule: add Zero n = n *)
  let lhs = App (App (add, zero), n) in
  let eq_thm =
    new_axiom (Result.get_ok (safe_make_eq lhs n)) |> Result.get_ok
  in

  (* Goal: add Zero Zero = Zero *)
  let goal =
    Result.get_ok
      (safe_make_eq (App (App (add, zero), two)) (App (App (add, one), one)))
  in
  let next_tactic =
    next_tactic_of_list [ rewrite_tac |> with_rewrites [ eq_thm ]; assume_tac ]
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
    assume_tac
    rewrite_tac
    Proof Complete!
    Two = add One One
    ========================================
    add Zero Two = add One One
    |}]

let proven = ref []
let lemma s = [ List.assoc s !proven ]

let%expect_test "rewrite_basic" =
  let open Theorems.Nat in
  let x = make_var "x" nat_ty in

  let zero_plus_x = make_plus zero x |> Result.get_ok in
  let goal = make_forall x (Result.get_ok (safe_make_eq zero_plus_x x)) in

  let next_tactic = next_tactic_of_list [ gen_tac; simp_tac ] in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Incomplete";
      Printing.print_term g);

  [%expect
    {|
    gen_tac
    Proof Complete!
    ========================================
    ∀x. plus Zero x = x
    |}]

let%expect_test "rewrite induction" =
  let open Theorems.Nat in
  let x = make_var "x" nat_ty in

  let x_plus_zero = make_plus x zero |> Result.get_ok in
  let goal = make_forall x (Result.get_ok (safe_make_eq x_plus_zero x)) in

  let next_tactic =
    next_tactic_of_list
    @@ wrap_all with_no_trace
         [ induct_tac; simp_tac; gen_tac; intro_tac; simp_tac ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      proven := ("plus_x_zero", thm) :: !proven;
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. plus x Zero = x
    |}]

let%expect_test "basic nat" =
  let open Theorems.Nat in
  let make_plus' a b = make_plus a b |> Result.get_ok in
  let two_plus_3 = make_plus' n2 n3 in

  let goal = Result.get_ok (safe_make_eq two_plus_3 n5) in

  let next_tactic =
    next_tactic_of_list @@ wrap_all with_no_trace [ simp_tac ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    plus (Suc (Suc Zero)) (Suc (Suc (Suc Zero))) = Suc (Suc (Suc (Suc (Suc Zero))))
    |}]

let%expect_test "plus assoc" =
  let open Theorems.Nat in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let z = make_var "z" nat_ty in

  let make_plus' a b = make_plus a b |> Result.get_ok in

  let plus_xy = make_plus' x y in
  let plus_yz = make_plus' y z in
  let plus_xy_z = make_plus' plus_xy z in
  let plus_x_yz = make_plus' x plus_yz in

  let goal =
    Derived.make_foralls [ x; y; z ]
      (Result.get_ok (safe_make_eq plus_x_yz plus_xy_z))
  in

  let next_tactic =
    next_tactic_of_list
    @@ wrap_all with_no_trace
         [
           with_term x induct_tac;
           gen_tac;
           gen_tac;
           simp_tac;
           gen_tac;
           intro_tac;
           gen_tac;
           gen_tac;
           simp_tac;
         ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      proven := ("plus_assoc", thm) :: !proven;
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. ∀z. plus x (plus y z) = plus (plus x y) z
    |}]

let%expect_test "suc injective" =
  let open Theorems.Nat in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in

  let suc_x = App (suc, x) in
  let suc_y = App (suc, y) in

  (* Suc x = Suc y -> x = y *)
  let goal =
    Derived.make_foralls [ x; y ]
      (make_imp
         (Result.get_ok (safe_make_eq suc_x suc_y))
         (Result.get_ok (safe_make_eq x y)))
  in

  List.iter Printing.print_thm Theorems.Nat.nat_def.injective;

  let next_tactic =
    next_tactic_of_list
    @@ wrap_all with_no_trace
         [
           with_repeat gen_tac;
           intro_tac;
           apply_thm_tac |> with_lemmas nat_def.injective;
           assumption_tac;
         ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      proven := ("plus_inj", thm) :: !proven;
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    ========================================
    ∀x0. ∀y0. Suc x0 = Suc y0 ==> x0 = y0

    Proof Complete!
    ========================================
    ∀x. ∀y. Suc x = Suc y ==> x = y
    |}]

(* Lemma needed for commutativity: plus x (Suc y) = Suc (plus x y) *)
let%expect_test "plus suc lemma" =
  let open Theorems.Nat in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in

  let suc_y = App (suc, y) in
  let plus_x_suc_y = Result.get_ok (make_plus x suc_y) in
  let plus_x_y = Result.get_ok (make_plus x y) in
  let suc_plus_x_y = App (suc, plus_x_y) in

  (* plus x (Suc y) = Suc (plus x y) *)
  let goal =
    Derived.make_foralls [ x; y ]
      (Result.get_ok (safe_make_eq plus_x_suc_y suc_plus_x_y))
  in

  let next_tactic =
    next_tactic_of_list
    @@ wrap_all with_no_trace
         [
           induct_tac;
           simp_tac;
           gen_tac;
           refl_tac;
           gen_tac;
           intro_tac;
           gen_tac;
           simp_tac;
         ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      proven := ("plus_suc", thm) :: !proven;
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. plus x (Suc y) = Suc (plus x y)
    |}]

let%expect_test "suc injective rev" =
  let open Theorems.Nat in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in

  let suc_x = App (suc, x) in
  let suc_y = App (suc, y) in

  (* x = y -> Suc x =  Suc y *)
  let goal =
    Derived.make_foralls [ x; y ]
      (make_imp
         (Result.get_ok (safe_make_eq x y))
         (Result.get_ok (safe_make_eq suc_x suc_y)))
  in

  (* List.iter Printing.print_thm Theorems.Nat.nat_def.injective; *)
  let next_tactic =
    next_tactic_of_list
    @@ wrap_all with_no_trace
         [
           gen_tac;
           gen_tac;
           intro_tac;
           rewrite_tac |> with_assumption_rewrites;
           refl_tac;
         ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      proven := ("plus_inj_rev", thm) :: !proven;
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Incomplete";
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. x = y ==> Suc x = Suc y
    |}]

(* Commutativity: plus x y = plus y x *)
let%expect_test "plus comm" =
  let open Theorems.Nat in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in

  let plus_x_y = Result.get_ok (make_plus x y) in
  let plus_y_x = Result.get_ok (make_plus y x) in

  (* plus x y = plus y x *)
  let goal =
    Derived.make_foralls [ x; y ]
      (Result.get_ok (safe_make_eq plus_x_y plus_y_x))
  in
  (* List.iter print_endline (List.map fst !proven); *)
  (* List.iter Printing.print_thm (List.map snd !proven); *)

  let next_tactic =
    next_tactic_of_list
    @@ wrap_all with_no_trace
         [
           induct_tac;
           gen_tac;
           simp_tac;
           with_first_success @@ rewrite_tac
           |> with_rewrites (lemma "plus_x_zero");
           refl_tac;
           gen_tac;
           intro_tac;
           gen_tac;
           simp_tac;
           sym_tac;
           with_first_success @@ apply_thm_tac |> with_lemmas (lemma "plus_suc");
         ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      proven := ("plus_comm", thm) :: !proven;
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. plus x y = plus y x
    |}]

let%expect_test "cancellation" =
  let open Theorems.Nat in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let z = make_var "z" nat_ty in

  let plus_x_y = Result.get_ok (make_plus x y) in
  let plus_x_z = Result.get_ok (make_plus x z) in
  let p_eq = Result.get_ok (safe_make_eq plus_x_y plus_x_z) in
  let y_eq_z = Result.get_ok (safe_make_eq y z) in

  (* plus x y = plus x z -> y = z *)
  let goal = Derived.make_foralls [ x; y ] (make_imp p_eq y_eq_z) in
  (* List.iter Printing.print_thm !proven; *)

  let next_tactic =
    next_tactic_of_list
    @@ wrap_all with_no_trace
         [
           induct_tac;
           gen_tac;
           simp_tac;
           intro_tac;
           assumption_tac;
           gen_tac;
           simp_tac;
           intro_tac;
           gen_tac;
           intro_tac;
           apply_thm_asm_tac |> with_lemmas nat_def.injective;
           with_first_success @@ apply_thm_asm_tac
           |> with_lemmas_and_assumptions [];
           assumption_tac;
         ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. plus x y = plus x z ==> y = z
    |}]

let%expect_test "cancellation rev" =
  let open Theorems.Nat in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let z = make_var "z" nat_ty in

  let plus_y_x = Result.get_ok (make_plus y x) in
  let plus_z_x = Result.get_ok (make_plus z x) in
  let p_eq = Result.get_ok (safe_make_eq plus_y_x plus_z_x) in
  let y_eq_z = Result.get_ok (safe_make_eq y z) in

  (* plus y x = plus z x -> y = z *)
  let goal = Derived.make_foralls [ x; y ] (make_imp p_eq y_eq_z) in
  (* List.iter Printing.print_thm !proven; *)

  let next_tactic =
    next_tactic_of_list
    @@ wrap_all with_no_trace
         [
           induct_tac;
           gen_tac;
           simp_tac;
           intro_tac;
           rewrite_asm_tac |> with_rewrites (lemma "plus_x_zero");
           rewrite_asm_tac |> with_rewrites (lemma "plus_x_zero");
           assumption_tac;
           gen_tac;
           intro_tac;
           gen_tac;
           intro_tac;
           with_first_success @@ apply_thm_tac |> with_lemmas_and_assumptions [];
           rewrite_asm_tac |> with_rewrites (lemma "plus_suc");
           rewrite_asm_tac |> with_rewrites (lemma "plus_suc");
           apply_thm_asm_tac |> with_lemmas (lemma "plus_inj");
           assumption_tac;
         ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. plus y x = plus z x ==> y = z
    |}]

let%expect_test "length Nil = Zero" =
  let open Theorems.Nat in
  let open Theorems.ListTheory in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let nil_nat = type_inst [ (a, nat_ty) ] nil |> Result.get_ok in

  let length_nil = App (length_const, nil_nat) in
  let goal = Result.get_ok (safe_make_eq length_nil zero) in

  let next_tactic = next_tactic_of_list [ simp_tac ~with_asms:false ] in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    length Nil = Zero
    |}]

let%expect_test "length (Cons Zero Nil) = Suc Zero" =
  let open Theorems.Nat in
  let open Theorems.ListTheory in
  let _ = length_def |> Result.get_ok in

  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let nil_nat = type_inst [ (a, nat_ty) ] nil |> Result.get_ok in
  let cons_nat = type_inst [ (a, nat_ty) ] cons |> Result.get_ok in

  (* Cons Zero Nil *)
  let cons_zero_nil = App (App (cons_nat, zero), nil_nat) in
  let length_cons = App (length_const, cons_zero_nil) in
  let goal = Result.get_ok (safe_make_eq length_cons n1) in

  let next_tactic =
    next_tactic_of_list @@ wrap_all with_no_trace [ simp_tac ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    length (Cons Zero Nil) = Suc Zero
    |}]

let%expect_test "length_cons" =
  let open Theorems.Nat in
  let open Theorems.ListTheory in
  let _ = length_def |> Result.get_ok in

  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let cons_nat = type_inst [ (a, nat_ty) ] cons |> Result.get_ok in

  let x = make_var "x" nat_ty in
  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in

  (* length (Cons x xs) *)
  let cons_x_xs = App (App (cons_nat, x), xs) in
  let length_cons_x_xs = App (length_const, cons_x_xs) in

  (* Suc (length xs) *)
  let length_xs = App (length_const, xs) in
  let suc_length_xs = App (suc, length_xs) in

  (* ∀x. ∀xs. length (Cons x xs) = Suc (length xs) *)
  let goal =
    Derived.make_foralls [ x; xs ]
      (Result.get_ok (safe_make_eq length_cons_x_xs suc_length_xs))
  in

  let next_tactic =
    next_tactic_of_list @@ wrap_all with_no_trace [ gen_tac; gen_tac; simp_tac ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀xs. length (Cons x xs) = Suc (length xs)
    |}]

(* xs = Nil ==> length xs = Zero *)
let%expect_test "nil_implies_length_zero" =
  let open Theorems.Nat in
  let open Theorems.ListTheory in
  let _ = length_def |> Result.get_ok in

  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let nil_nat = type_inst [ (a, nat_ty) ] nil |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in

  (* xs = Nil *)
  let xs_eq_nil = Result.get_ok (safe_make_eq xs nil_nat) in

  (* length xs = Zero *)
  let length_xs = App (length_const, xs) in
  let length_eq_zero = Result.get_ok (safe_make_eq length_xs zero) in

  (* ∀xs. xs = Nil ==> length xs = Zero *)
  let goal = make_forall xs (make_imp xs_eq_nil length_eq_zero) in

  let next_tactic =
    next_tactic_of_list
    @@ wrap_all with_no_trace
         [
           gen_tac; intro_tac; rewrite_tac |> with_assumption_rewrites; simp_tac;
         ]
  in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀xs. xs = Nil ==> length xs = Zero
    |}]

(* length xs = Zero ==> xs = Nil *)
let%expect_test "length_zero_implies_nil" =
  let open Theorems.Nat in
  let open Theorems.ListTheory in
  let _ = length_def |> Result.get_ok in

  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let nil_nat = type_inst [ (a, nat_ty) ] nil |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in

  (* length xs = Zero *)
  let length_xs = App (length_const, xs) in
  let length_eq_zero = Result.get_ok (safe_make_eq length_xs zero) in

  (* xs = Nil *)
  let xs_eq_nil = Result.get_ok (safe_make_eq xs nil_nat) in

  (* ∀xs. length xs = Zero ==> xs = Nil *)
  let goal = make_forall xs (make_imp length_eq_zero xs_eq_nil) in

  let next_tactic = next_tactic_of_list [ induct_tac ] in
  (match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter print_term asms;
      Printing.print_term g);

  [%expect {|
    (TyCon ("fun", [(TyCon ("list", [(TyVar "a")])); (TyCon ("bool", []))]))
    (TyCon ("fun",
       [(TyCon ("list", [(TyCon ("nat", []))])); (TyCon ("bool", []))]))
    TypesDontAgree
    Proof Incomplete
    ∀xs. length xs = Zero ==> xs = Nil
    |}]
