open Heft
open Derived
open Tactic

(* open Effect *)
open Printing

(* Storage for proven lemmas *)
let proven = ref []
let lemma s = [ List.assoc s !proven ]

(* Helper function to reduce boilerplate in tests *)
let run_proof ?(dfs = false) ?(asms = []) ?store goal tactics =
  let next_tactic = next_tactic_of_list tactics in
  let result =
    if dfs then prove_dfs (asms, goal) next_tactic
    else prove (asms, goal) next_tactic
  in
  match result with
  | Complete thm ->
      print_endline "Proof Complete!";
      (match store with
      | Some name -> proven := (name, thm) :: !proven
      | None -> ());
      Printing.print_thm thm
  | Incomplete (asms, g) ->
      print_endline "Proof Incomplete";
      List.iter Printing.print_term asms;
      Printing.print_term g

let%expect_test "basic" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = make_conj a b in
  run_proof ~asms:[ a; b ] goal
    [
      with_skip_fail conj_tac;
      with_first_success assumption_tac;
      with_first_success assumption_tac;
    ];
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
  run_proof goal [ refl_tac ];
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
  run_proof goal [ intro_tac; assumption_tac ];

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
  run_proof ~asms:[ a ] goal [ left_tac; assumption_tac ];
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
  run_proof ~asms:[ a; b ] goal
    (wrap_all with_first_success [ right_tac; assumption_tac ]);

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
  run_proof ~asms:[ imp_cab; imp_ab; a ] goal
    [ apply_asm_tac |> with_term imp_ab; with_first_success assumption_tac ];

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
  run_proof ~dfs:true
    ~asms:[ make_false () ]
    goal
    [ ccontr_tac; assumption_tac ];

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
  run_proof ~asms:[ make_false () ] goal [ false_elim_tac; assumption_tac ];

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
  run_proof goal [ gen_tac; intro_tac; assumption_tac ];

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
  let open Theories.NatTheory in
  let a = make_var "A" bool_ty in
  let x = make_var "x" nat_ty in
  let goal = make_forall x (make_imp a a) in
  run_proof goal
    [
      induct_tac; intro_tac; assumption_tac; gen_tac; intro_tac; assumption_tac;
    ];

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
  run_proof ~dfs:true ~asms:[ f ] goal [ with_repeat or_tac; assumption_tac ];
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
  run_proof ~dfs:true ~asms:[ b; c ] goal
    [ conj_tac; with_skip_fail or_tac; assumption_tac ];

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
  run_proof ~dfs:true goal
    [
      intro_tac;
      elim_conj_asm_tac;
      intro_tac;
      apply_asm_tac;
      apply_asm_tac;
      assumption_tac;
    ];

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
  run_proof goal [ with_dfs @@ with_repeat ctauto_tac ];

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
  run_proof ~dfs:true goal
    [
      intro_tac;
      intro_tac;
      intro_tac;
      elim_disj_asm_tac;
      apply_asm_tac;
      assumption_tac;
      apply_asm_tac;
      assumption_tac;
    ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ intro_tac; false_elim_tac ];
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
  run_proof ~dfs:true goal [ intro_tac; intro_tac; neg_elim_tac ];
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
  run_proof ~dfs:true goal [ intro_tac; neg_intro_tac; neg_elim_tac ];
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
  run_proof ~dfs:true goal [ intro_tac; ccontr_tac; neg_elim_tac ];
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
  run_proof goal
    [ intro_tac; intro_tac; neg_intro_tac; mp_asm_tac; neg_elim_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof goal [ with_dfs @@ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
  [%expect
    {|
    Proof Complete!
    ========================================
    P ==> P ∧ P ∨ Q
    |}]

let%expect_test "not_false_is_true" =
  (* ¬⊥ *)
  let goal = make_neg (make_false ()) in
  run_proof ~dfs:true goal [ with_repeat @@ with_no_trace ctauto_tac ];
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
  run_proof goal
    (wrap_all
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
       ]);
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
  let nat_ty = Theories.NatTheory.nat_ty in
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
  run_proof goal [ rewrite_tac |> with_rewrites [ eq_thm ]; assume_tac ];

  [%expect
    {|
    assume_tac
    rewrite_tac
    Proof Complete!
    Two = add One One
    ========================================
    add Zero Two = add One One
    |}]

let%expect_test "rewrite_basic" =
  let open Theories.NatTheory in
  let x = make_var "x" nat_ty in
  let zero_plus_x = make_plus zero x |> Result.get_ok in
  let goal = make_forall x (Result.get_ok (safe_make_eq zero_plus_x x)) in
  run_proof goal [ gen_tac; simp_tac ];

  [%expect
    {|
    gen_tac
    Proof Complete!
    ========================================
    ∀x. plus zero x = x
    |}]

let%expect_test "rewrite induction" =
  let open Theories.NatTheory in
  let x = make_var "x" nat_ty in
  let x_plus_zero = make_plus x zero |> Result.get_ok in
  let goal = make_forall x (Result.get_ok (safe_make_eq x_plus_zero x)) in
  run_proof ~store:"plus_x_zero" goal
    (wrap_all with_no_trace
       [ induct_tac; simp_tac; gen_tac; intro_tac; simp_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. plus x zero = x
    |}]

let%expect_test "basic nat" =
  let open Theories.NatTheory in
  let make_plus' a b = make_plus a b |> Result.get_ok in
  let two_plus_3 = make_plus' n2 n3 in
  let goal = Result.get_ok (safe_make_eq two_plus_3 n5) in
  run_proof goal (wrap_all with_no_trace [ simp_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    plus (suc (suc zero)) (suc (suc (suc zero))) = suc (suc (suc (suc (suc zero))))
    |}]

let%expect_test "plus assoc" =
  let open Theories.NatTheory in
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
  run_proof ~store:"plus_assoc" goal
    (wrap_all with_no_trace
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
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. ∀z. plus x (plus y z) = plus (plus x y) z
    |}]

let%expect_test "suc injective" =
  let open Theories.NatTheory in
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
  run_proof ~store:"plus_inj" goal
    (wrap_all with_no_trace
       [
         with_repeat gen_tac;
         intro_tac;
         apply_thm_tac |> with_lemmas nat_def.injective;
         assumption_tac;
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. suc x = suc y ==> x = y
    |}]

(* Lemma needed for commutativity: plus x (Suc y) = Suc (plus x y) *)
let%expect_test "plus suc lemma" =
  let open Theories.NatTheory in
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
  run_proof ~store:"plus_suc" goal
    (wrap_all with_no_trace
       [
         induct_tac;
         simp_tac;
         gen_tac;
         refl_tac;
         gen_tac;
         intro_tac;
         gen_tac;
         simp_tac;
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. plus x (suc y) = suc (plus x y)
    |}]

let%expect_test "suc injective rev" =
  let open Theories.NatTheory in
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
  run_proof ~store:"plus_inj_rev" goal
    (wrap_all with_no_trace
       [
         gen_tac;
         gen_tac;
         intro_tac;
         rewrite_tac |> with_assumption_rewrites;
         refl_tac;
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. x = y ==> suc x = suc y
    |}]

(* Commutativity: plus x y = plus y x *)
let%expect_test "plus comm" =
  let open Theories.NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let plus_x_y = Result.get_ok (make_plus x y) in
  let plus_y_x = Result.get_ok (make_plus y x) in
  (* plus x y = plus y x *)
  let goal =
    Derived.make_foralls [ x; y ]
      (Result.get_ok (safe_make_eq plus_x_y plus_y_x))
  in
  run_proof ~store:"plus_comm" goal
    (wrap_all with_no_trace
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
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. plus x y = plus y x
    |}]

let%expect_test "cancellation" =
  let open Theories.NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let z = make_var "z" nat_ty in
  let plus_x_y = Result.get_ok (make_plus x y) in
  let plus_x_z = Result.get_ok (make_plus x z) in
  let p_eq = Result.get_ok (safe_make_eq plus_x_y plus_x_z) in
  let y_eq_z = Result.get_ok (safe_make_eq y z) in
  (* plus x y = plus x z -> y = z *)
  let goal = Derived.make_foralls [ x; y ] (make_imp p_eq y_eq_z) in
  run_proof goal
    (wrap_all with_no_trace
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
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. plus x y = plus x z ==> y = z
    |}]

let%expect_test "cancellation rev" =
  let open Theories.NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let z = make_var "z" nat_ty in
  let plus_y_x = Result.get_ok (make_plus y x) in
  let plus_z_x = Result.get_ok (make_plus z x) in
  let p_eq = Result.get_ok (safe_make_eq plus_y_x plus_z_x) in
  let y_eq_z = Result.get_ok (safe_make_eq y z) in
  (* plus y x = plus z x -> y = z *)
  let goal = Derived.make_foralls [ x; y ] (make_imp p_eq y_eq_z) in
  run_proof goal
    (wrap_all with_no_trace
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
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀y. plus y x = plus z x ==> y = z
    |}]

let%expect_test "length Nil = Zero" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let nil_nat = type_inst [ (a, nat_ty) ] nil |> Result.get_ok in

  let length_nil = App (length_const, nil_nat) in
  let goal = Result.get_ok (safe_make_eq length_nil zero) in
  run_proof goal [ simp_tac ~with_asms:false ~add:[] ];

  [%expect
    {|
    Proof Complete!
    ========================================
    length nil = zero
    |}]

let%expect_test "length (Cons Zero Nil) = Suc Zero" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let nil_nat = type_inst [ (a, nat_ty) ] nil |> Result.get_ok in
  let cons_nat = type_inst [ (a, nat_ty) ] cons |> Result.get_ok in

  (* Cons Zero Nil *)
  let cons_zero_nil = App (App (cons_nat, zero), nil_nat) in
  let length_cons = App (length_const, cons_zero_nil) in
  let goal = Result.get_ok (safe_make_eq length_cons n1) in
  run_proof goal (wrap_all with_no_trace [ simp_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    length (cons zero nil) = suc zero
    |}]

let%expect_test "length_cons" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
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
  run_proof goal (wrap_all with_no_trace [ gen_tac; gen_tac; simp_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀xs. length (cons x xs) = suc (length xs)
    |}]

(* xs = Nil ==> length xs = Zero *)
let%expect_test "nil_implies_length_zero" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let length_const = make_const "length" [] |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ a ])) in

  (* xs = Nil *)
  let xs_eq_nil = Result.get_ok (safe_make_eq xs nil) in

  (* length xs = Zero *)
  let length_xs = App (length_const, xs) in
  let length_eq_zero = Result.get_ok (safe_make_eq length_xs zero) in

  (* ∀xs. xs = Nil ==> length xs = Zero *)
  let goal = make_forall xs (make_imp xs_eq_nil length_eq_zero) in
  run_proof goal
    (wrap_all with_no_trace
       [ gen_tac; intro_tac; rewrite_tac |> with_assumption_rewrites; simp_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀xs. xs = nil ==> length xs = zero
    |}]

(* length xs = Zero ==> xs = Nil *)
let%expect_test "length_zero_implies_nil" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
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
  run_proof goal
    (wrap_all with_no_trace
       [
         induct_tac;
         intro_tac;
         refl_tac;
         gen_tac;
         gen_tac;
         intro_tac;
         intro_tac;
         with_first_success @@ apply_thm_asm_tac
         |> with_lemmas_and_assumptions [];
         assumption_tac;
       ]);

  [%expect
    {|
    Proof Complete!
    ∀n0. ∀n1. (length n1 = zero ==> n1 = nil) ==> length (cons n0 n1) = zero ==> cons n0 n1 = nil
    ========================================
    ∀x. length x = zero ==> x = nil
    |}]

let%expect_test "append nil xs = xs" =
  let open Theories.ListTheory in
  let append_const = make_const "append" [] |> Result.get_ok in

  (* append Nil Nil = Nil *)
  let xs = make_var "xs" list_a in
  let append_nil = App (append_const, nil) in
  let append_nil_xs = App (append_nil, xs) in
  let goal = make_forall xs @@ Result.get_ok (safe_make_eq append_nil_xs xs) in
  run_proof goal (wrap_all with_no_trace [ gen_tac; simp_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀xs. append nil xs = xs
    |}]

let%expect_test "append (Cons x xs) ys = Cons x (append xs ys)" =
  let open Theories.ListTheory in
  let append_const = make_const "append" [] |> Result.get_ok in

  (* append (Cons x xs) ys = Cons x (append xs ys) *)
  let x = make_var "x" a in
  let xs = make_var "xs" list_a in
  let ys = make_var "ys" list_a in

  (* LHS: append (Cons x xs) ys *)
  let cons_x_xs = App (App (cons, x), xs) in
  let append_cons = App (append_const, cons_x_xs) in
  let lhs = App (append_cons, ys) in

  (* RHS: Cons x (append xs ys) *)
  let append_xs = App (append_const, xs) in
  let append_xs_ys = App (append_xs, ys) in
  let rhs = App (App (cons, x), append_xs_ys) in

  let goal =
    make_foralls [ x; xs; ys ] @@ Result.get_ok (safe_make_eq lhs rhs)
  in
  run_proof ~store:"append_cons" goal
    (wrap_all with_no_trace [ with_repeat gen_tac; simp_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀xs. ∀ys. append (cons x xs) ys = cons x (append xs ys)
    |}]

let%expect_test "append xs nil = xs" =
  let open Theories.ListTheory in
  let append_const = make_const "append" [] |> Result.get_ok in

  (* need a lemma *)
  let xs = make_var "xs" list_a in
  let append_xs = App (append_const, xs) in
  let append_nil_xs = App (append_xs, nil) in
  let goal = make_forall xs @@ Result.get_ok (safe_make_eq append_nil_xs xs) in
  run_proof ~store:"append_xs_nil" goal
    (wrap_all with_no_trace
       [
         induct_tac;
         simp_tac;
         with_repeat gen_tac;
         intro_tac;
         rewrite_tac |> with_rewrites (lemma "append_cons");
         simp_tac ~add:(lemma "append_cons");
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. append x nil = x
    |}]

let%expect_test "append (append xs ys) zs = append xs (append ys zs)" =
  let open Theories.ListTheory in
  let append_const = make_const "append" [] |> Result.get_ok in

  let xs = make_var "xs" list_a in
  let ys = make_var "ys" list_a in
  let zs = make_var "zs" list_a in

  (* LHS: append (append xs ys) zs *)
  let append_xs_ys = App (App (append_const, xs), ys) in
  let lhs = App (App (append_const, append_xs_ys), zs) in

  (* RHS: append xs (append ys zs) *)
  let append_ys_zs = App (App (append_const, ys), zs) in
  let rhs = App (App (append_const, xs), append_ys_zs) in

  let goal =
    make_foralls [ xs; ys; zs ] @@ Result.get_ok (safe_make_eq lhs rhs)
  in
  run_proof ~store:"append_assoc" goal
    (wrap_all with_no_trace [ induct_tac; auto_dfs_tac; auto_dfs_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀ys. ∀zs. append (append x ys) zs = append x (append ys zs)
    |}]

let%expect_test "length (append xs ys) = plus (length xs) (length ys)" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let append_const = make_const "append" [ (a, nat_ty) ] |> Result.get_ok in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in
  let ys = make_var "ys" (TyCon ("list", [ nat_ty ])) in

  (* LHS: length (append xs ys) *)
  let append_xs_ys = App (App (append_const, xs), ys) in
  let lhs = App (length_const, append_xs_ys) in

  (* RHS: plus (length xs) (length ys) *)
  let length_xs = App (length_const, xs) in
  let length_ys = App (length_const, ys) in
  let rhs = Result.get_ok (make_plus length_xs length_ys) in

  let goal = make_foralls [ xs; ys ] @@ Result.get_ok (safe_make_eq lhs rhs) in
  run_proof ~store:"append_length" goal
    (wrap_all with_no_trace [ induct_tac; auto_dfs_tac; auto_dfs_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀ys. length (append x ys) = plus (length x) (length ys)
    |}]

let%expect_test "length (reverse xs) = length xs" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let reverse_const = make_const "reverse" [ (a, nat_ty) ] |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in

  (* LHS: length (reverse xs) *)
  let reverse_xs = App (reverse_const, xs) in
  let lhs = App (length_const, reverse_xs) in

  (* RHS: length xs *)
  let rhs = App (length_const, xs) in

  let goal = make_forall xs @@ Result.get_ok (safe_make_eq lhs rhs) in
  run_proof goal
    (wrap_all with_no_trace
       [
         induct_tac;
         simp_tac;
         with_repeat gen_tac;
         intro_tac;
         simp_tac ~add:(lemma "append_length");
         with_first_success @@ rewrite_tac |> with_rewrites (lemma "plus_comm");
         simp_tac;
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. length (reverse x) = length x
    |}]

let%expect_test "reverse (append xs ys) = append (reverse ys) (reverse xs)" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let append_const = make_const "append" [ (a, nat_ty) ] |> Result.get_ok in
  let reverse_const = make_const "reverse" [ (a, nat_ty) ] |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in
  let ys = make_var "ys" (TyCon ("list", [ nat_ty ])) in

  (* LHS: reverse (append xs ys) *)
  let append_xs_ys = App (App (append_const, xs), ys) in
  let lhs = App (reverse_const, append_xs_ys) in

  (* RHS: append (reverse ys) (reverse xs) *)
  let reverse_xs = App (reverse_const, xs) in
  let reverse_ys = App (reverse_const, ys) in
  let rhs = App (App (append_const, reverse_ys), reverse_xs) in

  let goal = make_foralls [ xs; ys ] @@ Result.get_ok (safe_make_eq lhs rhs) in
  run_proof ~store:"append_reverse" goal
    (wrap_all with_no_trace
       [
         induct_tac;
         gen_tac;
         simp_tac ~add:(lemma "append_xs_nil");
         with_repeat gen_tac;
         intro_tac;
         gen_tac;
         simp_tac;
         with_first_success @@ apply_thm_tac
         |> with_lemmas (lemma "append_assoc");
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀ys. reverse (append x ys) = append (reverse ys) (reverse x)
    |}]

let%expect_test "reverse (reverse xs) = xs" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let reverse_const = make_const "reverse" [ (a, nat_ty) ] |> Result.get_ok in

  let xs = make_var "xs" (TyCon ("list", [ nat_ty ])) in

  (* LHS: reverse (reverse xs) *)
  let reverse_xs = App (reverse_const, xs) in
  let lhs = App (reverse_const, reverse_xs) in

  (* RHS: xs *)
  let rhs = xs in

  let goal = make_forall xs @@ Result.get_ok (safe_make_eq lhs rhs) in
  run_proof goal
    (wrap_all with_no_trace
       [
         induct_tac;
         simp_tac;
         with_repeat gen_tac;
         intro_tac;
         simp_tac ~add:(lemma "append_reverse");
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. reverse (reverse x) = x
    |}]

let%expect_test "test defining with elab" =
  let prg =
    {|
    vartype a
    variable x y : a
    theorem fst_snd_eq: imp (eq x y) (eq (fst (pair x y)) (snd (pair x y)))

  |}
  in
  let goal = List.hd (Elaborator.goals_from_string prg) in
  run_proof goal (wrap_all with_no_trace [ intro_tac; simp_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    x = y ==> fst (pair x y) = snd (pair x y)
    |}]

let%expect_test "test minus" =
  let prg =
    {|
    theorem three_minus_one_is_two : eq
        (pred (suc (suc (suc zero))) )
        (suc (suc zero))
  |}
  in
  let goal = List.hd (Elaborator.goals_from_string prg) in
  run_proof goal (wrap_all with_no_trace [ simp_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    pred (suc (suc (suc zero))) = suc (suc zero)
    |}]

let%expect_test "test minus 2" =
  let prg =
    {|
    theorem sub_add_elim: eq
        (minus
            (suc (suc (suc (suc zero))))
            (suc (suc (suc zero))))
        (suc zero)
  |}
  in
  let goal = List.hd (Elaborator.goals_from_string prg) in
  run_proof goal [ simp_tac ];

  [%expect
    {|
    Proof Complete!
    ========================================
    minus (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = suc zero
    |}]

let%expect_test "n - 0 = n" =
  let prg =
    {|
    variable n : nat
    theorem minus_zero:
            (forall λn.
                (eq
                    (minus n zero)
                    (n)
                ))

  |}
  in
  let goal = List.hd (Elaborator.goals_from_string prg) in
  run_proof ~store:"minus_zero" goal
    (wrap_all with_no_trace [ induct_tac; auto_dfs_tac; auto_dfs_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. minus x zero = x
    |}]

(* n - (suc m) = (n - m) - 1 *)
let%expect_test "minus suc right" =
  let prg =
    {|
    variable n m : nat
    theorem minus_suc_right:
            (forall λn.
                (forall λm.
                    (eq
                        (minus n (suc m))
                        (pred (minus n m))
                    )))

  |}
  in
  let goal = List.hd (Elaborator.goals_from_string prg) in
  run_proof ~store:"minus_suc_right" goal
    (wrap_all with_no_trace
       [ induct_tac; auto_dfs_tac ~add:(lemma "minus_zero"); auto_dfs_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀m. minus x (suc m) = pred (minus x m)
    |}]

(* (suc n) - (suc m) = n - m *)
let%expect_test "minus suc suc" =
  let prg =
    {|
    variable n m : nat
    theorem minus_suc_suc:
            (forall λn.
                (forall λm.
                    (eq
                        (minus (suc n) (suc m))
                        (minus n m)
                    )))

  |}
  in
  let goal = List.hd (Elaborator.goals_from_string prg) in
  run_proof ~store:"minus_suc_suc" goal
    (wrap_all with_no_trace
       [
         gen_tac;
         induct_tac;
         simp_tac ~add:(lemma "minus_zero");
         gen_tac;
         intro_tac;
         rewrite_tac |> with_rewrites (lemma "minus_suc_right");
         rewrite_tac |> with_assumption_rewrites;
         rewrite_tac |> with_rewrites (lemma "minus_suc_right");
         refl_tac;
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀n. ∀x. minus (suc n) (suc x) = minus n x
    |}]

let%expect_test "n - n = z" =
  let prg =
    {|
    variable n : nat
    theorem minus_zero:
            (forall λn.
                (eq
                    (minus n n)
                    (zero)
                ))

  |}
  in
  let goal = List.hd (Elaborator.goals_from_string prg) in
  run_proof ~store:"minus_self" goal
    (wrap_all with_no_trace
       [
         induct_tac;
         simp_tac;
         gen_tac;
         intro_tac;
         simp_tac ~add:(lemma "minus_suc_suc");
         simp_asm_tac ~with_asms:false;
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. minus x x = zero
    |}]

let%expect_test "x - n + n = x" =
  let prg =
    {|
    variable x n : nat
    theorem four_min_three_is_one:
        forall (λx.
            (forall λn.
                (eq
                    (minus (plus x n) n)
                    (x)
                )))

  |}
  in
  let goal = List.hd (Elaborator.goals_from_string prg) in
  run_proof goal
    (wrap_all with_no_trace
       [
         gen_tac;
         induct_tac;
         simp_tac ~add:(lemma "plus_x_zero" @ lemma "minus_zero");
         gen_tac;
         intro_tac;
         rewrite_tac |> with_rewrites (lemma "plus_suc");
         rewrite_tac |> with_rewrites (lemma "minus_suc_suc");
         assumption_tac;
       ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    ∀x. ∀x'. minus (plus x x') x' = x
    |}]

let%expect_test "pred twice" =
  let prg =
    {|
    theorem four_min_three_is_one:
        eq 
            (twice pred (suc (suc zero)))
            (zero)
  |}
  in
  let goal = List.hd (Elaborator.goals_from_string prg) in
  run_proof goal (wrap_all with_no_trace [ simp_tac ]);

  [%expect
    {|
    Proof Complete!
    ========================================
    twice pred (suc (suc zero)) = zero
    |}]
