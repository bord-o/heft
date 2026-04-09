open Heft
open Kernel
open Derived
open Tactic
open Heft_theories

let%expect_test "basic" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = ([ a; b ], make_conj a b) in
  let proof = conj_tac >> assumption_tac >> with_first assumption_tac in
  run_proof goal proof;
  [%expect
    {|
    A
    B
    ========================================
    A ∧ B

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "basic2" =
  let a = make_var "A" bool_ty in
  let goal = ([], safe_make_eq a a |> Result.get_ok) in
  run_proof goal refl_tac;
  [%expect
    {|
    ========================================
    A = A

    Proof Complete!
    with fuel: 1
    |}]

let%expect_test "basic3" =
  let a = make_var "A" bool_ty in
  let goal = ([], make_imp a a) in
  let proof = intro_tac >> assumption_tac in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    A ==> A

    Proof Complete!
    with fuel: 2
    |}]

let%expect_test "basic4" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = ([ a ], make_disj a b) in
  let proof = left_tac >> assumption_tac in
  run_proof goal proof;
  [%expect
    {|
    A
    ========================================
    A ∨ B

    Proof Complete!
    with fuel: 7
    |}]

let%expect_test "basic5" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = ([ a; b ], make_disj a b) in
  let proof = right_tac >> with_first assumption_tac in
  run_proof goal proof;
  [%expect
    {|
    B
    ========================================
    A ∨ B

    Proof Complete!
    with fuel: 7
    |}]

let%expect_test "basic6" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let imp_ab = make_imp a b in
  let imp_cab = make_imp (make_imp c a) b in
  let goal = ([ imp_cab; imp_ab; a ], b) in
  let proof = with_term imp_ab apply_asm_tac >> with_first assumption_tac in
  run_proof goal proof;

  [%expect
    {|
    A
    A ==> B
    ========================================
    B

    Proof Complete!
    with fuel: 5
    |}]

let%expect_test "new apply" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let imp_cab = make_imp c (make_imp a b) in
  let imp_ab = make_imp a b in
  let goal = ([ imp_cab; imp_ab; a ], b) in
  let proof =
    with_assumptions (with_nth_choice 1 apply_tac) >> with_first assumption_tac
  in
  run_proof goal proof;

  [%expect
    {|
    A
    A ==> B
    ========================================
    B

    Proof Complete!
    with fuel: 6
    |}]

let%expect_test "deep sequencing with conj" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let goal = ([ a; b; c ], make_conj (make_conj a b) c) in
  let proof =
    conj_tac >> conj_tac >> assumption_tac >> with_first assumption_tac
    >> with_first assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    A
    B
    C
    ========================================
    A ∧ B ∧ C

    Proof Complete!
    with fuel: 5
    |}]

let%expect_test "basic7" =
  let a = make_var "A" bool_ty in
  let goal = ([ make_false () ], a) in
  let proof = ccontr_tac >> with_first assumption_tac in
  run_proof goal proof;

  [%expect
    {|
    F
    ========================================
    A

    Proof Complete!
    with fuel: 11
    |}]

let%expect_test "basic8" =
  let a = make_var "A" bool_ty in
  let goal = ([ make_false () ], a) in
  let proof = false_elim_tac >> assumption_tac in
  run_proof goal proof;

  [%expect
    {|
    F
    ========================================
    A

    Proof Complete!
    with fuel: 1
    |}]

(* let err = Result.get_ok *)

let%expect_test "basic9" =
  let a = make_var "A" bool_ty in
  let x = make_var "x" bool_ty in
  let goal = ([], make_forall x (make_imp a a)) in
  let proof = gen_tac >> intro_tac >> assumption_tac in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    ∀x. A ==> A

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "basic10" =
  let open Nats in
  let a = make_var "A" bool_ty in
  let x = make_var "x" nat_ty in
  let goal = ([], make_forall x (make_imp a a)) in
  let proof =
    induct_tac >> intro_tac >> assumption_tac >> gen_tac >> intro_tac
    >> assumption_tac
  in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    ∀x. A ==> A

    Proof Complete!
    with fuel: 13
    |}]

let%expect_test "dfs_backtrack" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let d = make_var "D" bool_ty in
  let e = make_var "E" bool_ty in
  let f = make_var "F" bool_ty in
  let goal =
    ( [ f ],
      make_disj (make_disj e (make_disj (make_disj c d) (make_disj a b))) f )
  in
  let proof = with_best_first (try_ or_tac >> assumption_tac) in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      or_tac >>
      right_tac >>
      assumption_tac
    F
    ========================================
    E ∨ C ∨ D ∨ A ∨ B ∨ F

    Proof Complete!
    with fuel: 19
    |}]

let%expect_test "dfs_conj_backtrack" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  (* Goal: (A ∨ B) ∧ C, only have [B; C] *)
  let left = make_disj a b in
  let goal = ([ b; c ], make_conj left c) in
  let proof =
    with_best_first (try_ conj_tac >> try_ or_tac >> assumption_tac)
  in
  run_proof goal proof;

  [%expect
    {|
    Proof:
      conj_tac >>
      assumption_tac >>
      or_tac >>
      right_tac >>
      assumption_tac
    B
    C
    ========================================
    A ∨ B ∧ C

    Proof Complete!
    with fuel: 48
    |}]

let%expect_test "dfs_conj_assumptions" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let p_imp_q = make_imp p q in
  let q_imp_r = make_imp q r in
  let p_imp_r = make_imp p r in
  let goal = ([], make_imp (make_conj p_imp_q q_imp_r) p_imp_r) in
  let proof =
    with_best_first
      (pick_tac [ intro_tac; elim_conj_asm_tac; apply_asm_tac; assumption_tac ])
  in
  run_proof goal proof;

  [%expect
    {|
    Proof:
      intro_tac >>
      elim_conj_asm_tac >>
      intro_tac >>
      apply_asm_tac >>
      apply_asm_tac >>
      assumption_tac
    ========================================
    (P ==> Q) ∧ (Q ==> R) ==> P ==> R

    Proof Complete!
    with fuel: 62
    |}]

let%expect_test "complete_prop_automation" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let p_imp_q = make_imp p q in
  let q_imp_r = make_imp q r in
  let p_imp_r = make_imp p r in
  let goal = ([], make_imp (make_conj p_imp_q q_imp_r) p_imp_r) in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;

  [%expect
    {|
    Proof:
      intro_tac >>
      elim_conj_asm_tac >>
      intro_tac >>
      mp_asm_tac >>
      mp_asm_tac >>
      assumption_tac
    ========================================
    (P ==> Q) ∧ (Q ==> R) ==> P ==> R

    Proof Complete!
    with fuel: 79
    |}]

let%expect_test "dfs_disj_assumptions" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let p_or_q = make_disj p q in
  let p_imp_r = make_imp p r in
  let q_imp_r = make_imp q r in
  let goal = ([], make_imp p_or_q (make_imp p_imp_r (make_imp q_imp_r r))) in
  let proof =
    with_best_first
      (pick_tac [ intro_tac; elim_disj_asm_tac; apply_asm_tac; assumption_tac ])
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      intro_tac >>
      intro_tac >>
      elim_disj_asm_tac >>
      apply_asm_tac >>
      assumption_tac >>
      apply_asm_tac >>
      assumption_tac
    ========================================
    P ∨ Q ==> (P ==> R) ==> (Q ==> R) ==> R

    Proof Complete!
    with fuel: 69
    |}]

let%expect_test "pauto_disj_elimination" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let p_or_q = make_disj p q in
  let p_imp_r = make_imp p r in
  let q_imp_r = make_imp q r in
  let goal = ([], make_imp p_or_q (make_imp p_imp_r (make_imp q_imp_r r))) in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      intro_tac >>
      elim_disj_asm_tac >>
      intro_tac >>
      mp_asm_tac >>
      assumption_tac >>
      intro_tac >>
      mp_asm_tac >>
      assumption_tac
    ========================================
    P ∨ Q ==> (P ==> R) ==> (Q ==> R) ==> R

    Proof Complete!
    with fuel: 271
    |}]

let%expect_test "false_elim_tac_test" =
  (* ⊥ in assumptions, prove anything *)
  let p = make_var "P" bool_ty in
  let false_tm = make_false () in
  let goal = ([], make_imp false_tm p) in
  let proof = intro_tac >> false_elim_tac in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    F ==> P

    Proof Complete!
    with fuel: 2
    |}]

let%expect_test "neg_elim_tac_test" =
  (* P and ¬P in assumptions, prove anything *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp p (make_imp (make_neg p) q)) in
  let proof = with_repeat intro_tac >> neg_elim_tac in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    P ==> ¬P ==> Q

    Proof Complete!
    with fuel: 6
    |}]

let%expect_test "neg_intro_tac_test" =
  (* Goal is ¬P, reduce to [P] ⊢ ⊥ *)
  (* Prove: P ⟹ ¬¬P *)
  let p = make_var "P" bool_ty in
  let goal = ([], make_imp p (make_neg (make_neg p))) in
  let proof = intro_tac >> neg_intro_tac >> neg_elim_tac in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    P ==> ¬¬P

    Proof Complete!
    with fuel: 8
    |}]

let%expect_test "ccontr_tac_test" =
  (* Classical: assume ¬P, derive ⊥, conclude P *)
  (* Prove: ¬¬P ⟹ P (requires classical logic) *)
  let p = make_var "P" bool_ty in
  let goal = ([], make_imp (make_neg (make_neg p)) p) in
  let proof = intro_tac >> ccontr_tac >> with_best_first neg_elim_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      neg_elim_tac
    ========================================
    ¬¬P ==> P

    Proof Complete!
    with fuel: 14
    |}]

let%expect_test "modus_tollens" =
  (* (P ⟹ Q) ⟹ ¬Q ⟹ ¬P *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    ([], make_imp (make_imp p q) (make_imp (make_neg q) (make_neg p)))
  in
  let proof =
    intro_tac >> intro_tac >> neg_intro_tac >> mp_asm_tac >> neg_elim_tac
  in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    (P ==> Q) ==> ¬Q ==> ¬P

    Proof Complete!
    with fuel: 12
    |}]

let%expect_test "excluded_middle_pauto" =
  (* P ∨ ¬P (requires classical logic) *)
  let p = make_var "P" bool_ty in
  let goal = ([], make_disj p (make_neg p)) in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      ccontr_tac >>
      apply_neg_asm_tac >>
      right_tac >>
      neg_intro_tac >>
      apply_neg_asm_tac >>
      left_tac >>
      assumption_tac
    ========================================
    P ∨ ¬P

    Proof Complete!
    with fuel: 515
    |}]

let%expect_test "contraposition" =
  (* (P ⟹ Q) ⟹ (¬Q ⟹ ¬P) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    ([], make_imp (make_imp p q) (make_imp (make_neg q) (make_neg p)))
  in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      intro_tac >>
      neg_intro_tac >>
      mp_asm_tac >>
      neg_elim_tac
    ========================================
    (P ==> Q) ==> ¬Q ==> ¬P

    Proof Complete!
    with fuel: 96
    |}]

let%expect_test "distribution_and_over_or" =
  (* P ∧ (Q ∨ R) ⟹ (P ∧ Q) ∨ (P ∧ R) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let goal =
    ( [],
      make_imp
        (make_conj p (make_disj q r))
        (make_disj (make_conj p q) (make_conj p r)) )
  in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      elim_conj_asm_tac >>
      elim_disj_asm_tac >>
      right_tac >>
      conj_tac >>
      assumption_tac >>
      assumption_tac >>
      left_tac >>
      conj_tac >>
      assumption_tac >>
      assumption_tac
    ========================================
    P ∧ Q ∨ R ==> P ∧ Q ∨ P ∧ R

    Proof Complete!
    with fuel: 3561
    |}]

let%expect_test "distribution_or_over_and" =
  (* P ∨ (Q ∧ R) ⟹ (P ∨ Q) ∧ (P ∨ R) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let goal =
    ( [],
      make_imp
        (make_disj p (make_conj q r))
        (make_conj (make_disj p q) (make_disj p r)) )
  in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      conj_tac >>
      elim_disj_asm_tac >>
      elim_conj_asm_tac >>
      right_tac >>
      assumption_tac >>
      left_tac >>
      assumption_tac >>
      elim_disj_asm_tac >>
      elim_conj_asm_tac >>
      right_tac >>
      assumption_tac >>
      left_tac >>
      assumption_tac
    ========================================
    P ∨ Q ∧ R ==> P ∨ Q ∧ P ∨ R

    Proof Complete!
    with fuel: 808
    |}]

let%expect_test "de_morgan_and" =
  (* ¬(P ∧ Q) ⟹ ¬P ∨ ¬Q - requires classical *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    ( [],
      make_imp (make_neg (make_conj p q)) (make_disj (make_neg p) (make_neg q))
    )
  in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      ccontr_tac >>
      apply_neg_asm_tac >>
      intro_tac >>
      left_tac >>
      neg_intro_tac >>
      apply_neg_asm_tac >>
      intro_tac >>
      right_tac >>
      neg_intro_tac >>
      apply_neg_asm_tac >>
      conj_tac >>
      assumption_tac >>
      assumption_tac
    ========================================
    ¬P ∧ Q ==> ¬P ∨ ¬Q

    Proof Complete!
    with fuel: 2252
    |}]

let%expect_test "de_morgan_or" =
  (* ¬(P ∨ Q) ⟹ ¬P ∧ ¬Q - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    ( [],
      make_imp (make_neg (make_disj p q)) (make_conj (make_neg p) (make_neg q))
    )
  in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      conj_tac >>
      neg_intro_tac >>
      apply_neg_asm_tac >>
      right_tac >>
      assumption_tac >>
      neg_intro_tac >>
      apply_neg_asm_tac >>
      left_tac >>
      assumption_tac
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q

    Proof Complete!
    with fuel: 468
    |}]

let%expect_test "de_morgan_or_converse" =
  (* ¬P ∧ ¬Q ⟹ ¬(P ∨ Q) - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    ( [],
      make_imp (make_conj (make_neg p) (make_neg q)) (make_neg (make_disj p q))
    )
  in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      elim_conj_asm_tac >>
      neg_intro_tac >>
      elim_disj_asm_tac >>
      neg_elim_tac >>
      neg_elim_tac
    ========================================
    ¬P ∧ ¬Q ==> ¬P ∨ Q

    Proof Complete!
    with fuel: 198
    |}]

let%expect_test "implication_as_disjunction" =
  (* (P ⟹ Q) ⟹ ¬P ∨ Q - requires classical *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_imp p q) (make_disj (make_neg p) q)) in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      ccontr_tac >>
      apply_neg_asm_tac >>
      intro_tac >>
      left_tac >>
      neg_intro_tac >>
      apply_neg_asm_tac >>
      mp_asm_tac >>
      intro_tac >>
      right_tac >>
      assumption_tac
    ========================================
    (P ==> Q) ==> ¬P ∨ Q

    Proof Complete!
    with fuel: 973
    |}]

let%expect_test "disjunction_as_implication" =
  (* ¬P ∨ Q ⟹ (P ⟹ Q) - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_disj (make_neg p) q) (make_imp p q)) in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      intro_tac >>
      elim_disj_asm_tac >>
      assumption_tac >>
      neg_elim_tac
    ========================================
    ¬P ∨ Q ==> P ==> Q

    Proof Complete!
    with fuel: 127
    |}]

let%expect_test "triple_negation" =
  (* ¬¬¬P ⟹ ¬P - intuitionistic *)
  let p = make_var "P" bool_ty in
  let goal = ([], make_imp (make_neg (make_neg (make_neg p))) (make_neg p)) in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      neg_intro_tac >>
      apply_neg_asm_tac >>
      neg_intro_tac >>
      neg_elim_tac
    ========================================
    ¬¬¬P ==> ¬P

    Proof Complete!
    with fuel: 125
    |}]

let%expect_test "explosion" =
  (* P ⟹ ¬P ⟹ Q *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp p (make_imp (make_neg p) q)) in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      intro_tac >>
      neg_elim_tac
    ========================================
    P ==> ¬P ==> Q

    Proof Complete!
    with fuel: 33
    |}]

let%expect_test "complex_nested" =
  (* ((P ⟹ Q) ⟹ P) ⟹ P - Peirce's law, requires classical *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_imp (make_imp p q) p) p) in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      ccontr_tac >>
      apply_neg_asm_tac >>
      apply_asm_tac >>
      intro_tac >>
      neg_elim_tac
    ========================================
    ((P ==> Q) ==> P) ==> P

    Proof Complete!
    with fuel: 1381
    |}]

let%expect_test "four_variable_distribution" =
  (* (A ∨ B) ∧ (C ∨ D) ⟹ (A ∧ C) ∨ (A ∧ D) ∨ (B ∧ C) ∨ (B ∧ D) *)
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let d = make_var "D" bool_ty in
  let goal =
    ( [],
      make_imp
        (make_conj (make_disj a b) (make_disj c d))
        (make_disj (make_conj a c)
           (make_disj (make_conj a d)
              (make_disj (make_conj b c) (make_conj b d)))) )
  in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      elim_conj_asm_tac >>
      elim_disj_asm_tac >>
      right_tac >>
      right_tac >>
      elim_disj_asm_tac >>
      right_tac >>
      conj_tac >>
      assumption_tac >>
      assumption_tac >>
      left_tac >>
      conj_tac >>
      assumption_tac >>
      assumption_tac >>
      elim_disj_asm_tac >>
      right_tac >>
      left_tac >>
      conj_tac >>
      assumption_tac >>
      assumption_tac >>
      left_tac >>
      conj_tac >>
      assumption_tac >>
      assumption_tac
    ========================================
    A ∨ B ∧ C ∨ D ==> A ∧ C ∨ A ∧ D ∨ B ∧ C ∨ B ∧ D

    Proof Complete!
    with fuel: 11872
    |}]

let%expect_test "implication_chain" =
  (* (A ⟹ B) ⟹ (B ⟹ C) ⟹ (C ⟹ D) ⟹ (A ⟹ D) *)
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let d = make_var "D" bool_ty in
  let goal =
    ( [],
      make_imp (make_imp a b)
        (make_imp (make_imp b c) (make_imp (make_imp c d) (make_imp a d))) )
  in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      intro_tac >>
      intro_tac >>
      intro_tac >>
      mp_asm_tac >>
      mp_asm_tac >>
      mp_asm_tac >>
      assumption_tac
    ========================================
    (A ==> B) ==> (B ==> C) ==> (C ==> D) ==> A ==> D

    Proof Complete!
    with fuel: 88
    |}]

let%expect_test "contraposition_chain" =
  (* (A ⟹ B) ⟹ (B ⟹ C) ⟹ (¬C ⟹ ¬A) *)
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let goal =
    ( [],
      make_imp (make_imp a b)
        (make_imp (make_imp b c) (make_imp (make_neg c) (make_neg a))) )
  in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      intro_tac >>
      intro_tac >>
      neg_intro_tac >>
      mp_asm_tac >>
      mp_asm_tac >>
      neg_elim_tac
    ========================================
    (A ==> B) ==> (B ==> C) ==> ¬C ==> ¬A

    Proof Complete!
    with fuel: 128
    |}]

let%expect_test "absorption_law" =
  (* P ∧ (P ∨ Q) ⟺ P - just one direction here *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_conj p (make_disj p q)) p) in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      elim_conj_asm_tac >>
      assumption_tac
    ========================================
    P ∧ P ∨ Q ==> P

    Proof Complete!
    with fuel: 24
    |}]

let%expect_test "absorption_law_converse" =
  (* P ⟹ P ∧ (P ∨ Q) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp p (make_conj p (make_disj p q))) in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      conj_tac >>
      left_tac >>
      assumption_tac >>
      assumption_tac
    ========================================
    P ==> P ∧ P ∨ Q

    Proof Complete!
    with fuel: 174
    |}]

let%expect_test "not_false_is_true" =
  (* ¬⊥ *)
  let goal = ([], make_neg (make_false ())) in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      neg_intro_tac >>
      false_elim_tac
    ========================================
    ¬F

    Proof Complete!
    with fuel: 27
    |}]

let%expect_test "manual version " =
  (* ¬(P ∨ Q) ⟹ ¬P ∧ ¬Q - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    ( [],
      make_imp (make_neg (make_disj p q)) (make_conj (make_neg p) (make_neg q))
    )
  in
  (* let proof = with_best_first ctauto_tac in *)
  let proof =
    intro_tac >> conj_tac >> neg_intro_tac >> apply_neg_asm_tac >> left_tac
    >> assumption_tac >> neg_intro_tac >> apply_neg_asm_tac >> right_tac
    >> assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q

    Proof Complete!
    with fuel: 34
    |}]

let%expect_test "dfs demorgans" =
  (* ¬(P ∨ Q) ⟹ ¬P ∧ ¬Q - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    ( [],
      make_imp (make_neg (make_disj p q)) (make_conj (make_neg p) (make_neg q))
    )
  in
  let proof = with_best_first ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro_tac >>
      conj_tac >>
      neg_intro_tac >>
      apply_neg_asm_tac >>
      right_tac >>
      assumption_tac >>
      neg_intro_tac >>
      apply_neg_asm_tac >>
      left_tac >>
      assumption_tac
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q

    Proof Complete!
    with fuel: 468
    |}]

let%expect_test "rewrite_basic" =
  let nat_ty = Nats.nat_ty in
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
    ( [],
      Result.get_ok
        (safe_make_eq (App (App (add, zero), two)) (App (App (add, one), one)))
    )
  in
  let proof = with_rules [ eq_thm ] rewrite_tac >> assume_tac in
  run_proof goal proof;

  [%expect
    {|
    Two = add One One
    ========================================
    add Zero Two = add One One

    Proof Complete!
    with fuel: 7
    |}]

let%expect_test "rewrite_basic" =
  let open Nats in
  let x = make_var "x" nat_ty in
  let zero_plus_x = make_plus zero x |> Result.get_ok in
  let goal = ([], make_forall x (Result.get_ok (safe_make_eq zero_plus_x x))) in
  let proof = gen_tac >> simp_tac in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∀x. plus Zero x = x

    Proof Complete!
    with fuel: 20
    |}]

let%expect_test "basic4" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = ([ a ], make_disj a b) in
  let name, _ = cost_of_tactic left_tac goal in
  print_endline name;
  [%expect {| left_tac |}]

let%expect_test "exists_tac_bool" =
  let p = make_var "P" bool_ty in
  let goal = ([ make_true () ], make_exists p p) in
  (* ∃P. P *)
  run_proof goal
    (with_arbitrary_term (make_true ()) exists_tac >> assumption_tac);
  [%expect
    {|
    ========================================
    ∃P. P

    Proof Complete!
    with fuel: 9
    |}]

let%expect_test "exists_tac_refl" =
  let open Nats in
  let n = Var ("n", nat_ty) in
  let eq_nn = Result.get_ok (safe_make_eq n n) in
  let goal = ([], make_exists n eq_nn) in
  (* ∃n. n = n *)
  run_proof goal (with_arbitrary_term zero exists_tac >>> refl_tac);
  [%expect
    {|
    ========================================
    ∃n. n = n

    Proof Complete!
    with fuel: 9
    |}]

let%expect_test "exists_tac_nested" =
  let open Nats in
  let m = Var ("m", nat_ty) in
  let n = Var ("n", nat_ty) in
  let eq_mn = Result.get_ok (safe_make_eq m n) in
  let goal = ([], make_exists m (make_exists n eq_mn)) in
  (* ∃m. ∃n. m = n *)
  run_proof goal
    (with_arbitrary_term zero exists_tac
    >> with_arbitrary_term zero exists_tac
    >>> refl_tac);
  [%expect
    {|
    ========================================
    ∃m. ∃n. m = n

    Proof Complete!
    with fuel: 17
    |}]

let%expect_test "trans tac" =
  let open Nats in
  let m = Var ("m", nat_ty) in
  let n = Var ("n", nat_ty) in
  let o = Var ("o", nat_ty) in
  let eq_mo = Result.get_ok (safe_make_eq m o) in
  let eq_on = Result.get_ok (safe_make_eq o n) in
  let eq_mn = Result.get_ok (safe_make_eq m n) in
  let goal = ([ eq_mo; eq_on ], eq_mn) in

  run_proof goal
    (with_arbitrary_term o trans_tac
    >> with_first assumption_tac >> with_first assumption_tac);
  [%expect
    {|
    m = o
    o = n
    ========================================
    m = n

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "assert_tac_basic" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let pq = make_imp p q in
  let qr = make_imp q r in
  let goal = ([ p; pq; qr ], r) in
  let proof =
    with_arbitrary_term q assert_tac
    >> with_first mp_asm_tac >> with_first assumption_tac
    >> with_first mp_asm_tac >> with_first assumption_tac
  in
  run_proof ~notrace:false goal proof;

  [%expect
    {|
    Found matching assumption
    Assumption succeeded
    assumption_tac
    mp_asm_tac
    Found matching assumption
    Assumption succeeded
    assumption_tac
    mp_asm_tac
    assert_tac
    P
    P ==> Q
    Q ==> R
    ========================================
    R

    Proof Complete!
    with fuel: 13
    |}]

(* ---- cases_tac tests ---- *)

let%expect_test "cases_tac bool forall refl" =
  (* ∀b. b = b — trivial, both cases solved by refl *)
  let b = make_var "b" bool_ty in
  let goal = ([], make_forall b (Result.get_ok (safe_make_eq b b))) in
  let proof = cases_tac >> refl_tac >> with_first refl_tac in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∀b. b = b

    Proof Complete!
    with fuel: 10
    |}]

let%expect_test "cases_tac bool forall imp" =
  (* ∀b. b = T ==> b = T — each case trivially true *)
  let b = make_var "b" bool_ty in
  let b_eq_t = Result.get_ok (safe_make_eq b (make_true ())) in
  let goal = ([], make_forall b (make_imp b_eq_t b_eq_t)) in
  let proof =
    cases_tac >> intro_tac >> assumption_tac >> with_first intro_tac
    >> with_first assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∀b. b = T ==> b = T

    Proof Complete!
    with fuel: 12
    |}]

let%expect_test "cases_tac bool forall with body" =
  (* ∀b. b = T ∨ b = F — classic bool exhaustion *)
  let b = make_var "b" bool_ty in
  let b_eq_t = Result.get_ok (safe_make_eq b (make_true ())) in
  let b_eq_f = Result.get_ok (safe_make_eq b (make_false ())) in
  let goal = ([], make_forall b (make_disj b_eq_t b_eq_f)) in
  let proof =
    cases_tac >> left_tac >> refl_tac >> with_first right_tac
    >> with_first refl_tac
  in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∀b. b = T ∨ b = F

    Proof Complete!
    with fuel: 22
    |}]

let%expect_test "cases_tac bool forall conj" =
  (* ∀b. (b = T ∨ b = F) ∧ (b = T ∨ b = F) *)
  let b = make_var "b" bool_ty in
  let b_eq_t = Result.get_ok (safe_make_eq b (make_true ())) in
  let b_eq_f = Result.get_ok (safe_make_eq b (make_false ())) in
  let disj = make_disj b_eq_t b_eq_f in
  let goal = ([], make_forall b (make_conj disj disj)) in
  let case_proof =
    conj_tac >> left_tac >> refl_tac >> with_first left_tac
    >> with_first refl_tac
  in
  let proof =
    cases_tac >> case_proof
    >> with_first
         (conj_tac >> right_tac >> refl_tac >> with_first right_tac
        >> with_first refl_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∀b. b = T ∨ b = F ∧ b = T ∨ b = F

    Proof Complete!
    with fuel: 38
    |}]

let%expect_test "cases_tac inductive delegates to induct_tac" =
  (* ∀x:nat. x = x — cases on nat should delegate to induct_tac *)
  let open Nats in
  let x = make_var "x" nat_ty in
  let goal = ([], make_forall x (Result.get_ok (safe_make_eq x x))) in
  let proof =
    cases_tac >> refl_tac >> with_first gen_tac >> with_first intro_tac
    >> with_first refl_tac
  in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∀x. x = x

    Proof Complete!
    with fuel: 20
    |}]

let%expect_test "cases_tac arbitrary bool expr" =
  (* Given A ∨ B, case split on A to add A=T or A=F as assumption *)
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let a_eq_t = Result.get_ok (safe_make_eq a (make_true ())) in
  let goal = ([ a_eq_t; b ], Result.get_ok (safe_make_eq a (make_true ()))) in
  let proof =
    with_arbitrary_term a cases_tac
    >> assumption_tac >> with_first assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    A = T
    ========================================
    A = T

    Proof Complete!
    with fuel: 10
    |}]

let%expect_test "cases_tac preserves assumptions" =
  (* {P} ⊢ ∀b. P — case split on b, P should be available in both subgoals *)
  let p = make_var "P" bool_ty in
  let b = make_var "b" bool_ty in
  let goal = ([ p ], make_forall b p) in
  let proof =
    cases_tac >> with_first assumption_tac >> with_first assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    P
    ========================================
    ∀b. P

    Proof Complete!
    with fuel: 10
    |}]

let%expect_test "spec_asm_tac basic" =
  (* ∀x. P x as assumption, goal is P a *)
  let nat_ty = Kernel.TyCon ("nat", []) in
  let x = make_var "x" nat_ty in
  let a = make_var "a" nat_ty in
  let p_x = App (make_var "P" (make_fun_ty nat_ty bool_ty), x) in
  let p_a = App (make_var "P" (make_fun_ty nat_ty bool_ty), a) in
  let forall_px = make_forall x p_x in
  let goal = ([ forall_px ], p_a) in
  let proof = spec_asm_tac a >> with_first assumption_tac in
  run_proof goal proof;
  [%expect
    {|
    ∀x. P x
    ========================================
    P a

    Proof Complete!
    with fuel: 4
    |}]

let%expect_test "sym_asm_tac basic" =
  let nat_ty = Kernel.TyCon ("nat", []) in
  let a = make_var "a" nat_ty in
  let b = make_var "b" nat_ty in
  let a_eq_b = safe_make_eq a b |> Result.get_ok in
  let b_eq_a = safe_make_eq b a |> Result.get_ok in
  let goal = ([ a_eq_b ], b_eq_a) in
  let proof = sym_asm_tac >> with_first assumption_tac in
  run_proof goal proof;
  [%expect
    {|
    a = b
    ========================================
    b = a

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "eq_true_asm_tac" =
  let p = make_var "P" bool_ty in
  let p_eq_t = Result.get_ok (safe_make_eq p (make_true ())) in
  let goal = ([ p ], p_eq_t) in
  let proof = eq_true_asm_tac >> assumption_tac in
  run_proof goal proof;
  [%expect
    {|
    P
    ========================================
    P = T

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "destruct_tac" =
  let open Nats in
  let n = make_var "n" nat_ty in
  let p = make_var "P" (TyCon ("fun", [ nat_ty; bool_ty ])) in
  let pn = Kernel.make_app p n |> Result.get_ok in
  let goal = ([ pn ], pn) in
  let proof =
    with_arbitrary_term n induct_tac
    >> intros_tac >> assumption_tac >> intros_tac >> assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    P n
    ========================================
    P n

    Proof Complete!
    with fuel: 27
    |}]
