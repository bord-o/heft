open Heft
open Kernel
open Derived
open Tactic
open Auto
open Nats

let%expect_test "basic" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = make_goal ~asms:[ ("ha", a); ("hb", b) ] (make_conj a b) in
  let proof = conj >> assumption >> assumption in
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
  run_proof goal refl;
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
  let proof = intro >> assumption in
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
  let goal = make_goal ~asms:[ ("ha", a) ] (make_disj a b) in
  let proof = left >> assumption in
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
  let goal = make_goal ~asms:[ ("ha", a); ("hb", b) ] (make_disj a b) in
  let proof = right >> assumption in
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
  let goal =
    make_goal ~asms:[ ("himp", imp_cab); ("himp2", imp_ab); ("ha", a) ] b
  in
  let proof = with_nth_choice 1 (with_assumptions apply) >> assumption in
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

let%expect_test "new apply" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let imp_cab = make_imp c (make_imp a b) in
  let imp_ab = make_imp a b in
  let goal =
    make_goal ~asms:[ ("himp", imp_cab); ("himp2", imp_ab); ("ha", a) ] b
  in
  let proof = with_assumptions (with_nth_choice 1 apply) >> assumption in
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
  let goal =
    make_goal
      ~asms:[ ("ha", a); ("hb", b); ("hc", c) ]
      (make_conj (make_conj a b) c)
  in
  let proof = conj >> conj >> assumption >> assumption >> assumption in
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
  let goal = make_goal ~asms:[ ("hfalse", make_false ()) ] a in
  let proof = ccontr >> assumption in
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
  let goal = make_goal ~asms:[ ("hfalse", make_false ()) ] a in
  let proof = false_elim >> assumption in
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
  let proof = gen >> intro >> assumption in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    ∀x. A ==> A

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "basic10" =
  let a = make_var "A" bool_ty in
  let x = make_var "x" nat_ty in
  let goal = ([], make_forall x (make_imp a a)) in
  let proof = induct >> intro >> assumption >> gen >> intro >> assumption in
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
    make_goal
      ~asms:[ ("hf", f) ]
      (make_disj (make_disj e (make_disj (make_disj c d) (make_disj a b))) f)
  in
  let proof = with_best_first (try_ or_ >> assumption) in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      or >>
      right >>
      assumption
    F
    ========================================
    E ∨ C ∨ D ∨ A ∨ B ∨ F

    Proof Complete!
    with fuel: 13
    |}]

let%expect_test "dfs_conj_backtrack" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  (* Goal: (A ∨ B) ∧ C, only have [B; C] *)
  let left = make_disj a b in
  let goal = make_goal ~asms:[ ("hb", b); ("hc", c) ] (make_conj left c) in
  let proof = with_best_first (try_ conj >> try_ or_ >> assumption) in
  run_proof goal proof;

  [%expect
    {|
    Proof:
      conj >>
      assumption >>
      or >>
      right >>
      assumption
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
      (pick [ intro; elim_conj_asm; with_assumptions apply; assumption ])
  in
  run_proof goal proof;

  [%expect
    {|
    Proof:
      intro >>
      intro >>
      elim_conj_asm >>
      apply >>
      apply >>
      assumption
    ========================================
    (P ==> Q) ∧ (Q ==> R) ==> P ==> R

    Proof Complete!
    with fuel: 54
    |}]

let%expect_test "complete_prop_automation" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let p_imp_q = make_imp p q in
  let q_imp_r = make_imp q r in
  let p_imp_r = make_imp p r in
  let goal = ([], make_imp (make_conj p_imp_q q_imp_r) p_imp_r) in
  let proof = with_best_first ctauto in
  run_proof goal proof;

  [%expect
    {|
    Proof:
      intro >>
      intro >>
      elim_conj_asm >>
      apply >>
      apply >>
      assumption
    ========================================
    (P ==> Q) ∧ (Q ==> R) ==> P ==> R

    Proof Complete!
    with fuel: 290
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
      (pick [ intro; elim_disj_asm; with_assumptions apply; assumption ])
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      intro >>
      elim_disj_asm >>
      intro >>
      apply >>
      assumption >>
      intro >>
      apply >>
      assumption
    ========================================
    P ∨ Q ==> (P ==> R) ==> (Q ==> R) ==> R

    Proof Complete!
    with fuel: 178
    |}]

let%expect_test "pauto_disj_elimination" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let p_or_q = make_disj p q in
  let p_imp_r = make_imp p r in
  let q_imp_r = make_imp q r in
  let goal = ([], make_imp p_or_q (make_imp p_imp_r (make_imp q_imp_r r))) in
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      intro >>
      elim_disj_asm >>
      intro >>
      apply >>
      assumption >>
      intro >>
      apply_asm >>
      assumption
    ========================================
    P ∨ Q ==> (P ==> R) ==> (Q ==> R) ==> R

    Proof Complete!
    with fuel: 509
    |}]

let%expect_test "false_elim_test" =
  (* ⊥ in assumptions, prove anything *)
  let p = make_var "P" bool_ty in
  let false_tm = make_false () in
  let goal = ([], make_imp false_tm p) in
  let proof = intro >> false_elim in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    F ==> P

    Proof Complete!
    with fuel: 2
    |}]

let%expect_test "neg_elim_test" =
  (* P and ¬P in assumptions, prove anything *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp p (make_imp (make_neg p) q)) in
  let proof = with_repeat intro >> neg_elim in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    P ==> ¬P ==> Q

    Proof Complete!
    with fuel: 6
    |}]

let%expect_test "neg_intro_test" =
  (* Goal is ¬P, reduce to [P] ⊢ ⊥ *)
  (* Prove: P ⟹ ¬¬P *)
  let p = make_var "P" bool_ty in
  let goal = ([], make_imp p (make_neg (make_neg p))) in
  let proof = intro >> neg_intro >> neg_elim in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    P ==> ¬¬P

    Proof Complete!
    with fuel: 8
    |}]

let%expect_test "ccontr_test" =
  (* Classical: assume ¬P, derive ⊥, conclude P *)
  (* Prove: ¬¬P ⟹ P (requires classical logic) *)
  let p = make_var "P" bool_ty in
  let goal = ([], make_imp (make_neg (make_neg p)) p) in
  let proof = intro >> ccontr >> with_best_first neg_elim in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      neg_elim
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
    intro >> intro >> neg_intro
    >> with_first (with_assumptions (with_first_term apply_asm))
    >> neg_elim
  in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    (P ==> Q) ==> ¬Q ==> ¬P

    Proof Complete!
    with fuel: 14
    |}]

let%expect_test "excluded_middle_pauto" =
  (* P ∨ ¬P (requires classical logic) *)
  let p = make_var "P" bool_ty in
  let goal = ([], make_disj p (make_neg p)) in
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      ccontr >>
      contradict_asm >>
      right >>
      neg_intro >>
      contradict_asm >>
      left >>
      assumption
    ========================================
    P ∨ ¬P

    Proof Complete!
    with fuel: 681
    |}]

let%expect_test "contraposition" =
  (* (P ⟹ Q) ⟹ (¬Q ⟹ ¬P) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    ([], make_imp (make_imp p q) (make_imp (make_neg q) (make_neg p)))
  in
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      intro >>
      neg_intro >>
      contradict_asm >>
      apply_asm >>
      assumption
    ========================================
    (P ==> Q) ==> ¬Q ==> ¬P

    Proof Complete!
    with fuel: 127
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
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      elim_conj_asm >>
      elim_disj_asm >>
      right >>
      conj >>
      assumption >>
      assumption >>
      left >>
      conj >>
      assumption >>
      assumption
    ========================================
    P ∧ Q ∨ R ==> P ∧ Q ∨ P ∧ R

    Proof Complete!
    with fuel: 1266
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
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      elim_disj_asm >>
      elim_conj_asm >>
      conj >>
      right >>
      assumption >>
      right >>
      assumption >>
      conj >>
      left >>
      assumption >>
      left >>
      assumption
    ========================================
    P ∨ Q ∧ R ==> P ∨ Q ∧ P ∨ R

    Proof Complete!
    with fuel: 950
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
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      ccontr >>
      contradict_asm >>
      intro >>
      left >>
      neg_intro >>
      contradict_asm >>
      intro >>
      right >>
      neg_intro >>
      contradict_asm >>
      conj >>
      assumption >>
      assumption
    ========================================
    ¬P ∧ Q ==> ¬P ∨ ¬Q

    Proof Complete!
    with fuel: 2836
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
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      conj >>
      neg_intro >>
      contradict_asm >>
      right >>
      assumption >>
      neg_intro >>
      contradict_asm >>
      left >>
      assumption
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q

    Proof Complete!
    with fuel: 389
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
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      elim_conj_asm >>
      neg_intro >>
      elim_disj_asm >>
      neg_elim >>
      neg_elim
    ========================================
    ¬P ∧ ¬Q ==> ¬P ∨ Q

    Proof Complete!
    with fuel: 129
    |}]

let%expect_test "implication_as_disjunction" =
  (* (P ⟹ Q) ⟹ ¬P ∨ Q - requires classical *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_imp p q) (make_disj (make_neg p) q)) in
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      ccontr >>
      contradict_asm >>
      left >>
      neg_intro >>
      apply_asm >>
      contradict_asm >>
      right >>
      assumption
    ========================================
    (P ==> Q) ==> ¬P ∨ Q

    Proof Complete!
    with fuel: 1149
    |}]

let%expect_test "disjunction_as_implication" =
  (* ¬P ∨ Q ⟹ (P ⟹ Q) - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_disj (make_neg p) q) (make_imp p q)) in
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      elim_disj_asm >>
      intro >>
      assumption >>
      intro >>
      neg_elim
    ========================================
    ¬P ∨ Q ==> P ==> Q

    Proof Complete!
    with fuel: 110
    |}]

let%expect_test "triple_negation" =
  (* ¬¬¬P ⟹ ¬P - intuitionistic *)
  let p = make_var "P" bool_ty in
  let goal = ([], make_imp (make_neg (make_neg (make_neg p))) (make_neg p)) in
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      neg_intro >>
      contradict_asm >>
      neg_intro >>
      neg_elim
    ========================================
    ¬¬¬P ==> ¬P

    Proof Complete!
    with fuel: 105
    |}]

let%expect_test "explosion" =
  (* P ⟹ ¬P ⟹ Q *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp p (make_imp (make_neg p) q)) in
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      intro >>
      neg_elim
    ========================================
    P ==> ¬P ==> Q

    Proof Complete!
    with fuel: 31
    |}]

let%expect_test "complex_nested" =
  (* ((P ⟹ Q) ⟹ P) ⟹ P - Peirce's law, requires classical *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_imp (make_imp p q) p) p) in
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      ccontr >>
      contradict_asm >>
      intro >>
      ccontr >>
      contradict_asm >>
      apply >>
      intro >>
      neg_elim
    ========================================
    ((P ==> Q) ==> P) ==> P

    Proof Complete!
    with fuel: 1142
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
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      elim_conj_asm >>
      elim_disj_asm >>
      right >>
      elim_disj_asm >>
      right >>
      right >>
      conj >>
      assumption >>
      assumption >>
      right >>
      left >>
      conj >>
      assumption >>
      assumption >>
      elim_disj_asm >>
      right >>
      left >>
      conj >>
      assumption >>
      assumption >>
      left >>
      conj >>
      assumption >>
      assumption
    ========================================
    A ∨ B ∧ C ∨ D ==> A ∧ C ∨ A ∧ D ∨ B ∧ C ∨ B ∧ D

    Proof Complete!
    with fuel: 6610
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
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      intro >>
      intro >>
      intro >>
      apply >>
      apply_asm >>
      apply >>
      assumption
    ========================================
    (A ==> B) ==> (B ==> C) ==> (C ==> D) ==> A ==> D

    Proof Complete!
    with fuel: 232
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
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      intro >>
      intro >>
      neg_intro >>
      contradict_asm >>
      apply_asm >>
      apply >>
      assumption
    ========================================
    (A ==> B) ==> (B ==> C) ==> ¬C ==> ¬A

    Proof Complete!
    with fuel: 202
    |}]

let%expect_test "absorption_law" =
  (* P ∧ (P ∨ Q) ⟺ P - just one direction here *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_conj p (make_disj p q)) p) in
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      elim_conj_asm >>
      assumption
    ========================================
    P ∧ P ∨ Q ==> P

    Proof Complete!
    with fuel: 21
    |}]

let%expect_test "absorption_law_converse" =
  (* P ⟹ P ∧ (P ∨ Q) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp p (make_conj p (make_disj p q))) in
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      conj >>
      left >>
      assumption >>
      assumption
    ========================================
    P ==> P ∧ P ∨ Q

    Proof Complete!
    with fuel: 119
    |}]

let%expect_test "not_false_is_true" =
  (* ¬⊥ *)
  let goal = ([], make_neg (make_false ())) in
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      neg_intro >>
      false_elim
    ========================================
    ¬F

    Proof Complete!
    with fuel: 19
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
  (* let proof = with_best_first ctauto in *)
  let proof =
    intro >> conj >> neg_intro >> contradict_asm >> left >> assumption
    >> neg_intro >> contradict_asm >> right >> assumption
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
  let proof = with_best_first ctauto in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      intro >>
      conj >>
      neg_intro >>
      contradict_asm >>
      right >>
      assumption >>
      neg_intro >>
      contradict_asm >>
      left >>
      assumption
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q

    Proof Complete!
    with fuel: 389
    |}]

let%expect_test "rewrite_basic" =
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
  let proof = with_rules [ eq_thm ] rewrite >> sorry in
  run_proof goal proof;

  [%expect
    {|
    ========================================
    add Zero Two = add One One

    Proof Complete!
    with fuel: 6
    |}]

let%expect_test "rewrite_basic" =
  let x = make_var "x" nat_ty in
  let zero_plus_x = make_plus zero x |> Result.get_ok in
  let goal = ([], make_forall x (Result.get_ok (safe_make_eq zero_plus_x x))) in
  let proof = gen >> simp in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∀x. plus Zero x = x

    Proof Complete!
    with fuel: 22
    |}]

let%expect_test "basic4" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = make_goal ~asms:[ ("ha", a) ] (make_disj a b) in
  let name, _ = cost_of_tactic left goal in
  print_endline name;
  [%expect {| left |}]

let%expect_test "exists_bool" =
  let p = make_var "P" bool_ty in
  let goal = make_goal ~asms:[ ("htrue", make_true ()) ] (make_exists p p) in
  (* ∃P. P *)
  run_proof goal (with_term (make_true ()) exists >> assumption);
  [%expect
    {|
    ========================================
    ∃P. P

    Proof Complete!
    with fuel: 9
    |}]

let%expect_test "exists_refl" =
  let n = Var ("n", nat_ty) in
  let eq_nn = Result.get_ok (safe_make_eq n n) in
  let goal = ([], make_exists n eq_nn) in
  (* ∃n. n = n *)
  run_proof goal (with_term zero exists @>> refl);
  [%expect
    {|
    ========================================
    ∃n. n = n

    Proof Complete!
    with fuel: 9
    |}]

let%expect_test "exists_nested" =
  let m = Var ("m", nat_ty) in
  let n = Var ("n", nat_ty) in
  let eq_mn = Result.get_ok (safe_make_eq m n) in
  let goal = ([], make_exists m (make_exists n eq_mn)) in
  (* ∃m. ∃n. m = n *)
  run_proof goal (with_term zero exists >> with_term zero exists @>> refl);
  [%expect
    {|
    ========================================
    ∃m. ∃n. m = n

    Proof Complete!
    with fuel: 17
    |}]

let%expect_test "trans tac" =
  let m = Var ("m", nat_ty) in
  let n = Var ("n", nat_ty) in
  let o = Var ("o", nat_ty) in
  let eq_mo = Result.get_ok (safe_make_eq m o) in
  let eq_on = Result.get_ok (safe_make_eq o n) in
  let eq_mn = Result.get_ok (safe_make_eq m n) in
  let goal = make_goal ~asms:[ ("heq", eq_mo); ("heq2", eq_on) ] eq_mn in

  run_proof goal (with_term o trans >> assumption >> assumption);
  [%expect
    {|
    m = o
    o = n
    ========================================
    m = n

    Proof Complete!
    with fuel: 3
    |}]

let make_goal' (unnamed, conc) =
  let asms = unnamed |> List.map (fun p -> ("", p)) in
  make_goal ~asms conc

let%expect_test "have_basic" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let pq = make_imp p q in
  let qr = make_imp q r in
  let goal = make_goal' ([ p; pq; qr ], r) in
  let proof =
    with_term q have
    >> with_first (with_assumptions (with_first_term apply_asm))
    >> assumption
    >> with_first (with_assumptions (with_first_term apply_asm))
    >> assumption
  in
  run_proof ~notrace:false goal proof;

  [%expect
    {|
    no choices available
    Found matching assumption
    Assumption succeeded
    assumption
    apply_asm
    no choices available
    no choices available
    no choices available
    Found matching assumption
    Assumption succeeded
    assumption
    apply_asm
    have
    P
    P ==> Q
    Q ==> R
    ========================================
    R

    Proof Complete!
    with fuel: 17
    |}]

(* ---- cases tests ---- *)

let%expect_test "cases bool forall refl" =
  (* ∀b. b = b — trivial, both cases solved by refl *)
  let b = make_var "b" bool_ty in
  let goal = ([], make_forall b (Result.get_ok (safe_make_eq b b))) in
  let proof = gen >> with_term b destruct >> refl >> with_first refl in
  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∀b. b = b

    Proof Complete!
    with fuel: 8
    |}]

let%expect_test "cases arbitrary bool expr" =
  (* Given A ∨ B, case split on A to add A=T or A=F as assumption *)
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let a_eq_t = Result.get_ok (safe_make_eq a (make_true ())) in
  let goal =
    make_goal' ([ a_eq_t; b ], Result.get_ok (safe_make_eq a (make_true ())))
  in
  let proof = with_term a destruct >> assumption >> assumption in
  run_proof goal proof;
  [%expect
    {|
    A = T
    ========================================
    A = T

    Proof Complete!
    with fuel: 7
    |}]

let%expect_test "cases preserves assumptions" =
  (* {P} ⊢ ∀b. P — case split on b, P should be available in both subgoals *)
  let p = make_var "P" bool_ty in
  let b = make_var "b" bool_ty in
  let goal = make_goal' ([ p ], make_forall b p) in
  let proof =
    gen >> with_term b destruct >> elim_disj_asm >> assumption >> assumption
  in
  run_proof goal proof;
  [%expect
    {|
    P
    ========================================
    ∀b. P

    Proof Complete!
    with fuel: 14
    |}]

let%expect_test "spec_asm basic" =
  (* ∀x. P x as assumption, goal is P a *)
  let nat_ty = Kernel.TyCon ("nat", []) in
  let x = make_var "x" nat_ty in
  let a = make_var "a" nat_ty in
  let p_x = App (make_var "P" (make_fun_ty nat_ty bool_ty), x) in
  let p_a = App (make_var "P" (make_fun_ty nat_ty bool_ty), a) in
  let forall_px = make_forall x p_x in
  let goal = make_goal' ([ forall_px ], p_a) in
  let proof = spec_asm a >> assumption in
  run_proof goal proof;
  [%expect
    {|
    ∀x. P x
    ========================================
    P a

    Proof Complete!
    with fuel: 4
    |}]

let%expect_test "sym_asm basic" =
  let nat_ty = Kernel.TyCon ("nat", []) in
  let a = make_var "a" nat_ty in
  let b = make_var "b" nat_ty in
  let a_eq_b = safe_make_eq a b |> Result.get_ok in
  let b_eq_a = safe_make_eq b a |> Result.get_ok in
  let goal = make_goal' ([ a_eq_b ], b_eq_a) in
  let proof = sym_asm >> assumption in
  run_proof goal proof;
  [%expect
    {|
    a = b
    ========================================
    b = a

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "eq_true_asm" =
  let p = make_var "P" bool_ty in
  let p_eq_t = Result.get_ok (safe_make_eq p (make_true ())) in
  let goal = make_goal' ([ p ], p_eq_t) in
  let proof = eq_true_asm >> assumption in
  run_proof goal proof;
  [%expect
    {|
    P
    ========================================
    P = T

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "destruct" =
  let n = make_var "n" nat_ty in
  let p = make_var "P" (TyCon ("fun", [ nat_ty; bool_ty ])) in
  let pn = Kernel.make_app p n |> Result.get_ok in
  let goal = make_goal' ([ pn ], pn) in
  let proof =
    with_term n induct >> intros >> assumption >> intros >> assumption
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

(* ===== apply tests ===== *)

let%expect_test "apply direct match" =
  let x = make_var "x" nat_ty in
  let thm = Result.get_ok (Derived.gen x (Result.get_ok (Kernel.refl x))) in
  let three = nat_of_int 3 in
  let goal = make_goal (Result.get_ok (safe_make_eq three three)) in
  run_proof goal (with_rules [ thm ] apply);
  [%expect
    {|
    ========================================
    Suc (Suc (Suc Zero)) = Suc (Suc (Suc Zero))

    Proof Complete!
    with fuel: 5
    |}]

let%expect_test "apply single premise" =
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let x_eq_y = Result.get_ok (safe_make_eq x y) in
  let suc_x_eq_suc_y =
    Result.get_ok (safe_make_eq (App (suc, x)) (App (suc, y)))
  in
  let thm_term =
    make_forall x (make_forall y (make_imp x_eq_y suc_x_eq_suc_y))
  in
  let thm = Result.get_ok (new_axiom thm_term) in
  let suc_zero = App (suc, zero) in
  let goal = make_goal (Result.get_ok (safe_make_eq suc_zero suc_zero)) in
  run_proof goal (with_rules [ thm ] apply >> refl);
  [%expect
    {|
    ========================================
    Suc Zero = Suc Zero

    Proof Complete!
    with fuel: 6
    |}]

let%expect_test "apply multiple premises isolated" =
  let nat_ty = nat_ty in
  let a = make_var "a" nat_ty in
  let b = make_var "b" nat_ty in
  let p = make_var "P" (make_fun_ty nat_ty bool_ty) in
  let q = make_var "Q" (make_fun_ty nat_ty bool_ty) in
  let r = make_var "R" (make_fun_ty nat_ty (make_fun_ty nat_ty bool_ty)) in
  let pa = Result.get_ok (make_app p a) in
  let qb = Result.get_ok (make_app q b) in
  let rab = Result.get_ok (make_app (Result.get_ok (make_app r a)) b) in
  let body = make_imp pa (make_imp qb rab) in
  let thm_term = make_forall a (make_forall b body) in
  let thm = Result.get_ok (new_axiom thm_term) in
  let zero = zero in
  let p0 = Result.get_ok (make_app p zero) in
  let q0 = Result.get_ok (make_app q zero) in
  let r00 = Result.get_ok (make_app (Result.get_ok (make_app r zero)) zero) in
  let goal = make_goal' ([ p0; q0 ], r00) in
  run_proof goal (with_rules [ thm ] apply >> assumption >> assumption);
  [%expect
    {|
    P Zero
    Q Zero
    ========================================
    R Zero Zero

    Proof Complete!
    with fuel: 7
    |}]

let%expect_test "apply undetermined variable" =
  let nat_ty = nat_ty in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let p = make_var "P" (make_fun_ty nat_ty bool_ty) in
  let q = make_var "Q" (make_fun_ty nat_ty bool_ty) in
  let px = Result.get_ok (make_app p x) in
  let qy = Result.get_ok (make_app q y) in
  let body = make_imp px qy in
  let thm_term = make_forall x (make_forall y body) in
  let thm = Result.get_ok (new_axiom thm_term) in
  let three = nat_of_int 3 in
  let q3 = Result.get_ok (make_app q three) in
  let goal = make_goal q3 in
  run_proof goal (with_rules [ thm ] apply >> gen >> sorry);
  [%expect
    {|
    ========================================
    Q (Suc (Suc (Suc Zero)))

    Proof Complete!
    with fuel: 7
    |}]

let%expect_test "apply undetermined per premise" =
  let nat_ty = nat_ty in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let z = make_var "z" nat_ty in
  let p = make_var "P" (make_fun_ty nat_ty bool_ty) in
  let q = make_var "Q" (make_fun_ty nat_ty bool_ty) in
  let r = make_var "R" (make_fun_ty nat_ty bool_ty) in
  let px = Result.get_ok (make_app p x) in
  let qy = Result.get_ok (make_app q y) in
  let rz = Result.get_ok (make_app r z) in
  let body = make_imp px (make_imp qy rz) in
  let thm_term = make_forall x (make_forall y (make_forall z body)) in
  let thm = Result.get_ok (new_axiom thm_term) in
  let five = nat_of_int 5 in
  let r5 = Result.get_ok (make_app r five) in
  let goal = make_goal r5 in
  run_proof goal
    (with_rules [ thm ] apply >> gen >> sorry >> with_first gen
   >> with_first sorry);
  [%expect
    {|
    ========================================
    R (Suc (Suc (Suc (Suc (Suc Zero)))))

    Proof Complete!
    with fuel: 9
    |}]

let%expect_test "apply implication premise intact" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let ab = make_imp a b in
  let thm = Result.get_ok (new_axiom (make_imp ab c)) in
  let goal = make_goal' ([ ab ], c) in
  run_proof goal (with_rules [ thm ] apply >> assumption);
  [%expect
    {|
    A ==> B
    ========================================
    C

    Proof Complete!
    with fuel: 6
    |}]

let%expect_test "apply no premises" =
  let t = make_true () in
  let thm = Derived.truth in
  let goal = make_goal t in
  run_proof goal (with_rules [ thm ] apply);
  [%expect
    {|
    ========================================
    T

    Proof Complete!
    with fuel: 5
    |}]

let%expect_test "apply match failure" =
  let thm = Derived.truth in
  let goal = make_goal (make_false ()) in
  run_proof goal (with_rules [ thm ] apply);
  [%expect {| F |}]

let%expect_test "apply polymorphic no premises" =
  (* ∀(x:'a). x = x applied to T = T — type 'a instantiated to bool *)
  let a = TyVar "a" in
  let x = make_var "x" a in
  let thm = Result.get_ok (Derived.gen x (Result.get_ok (Kernel.refl x))) in
  let goal =
    make_goal (Result.get_ok (safe_make_eq (make_true ()) (make_true ())))
  in
  run_proof goal (with_rules [ thm ] apply);
  [%expect
    {|
    ========================================
    T = T

    Proof Complete!
    with fuel: 5
    |}]

let%expect_test "apply polymorphic with premise" =
  (* ∀(x:'a)(y:'a). x = y ==> y = x applied to goal Zero = Suc Zero
     type 'a instantiated to nat, subgoal: Suc Zero = Zero *)
  let a = TyVar "a" in
  let x = make_var "x" a in
  let y = make_var "y" a in
  let x_eq_y = Result.get_ok (safe_make_eq x y) in
  let y_eq_x = Result.get_ok (safe_make_eq y x) in
  let thm_term = make_forall x (make_forall y (make_imp x_eq_y y_eq_x)) in
  let thm = Result.get_ok (new_axiom thm_term) in
  let zero = zero in
  let suc_zero = App (suc, zero) in
  let goal_term = Result.get_ok (safe_make_eq zero suc_zero) in
  let suc_zero_eq_zero = Result.get_ok (safe_make_eq suc_zero zero) in
  let goal = make_goal' ([ suc_zero_eq_zero ], goal_term) in
  run_proof goal (with_rules [ thm ] apply >> assumption);
  [%expect
    {|
    Suc Zero = Zero
    ========================================
    Zero = Suc Zero

    Proof Complete!
    with fuel: 6
    |}]

let%expect_test "apply polymorphic to nat" =
  (* ∀(x:'a). x = x applied to Zero = Zero — type 'a instantiated to nat *)
  let a = TyVar "a" in
  let x = make_var "x" a in
  let thm = Result.get_ok (Derived.gen x (Result.get_ok (Kernel.refl x))) in
  let goal = make_goal (Result.get_ok (safe_make_eq zero zero)) in
  run_proof goal (with_rules [ thm ] apply);
  [%expect
    {|
    ========================================
    Zero = Zero

    Proof Complete!
    with fuel: 5
    |}]

let%expect_test "apply polymorphic undetermined" =
  (* ∀(x:'a)(y:'a). P x ==> Q y where P : 'a -> bool, Q : 'a -> bool
     Goal: Q Zero — 'a instantiated to nat, y=Zero determined, x undetermined
     Subgoal should be ∀x. P x *)
  let a = TyVar "a" in
  let x = make_var "x" a in
  let y = make_var "y" a in
  let p = make_var "P" (make_fun_ty a bool_ty) in
  let q = make_var "Q" (make_fun_ty a bool_ty) in
  let px = Result.get_ok (make_app p x) in
  let qy = Result.get_ok (make_app q y) in
  let body = make_imp px qy in
  let thm_term = make_forall x (make_forall y body) in
  let thm = Result.get_ok (new_axiom thm_term) in
  let q_nat = make_var "Q" (make_fun_ty nat_ty bool_ty) in
  let q_zero = Result.get_ok (make_app q_nat zero) in
  let goal = make_goal q_zero in
  run_proof goal (with_rules [ thm ] apply >> gen >> sorry);
  [%expect
    {|
    ========================================
    Q Zero

    Proof Complete!
    with fuel: 7
    |}]

let%expect_test "apply polymorphic multiple type vars" =
  (* ∀(x:'a)(y:'b). f x y ==> g x y where f : 'a -> 'b -> bool, g : 'a -> 'b -> bool
     Goal: g Zero T — 'a=nat, 'b=bool, x=Zero, y=T all determined
     Subgoal: f Zero T *)
  let a = TyVar "a" in
  let b = TyVar "b" in
  let x = make_var "x" a in
  let y = make_var "y" b in
  let f = make_var "f" (make_fun_ty a (make_fun_ty b bool_ty)) in
  let g = make_var "g" (make_fun_ty a (make_fun_ty b bool_ty)) in
  let fxy = Result.get_ok (make_app (Result.get_ok (make_app f x)) y) in
  let gxy = Result.get_ok (make_app (Result.get_ok (make_app g x)) y) in
  let body = make_imp fxy gxy in
  let thm_term = make_forall x (make_forall y body) in
  let thm = Result.get_ok (new_axiom thm_term) in
  let nat_ty = nat_ty in
  let f_concrete =
    make_var "f" (make_fun_ty nat_ty (make_fun_ty bool_ty bool_ty))
  in
  let g_concrete =
    make_var "g" (make_fun_ty nat_ty (make_fun_ty bool_ty bool_ty))
  in
  let g_zero_t =
    Result.get_ok
      (make_app (Result.get_ok (make_app g_concrete zero)) (make_true ()))
  in
  let f_zero_t =
    Result.get_ok
      (make_app (Result.get_ok (make_app f_concrete zero)) (make_true ()))
  in
  let goal = make_goal' ([ f_zero_t ], g_zero_t) in
  run_proof goal (with_rules [ thm ] apply >> assumption);
  [%expect
    {|
    f Zero T
    ========================================
    g Zero T

    Proof Complete!
    with fuel: 6
    |}]

(* ===== apply_asm tests ===== *)

let%expect_test "apply_asm simple mp" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let pq = make_imp p q in
  let thm = Result.get_ok (new_axiom pq) in
  let goal = make_goal' ([ p; pq ], q) in
  run_proof goal (with_rules [ thm ] apply_asm >> assumption);
  [%expect
    {|
    P
    ========================================
    Q

    Proof Complete!
    with fuel: 6
    |}]

let%expect_test "apply_asm quantified" =
  let nat_ty = nat_ty in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let x_eq_y = Result.get_ok (safe_make_eq x y) in
  let suc_x_eq_suc_y =
    Result.get_ok (safe_make_eq (App (suc, x)) (App (suc, y)))
  in
  let thm_term =
    make_forall x (make_forall y (make_imp x_eq_y suc_x_eq_suc_y))
  in
  let thm = Result.get_ok (new_axiom thm_term) in
  let zero_eq = Result.get_ok (safe_make_eq zero zero) in
  let suc_zero = App (suc, zero) in
  let suc_zero_eq = Result.get_ok (safe_make_eq suc_zero suc_zero) in
  let goal = make_goal' ([ zero_eq ], suc_zero_eq) in
  run_proof goal (with_rules [ thm ] apply_asm >> assumption);
  [%expect
    {|
    Zero = Zero
    ========================================
    Suc Zero = Suc Zero

    Proof Complete!
    with fuel: 6
    |}]

let%expect_test "apply_asm multiple premises" =
  let nat_ty = nat_ty in
  let x = make_var "x" nat_ty in
  let p = make_var "P" (make_fun_ty nat_ty bool_ty) in
  let q = make_var "Q" (make_fun_ty nat_ty bool_ty) in
  let r = make_var "R" (make_fun_ty nat_ty bool_ty) in
  let px = Result.get_ok (make_app p x) in
  let qx = Result.get_ok (make_app q x) in
  let rx = Result.get_ok (make_app r x) in
  let body = make_imp px (make_imp qx rx) in
  let thm_term = make_forall x body in
  let thm = Result.get_ok (new_axiom thm_term) in
  let three = nat_of_int 3 in
  let p3 = Result.get_ok (make_app p three) in
  let q3 = Result.get_ok (make_app q three) in
  let r3 = Result.get_ok (make_app r three) in
  let goal = make_goal' ([ p3; q3 ], r3) in
  run_proof goal
    (with_rules [ thm ] apply_asm
    >> with_assumptions (with_first_term apply_asm)
    >> assumption);
  [%expect
    {|
    P (Suc (Suc (Suc Zero)))
    Q (Suc (Suc (Suc Zero)))
    ========================================
    R (Suc (Suc (Suc Zero)))

    Proof Complete!
    with fuel: 11
    |}]

let%expect_test "apply_asm undetermined in remainder" =
  let nat_ty = nat_ty in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let p = make_var "P" (make_fun_ty nat_ty bool_ty) in
  let q = make_var "Q" (make_fun_ty nat_ty bool_ty) in
  let px = Result.get_ok (make_app p x) in
  let qy = Result.get_ok (make_app q y) in
  let body = make_imp px qy in
  let thm_term = make_forall x (make_forall y body) in
  let thm = Result.get_ok (new_axiom thm_term) in
  let three = nat_of_int 3 in
  let p3 = Result.get_ok (make_app p three) in
  let q_zero = Result.get_ok (make_app q zero) in
  let goal = make_goal' ([ p3 ], q_zero) in
  run_proof goal (with_rules [ thm ] apply_asm >> spec_asm zero >> assumption);
  [%expect
    {|
    P (Suc (Suc (Suc Zero)))
    ========================================
    Q Zero

    Proof Complete!
    with fuel: 9
    |}]

let%expect_test "apply_asm no match" =
  let t = make_true () in
  let f = make_false () in
  let thm = Result.get_ok (new_axiom (make_imp t f)) in
  let goal = make_goal' ([ f ], f) in
  run_proof goal (with_rules [ thm ] apply_asm);
  [%expect
    {|
       F
    ────────────────────────────────────────
    F
    |}]

let%expect_test "apply_asm no premises fails" =
  let a = make_var "A" bool_ty in
  let thm = Result.get_ok (new_axiom a) in
  let goal = make_goal' ([ a ], a) in
  run_proof goal (with_rules [ thm ] apply_asm);
  [%expect
    {|
       A
    ────────────────────────────────────────
    A
    |}]

let%expect_test "apply_asm polymorphic simple" =
  (* ∀(x:'a)(y:'a). x = y ==> y = x with assumption T = F
     type 'a instantiated to bool, new assumption: F = T *)
  let a = TyVar "a" in
  let x = make_var "x" a in
  let y = make_var "y" a in
  let x_eq_y = Result.get_ok (safe_make_eq x y) in
  let y_eq_x = Result.get_ok (safe_make_eq y x) in
  let thm_term = make_forall x (make_forall y (make_imp x_eq_y y_eq_x)) in
  let thm = Result.get_ok (new_axiom thm_term) in
  let t_eq_f = Result.get_ok (safe_make_eq (make_true ()) (make_false ())) in
  let f_eq_t = Result.get_ok (safe_make_eq (make_false ()) (make_true ())) in
  let goal = make_goal' ([ t_eq_f ], f_eq_t) in
  run_proof goal (with_rules [ thm ] apply_asm >> assumption);
  [%expect
    {|
    T = F
    ========================================
    F = T

    Proof Complete!
    with fuel: 6
    |}]

let%expect_test "apply_asm polymorphic to nat" =
  (* ∀(x:'a)(y:'a). x = y ==> y = x with assumption Zero = Suc Zero
     type 'a instantiated to nat, new assumption: Suc Zero = Zero *)
  let a = TyVar "a" in
  let x = make_var "x" a in
  let y = make_var "y" a in
  let x_eq_y = Result.get_ok (safe_make_eq x y) in
  let y_eq_x = Result.get_ok (safe_make_eq y x) in
  let thm_term = make_forall x (make_forall y (make_imp x_eq_y y_eq_x)) in
  let thm = Result.get_ok (new_axiom thm_term) in
  let suc_zero = App (suc, zero) in
  let zero_eq_suc = Result.get_ok (safe_make_eq zero suc_zero) in
  let suc_eq_zero = Result.get_ok (safe_make_eq suc_zero zero) in
  let goal = make_goal' ([ zero_eq_suc ], suc_eq_zero) in
  run_proof goal (with_rules [ thm ] apply_asm >> assumption);
  [%expect
    {|
    Zero = Suc Zero
    ========================================
    Suc Zero = Zero

    Proof Complete!
    with fuel: 6
    |}]

let%expect_test "apply_asm polymorphic undetermined in remainder" =
  (* ∀(x:'a)(y:'a). P x ==> Q y with assumption P Zero
     'a instantiated to nat, x=Zero determined, y undetermined
     New assumption: ∀y. Q y *)
  let a = TyVar "a" in
  let x = make_var "x" a in
  let y = make_var "y" a in
  let p = make_var "P" (make_fun_ty a bool_ty) in
  let q = make_var "Q" (make_fun_ty a bool_ty) in
  let px = Result.get_ok (make_app p x) in
  let qy = Result.get_ok (make_app q y) in
  let body = make_imp px qy in
  let thm_term = make_forall x (make_forall y body) in
  let thm = Result.get_ok (new_axiom thm_term) in
  let nat_ty = nat_ty in
  let p_nat = make_var "P" (make_fun_ty nat_ty bool_ty) in
  let q_nat = make_var "Q" (make_fun_ty nat_ty bool_ty) in
  let p_zero = Result.get_ok (make_app p_nat zero) in
  let q_zero = Result.get_ok (make_app q_nat zero) in
  let goal = make_goal' ([ p_zero ], q_zero) in
  run_proof goal (with_rules [ thm ] apply_asm >> spec_asm zero >> assumption);
  [%expect
    {|
    P Zero
    ========================================
    Q Zero

    Proof Complete!
    with fuel: 9
    |}]

let%expect_test "apply_asm polymorphic multiple type vars" =
  (* ∀(x:'a)(y:'b). f x y ==> g x y with assumption f Zero T
     'a=nat, 'b=bool determined. New assumption: g Zero T *)
  let a = TyVar "a" in
  let b = TyVar "b" in
  let x = make_var "x" a in
  let y = make_var "y" b in
  let f = make_var "f" (make_fun_ty a (make_fun_ty b bool_ty)) in
  let g = make_var "g" (make_fun_ty a (make_fun_ty b bool_ty)) in
  let fxy = Result.get_ok (make_app (Result.get_ok (make_app f x)) y) in
  let gxy = Result.get_ok (make_app (Result.get_ok (make_app g x)) y) in
  let body = make_imp fxy gxy in
  let thm_term = make_forall x (make_forall y body) in
  let thm = Result.get_ok (new_axiom thm_term) in
  let nat_ty = nat_ty in
  let f_concrete =
    make_var "f" (make_fun_ty nat_ty (make_fun_ty bool_ty bool_ty))
  in
  let g_concrete =
    make_var "g" (make_fun_ty nat_ty (make_fun_ty bool_ty bool_ty))
  in
  let f_zero_t =
    Result.get_ok
      (make_app (Result.get_ok (make_app f_concrete zero)) (make_true ()))
  in
  let g_zero_t =
    Result.get_ok
      (make_app (Result.get_ok (make_app g_concrete zero)) (make_true ()))
  in
  let goal = make_goal' ([ f_zero_t ], g_zero_t) in
  run_proof goal (with_rules [ thm ] apply_asm >> assumption);
  [%expect
    {|
    f Zero T
    ========================================
    g Zero T

    Proof Complete!
    with fuel: 6
    |}]

(* ===== fun_ext tests ===== *)

let%expect_test "fun_ext basic" =
  let nat_ty = nat_ty in
  let n = make_var "n" nat_ty in
  let id_fn = Lam (n, n) in
  let goal = make_goal (Result.get_ok (safe_make_eq id_fn id_fn)) in
  run_proof goal (fun_ext >> refl);
  [%expect
    {|
    ========================================
    (λ_ext_x. _ext_x) = (λ_ext_x. _ext_x)

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "fun_ext two different lambdas" =
  let nat_ty = nat_ty in
  let n = make_var "n" nat_ty in
  let m = make_var "m" nat_ty in
  let f = Lam (n, App (suc, n)) in
  let g = Lam (m, App (suc, m)) in
  let goal = make_goal (Result.get_ok (safe_make_eq f g)) in
  run_proof goal (fun_ext >> refl);
  [%expect
    {|
    ========================================
    (λ_ext_x. Suc _ext_x) = (λ_ext_x. Suc _ext_x)

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "fun_ext non function fails" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = make_goal (Result.get_ok (safe_make_eq a b)) in
  run_proof goal fun_ext;
  [%expect {| A = B |}]

let%expect_test "fun_ext not equality fails" =
  let a = make_var "A" bool_ty in
  let goal = make_goal a in
  run_proof goal fun_ext;
  [%expect {| A |}]

let%expect_test "fun_ext freshens variable" =
  let nat_ty = nat_ty in
  let x = make_var "_ext_x" nat_ty in
  let f = Lam (x, x) in
  let goal = make_goal' ([ x ], Result.get_ok (safe_make_eq f f)) in
  run_proof goal (fun_ext >> refl);
  [%expect
    {|
    ========================================
    (λ_ext_x'. _ext_x') = (λ_ext_x'. _ext_x')

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "fun_ext bool to bool" =
  let p = make_var "p" bool_ty in
  let q = make_var "q" bool_ty in
  let f = Lam (p, p) in
  let g = Lam (q, q) in
  let goal = make_goal (Result.get_ok (safe_make_eq f g)) in
  run_proof goal (fun_ext >> refl);
  [%expect
    {|
    ========================================
    (λ_ext_x. _ext_x) = (λ_ext_x. _ext_x)

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "fun_ext polymorphic" =
  let a = TyVar "a" in
  let x = make_var "x" a in
  let y = make_var "y" a in
  let f = Lam (x, x) in
  let g = Lam (y, y) in
  let goal = make_goal (Result.get_ok (safe_make_eq f g)) in
  run_proof goal (fun_ext >> refl);
  [%expect
    {|
    ========================================
    (λ_ext_x. _ext_x) = (λ_ext_x. _ext_x)

    Proof Complete!
    with fuel: 3
    |}]

(* ===== eq_iff tests ===== *)

let%expect_test "eq_iff basic" =
  let a = make_var "A" bool_ty in
  let goal = make_goal (Result.get_ok (safe_make_eq a a)) in
  run_proof goal (eq_iff >> assumption >> assumption);
  [%expect
    {|
    ========================================
    A = A

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "eq_iff conj comm" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let pq = make_conj p q in
  let qp = make_conj q p in
  let goal = make_goal' ([ p; q ], Result.get_ok (safe_make_eq pq qp)) in
  run_proof goal
    (eq_iff >> elim_conj_asm >> conj >> assumption >> assumption
   >> with_first elim_conj_asm >> with_first conj >> assumption >> assumption);
  [%expect
    {|
    ========================================
    P ∧ Q = Q ∧ P

    Proof Complete!
    with fuel: 9
    |}]

let%expect_test "eq_iff preserves assumptions" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let rp = make_imp r p in
  let rq = make_imp r q in
  let goal = make_goal' ([ r; rp; rq ], Result.get_ok (safe_make_eq p q)) in
  run_proof goal
    (eq_iff
    >> with_first (with_assumptions (with_first_term apply_asm))
    >> assumption
    >> with_first (with_assumptions (with_first_term apply_asm))
    >> assumption);
  [%expect
    {|
    R
    R ==> P
    R ==> Q
    ========================================
    P = Q

    Proof Complete!
    with fuel: 13
    |}]

let%expect_test "eq_iff non bool fails" =
  let nat_ty = nat_ty in
  let a = make_var "a" nat_ty in
  let b = make_var "b" nat_ty in
  let goal = make_goal (Result.get_ok (safe_make_eq a b)) in
  run_proof goal eq_iff;
  [%expect {| a = b |}]

let%expect_test "eq_iff not equality fails" =
  let a = make_var "A" bool_ty in
  let goal = make_goal a in
  run_proof goal eq_iff;
  [%expect {| A |}]

let%expect_test "eq_iff with automation" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let pq = make_conj p q in
  let qp = make_conj q p in
  let goal = make_goal (Result.get_ok (safe_make_eq pq qp)) in
  run_proof goal
    (eq_iff >> with_best_first ctauto >> with_first (with_best_first ctauto));
  [%expect
    {|
    Proof:
      conj >>
      elim_conj_asm >>
      assumption >>
      elim_conj_asm >>
      assumption
    Proof:
      conj >>
      elim_conj_asm >>
      assumption >>
      elim_conj_asm >>
      assumption
    ========================================
    P ∧ Q = Q ∧ P

    Proof Complete!
    with fuel: 67
    |}]

let%expect_test "example" =
  let%thm _test (p : bool) (q : bool) = p ==> (q ==> (p && q))
  and proof =
    begin
      gen >> gen >> intro @: [ "hp" ] >> intro @: [ "hq" ]
    end
  in
  ();

  [%expect
    {|
    hq  q
    hp  p
    ────────────────────────────────────────
    p ∧ q
    |}]

let%expect_test "with_names elim_conj" =
  let%thm _test (p : bool) (q : bool) = (p && q) ==> (q && p)
  and proof =
    begin
      gen >> gen >> intro >> elim_conj_asm @: [ "hp"; "hq" ]
    end
  in
  ();
  [%expect
    {|
    hq  p
    hp  q
    ────────────────────────────────────────
    q ∧ p
    |}]

let%expect_test "with_names partial fallback" =
  let%thm _test (p : bool) (q : bool) (r : bool) =
    p ==> (q ==> (r ==> (p && q && r)))
  and proof =
    begin
      gen >> gen >> gen >> intro @: [ "hp" ] >> intro >> intro
    end
  in
  ();
  [%expect
    {|
    _h1  r
    _h   q
    hp   p
    ────────────────────────────────────────
    p ∧ q ∧ r
    |}]
