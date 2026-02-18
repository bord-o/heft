open Heft
open Derived
open Tactic

(* open Effect *)
open Printing

(* Storage for proven lemmas *)
(* let proven = ref [] *)
(* let lemma s = [ List.assoc s !proven ] *)

let run_proof ?(notrace = true) ?(name = "") goal tac =
  let fuel_count = ref 0 in
  let limit = ref 10_000 in
  let wrapped =
    (if notrace then with_no_trace ~show_proof:true else Fun.id)
    @@ (with_fuel_limit limit) (with_fuel_counter fuel_count tac)
  in
  match prove ~name goal wrapped with
  | Complete thm ->
      print_thm thm;
      print_endline "Proof Complete!";
      Printf.printf "with fuel: %d\n" !fuel_count
  | Incomplete (asms, c) ->
      List.iter print_term asms;
      print_term c;
      print_endline "Proof Incomplete";
      Printf.printf "with fuel: %d\n" !fuel_count

let%expect_test "basic" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = ([ a; b ], make_conj a b) in
  let proof = conj_tac >> assumption_tac >> with_first_success assumption_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    assumption_tac
    conj_tac
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
    refl_tac
    ========================================
    A = A

    Proof Complete!
    with fuel: 0
    |}]

let%expect_test "basic3" =
  let a = make_var "A" bool_ty in
  let goal = ([], make_imp a a) in
  let proof = intro_tac >> assumption_tac in
  run_proof goal proof;

  [%expect
    {|
    assumption_tac
    intro_tac
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
    assumption_tac
    left_tac
    A
    ========================================
    A ∨ B

    Proof Complete!
    with fuel: 4
    |}]

let%expect_test "basic5" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = ([ a; b ], make_disj a b) in
  let proof = right_tac >> with_first_success assumption_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    right_tac
    B
    ========================================
    A ∨ B

    Proof Complete!
    with fuel: 4
    |}]

let%expect_test "basic6" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let imp_ab = make_imp a b in
  let imp_cab = make_imp (make_imp c a) b in
  let goal = ([ imp_cab; imp_ab; a ], b) in
  let proof =
    with_term imp_ab apply_asm_tac >> with_first_success assumption_tac
  in
  run_proof goal proof;

  [%expect
    {|
    assumption_tac
    apply_asm_tac
    A
    A ==> B
    ========================================
    B

    Proof Complete!
    with fuel: 4
    |}]

let%expect_test "deep sequencing with conj" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  let goal = ([ a; b; c ], make_conj (make_conj a b) c) in
  let proof =
    conj_tac >> conj_tac >> assumption_tac
    >> with_first_success assumption_tac
    >> with_first_success assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    assumption_tac
    conj_tac
    assumption_tac
    conj_tac
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
  let proof = ccontr_tac >> with_first_success assumption_tac in
  run_proof goal proof;

  [%expect
    {|
    assumption_tac
    ccontr_tac
    F
    ========================================
    A

    Proof Complete!
    with fuel: 9
    |}]

let%expect_test "basic8" =
  let a = make_var "A" bool_ty in
  let goal = ([ make_false () ], a) in
  let proof = false_elim_tac >> assumption_tac in
  run_proof goal proof;

  [%expect
    {|
    false_elim_tac
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
    assumption_tac
    intro_tac
    gen_tac
    ========================================
    ∀x. A ==> A

    Proof Complete!
    with fuel: 3
    |}]

let%expect_test "basic10" =
  let open Theories.NatTheory in
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
    assumption_tac
    intro_tac
    assumption_tac
    intro_tac
    gen_tac
    induction_tac
    ========================================
    ∀x. A ==> A

    Proof Complete!
    with fuel: 10
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
  let proof = with_dfs (try_ or_tac >> assumption_tac) in
  run_proof ~notrace:false goal proof;
  [%expect
    {|
    assumption doesn't match the goal
    OperationDoesntMatch
    Found matching assumption
    Assumption succeeded
    assumption_tac
    disj_right success
    right_tac
    or_tac
    F
    ========================================
    E ∨ C ∨ D ∨ A ∨ B ∨ F

    Proof Complete!
    with fuel: 17
    |}]

let%expect_test "dfs_conj_backtrack" =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let c = make_var "C" bool_ty in
  (* Goal: (A ∨ B) ∧ C, only have [B; C] *)
  let left = make_disj a b in
  let goal = ([ b; c ], make_conj left c) in
  let proof = with_dfs (try_ conj_tac >> try_ or_tac >> assumption_tac) in
  run_proof goal proof;

  [%expect
    {|
    assumption_tac
    right_tac
    or_tac
    assumption_tac
    conj_tac
    B
    C
    ========================================
    A ∨ B ∧ C

    Proof Complete!
    with fuel: 27
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
    with_dfs
      (pick_tac [ intro_tac; elim_conj_asm_tac; apply_asm_tac; assumption_tac ])
  in
  run_proof goal proof;

  [%expect
    {|
    assumption_tac
    apply_asm_tac
    apply_asm_tac
    elim_conj_asm_tac
    intro_tac
    intro_tac
    ========================================
    (P ==> Q) ∧ (Q ==> R) ==> P ==> R

    Proof Complete!
    with fuel: 20
    |}]

let%expect_test "complete_prop_automation" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let p_imp_q = make_imp p q in
  let q_imp_r = make_imp q r in
  let p_imp_r = make_imp p r in
  let goal = ([], make_imp (make_conj p_imp_q q_imp_r) p_imp_r) in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;

  [%expect
    {|
    assumption_tac
    apply_asm_tac
    apply_asm_tac
    elim_conj_asm_tac
    intro_tac
    intro_tac
    ========================================
    (P ==> Q) ∧ (Q ==> R) ==> P ==> R

    Proof Complete!
    with fuel: 46
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
    with_dfs
      (pick_tac [ intro_tac; elim_disj_asm_tac; apply_asm_tac; assumption_tac ])
  in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    apply_asm_tac
    assumption_tac
    apply_asm_tac
    elim_disj_asm_tac
    intro_tac
    intro_tac
    intro_tac
    ========================================
    P ∨ Q ==> (P ==> R) ==> (Q ==> R) ==> R

    Proof Complete!
    with fuel: 51
    |}]

let%expect_test "pauto_disj_elimination" =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let p_or_q = make_disj p q in
  let p_imp_r = make_imp p r in
  let q_imp_r = make_imp q r in
  let goal = ([], make_imp p_or_q (make_imp p_imp_r (make_imp q_imp_r r))) in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    apply_asm_tac
    assumption_tac
    apply_asm_tac
    elim_disj_asm_tac
    intro_tac
    intro_tac
    intro_tac
    ========================================
    P ∨ Q ==> (P ==> R) ==> (Q ==> R) ==> R

    Proof Complete!
    with fuel: 386
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
    false_elim_tac
    intro_tac
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
    neg_elim_tac
    intro_tac
    intro_tac
    ========================================
    P ==> ¬P ==> Q

    Proof Complete!
    with fuel: 5
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
    neg_elim_tac
    neg_intro_tac
    intro_tac
    ========================================
    P ==> ¬¬P

    Proof Complete!
    with fuel: 5
    |}]

let%expect_test "ccontr_tac_test" =
  (* Classical: assume ¬P, derive ⊥, conclude P *)
  (* Prove: ¬¬P ⟹ P (requires classical logic) *)
  let p = make_var "P" bool_ty in
  let goal = ([], make_imp (make_neg (make_neg p)) p) in
  let proof = intro_tac >> ccontr_tac >> with_dfs neg_elim_tac in
  run_proof goal proof;
  [%expect
    {|
    neg_elim_tac
    ccontr_tac
    intro_tac
    ========================================
    ¬¬P ==> P

    Proof Complete!
    with fuel: 11
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
    neg_elim_tac
    mp_asm_tac
    neg_intro_tac
    intro_tac
    intro_tac
    ========================================
    (P ==> Q) ==> ¬Q ==> ¬P

    Proof Complete!
    with fuel: 9
    |}]

let%expect_test "excluded_middle_pauto" =
  (* P ∨ ¬P (requires classical logic) *)
  let p = make_var "P" bool_ty in
  let goal = ([], make_disj p (make_neg p)) in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    right_tac
    apply_neg_asm_tac
    ccontr_tac
    left_tac
    apply_neg_asm_tac
    ccontr_tac
    ========================================
    P ∨ ¬P

    Proof Complete!
    with fuel: 577
    |}]

let%expect_test "contraposition" =
  (* (P ⟹ Q) ⟹ (¬Q ⟹ ¬P) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal =
    ([], make_imp (make_imp p q) (make_imp (make_neg q) (make_neg p)))
  in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    apply_asm_tac
    apply_neg_asm_tac
    neg_intro_tac
    intro_tac
    intro_tac
    ========================================
    (P ==> Q) ==> ¬Q ==> ¬P

    Proof Complete!
    with fuel: 46
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
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    assumption_tac
    conj_tac
    left_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    conj_tac
    right_tac
    elim_disj_asm_tac
    elim_conj_asm_tac
    intro_tac
    ========================================
    P ∧ Q ∨ R ==> P ∧ Q ∨ P ∧ R

    Proof Complete!
    with fuel: 872
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
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    left_tac
    assumption_tac
    right_tac
    elim_conj_asm_tac
    elim_disj_asm_tac
    assumption_tac
    left_tac
    assumption_tac
    right_tac
    elim_conj_asm_tac
    elim_disj_asm_tac
    conj_tac
    intro_tac
    ========================================
    P ∨ Q ∧ R ==> P ∨ Q ∧ P ∨ R

    Proof Complete!
    with fuel: 380
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
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    neg_elim_tac
    ccontr_tac
    assumption_tac
    neg_elim_tac
    ccontr_tac
    assumption_tac
    neg_elim_tac
    ccontr_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    neg_elim_tac
    ccontr_tac
    neg_elim_tac
    ccontr_tac
    assumption_tac
    neg_elim_tac
    ccontr_tac
    assumption_tac
    assumption_tac
    conj_tac
    apply_neg_asm_tac
    ccontr_tac
    right_tac
    apply_neg_asm_tac
    neg_intro_tac
    right_tac
    apply_neg_asm_tac
    ccontr_tac
    left_tac
    apply_neg_asm_tac
    neg_intro_tac
    left_tac
    apply_neg_asm_tac
    ccontr_tac
    intro_tac
    ========================================
    ¬P ∧ Q ==> ¬P ∨ ¬Q

    Proof Complete!
    with fuel: 5508
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
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    left_tac
    apply_neg_asm_tac
    neg_intro_tac
    assumption_tac
    right_tac
    apply_neg_asm_tac
    ccontr_tac
    left_tac
    apply_neg_asm_tac
    neg_intro_tac
    conj_tac
    intro_tac
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q

    Proof Complete!
    with fuel: 270
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
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    neg_elim_tac
    neg_elim_tac
    elim_disj_asm_tac
    elim_conj_asm_tac
    neg_intro_tac
    intro_tac
    ========================================
    ¬P ∧ ¬Q ==> ¬P ∨ Q

    Proof Complete!
    with fuel: 52
    |}]

let%expect_test "implication_as_disjunction" =
  (* (P ⟹ Q) ⟹ ¬P ∨ Q - requires classical *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_imp p q) (make_disj (make_neg p) q)) in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    right_tac
    apply_neg_asm_tac
    ccontr_tac
    left_tac
    mp_asm_tac
    apply_neg_asm_tac
    neg_intro_tac
    left_tac
    apply_neg_asm_tac
    ccontr_tac
    intro_tac
    ========================================
    (P ==> Q) ==> ¬P ∨ Q

    Proof Complete!
    with fuel: 1096
    |}]

let%expect_test "disjunction_as_implication" =
  (* ¬P ∨ Q ⟹ (P ⟹ Q) - intuitionistic *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_disj (make_neg p) q) (make_imp p q)) in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    neg_elim_tac
    assumption_tac
    elim_disj_asm_tac
    intro_tac
    intro_tac
    ========================================
    ¬P ∨ Q ==> P ==> Q

    Proof Complete!
    with fuel: 30
    |}]

let%expect_test "triple_negation" =
  (* ¬¬¬P ⟹ ¬P - intuitionistic *)
  let p = make_var "P" bool_ty in
  let goal = ([], make_imp (make_neg (make_neg (make_neg p))) (make_neg p)) in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    neg_elim_tac
    neg_intro_tac
    apply_neg_asm_tac
    neg_intro_tac
    intro_tac
    ========================================
    ¬¬¬P ==> ¬P

    Proof Complete!
    with fuel: 44
    |}]

let%expect_test "explosion" =
  (* P ⟹ ¬P ⟹ Q *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp p (make_imp (make_neg p) q)) in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    neg_elim_tac
    intro_tac
    intro_tac
    ========================================
    P ==> ¬P ==> Q

    Proof Complete!
    with fuel: 18
    |}]

let%expect_test "complex_nested" =
  (* ((P ⟹ Q) ⟹ P) ⟹ P - Peirce's law, requires classical *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_imp (make_imp p q) p) p) in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    neg_elim_tac
    intro_tac
    apply_asm_tac
    apply_neg_asm_tac
    ccontr_tac
    intro_tac
    ========================================
    ((P ==> Q) ==> P) ==> P

    Proof Complete!
    with fuel: 499
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
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    assumption_tac
    conj_tac
    left_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    conj_tac
    left_tac
    right_tac
    elim_disj_asm_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    conj_tac
    left_tac
    right_tac
    right_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    assumption_tac
    conj_tac
    right_tac
    right_tac
    right_tac
    elim_disj_asm_tac
    elim_disj_asm_tac
    elim_conj_asm_tac
    intro_tac
    ========================================
    A ∨ B ∧ C ∨ D ==> A ∧ C ∨ A ∧ D ∨ B ∧ C ∨ B ∧ D

    Proof Complete!
    with fuel: 5892
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
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    apply_asm_tac
    apply_asm_tac
    apply_asm_tac
    intro_tac
    intro_tac
    intro_tac
    intro_tac
    ========================================
    (A ==> B) ==> (B ==> C) ==> (C ==> D) ==> A ==> D

    Proof Complete!
    with fuel: 60
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
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    apply_asm_tac
    apply_asm_tac
    apply_neg_asm_tac
    neg_intro_tac
    intro_tac
    intro_tac
    intro_tac
    ========================================
    (A ==> B) ==> (B ==> C) ==> ¬C ==> ¬A

    Proof Complete!
    with fuel: 65
    |}]

let%expect_test "absorption_law" =
  (* P ∧ (P ∨ Q) ⟺ P - just one direction here *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp (make_conj p (make_disj p q)) p) in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    elim_conj_asm_tac
    intro_tac
    ========================================
    P ∧ P ∨ Q ==> P

    Proof Complete!
    with fuel: 10
    |}]

let%expect_test "absorption_law_converse" =
  (* P ⟹ P ∧ (P ∨ Q) *)
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let goal = ([], make_imp p (make_conj p (make_disj p q))) in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    assumption_tac
    left_tac
    conj_tac
    intro_tac
    ========================================
    P ==> P ∧ P ∨ Q

    Proof Complete!
    with fuel: 36
    |}]

let%expect_test "not_false_is_true" =
  (* ¬⊥ *)
  let goal = ([], make_neg (make_false ())) in
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    neg_intro_tac
    ========================================
    ¬F

    Proof Complete!
    with fuel: 5
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
  (* let proof = with_dfs ctauto_tac in *)
  let proof =
    intro_tac >> conj_tac >> neg_intro_tac >> apply_neg_asm_tac >> left_tac
    >> assumption_tac >> neg_intro_tac >> apply_neg_asm_tac >> right_tac
    >> assumption_tac
  in
  run_proof goal proof;
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
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q

    Proof Complete!
    with fuel: 20
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
  let proof = with_dfs ctauto_tac in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    left_tac
    apply_neg_asm_tac
    neg_intro_tac
    assumption_tac
    right_tac
    apply_neg_asm_tac
    ccontr_tac
    left_tac
    apply_neg_asm_tac
    neg_intro_tac
    conj_tac
    intro_tac
    ========================================
    ¬P ∨ Q ==> ¬P ∧ ¬Q

    Proof Complete!
    with fuel: 270
    |}]

(* let%expect_test "bfs demorgans" = *)
(*   (* ¬(P ∨ Q) ⟹ ¬P ∧ ¬Q - intuitionistic *) *)
(*   let p = make_var "P" bool_ty in *)
(*   let q = make_var "Q" bool_ty in *)
(*   let goal = *)
(*     make_imp (make_neg (make_disj p q)) (make_conj (make_neg p) (make_neg q)) *)
(*   in *)
(*   let fuel = ref 0 in *)
(*   let next_tactic = *)
(*     next_tactic_of_list *)
(*       [ *)
(*         with_repeat *)
(*         @@ with_no_trace ~show_proof:true *)
(*         @@ (with_fuel_counter fuel) ctauto_tac; *)
(*       ] *)
(*   in *)
(*   (match prove_bfs_with_trace ([], goal) next_tactic with *)
(*   | t, Complete thm -> *)
(*       List.iter print_endline t; *)
(*       print_endline "Proof Complete!"; *)
(*       Printf.printf "With fuel usage: %d\n" !fuel; *)
(*       Printing.print_thm thm *)
(*   | _t, Incomplete _ -> print_endline "Proof Failed"); *)
(*   [%expect *)
(*     {| *)
(*     intro_tac *)
(*     conj_tac *)
(*     neg_intro_tac *)
(*     apply_neg_asm_tac *)
(*     right_tac *)
(*     assumption_tac *)
(*     neg_intro_tac *)
(*     apply_neg_asm_tac *)
(*     left_tac *)
(*     assumption_tac *)
(*     Proof Complete! *)
(*     With fuel usage: 29526 *)
(*     ======================================== *)
(*     ¬P ∨ Q ==> ¬P ∧ ¬Q *)
(*     |}] *)

(* let%expect_test "another tautology" = *)
(*   let mkvar s = make_var s bool_ty in *)

(*   let a = mkvar "a" in *)
(*   let b = mkvar "b" in *)
(*   (* let c = mkvar "c" in *) *)

(*   let na = make_neg a in *)
(*   let nb = make_neg b in *)

(*   let na_imp_nb = make_imp na nb in *)
(*   let na_imp_b = make_imp na b in *)

(*   let conjd = make_conj na_imp_b na_imp_nb in *)

(*   let goal = make_imp conjd a in *)

(*   let initial_fuel = 900 in *)
(*   let fuel = ref initial_fuel in *)

(*   let next_tactic = *)
(*     next_tactic_of_list *)
(*       [ *)
(*         with_repeat *)
(*         @@ with_no_trace ~show_proof:true *)
(*         @@ (with_fuel_limit fuel) ctauto_tac; *)
(*       ] *)
(*   in *)
(*   (match prove_bfs_with_trace ([], goal) next_tactic with *)
(*   | exception Out_of_fuel -> *)
(*       print_endline "out of fuel"; *)
(*       Printf.printf "With fuel usage: %d\n" (initial_fuel - !fuel) *)
(*   | t, Complete thm -> *)
(*       List.iter print_endline t; *)
(*       print_endline "Proof Complete!"; *)
(*       Printf.printf "With fuel usage: %d\n" !fuel; *)
(*       Printing.print_thm thm *)
(*   | _t, Incomplete _ -> *)
(*       Printf.printf "With fuel usage: %d\n" !fuel; *)
(*       print_endline "Proof Failed"); *)
(*   [%expect {| *)
(*     out of fuel *)
(*     With fuel usage: 900 *)
(*     |}] *)

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
    ( [],
      Result.get_ok
        (safe_make_eq (App (App (add, zero), two)) (App (App (add, one), one)))
    )
  in
  let proof = with_rules [ eq_thm ] rewrite_tac >> assume_tac in
  run_proof goal proof;

  [%expect
    {|
    assume_tac
    rewrite_tac
    Two = add One One
    ========================================
    add Zero Two = add One One

    Proof Complete!
    with fuel: 2
    |}]

let%expect_test "rewrite_basic" =
  let open Theories.NatTheory in
  let x = make_var "x" nat_ty in
  let zero_plus_x = make_plus zero x |> Result.get_ok in
  let goal = ([], make_forall x (Result.get_ok (safe_make_eq zero_plus_x x))) in
  let proof = gen_tac >> simp_tac in
  run_proof goal proof;
  [%expect
    {|
    refl_tac
    beta_tac
    rewrite_tac
    gen_tac
    ========================================
    ∀x. plus zero x = x

    Proof Complete!
    with fuel: 10
    |}]

let%expect_test "rewrite induction" =
  let open Theories.NatTheory in
  let x = make_var "x" nat_ty in
  let x_plus_zero = make_plus x zero |> Result.get_ok in
  let goal = ([], make_forall x (Result.get_ok (safe_make_eq x_plus_zero x))) in
  let proof = induct_tac >> simp_tac >> gen_tac >> intro_tac >> simp_tac in
  run_proof ~name:"plus_x_zero" goal proof;

  [%expect
    {|
    refl_tac
    beta_tac
    rewrite_tac
    refl_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    intro_tac
    gen_tac
    induction_tac
    ========================================
    ∀x. plus x zero = x

    Proof Complete!
    with fuel: 27
    |}]

let%expect_test "basic nat" =
  let open Theories.NatTheory in
  let make_plus' a b = make_plus a b |> Result.get_ok in
  let two_plus_3 = make_plus' n2 n3 in
  let goal = ([], Result.get_ok (safe_make_eq two_plus_3 n5)) in
  run_proof goal simp_tac;

  [%expect
    {|
    refl_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    ========================================
    plus (suc (suc zero)) (suc (suc (suc zero))) = suc (suc (suc (suc (suc zero))))

    Proof Complete!
    with fuel: 13
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
    ( [],
      Derived.make_foralls [ x; y; z ]
        (Result.get_ok (safe_make_eq plus_x_yz plus_xy_z)) )
  in
  let proof =
    with_term x induct_tac >> intros_tac >> simp_tac >> intros_tac >> simp_tac
  in
  run_proof ~name:"plus_assoc" goal proof;
  [%expect
    {|
    refl_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    gen_tac
    gen_tac
    refl_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    gen_tac
    gen_tac
    intro_tac
    gen_tac
    induction_tac
    ========================================
    ∀x. ∀y. ∀z. plus x (plus y z) = plus (plus x y) z

    Proof Complete!
    with fuel: 50
    |}]

let%expect_test "suc injective" =
  let open Theories.NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let suc_x = App (suc, x) in
  let suc_y = App (suc, y) in
  (* Suc x = Suc y -> x = y *)
  let goal =
    ( [],
      Derived.make_foralls [ x; y ]
        (make_imp
           (Result.get_ok (safe_make_eq suc_x suc_y))
           (Result.get_ok (safe_make_eq x y))) )
  in
  let proof =
    intros_tac
    >> (apply_thm_tac |> with_rules nat_def.injective)
    >> assumption_tac
  in
  run_proof ~name:"plus_inj" goal proof;

  [%expect
    {|
    assumption_tac
    apply_thm_tac
    intro_tac
    gen_tac
    gen_tac
    ========================================
    ∀x. ∀y. suc x = suc y ==> x = y

    Proof Complete!
    with fuel: 11
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
    ( [],
      Derived.make_foralls [ x; y ]
        (Result.get_ok (safe_make_eq plus_x_suc_y suc_plus_x_y)) )
  in
  let proof = induct_tac >> gen_tac >> simp_tac >> intros_tac >> simp_tac in
  run_proof ~name:"plus_suc" goal proof;
  [%expect
    {|
    refl_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    gen_tac
    refl_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    gen_tac
    intro_tac
    gen_tac
    induction_tac
    ========================================
    ∀x. ∀y. plus x (suc y) = suc (plus x y)

    Proof Complete!
    with fuel: 37
    |}]

let%expect_test "suc injective rev" =
  let open Theories.NatTheory in
  let x = make_var "x" nat_ty in
  let y = make_var "y" nat_ty in
  let suc_x = App (suc, x) in
  let suc_y = App (suc, y) in
  (* x = y -> Suc x =  Suc y *)
  let goal =
    ( [],
      Derived.make_foralls [ x; y ]
        (make_imp
           (Result.get_ok (safe_make_eq x y))
           (Result.get_ok (safe_make_eq suc_x suc_y))) )
  in
  let proof = intros_tac >> (rewrite_tac |> with_assumptions) >> refl_tac in
  run_proof ~name:"plus_inj_rev" goal proof;
  [%expect
    {|
    refl_tac
    rewrite_tac
    intro_tac
    gen_tac
    gen_tac
    ========================================
    ∀x. ∀y. x = y ==> suc x = suc y

    Proof Complete!
    with fuel: 9
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
    ( [],
      Derived.make_foralls [ x; y ]
        (Result.get_ok (safe_make_eq plus_x_y plus_y_x)) )
  in
  let proof =
    induct_tac >> gen_tac >> simp_tac
    >> with_first_success (with_proven [ "plus_x_zero" ] rewrite_tac)
    >> refl_tac >> intros_tac >> simp_tac >> sym_tac
    >> with_first_success (with_proven [ "plus_suc" ] apply_thm_tac)
  in
  run_proof ~name:"plus_comm" goal proof;

  [%expect
    {|
    refl_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    gen_tac
    apply_thm_tac
    sym_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    gen_tac
    intro_tac
    gen_tac
    induction_tac
    ========================================
    ∀x. ∀y. plus x y = plus y x

    Proof Complete!
    with fuel: 39
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
  let goal = ([], Derived.make_foralls [ x; y ] (make_imp p_eq y_eq_z)) in
  let proof =
    induct_tac >> simp_tac >> intros_tac >> assumption_tac >> intros_tac
    >> with_first_success (with_assumptions apply_thm_asm_tac)
    >> assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    assumption_tac
    intro_tac
    gen_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    assumption_tac
    apply_thm_asm_tac
    intro_tac
    gen_tac
    intro_tac
    gen_tac
    induction_tac
    ∀n0. (∀y. plus n0 y = plus n0 z ==> y = z) ==> ∀y. plus (suc n0) y = plus (suc n0) z ==> y = z
    ========================================
    ∀x. ∀y. plus x y = plus x z ==> y = z

    Proof Complete!
    with fuel: 34
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
  let goal = ([], Derived.make_foralls [ x; y ] (make_imp p_eq y_eq_z)) in
  let proof =
    induct_tac >> gen_tac
    >> with_proven [ "plus_x_zero" ] simp_tac
    >> intros_tac >> assumption_tac >> intros_tac
    >> with_proven [ "plus_suc" ] rewrite_asm_tac
    >> with_proven [ "plus_suc" ] rewrite_asm_tac
    >> with_proven [ "plus_inj" ] apply_thm_asm_tac
    >> with_first_success (with_assumptions apply_thm_tac)
    >> assumption_tac
  in
  run_proof goal proof;

  [%expect
    {|
    assumption_tac
    intro_tac
    rewrite_tac
    rewrite_tac
    gen_tac
    assumption_tac
    apply_thm_tac
    apply_thm_asm_tac
    rewrite_asm_tac
    rewrite_asm_tac
    intro_tac
    gen_tac
    intro_tac
    gen_tac
    induction_tac
    ========================================
    ∀x. ∀y. plus y x = plus z x ==> y = z

    Proof Complete!
    with fuel: 36
    |}]

let%expect_test "length Nil = Zero" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let length_const = make_const "length" [ (a, nat_ty) ] |> Result.get_ok in
  let nil_nat = type_inst [ (a, nat_ty) ] nil |> Result.get_ok in

  let length_nil = App (length_const, nil_nat) in
  let goal = ([], Result.get_ok (safe_make_eq length_nil zero)) in
  let proof = simp_tac in
  run_proof goal proof;

  [%expect
    {|
    refl_tac
    rewrite_tac
    ========================================
    length nil = zero

    Proof Complete!
    with fuel: 5
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
  let goal = ([], Result.get_ok (safe_make_eq length_cons n1)) in
  let proof = simp_tac in
  run_proof goal proof;

  [%expect
    {|
    refl_tac
    rewrite_tac
    rewrite_tac
    ========================================
    length (cons zero nil) = suc zero

    Proof Complete!
    with fuel: 7
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
    ( [],
      Derived.make_foralls [ x; xs ]
        (Result.get_ok (safe_make_eq length_cons_x_xs suc_length_xs)) )
  in
  let proof = intros_tac >> simp_tac in
  run_proof goal proof;

  [%expect
    {|
    refl_tac
    rewrite_tac
    gen_tac
    gen_tac
    ========================================
    ∀x. ∀xs. length (cons x xs) = suc (length xs)

    Proof Complete!
    with fuel: 11
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
  let goal = ([], make_forall xs (make_imp xs_eq_nil length_eq_zero)) in
  let proof = intros_tac >> simp_tac ~with_asms:true in
  run_proof goal proof;

  [%expect
    {|
    refl_tac
    rewrite_tac
    rewrite_tac
    intro_tac
    gen_tac
    ========================================
    ∀xs. xs = nil ==> length xs = zero

    Proof Complete!
    with fuel: 12
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
  let goal = ([], make_forall xs (make_imp length_eq_zero xs_eq_nil)) in
  let proof =
    induct_tac >> intros_tac >> refl_tac >> intros_tac
    >> with_first_success (with_assumptions apply_thm_asm_tac)
    >> assumption_tac
  in
  run_proof goal proof;
  [%expect
    {|
    refl_tac
    intro_tac
    assumption_tac
    apply_thm_asm_tac
    intro_tac
    intro_tac
    gen_tac
    gen_tac
    induction_tac
    ∀n0. ∀n1. (length n1 = zero ==> n1 = nil) ==> length (cons n0 n1) = zero ==> cons n0 n1 = nil
    ========================================
    ∀x. length x = zero ==> x = nil

    Proof Complete!
    with fuel: 20
    |}]

let%expect_test "append nil xs = xs" =
  let open Theories.ListTheory in
  let append_const = make_const "append" [] |> Result.get_ok in

  (* append Nil Nil = Nil *)
  let xs = make_var "xs" list_a in
  let append_nil = App (append_const, nil) in
  let append_nil_xs = App (append_nil, xs) in
  let goal =
    ([], make_forall xs @@ Result.get_ok (safe_make_eq append_nil_xs xs))
  in
  let proof = intros_tac >> simp_tac in
  run_proof goal proof;

  [%expect
    {|
    refl_tac
    beta_tac
    rewrite_tac
    gen_tac
    ========================================
    ∀xs. append nil xs = xs

    Proof Complete!
    with fuel: 13
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
    ([], make_foralls [ x; xs; ys ] @@ Result.get_ok (safe_make_eq lhs rhs))
  in
  let proof = intros_tac >> simp_tac in
  run_proof ~name:"append_cons" goal proof;

  [%expect
    {|
    refl_tac
    beta_tac
    rewrite_tac
    gen_tac
    gen_tac
    gen_tac
    ========================================
    ∀x. ∀xs. ∀ys. append (cons x xs) ys = cons x (append xs ys)

    Proof Complete!
    with fuel: 17
    |}]

let%expect_test "append xs nil = xs" =
  let open Theories.ListTheory in
  let append_const = make_const "append" [] |> Result.get_ok in

  (* need a lemma *)
  let xs = make_var "xs" list_a in
  let append_xs = App (append_const, xs) in
  let append_nil_xs = App (append_xs, nil) in
  let proof =
    induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_cons" ] rewrite_tac
    >> with_proven [ "append_cons" ] simp_tac
  in
  let goal =
    ([], make_forall xs @@ Result.get_ok (safe_make_eq append_nil_xs xs))
  in
  run_proof ~name:"append_xs_nil" goal proof;

  [%expect
    {|
    refl_tac
    beta_tac
    rewrite_tac
    refl_tac
    rewrite_tac
    rewrite_tac
    intro_tac
    gen_tac
    gen_tac
    induction_tac
    ========================================
    ∀x. append x nil = x

    Proof Complete!
    with fuel: 28
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

  let proof = induct_tac |> then_each [ auto_dfs_tac; auto_dfs_tac ] in
  let goal =
    ([], make_foralls [ xs; ys; zs ] @@ Result.get_ok (safe_make_eq lhs rhs))
  in
  run_proof ~name:"append_assoc" goal proof;
  [%expect
    {|
    refl_tac
    gen_tac
    gen_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    refl_tac
    gen_tac
    gen_tac
    rewrite_tac
    intro_tac
    gen_tac
    gen_tac
    beta_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    induction_tac
    ========================================
    ∀x. ∀ys. ∀zs. append (append x ys) zs = append x (append ys zs)

    Proof Complete!
    with fuel: 73
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

  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  let goal =
    ([], make_foralls [ xs; ys ] @@ Result.get_ok (safe_make_eq lhs rhs))
  in
  run_proof ~name:"append_length" goal proof;

  [%expect
    {|
    refl_tac
    gen_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    refl_tac
    gen_tac
    rewrite_tac
    intro_tac
    gen_tac
    gen_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    induction_tac
    ========================================
    ∀x. ∀ys. length (append x ys) = plus (length x) (length ys)

    Proof Complete!
    with fuel: 65
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

  let proof =
    induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_length" ] simp_tac
    >> with_first_success (with_proven [ "plus_comm" ] rewrite_tac)
    >> simp_tac
  in
  let goal = ([], make_forall xs @@ Result.get_ok (safe_make_eq lhs rhs)) in
  run_proof goal proof;

  [%expect
    {|
    refl_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    refl_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    intro_tac
    gen_tac
    gen_tac
    induction_tac
    ========================================
    ∀x. length (reverse x) = length x

    Proof Complete!
    with fuel: 49
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

  let proof =
    induct_tac >> intros_tac
    >> with_proven [ "append_xs_nil" ] simp_tac
    >> intros_tac >> simp_tac
    >> with_first_success (with_proven [ "append_assoc" ] apply_thm_tac)
  in
  let goal =
    ([], make_foralls [ xs; ys ] @@ Result.get_ok (safe_make_eq lhs rhs))
  in
  run_proof ~name:"append_reverse" goal proof;

  [%expect
    {|
    refl_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    gen_tac
    apply_thm_tac
    rewrite_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    gen_tac
    intro_tac
    gen_tac
    gen_tac
    induction_tac
    ========================================
    ∀x. ∀ys. reverse (append x ys) = append (reverse ys) (reverse x)

    Proof Complete!
    with fuel: 49
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

  let proof =
    induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "append_reverse" ] simp_tac
  in
  let goal = ([], make_forall xs @@ Result.get_ok (safe_make_eq lhs rhs)) in
  run_proof goal proof;
  [%expect
    {|
    refl_tac
    rewrite_tac
    rewrite_tac
    refl_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    intro_tac
    gen_tac
    gen_tac
    induction_tac
    ========================================
    ∀x. reverse (reverse x) = x

    Proof Complete!
    with fuel: 46
    |}]

let%expect_test "test defining with elab" =
  let prg =
    {|
    vartype a
    variable x y : a
    theorem fst_snd_eq: imp (eq x y) (eq (fst (pair x y)) (snd (pair x y)))

  |}
  in
  let proof = intros_tac >> simp_tac in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal proof;

  [%expect
    {|
    refl_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    intro_tac
    ========================================
    x = y ==> fst (pair x y) = snd (pair x y)

    Proof Complete!
    with fuel: 12
    |}]

let%expect_test "test minus" =
  let prg =
    {|
    theorem three_minus_one_is_two : eq
        (pred (suc (suc (suc zero))) )
        (suc (suc zero))
  |}
  in
  let proof = simp_tac in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal proof;

  [%expect
    {|
    refl_tac
    rewrite_tac
    ========================================
    pred (suc (suc (suc zero))) = suc (suc zero)

    Proof Complete!
    with fuel: 5
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
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal simp_tac;

  [%expect
    {|
    refl_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    ========================================
    minus (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = suc zero

    Proof Complete!
    with fuel: 29
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
  let proof = induct_tac >> auto_dfs_tac >> auto_dfs_tac in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof ~name:"minus_zero" goal proof;

  [%expect
    {|
    refl_tac
    beta_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    refl_tac
    intro_tac
    gen_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    induction_tac
    ========================================
    ∀x. minus x zero = x

    Proof Complete!
    with fuel: 57
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
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> with_proven [ "minus_zero" ] auto_dfs_tac >> auto_dfs_tac
  in
  run_proof ~name:"minus_suc_right" goal proof;
  [%expect
    {|
    refl_tac
    gen_tac
    beta_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    refl_tac
    gen_tac
    intro_tac
    gen_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    induction_tac
    ========================================
    ∀x. ∀m. minus x (suc m) = pred (minus x m)

    Proof Complete!
    with fuel: 80
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
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    gen_tac >> induct_tac
    >> with_proven [ "minus_zero" ] simp_tac
    >> intros_tac
    >> with_proven [ "minus_suc_right" ] rewrite_tac
    >> with_assumptions rewrite_tac
    >> with_proven [ "minus_suc_right" ] rewrite_tac
    >> refl_tac
  in

  run_proof ~name:"minus_suc_suc" goal proof;
  [%expect
    {|
    refl_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    refl_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    intro_tac
    gen_tac
    induction_tac
    gen_tac
    ========================================
    ∀n. ∀x. minus (suc n) (suc x) = minus n x

    Proof Complete!
    with fuel: 40
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
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> simp_tac >> intros_tac
    >> with_proven [ "minus_suc_suc" ] simp_tac
    >> simp_asm_tac ~with_asms:false
  in
  run_proof ~name:"minus_self" goal proof;

  [%expect
    {|
    refl_tac
    beta_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    assumption_tac
    beta_asm_tac
    rewrite_asm_tac
    rewrite_asm_tac
    beta_tac
    rewrite_tac
    rewrite_tac
    rewrite_tac
    intro_tac
    gen_tac
    induction_tac
    ========================================
    ∀x. minus x x = zero

    Proof Complete!
    with fuel: 52
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

  let proof =
    gen_tac >> induct_tac
    >> with_proven [ "plus_x_zero"; "minus_zero" ] simp_tac
    >> intros_tac
    >> with_proven [ "plus_suc" ] rewrite_tac
    >> with_proven [ "minus_suc_suc" ] rewrite_tac
    >> assumption_tac
  in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal proof;
  [%expect
    {|
    refl_tac
    rewrite_tac
    rewrite_tac
    assumption_tac
    rewrite_tac
    rewrite_tac
    intro_tac
    gen_tac
    induction_tac
    gen_tac
    ========================================
    ∀x. ∀x'. minus (plus x x') x' = x

    Proof Complete!
    with fuel: 23
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
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  run_proof goal simp_tac;

  [%expect
    {|
    refl_tac
    rewrite_tac
    rewrite_tac
    beta_tac
    rewrite_tac
    ========================================
    twice pred (suc (suc zero)) = zero

    Proof Complete!
    with fuel: 13
    |}]
