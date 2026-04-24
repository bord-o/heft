open Heft
open Auto
(* Search benchmark suite: tests that exercise different dimensions of
   proof search — forward chaining, case splitting, classical reasoning,
   and disjunction routing. *)

(* --- Forward chaining through hypotheses --- *)

let%expect_test "forward_chain" =
  let%thm _fwd (a : bool) (b : bool) (c : bool) (d : bool) (e : bool) =
    a ==> b ==> ((b ==> c || d) ==> (c ==> e ==> (d ==> e ==> (a ==> e))))
  and proof =
    begin
      with_best_first ctauto (* with_info_trace (with_best_first ctauto) *)
    end
  in
  ignore _fwd;
  [%expect
    {|
    Proof:
      gen >>
      gen >>
      gen >>
      gen >>
      gen >>
      intro >>
      intro >>
      intro >>
      intro >>
      intro >>
      elim_disj_asm >>
      apply >>
      assumption >>
      apply >>
      apply >>
      apply_asm >>
      assumption
    ========================================
    ∀a. ∀b. ∀c. ∀d. ∀e. (a ==> b) ==> (b ==> c) ∨ d ==> (c ==> e) ==> (d ==> e) ==> a ==> e

    Proof Complete!
    with fuel: 985
    |}]

(* --- Multi-phase: application + case split + elimination --- *)

let%expect_test "multi_phase" =
  let%thm _mp (a : bool) (b : bool) (c : bool) (d : bool) (e : bool) (f : bool)
      =
    (a ==> b || c) ==> (b ==> d ==> (c ==> d ==> ((d ==> e && f) ==> (a ==> e))))
  and proof =
    begin
      with_best_first ctauto
    end
  in
  ignore _mp;
  [%expect
    {|
    Proof:
      gen >>
      gen >>
      gen >>
      gen >>
      gen >>
      gen >>
      intro >>
      intro >>
      elim_disj_asm >>
      intro >>
      intro >>
      elim_conj_asm >>
      intro >>
      apply >>
      apply >>
      assumption >>
      intro >>
      intro >>
      elim_conj_asm >>
      intro >>
      apply_asm >>
      apply >>
      apply >>
      assumption
    ========================================
    ∀a. ∀b. ∀c. ∀d. ∀e. ∀f. (a ==> b) ∨ c ==> (b ==> d) ==> (c ==> d) ==> (d ==> e) ∧ f ==> a ==> e

    Proof Complete!
    with fuel: 1941
    |}]

(* --- Disjunction routing --- *)

let%expect_test "four_var_distribution" =
  let%thm _dist (a : bool) (b : bool) (c : bool) (d : bool) =
    ((a || b) && (c || d)) ==> ((a && c) || (a && d) || (b && c) || (b && d))
  and proof =
    begin
      with_best_first ctauto
    end
  in
  ignore _dist;
  [%expect
    {|
    Proof:
      gen >>
      gen >>
      gen >>
      gen >>
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
    ∀a. ∀b. ∀c. ∀d. a ∨ b ∧ c ∨ d ==> a ∧ c ∨ a ∧ d ∨ b ∧ c ∨ b ∧ d

    Proof Complete!
    with fuel: 17033
    |}]

(* --- Classical: De Morgan --- *)

let%expect_test "de_morgan_and" =
  let%thm _dm (p : bool) (q : bool) = (not (p && q)) ==> ((not p) || not q)
  and proof =
    begin
      with_best_first ctauto
    end
  in
  ignore _dm;
  [%expect
    {|
    Proof:
      gen >>
      gen >>
      intro >>
      ccontr >>
      contradict_asm >>
      right >>
      neg_intro >>
      contradict_asm >>
      left >>
      neg_intro >>
      contradict_asm >>
      conj >>
      assumption >>
      assumption
    ========================================
    ∀p. ∀q. ¬p ∧ q ==> ¬p ∨ ¬q

    Proof Complete!
    with fuel: 1213
    |}]

(* --- Contrapositive chain --- *)

let%expect_test "contrapositive_chain" =
  let%thm _cc (a : bool) (b : bool) (c : bool) (d : bool) =
    a ==> b ==> (b ==> c ==> (c ==> d ==> ((not d) ==> not a)))
  and proof =
    begin
      with_best_first ctauto
    end
  in
  ignore _cc;
  [%expect
    {|
    Proof:
      gen >>
      gen >>
      gen >>
      gen >>
      intro >>
      intro >>
      intro >>
      intro >>
      neg_intro >>
      contradict_asm >>
      apply >>
      apply_asm >>
      apply_asm >>
      assumption
    ========================================
    ∀a. ∀b. ∀c. ∀d. (a ==> b) ==> (b ==> c) ==> (c ==> d) ==> ¬d ==> ¬a

    Proof Complete!
    with fuel: 450
    |}]

(* --- Peirce's law: classical, no safe tactics help --- *)

let%expect_test "peirce" =
  let%thm _peirce (p : bool) (q : bool) = p ==> q ==> p ==> p
  and proof =
    begin
      with_best_first ctauto
    end
  in
  ignore _peirce;
  [%expect
    {|
    Proof:
      ccontr >>
      contradict_asm >>
      gen >>
      ccontr >>
      contradict_asm >>
      gen >>
      gen >>
      intro >>
      ccontr >>
      contradict_asm >>
      apply >>
      intro >>
      neg_elim
    ========================================
    ∀p. ∀q. ((p ==> q) ==> p) ==> p

    Proof Complete!
    with fuel: 2278
    |}]

(* --- Diamond: two paths to the same conclusion --- *)

let%expect_test "diamond" =
  let%thm _diamond (a : bool) (b : bool) (c : bool) (d : bool) =
    a ==> b ==> (a ==> c ==> (b ==> d ==> (c ==> d ==> (a ==> d))))
  and proof =
    begin
      with_best_first ctauto
    end
  in
  ignore _diamond;
  [%expect
    {|
    Proof:
      gen >>
      gen >>
      gen >>
      gen >>
      intro >>
      intro >>
      intro >>
      intro >>
      intro >>
      apply_asm >>
      apply_asm >>
      assumption
    ========================================
    ∀a. ∀b. ∀c. ∀d. (a ==> b) ==> (a ==> c) ==> (b ==> d) ==> (c ==> d) ==> a ==> d

    Proof Complete!
    with fuel: 334
    |}]

(* --- Excluded middle consequence --- *)

let%expect_test "excluded_middle_consequence" =
  let%thm _emc (p : bool) (q : bool) = p ==> q ==> ((not p) ==> q ==> q)
  and proof =
    begin
      with_best_first ctauto
    end
  in
  ignore _emc;
  [%expect
    {|
    Proof:
      gen >>
      gen >>
      ccontr >>
      contradict_asm >>
      intro >>
      intro >>
      apply >>
      neg_intro >>
      contradict_asm >>
      intro >>
      apply_asm >>
      intro >>
      assumption
    ========================================
    ∀p. ∀q. (p ==> q) ==> (¬p ==> q) ==> q

    Proof Complete!
    with fuel: 769
    |}]

(* --- Five variable or chain: deep disjunction navigation --- *)

let%expect_test "five_var_or_chain" =
  let%thm _chain (a : bool) (b : bool) (c : bool) (d : bool) (e : bool) =
    (a || b || c || d || e) ==> (e || d || c || b || a)
  and proof =
    begin
      with_best_first ctauto
    end
  in
  ignore _chain;
  [%expect
    {|
    Proof:
      gen >>
      gen >>
      gen >>
      gen >>
      gen >>
      intro >>
      elim_disj_asm >>
      elim_disj_asm >>
      elim_disj_asm >>
      elim_disj_asm >>
      left >>
      assumption >>
      right >>
      left >>
      assumption >>
      right >>
      right >>
      left >>
      assumption >>
      right >>
      right >>
      right >>
      left >>
      assumption >>
      right >>
      right >>
      right >>
      right >>
      assumption
    ========================================
    ∀a. ∀b. ∀c. ∀d. ∀e. a ∨ b ∨ c ∨ d ∨ e ==> e ∨ d ∨ c ∨ b ∨ a

    Proof Complete!
    with fuel: 17546
    |}]

(* --- Currying --- *)

let%expect_test "curry_uncurry" =
  let%thm _cu (a : bool) (b : bool) (c : bool) =
    (a && b) ==> c ==> (a ==> (b ==> c))
  and proof =
    begin
      with_best_first ctauto
    end
  in
  ignore _cu;
  [%expect
    {|
    Proof:
      gen >>
      gen >>
      gen >>
      intro >>
      intro >>
      intro >>
      apply >>
      conj >>
      assumption >>
      assumption
    ========================================
    ∀a. ∀b. ∀c. (a ∧ b ==> c) ==> a ==> b ==> c

    Proof Complete!
    with fuel: 209
    |}]
