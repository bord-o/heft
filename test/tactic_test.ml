open Heft
open Derived
open Inductive
open Tactic

(* open Effect *)
open Printing

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
        apply_tac;
        apply_tac;
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

  let next_tactic = next_tactic_of_list [ with_repeat ctauto_tac ] in
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
    assumption doesn't match the goal
    destruct success
    assumption doesn't match the goal
    assumption doesn't match the goal
    OperationDoesntMatch
    NotANegation
    NotAConj
    assumption doesn't match the goal
    assumption doesn't match the goal
    assumption doesn't match the goal
    OperationDoesntMatch
    NotANegation
    NotAConj
    assume chosen h success
    assumption doesn't match the goal
    assumption doesn't match the goal
    assumption doesn't match the goal
    OperationDoesntMatch
    NotANegation
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
        apply_tac;
        assumption_tac;
        apply_tac;
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
           apply_neg_tac;
           left_tac;
           assumption_tac;
           neg_intro_tac;
           apply_neg_tac;
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
    apply_neg_tac
    neg_intro_tac
    assumption_tac
    right_tac
    apply_neg_tac
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
    apply_neg_tac
    left_tac
    ccontr_tac
    apply_neg_tac
    right_tac
    assumption_tac
    neg_intro_tac
    apply_neg_tac
    left_tac
    assumption_tac
    Proof Complete!
    With fuel usage: 260
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
    apply_neg_tac
    right_tac
    assumption_tac
    neg_intro_tac
    apply_neg_tac
    left_tac
    assumption_tac
    Proof Complete!
    With fuel usage: 28728
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
  | _t, Incomplete _ ->
      Printf.printf "With fuel usage: %d\n" !fuel;
      print_endline "Proof Failed");
  [%expect
    {|
    intro_tac
    elim_conj_asm_tac
    ccontr_tac
    mp_asm_tac
    mp_asm_tac
    neg_elim_tac
    Proof Complete!
    With fuel usage: 1440
    ========================================
    (¬a ==> b) ∧ (¬a ==> ¬b) ==> a
    |}]
