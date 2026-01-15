open Heft 
open Derived
open Printing
open Result.Syntax

let p = Var ("P", bool_ty)
let q = Var ("Q", bool_ty)
let r = Var ("R", bool_ty)
let s = Var ("S", bool_ty)
let g = Var ("f", TyCon ("fun", [ bool_ty; bool_ty ]))
let x = Var ("x", bool_ty)
let y = Var ("y", bool_ty)
let z = Var ("z", bool_ty)
let axiom_for_test tm = Result.get_ok (new_axiom tm)
let print_types = ref false

let print_thm_result r =
  Format.pp_print_result
    ~ok:(fun fmt thm ->
      Format.pp_print_string fmt (pretty_print_thm ~with_type:!print_types thm))
    ~error:(fun _f e -> print_endline @@ Printing.print_error e)
    Format.std_formatter r

let print_term_result r =
  Format.pp_print_result
    ~ok:(fun fmt term ->
      Format.pp_print_string fmt
        (pretty_print_hol_term ~with_type:!print_types term))
    ~error:(fun _f e -> print_endline @@ Printing.print_error e)
    Format.std_formatter r

let%expect_test "beta_conv_simple" =
  let () = reset () |> Result.get_ok in

  let thm =
    let binder = make_var "x" bool_ty in
    let body = make_conj binder binder in
    let* lambda = make_lam binder body in
    let arg = make_var "arg" bool_ty in
    let* applied = make_app lambda arg in
    beta_conv applied
  in
  print_thm_result thm;
  [%expect
    {|
    ========================================
    (λx. x ∧ x) arg = arg ∧ arg
    |}]

let%expect_test "beta_conv_binder_eq_arg" =
  let () = reset () |> Result.get_ok in

  let thm =
    let binder = make_var "x" bool_ty in
    let body = make_conj binder binder in
    let* lambda = make_lam binder body in
    let arg = make_var "x" bool_ty in
    let* applied = make_app lambda arg in
    beta_conv applied
  in
  print_thm_result thm;
  [%expect
    {|
    ========================================
    (λx. x ∧ x) x = x ∧ x
    |}]

let%expect_test "rhs_simple" =
  let () = reset () |> Result.get_ok in

  let thm =
    let* conj_def = conj_def in
    rhs conj_def
  in
  print_term_result thm;
  [%expect {| λp. λq. (λf. f p q) = (λf. f T T) |}]

let%expect_test "lhs_simple" =
  let () = reset () |> Result.get_ok in

  let thm =
    let* conj_def = conj_def in
    lhs conj_def
  in
  print_term_result thm;
  [%expect {| /\ |}]

let%expect_test "unfold_definition_simple" =
  let () = reset () |> Result.get_ok in

  let thm =
    let* conj_def = conj_def in
    unfold_definition conj_def [ p; q ]
  in
  print_thm_result thm;
  [%expect
    {|
    ========================================
    (λf. f P Q) = (λf. f T T) = P ∧ Q
    |}]

let%expect_test "conj_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* thl = assume p in
    let* thr = assume q in
    conj thl thr
  in
  print_thm_result thm;
  [%expect
    {|
    P
    Q
    ========================================
    P ∧ Q
    |}]

let%expect_test "conj_left_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* thl = assume p in
    let* thr = assume q in
    let* conj_pq = conj thl thr in
    conj_left conj_pq
  in
  print_thm_result thm;
  [%expect
    {|
    P
    Q
    ========================================
    P
    |}]

let%expect_test "conj_left_nested" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* p_th = assume p in
    let* q_th = assume q in
    let* r_th = assume r in
    let* conj_pq = conj p_th q_th in
    let* conj_pq_r = conj conj_pq r_th in
    conj_left conj_pq_r
  in
  print_thm_result thm;
  [%expect
    {|
    P
    Q
    R
    ========================================
    P ∧ Q
    |}]

let%expect_test "conj_right_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* thl = assume p in
    let* thr = assume q in
    let* conj_pq = conj thl thr in
    conj_right conj_pq
  in
  print_thm_result thm;
  [%expect
    {|
    P
    Q
    ========================================
    Q
    |}]

let%expect_test "undisch_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let p_imp_q = make_imp p q in
    let* p_imp_q_th = assume p_imp_q in
    undisch p_imp_q_th
  in
  print_thm_result thm;
  [%expect
    {|
    P
    P ==> Q
    ========================================
    Q
    |}]

let%expect_test "disch_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* q_th = assume q in
    disch q q_th
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    Q ==> Q
    |}]

let%expect_test "disch_with_real_derivation" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* pq_th = assume (make_conj p q) in
    let* q_th = conj_right pq_th in
    disch (make_conj p q) q_th
  in
  print_thm_result thm;
  [%expect
    {|
    ========================================
    P ∧ Q ==> Q
    |}]

let%expect_test "prove_hyp_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* p_th = assume p in
    let* p_imp_q = assume (make_imp p q) in
    let* q_under_p = undisch p_imp_q in
    prove_hyp p_th q_under_p
  in
  print_thm_result thm;
  [%expect
    {|
    P
    P ==> Q
    ========================================
    Q
    |}]

let%expect_test "prove_hyp_removes_assumption" =
  let () = reset () |> Result.get_ok in
  let thm =
    let t = make_true () in
    let* t_th = assume t in
    prove_hyp truth t_th
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    T
    |}]

let%expect_test "mp_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* p_imp_q_th = assume @@ make_imp (make_true ()) q in
    mp p_imp_q_th truth
  in
  print_thm_result thm;
  [%expect
    {|
    T ==> Q
    ========================================
    Q
    |}]

let%expect_test "gen_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* x_refl = refl x in
    gen x x_refl
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    ∀x. x = x
    |}]

let%expect_test "spec_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* x_refl = refl x in
    let* gen_x = gen x x_refl in
    spec y gen_x
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    y = y
    |}]

let%expect_test "disj_left_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* x_refl = refl x in
    disj_left y x_refl
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    x = x ∨ y
    |}]

let%expect_test "disj_right_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* x_refl = refl x in
    disj_right x_refl y
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    y ∨ x = x
    |}]

let%expect_test "disj_cases_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* pr_imp = assume (make_imp p r) in
    let* pr_th = undisch pr_imp in

    let* qr_imp = assume (make_imp q r) in
    let* qr_th = undisch qr_imp in

    let* disj_th = assume @@ make_disj p q in

    disj_cases disj_th pr_th qr_th
  in
  print_thm_result thm;
  [%expect
    {|
    P ==> R
    Q ==> R
    P ∨ Q
    ========================================
    R
    |}]

let%expect_test "not_elim_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* neg_p = assume (make_neg p) in
    not_elim neg_p
  in
  print_thm_result thm;
  [%expect
    {|
    P
    ¬P
    ========================================
    F
    |}]

let%expect_test "not_intro_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* neg_p = assume (make_neg p) in
    let* p_gives_f = not_elim neg_p in
    not_intro p p_gives_f
  in
  print_thm_result thm;
  [%expect {|
    ¬P
    ========================================
    ¬P
    |}]

let%expect_test "contr_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let open Result.Syntax in
    let* false_tm = make_false () |> Result.ok in
    let* false_th = assume false_tm in
    contr x false_th
  in
  print_thm_result thm;
  [%expect {|
    F
    ========================================
    x
    |}]

let%expect_test "ccontr_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let open Result.Syntax in
    let p = make_var "p" bool_ty in
    let not_p = make_neg p in
    let* assumed_not_p = assume not_p in
    let* false_from_contradiction = not_elim assumed_not_p in
    ccontr p false_from_contradiction
  in
  print_thm_result thm;
  [%expect {|
    p
    ========================================
    p
    |}]

let%expect_test "exists_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let x = make_var "x" bool_ty in
    let* p_eq_p = refl p in
    exists x p p_eq_p
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    ∃x. x = x
    |}]

let%expect_test "exists_different_witness" =
  let () = reset () |> Result.get_ok in
  let thm =
    let x = make_var "x" bool_ty in
    let y = make_var "y" bool_ty in
    let* y_eq_y = refl y in
    exists x y y_eq_y
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    ∃x. x = x
    |}]

let%expect_test "exists_with_implication" =
  let () = reset () |> Result.get_ok in
  let thm =
    let x = make_var "x" bool_ty in
    let* p_imp_p = assume (make_imp p p) in
    let* proved = mp p_imp_p (Result.get_ok (assume p)) in
    let* p_eq_p = deduct_antisym_rule (Result.get_ok (assume p)) proved in
    exists x p p_eq_p
  in
  print_thm_result thm;
  [%expect
    {|
    P ==> P
    ========================================
    ∃x. x = x
    |}]

let%expect_test "exists_witness_different_from_bound" =
  let () = reset () |> Result.get_ok in
  let thm =
    let x = make_var "x" bool_ty in
    let y = make_var "y" bool_ty in
    let z = make_var "z" bool_ty in
    let* y_eq_z = assume (Result.get_ok (safe_make_eq y z)) in
    exists x y y_eq_z
  in
  print_thm_result thm;
  [%expect
    {|
    y = z
    ========================================
    ∃x. x = z
    |}]

let%expect_test "exists_polymorphic_type" =
  let () = reset () |> Result.get_ok in
  let thm =
    let a = TyVar "a" in
    let x = make_var "x" a in
    let y = make_var "y" a in
    let* y_eq_y = refl y in
    exists x y y_eq_y
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    ∃x. x = x
    |}]

let%expect_test "choose_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let x = make_var "x" bool_ty in
    let p_x = Result.get_ok (safe_make_eq x x) in
    let* x_refl = refl x in
    let* exists_th = exists x x x_refl in
    let* px_assumed = assume p_x in
    let* conj_th = conj px_assumed truth in
    let* q_th = conj_right conj_th in
    choose x exists_th q_th
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    T
    |}]

let%expect_test "choose_exists_from_assumption" =
  let () = reset () |> Result.get_ok in
  let thm =
    let x = make_var "x" bool_ty in
    let p_x = Result.get_ok (safe_make_eq x x) in
    let exists_px = make_exists x p_x in
    let* exists_assumed = assume exists_px in
    let* px_assumed = assume p_x in
    let* q_th = prove_hyp truth px_assumed in
    let* final = conj q_th truth in
    let* q_th' = conj_right final in
    choose x exists_assumed q_th'
  in
  print_thm_result thm;
  [%expect
    {|
    ∃x. x = x
    ========================================
    T
    |}]

let%expect_test "choose_polymorphic" =
  let () = reset () |> Result.get_ok in
  let thm =
    let a = TyVar "a" in
    let y = make_var "y" a in
    let p_y = Result.get_ok (safe_make_eq y y) in
    let* y_refl = refl y in
    let* exists_th = exists y y y_refl in
    let* py_assumed = assume p_y in
    let* conj_th = conj py_assumed truth in
    let* q_th = conj_right conj_th in
    choose y exists_th q_th
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    T
    |}]

let%expect_test "choose_clean" =
  let () = reset () |> Result.get_ok in
  let thm =
    let x = make_var "x" bool_ty in
    let p_x = Result.get_ok (safe_make_eq x x) in
    let* x_refl = refl x in
    let* exists_th = exists x x x_refl in
    let q_th =
      let* undischd = undisch (axiom_for_test (make_imp p_x p)) in
      Ok undischd
    in
    choose x exists_th (Result.get_ok q_th)
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    P
    |}]

let%expect_test "choose_with_real_predicate" =
  let () = reset () |> Result.get_ok in
  let thm =
    let x = make_var "x" bool_ty in
    let p_x = make_conj x (make_neg x) in
    (* x ∧ ¬x *)
    let exists_th = axiom_for_test (make_exists x p_x) in
    let* px_assumed = assume p_x in
    let* x_th = conj_left px_assumed in
    let* neg_x_th = conj_right px_assumed in
    let* false_th = not_elim neg_x_th in
    let* false_th' = prove_hyp x_th false_th in
    let* q_th = contr p false_th' in
    choose x exists_th q_th
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    P
    |}]

let%expect_test "double_negation_implies_p" =
  let () = reset () |> Result.get_ok in
  let thm =
    let neg_neg_p = make_neg (make_neg p) in
    let p = p in
    let* start = assume neg_neg_p in
    let* nelim = not_elim start in
    let* contr = ccontr p nelim in
    disch neg_neg_p contr
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    ¬¬P ==> P
    |}]

let%expect_test "forall_symmetry" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* x_eq_y = safe_make_eq x y in

    let* xy_th = assume x_eq_y in
    let* yx_th = sym xy_th in
    let* imp = disch x_eq_y yx_th in
    gens [ x; y ] imp
  in
  print_thm_result thm;
  [%expect
    {|
    ========================================
    ∀y. ∀x. x = y ==> y = x
    |}]

let%expect_test "identity" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* p_th = assume p in
    disch p p_th
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    P ==> P
    |}]

let%expect_test "contrapositive" =
  let () = reset () |> Result.get_ok in
  let thm =
    let p_imp_q = make_imp p q in

    let* pq_th = assume p_imp_q in
    let* nq_th = assume (make_neg q) in
    let* p_th = assume p in
    let* qmp = mp pq_th p_th in
    let* nnq = not_elim nq_th in
    let* combined = prove_hyp qmp nnq in
    let* np = not_intro p combined in
    let* d1 = disch (make_neg q) np in
    let* d2 = disch p_imp_q d1 in
    Ok d2
  in
  print_thm_result thm;
  [%expect
    {|
    ========================================
    (P ==> Q) ==> ¬Q ==> ¬P
    |}]

let%expect_test "neg_sym_simple" =
  let () = reset () |> Result.get_ok in
  let thm =
    let* p_eq_q = safe_make_eq p q in
    let npq = axiom_for_test (make_neg p_eq_q) in

    neg_sym npq
  in
  print_thm_result thm;
  [%expect {|
    ========================================
    ¬Q = P
    |}]

let%expect_test "" =
  let () = reset () |> Result.get_ok in
  let thm = Ok truth in
  print_thm_result thm;
  [%expect {|
    ========================================
    T
    |}]
