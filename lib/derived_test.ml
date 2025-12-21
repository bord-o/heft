open Kernel
open Derived
open Printing
open Result.Syntax

let p = Var ("P", bool_ty)
let q = Var ("Q", bool_ty)
let r = Var ("R", bool_ty)
let s = Var ("S", bool_ty)
let g = Var ("f", TyCon ("fun", [ bool_ty; bool_ty ]))

(* let g = Var ("g", TyCon ("fun", [ bool_ty; bool_ty ])) *)
let x = Var ("x", bool_ty)
let y = Var ("y", bool_ty)
let z = Var ("z", bool_ty)

let clear_env () =
  Hashtbl.clear the_inductives;
  Hashtbl.clear the_term_constants;
  Hashtbl.clear the_type_constants;
  the_axioms := [];
  the_definitions := []

let print_term = Fun.compose print_endline show_term
let print_thm = Fun.compose print_endline show_thm
let print_types = ref false

let print_thm_result =
  Format.pp_print_result
    ~ok:(fun fmt thm ->
      Format.pp_print_string fmt (pretty_print_thm ~with_type:!print_types thm))
    ~error:pp_kernel_error Format.std_formatter

let print_term_result =
  Format.pp_print_result
    ~ok:(fun fmt term ->
      Format.pp_print_string fmt
        (pretty_print_hol_term ~with_type:!print_types term))
    ~error:pp_kernel_error Format.std_formatter

let%expect_test "beta_conv_simple" =
  let () = clear_env () in
  let _ = init_types () in

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
  let () = clear_env () in
  let _ = init_types () in

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
  let () = clear_env () in
  let _ = init_types () in

  let thm =
    let* conj_def = conj_def in
    rhs conj_def
  in
  print_term_result thm;
  [%expect {| λp. λq. (λf. f p q) = (λf. f T T) |}]

let%expect_test "lhs_simple" =
  let () = clear_env () in
  let _ = init_types () in

  let thm =
    let* conj_def = conj_def in
    lhs conj_def
  in
  print_term_result thm;
  [%expect {| /\ |}]

let%expect_test "unfold_definition_simple" =
  let () = clear_env () in
  let _ = init_types () in

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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
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
  let () = clear_env () in
  let _ = init_types () in
  let thm =
    let open Result.Syntax in
    let* false_def = false_def in
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
  let () = clear_env () in
  let _ = init_types () in
  let thm =
    let open Result.Syntax in
    let p = make_var "p" bool_ty in
    let not_p = make_neg p in
    let* assumed_not_p = assume not_p in
    let* false_tm = make_false () |> Result.ok in
    let* false_th = assume false_tm in
    let* p_assumed = assume p in
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
  let () = clear_env () in
  let _ = init_types () in
  let thm =
    let x = make_var "x" bool_ty in
    let* p_eq_p = refl p in
    exists x p p_eq_p 
  in
  print_thm_result thm;
  [%expect {|
  |}]
