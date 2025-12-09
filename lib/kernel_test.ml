open Kernel
open Result.Syntax
open Printing

let _ = init ()
let p = Var ("P", bool_ty)
let q = Var ("Q", bool_ty)
let r = Var ("R", bool_ty)
let f = Var ("f", TyCon ("fun", [ bool_ty; bool_ty ]))
let g = Var ("g", TyCon ("fun", [ bool_ty; bool_ty ]))
let x = Var ("x", bool_ty)
let y = Var ("y", bool_ty)
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

(* Template
let%expect_test "" =
    let thm = _ in
    print_thm_result thm;
    [%expect {||}]
   
 *)

let%expect_test "assume_simple" =
  let thm1 = assume p in
  print_thm_result thm1;
  [%expect {|
    P

    ================================

    P
    |}]

let%expect_test "refl_simple" =
  let thm1 = refl p in
  print_thm_result thm1;
  [%expect {|
    ================================

    P = P
    |}]

let%expect_test "trans_simple" =
  let thm3 =
    let* pq_eq = safe_make_eq p q in
    let* qr_eq = safe_make_eq q r in
    let* thm1 = assume pq_eq in
    let* thm2 = assume qr_eq in
    trans thm1 thm2
  in
  print_thm_result thm3;
  [%expect
    {|
    P = Q
    Q = R

    ================================

    P = R
    |}]

let%expect_test "mk_comb_simple" =
  let thm =
    let* fg_eq = safe_make_eq f g in
    let* pq_eq = safe_make_eq p q in
    let* thm1 = assume fg_eq in
    let* thm2 = assume pq_eq in
    mk_comb thm1 thm2
  in
  print_thm_result thm;
  [%expect
    {|
      P = Q
      f = g

      ================================

      (f P) = (g Q)
      |}]

let%expect_test "lam_simple" =
  let thm =
    let x = Var ("x", bool_ty) in
    let* thm1 = refl x in
    lam x thm1
  in
  print_thm_result thm;
  [%expect
    {|
    ================================

    (λx. x) = (λx. x)
    |}]

let%expect_test "beta_simple" =
  let thm =
    let id_app = App (Lam (x, App (f, x)), x) in
    beta id_app
  in
  print_thm_result thm;
  [%expect
    {|
    ================================

    ((λx. (f x)) x) = (f x)
    |}]

let%expect_test "eq_mp_simple" =
  let thm =
    let* pq_eq = safe_make_eq p q in
    let* thm1 = assume pq_eq in
    let* thm2 = assume p in
    eq_mp thm1 thm2
  in
  print_thm_result thm;
  [%expect
    {|
    P
    P = Q

    ================================

    Q
    |}]

let%expect_test "deduct_antisym_simple" =
  let thm =
    let* pq_eq = safe_make_eq p q in
    let* thm1 = assume p in
    let* thm2 = assume q in

    let* qp_eq = safe_make_eq q p in
    let* thm_qp = assume qp_eq in
    let* thm_q_gives_p = eq_mp thm_qp thm2 in
    let* thm_pq = assume pq_eq in
    let* thm_p_gives_q = eq_mp thm_pq thm1 in
    deduct_antisym_rule thm_q_gives_p thm_p_gives_q
  in
  print_thm_result thm;
  [%expect
    {|
    P = Q
    Q = P

    ================================

    P = Q
    |}]

let%expect_test "deduct_antisym_reflexive" =
  let thm =
    let* thm1 = assume p in
    let* thm2 = assume p in
    deduct_antisym_rule thm1 thm2
  in
  print_thm_result thm;
  [%expect {|
    ================================

    P = P
    |}]

let s = List.to_seq

let%expect_test "inst_type_simple" =
  let thm =
    let a = TyVar "a" in
    let x_poly = Var ("x", a) in
    let* thm1 = refl x_poly in
    let env = Hashtbl.of_seq (s [ (a, bool_ty) ]) in
    inst_type env thm1
  in
  print_types := true;
  print_thm_result thm;
  print_types := false;
  [%expect
    {|
    ================================

    x :  bool = x :  bool
    |}]

let%expect_test "inst_simple" =
  let thm =
    let* thm1 = refl x in
    inst [ (p, x) ] thm1
  in
  print_thm_result thm;
  [%expect {|
    ================================

    P = P
    |}]

let%expect_test "inst_with_hyps" =
  let thm =
    let* xy_eq = safe_make_eq x y in
    let* thm1 = assume xy_eq in
    inst [ (p, x); (q, y) ] thm1
  in
  print_thm_result thm;
  [%expect {|
    P = Q

    ================================

    P = Q
    |}]

let%expect_test "beta_reduce_combined" =
  let thm =
    let id_app = App (Lam (x, App (f, x)), x) in
    let* thm1 = beta id_app in
    inst [ (p, x) ] thm1
  in
  print_thm_result thm;
  [%expect
    {|
    ================================

    ((λx. (f x)) P) = (f P)
    |}]
