open Kernel
open Result.Syntax

let p = Var ("P", bool_ty)
let q = Var ("Q", bool_ty)
let r = Var ("R", bool_ty)
let f = Var ("f", TyCon ("fun", [ bool_ty; bool_ty ]))
let g = Var ("g", TyCon ("fun", [ bool_ty; bool_ty ]))
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
    let thm1 = _ in
    print_thm_result thm1;
    [%expect {||}]
   
 *)

let%expect_test "assume_simple" =
  let thm1 = assume p in
  print_thm_result thm1;
  [%expect
    {|
    P

    ================================

    P
    |}]

let%expect_test "refl_simple" =
  let thm1 = refl p in
  print_thm_result thm1;
  [%expect
    {|
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
