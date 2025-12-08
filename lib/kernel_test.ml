open Kernel

let p = Var ("P", bool_ty)
let q = Var ("Q", bool_ty)
let f = Var ("f", TyCon ("fun", [bool_ty; bool_ty]))
let g = Var ("g", TyCon ("fun", [bool_ty; bool_ty]))

let print_term = 
    Fun.compose print_endline show_term

let print_thm =
    Fun.compose print_endline show_thm

let print_thm_result =
    Format.pp_print_result ~ok:pp_thm ~error:pp_kernel_error Format.std_formatter

let print_term_result =
    Format.pp_print_result ~ok:pp_term ~error:pp_kernel_error Format.std_formatter

let%expect_test "assume_simple" =
    let thm1 = assume p in
    print_thm_result thm1;
    [%expect {|
      (Sequent ([(Var ("P", (TyCon ("bool", []))))],
         (Var ("P", (TyCon ("bool", []))))))
      |}]
