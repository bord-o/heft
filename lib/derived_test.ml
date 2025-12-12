open Kernel
open Derived
open Printing
open Result.Syntax

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
  [%expect {| |}]

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
  [%expect {| |}]
