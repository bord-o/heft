open Heft
open Kernel

let%expect_test "basic transformation" =
  let (t : term) = [%term (test : nat list)] in
  let s = (Printing.pretty_print_hol_term ~with_type:true t) in
  print_endline s;
  [%expect {| test:(nat list) |}]
