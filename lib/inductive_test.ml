open Kernel
open Result.Syntax

let print_bool_result r =
  match r with
  | Ok b -> print_endline (string_of_bool b)
  | Error e -> print_endline ("Error: " ^ show_kernel_error e)

let print_induction_thm def =
  match def with
  | Ok d -> 
      print_endline (Printing.pretty_print_thm d.induction)
  | Error e -> 
      print_endline ("Error: " ^ show_kernel_error e)

let nat_ty = TyCon ("nat", [])
let int_ty = TyCon ("int", [])
let bool_ty = TyCon ("bool", [])
let mk_fun_ty a b = TyCon ("fun", [ a; b ])

(* Positivity Tests *)
let%expect_test "positivity_no_recursion" =
  let constructors = [ { name = "Zero"; arg_types = [] } ] in
  print_bool_result (check_positivity "nat" constructors);
  [%expect {| true |}]

(* Direct recursion, no arrows — OK *)
let%expect_test "positivity_direct_recursion" =
  let constructors =
    [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]
  in
  print_bool_result (check_positivity "nat" constructors);
  [%expect {| true |}]

(* Type appears right of arrow — OK *)
let%expect_test "positivity_right_of_arrow" =
  let constructors =
    [
      { name = "Leaf"; arg_types = [] };
      { name = "Branch"; arg_types = [ mk_fun_ty int_ty nat_ty ] };
    ]
  in
  print_bool_result (check_positivity "nat" constructors);
  [%expect {| true |}]

(* Type appears left of arrow — BAD *)
let%expect_test "positivity_left_of_arrow" =
  let constructors =
    [ { name = "Bad"; arg_types = [ mk_fun_ty nat_ty int_ty ] } ]
  in
  print_bool_result (check_positivity "nat" constructors);
  [%expect {| false |}]

(* Type appears left of arrow in nested function — BAD *)
let%expect_test "positivity_nested_left" =
  let constructors =
    [
      {
        name = "Bad";
        arg_types = [ mk_fun_ty (mk_fun_ty nat_ty int_ty) bool_ty ];
      };
    ]
  in
  print_bool_result (check_positivity "nat" constructors);
  [%expect {| false |}]

(* Type appears left in one constructor, OK in another — BAD overall *)
let%expect_test "positivity_mixed" =
  let constructors =
    [
      { name = "Good"; arg_types = [ nat_ty ] };
      { name = "Bad"; arg_types = [ mk_fun_ty nat_ty int_ty ] };
    ]
  in
  print_bool_result (check_positivity "nat" constructors);
  [%expect {| false |}]

(* Multiple args, one bad — BAD *)
let%expect_test "positivity_multiple_args_one_bad" =
  let constructors =
    [
      { name = "Bad"; arg_types = [ int_ty; mk_fun_ty nat_ty bool_ty; nat_ty ] };
    ]
  in
  print_bool_result (check_positivity "nat" constructors);
  [%expect {| false |}]

(* Deeply nested but OK — type only on right *)
let%expect_test "positivity_deeply_nested_ok" =
  let constructors =
    [
      {
        name = "Deep";
        arg_types = [ mk_fun_ty int_ty (mk_fun_ty bool_ty nat_ty) ];
      };
    ]
  in
  print_bool_result (check_positivity "nat" constructors);
  [%expect {| true |}]

(* Base Case Tests *)

(* Has nullary constructor — OK *)
let%expect_test "base_case_nullary" =
  let constructors =
    [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]
  in
  print_bool_result (check_base_case "nat" constructors);
  [%expect {| true |}]

(* Has constructor with only non-recursive args — OK *)
let%expect_test "base_case_non_recursive_args" =
  let constructors =
    [
      { name = "Leaf"; arg_types = [ int_ty ] };
      { name = "Node"; arg_types = [ nat_ty; nat_ty ] };
    ]
  in
  print_bool_result (check_base_case "nat" constructors);
  [%expect {| true |}]

(* All constructors mention type — BAD *)
let%expect_test "base_case_all_recursive" =
  let constructors =
    [
      { name = "A"; arg_types = [ nat_ty ] };
      { name = "B"; arg_types = [ nat_ty; nat_ty ] };
    ]
  in
  print_bool_result (check_base_case "nat" constructors);
  [%expect {| false |}]

(* Type mentioned inside another type constructor — BAD *)
let%expect_test "base_case_nested_mention" =
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let constructors = [ { name = "MkFoo"; arg_types = [ list_nat ] } ] in
  print_bool_result (check_base_case "nat" constructors);
  [%expect {| false |}]

(* Type mentioned in function result — BAD (still mentions it) *)
let%expect_test "base_case_in_function" =
  let constructors =
    [ { name = "MkFoo"; arg_types = [ mk_fun_ty int_ty nat_ty ] } ]
  in
  print_bool_result (check_base_case "nat" constructors);
  [%expect {| false |}]

(* Single nullary constructor — OK *)
let%expect_test "base_case_only_nullary" =
  let constructors = [ { name = "Unit"; arg_types = [] } ] in
  print_bool_result (check_base_case "unit" constructors);
  [%expect {| true |}]

(* Empty constructors list — BAD (no base case) *)
let%expect_test "base_case_empty" =
  let constructors = [] in
  print_bool_result (check_base_case "empty" constructors);
  [%expect {| false |}]


(* Test 1: Simple monomorphic type - nat *)
let%expect_test "nat_induction" =
  let _ = init () in
  let nat_ty = TyCon ("nat", []) in
  let constructors = [
    { name = "Zero"; arg_types = [] };
    { name = "Suc"; arg_types = [nat_ty] };
  ] in
  let def = define_inductive "nat" [] constructors in
  print_induction_thm def;
  [%expect {|
    ========================================
    ∀P. P Zero ==> ∀n0. P n0 ==> P Suc n0 ==> ∀x. P x
    |}]
