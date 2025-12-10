open Kernel

let clear_env () =
  Hashtbl.clear the_inductives;
  Hashtbl.clear the_term_constants;
  Hashtbl.clear the_type_constants;
  the_axioms := [];
  the_definitions := []

let print_bool_result r =
  match r with
  | Ok b -> print_endline (string_of_bool b)
  | Error e -> print_endline ("Error: " ^ show_kernel_error e)

let print_induction_thm def =
  match def with
  | Ok d -> print_endline (Printing.pretty_print_thm d.induction)
  | Error e -> print_endline ("Error: " ^ show_kernel_error e)

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
  let () = clear_env () in
  let _ = init () in
  let nat_ty = TyCon ("nat", []) in
  let constructors =
    [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]
  in
  let def = define_inductive "nat" [] constructors in
  print_induction_thm def;
  [%expect
    {|
    ========================================
    ∀P. P Zero ==> ∀n0. P n0 ==> P (Suc n0) ==> ∀x. P x
    |}]

(* Test 2: Polymorphic type - list *)
let%expect_test "list_induction" =
  let () = clear_env () in
  let _ = init () in
  let a = TyVar "a" in
  let list_a = TyCon ("list", [ a ]) in
  let constructors =
    [
      { name = "Nil"; arg_types = [] };
      { name = "Cons"; arg_types = [ a; list_a ] };
    ]
  in
  let def = define_inductive "list" [ "a" ] constructors in
  print_induction_thm def;
  [%expect
    {|
    ========================================
    ∀P. P Nil ==> ∀n0. ∀n1. P n1 ==> P (Cons n0 n1) ==> ∀x. P x
    |}]

(* Test 3: Multiple base cases *)
let%expect_test "bool_like_induction" =
  let () = clear_env () in
  let _ = init () in
  let constructors =
    [ { name = "True"; arg_types = [] }; { name = "False"; arg_types = [] } ]
  in
  let def = define_inductive "bool_like" [] constructors in
  print_induction_thm def;
  [%expect
    {|
    ========================================
    ∀P. P True ==> P False ==> ∀x. P x
    |}]

(* Test 4: Multiple recursive arguments - binary tree *)
let%expect_test "tree_induction" =
  let () = clear_env () in
  let _ = init () in
  let a = TyVar "a" in
  let tree_a = TyCon ("tree", [ a ]) in
  let constructors =
    [
      { name = "Leaf"; arg_types = [] };
      { name = "Node"; arg_types = [ a; tree_a; tree_a ] };
    ]
  in
  let def = define_inductive "tree" [ "a" ] constructors in
  print_induction_thm def;
  [%expect
    {|
    ========================================
    ∀P. P Leaf ==> ∀n0. ∀n1. ∀n2. P n1 ==> P n2 ==> P (Node n0 n1 n2) ==> ∀x. P x
    |}]

(* Test 5: Constructor with only non-recursive args *)
let%expect_test "option_induction" =
  let () = clear_env () in
  let _ = init () in
  let a = TyVar "a" in
  let constructors =
    [ { name = "None"; arg_types = [] }; { name = "Some"; arg_types = [ a ] } ]
  in
  let def = define_inductive "option" [ "a" ] constructors in
  print_induction_thm def;
  [%expect
    {|
    ========================================
    ∀P. P None ==> ∀n0. P (Some n0) ==> ∀x. P x
    |}]

(* Test 6: Verify constructors are registered *)
let%expect_test "constructors_registered" =
  let () = clear_env () in
  let _ = init () in
  let nat_ty = TyCon ("nat", []) in
  let constructors =
    [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]
  in
  let _ = define_inductive "nat" [] constructors in
  let zero_ty = get_const_term_type "Zero" in
  let suc_ty = get_const_term_type "Suc" in
  print_endline
    (match zero_ty with
    | Some _ -> "Zero registered"
    | None -> "Zero NOT registered");
  print_endline
    (match suc_ty with
    | Some _ -> "Suc registered"
    | None -> "Suc NOT registered");
  [%expect {|
    Zero registered
    Suc registered
    |}]

(* Test 7: Reject non-positive type *)
let%expect_test "reject_non_positive" =
  let () = clear_env () in
  let _ = init () in
  let bad_ty = TyCon ("bad", []) in
  let int_ty = TyCon ("int", []) in
  let constructors =
    [ { name = "Bad"; arg_types = [ TyCon ("fun", [ bad_ty; int_ty ]) ] } ]
  in
  let result = define_inductive "bad" [] constructors in
  (match result with
  | Error NotPositive -> print_endline "Correctly rejected non-positive"
  | Error e -> print_endline ("Wrong error: " ^ show_kernel_error e)
  | Ok _ -> print_endline "ERROR: Should have been rejected!");
  [%expect {| Correctly rejected non-positive |}]

(* Test 8: Reject no base case *)
let%expect_test "reject_no_base_case" =
  let () = clear_env () in
  let _ = init () in
  let loop_ty = TyCon ("loop", []) in
  let constructors = [ { name = "Loop"; arg_types = [ loop_ty ] } ] in
  let result = define_inductive "loop" [] constructors in
  (match result with
  | Error NoBaseCase -> print_endline "Correctly rejected no base case"
  | Error e -> print_endline ("Wrong error: " ^ show_kernel_error e)
  | Ok _ -> print_endline "ERROR: Should have been rejected!");
  [%expect {| Correctly rejected no base case |}]

let%expect_test "three_variant_induction" =
  let () = clear_env () in
  let _ = init () in
  let a = TyVar "a" in
  let result_ty = TyCon ("result", [ a ]) in
  let constructors =
    [
      { name = "Ok"; arg_types = [ a ] };
      (* Base case - non-recursive *)
      { name = "Err"; arg_types = [] };
      (* Base case - nullary *)
      { name = "Pending"; arg_types = [ result_ty ] };
      (* Recursive case *)
    ]
  in
  let def = define_inductive "result" [ "a" ] constructors in
  print_induction_thm def;
  [%expect
    {|
    ========================================
    ∀P. P Err ==> ∀n0. P (Ok n0) ==> ∀n0. P n0 ==> P (Pending n0) ==> ∀x. P x
    |}]

(* Test recursion theorems *)

let print_recursion_thm def =
  match def with
  | Ok d -> print_endline (Printing.pretty_print_thm d.recursion)
  | Error e -> print_endline ("Error: " ^ show_kernel_error e)

(* Test 1: Simple monomorphic type - nat *)
let%expect_test "nat_recursion" =
  let () = clear_env () in
  let _ = init () in
  let nat_ty = TyCon ("nat", []) in
  let constructors =
    [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]
  in
  let def = define_inductive "nat" [] constructors in
  print_recursion_thm def;
  [%expect
    {|
    ========================================
    ∀Zero_case. ∀Suc_case. ∃g. g Zero = Zero_case ∧ (∀x0. g (Suc x0) = Suc_case x0 (g x0))
    |}]

(* Test 2: Polymorphic type - list *)
let%expect_test "list_recursion" =
  let () = clear_env () in
  let _ = init () in
  let a = TyVar "a" in
  let list_a = TyCon ("list", [ a ]) in
  let constructors =
    [
      { name = "Nil"; arg_types = [] };
      { name = "Cons"; arg_types = [ a; list_a ] };
    ]
  in
  let def = define_inductive "list" [ "a" ] constructors in
  print_recursion_thm def;
  [%expect
    {|
    ========================================
    ∀Nil_case. ∀Cons_case. ∃g. g Nil = Nil_case ∧ (∀x0. ∀x1. g (Cons x0 x1) = Cons_case x0 x1 (g x1))
    |}]

(* Test 3: Multiple base cases - bool_like *)
let%expect_test "bool_like_recursion" =
  let () = clear_env () in
  let _ = init () in
  let constructors =
    [
      { name = "TrueVal"; arg_types = [] };
      { name = "FalseVal"; arg_types = [] };
    ]
  in
  let def = define_inductive "bool_like" [] constructors in
  print_recursion_thm def;
  [%expect
    {|
    ========================================
    ∀TrueVal_case. ∀FalseVal_case. ∃g. g TrueVal = TrueVal_case ∧ g FalseVal = FalseVal_case
    |}]

(* Test 4: Multiple recursive arguments - binary tree *)
let%expect_test "tree_recursion" =
  let () = clear_env () in
  let _ = init () in
  let a = TyVar "a" in
  let tree_a = TyCon ("tree", [ a ]) in
  let constructors =
    [
      { name = "Leaf"; arg_types = [] };
      { name = "Node"; arg_types = [ a; tree_a; tree_a ] };
    ]
  in
  let def = define_inductive "tree" [ "a" ] constructors in
  print_recursion_thm def;
  [%expect
    {|
    ========================================
    ∀Leaf_case. ∀Node_case. ∃g. g Leaf = Leaf_case ∧ (∀x0. ∀x1. ∀x2. g (Node x0 x1 x2) = Node_case x0 x1 x2 (g x1) (g x2))
    |}]

(* Test 5: Three variants with mixed cases - result *)
let%expect_test "result_recursion" =
  let () = clear_env () in
  let _ = init () in
  let a = TyVar "a" in
  let result_ty = TyCon ("result", [ a ]) in
  let constructors =
    [
      { name = "Ok"; arg_types = [ a ] };
      { name = "Err"; arg_types = [] };
      { name = "Pending"; arg_types = [ result_ty ] };
    ]
  in
  let def = define_inductive "result" [ "a" ] constructors in
  print_recursion_thm def;
  [%expect
    {|
    ========================================
    ∀Ok_case. ∀Err_case. ∀Pending_case. ∃g. (∀x0. g (Ok x0) = Ok_case x0) ∧ g Err = Err_case ∧ (∀x0. g (Pending x0) = Pending_case x0 (g x0))
    |}]

(* Test distinctness theorems *)

let print_distinct_thms def =
  match def with
  | Ok d ->
      List.iter
        (fun thm -> print_endline (Printing.pretty_print_thm thm))
        d.distinct
  | Error e -> print_endline ("Error: " ^ show_kernel_error e)

(* Test 1: Two constructors - nat *)
let%expect_test "nat_distinctness" =
  let () = clear_env () in
  let _ = init () in
  let nat_ty = TyCon ("nat", []) in
  let constructors =
    [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]
  in
  let def = define_inductive "nat" [] constructors in
  print_distinct_thms def;
  [%expect {||}]

(* Test 2: Two constructors - list *)
let%expect_test "list_distinctness" =
  let () = clear_env () in
  let _ = init () in
  let a = TyVar "a" in
  let list_a = TyCon ("list", [ a ]) in
  let constructors =
    [
      { name = "Nil"; arg_types = [] };
      { name = "Cons"; arg_types = [ a; list_a ] };
    ]
  in
  let def = define_inductive "list" [ "a" ] constructors in
  print_distinct_thms def;
  [%expect {||}]

(* Test 3: Three constructors - result *)
let%expect_test "result_distinctness" =
  let () = clear_env () in
  let _ = init () in
  let a = TyVar "a" in
  let result_ty = TyCon ("result", [ a ]) in
  let constructors =
    [
      { name = "Ok"; arg_types = [ a ] };
      { name = "Err"; arg_types = [] };
      { name = "Pending"; arg_types = [ result_ty ] };
    ]
  in
  let def = define_inductive "result" [ "a" ] constructors in
  print_distinct_thms def;
  [%expect {||}]

(* Test 4: Four constructors - multiple pairs *)
let%expect_test "four_constructor_distinctness" =
  let () = clear_env () in
  let _ = init () in
  let constructors =
    [
      { name = "A"; arg_types = [] };
      { name = "B"; arg_types = [] };
      { name = "C"; arg_types = [] };
      { name = "D"; arg_types = [] };
    ]
  in
  let def = define_inductive "four" [] constructors in
  print_distinct_thms def;
  [%expect {||}]

(* Test injectivity theorems *)

let print_injective_thms def =
  match def with
  | Ok d ->
      List.iter
        (fun thm -> print_endline (Printing.pretty_print_thm thm))
        d.injective
  | Error e -> print_endline ("Error: " ^ show_kernel_error e)

(* Test 5: One constructor with one arg - nat *)
let%expect_test "nat_injectivity" =
  let () = clear_env () in
  let _ = init () in
  let nat_ty = TyCon ("nat", []) in
  let constructors =
    [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]
  in
  let def = define_inductive "nat" [] constructors in
  print_injective_thms def;
  [%expect {||}]

(* Test 6: Constructor with multiple args - list *)
let%expect_test "list_injectivity" =
  let () = clear_env () in
  let _ = init () in
  let a = TyVar "a" in
  let list_a = TyCon ("list", [ a ]) in
  let constructors =
    [
      { name = "Nil"; arg_types = [] };
      { name = "Cons"; arg_types = [ a; list_a ] };
    ]
  in
  let def = define_inductive "list" [ "a" ] constructors in
  print_injective_thms def;
  [%expect {||}]

(* Test 7: Constructor with three args - tree *)
let%expect_test "tree_injectivity" =
  let () = clear_env () in
  let _ = init () in
  let a = TyVar "a" in
  let tree_a = TyCon ("tree", [ a ]) in
  let constructors =
    [
      { name = "Leaf"; arg_types = [] };
      { name = "Node"; arg_types = [ a; tree_a; tree_a ] };
    ]
  in
  let def = define_inductive "tree" [ "a" ] constructors in
  print_injective_thms def;
  [%expect {||}]

(* Test 8: Only nullary constructors - no injectivity theorems *)
let%expect_test "no_injectivity" =
  let () = clear_env () in
  let _ = init () in
  let constructors =
    [ { name = "True"; arg_types = [] }; { name = "False"; arg_types = [] } ]
  in
  let def = define_inductive "bool_like" [] constructors in
  print_injective_thms def;
  [%expect {||}]
