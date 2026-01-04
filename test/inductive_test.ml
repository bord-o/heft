open Holinone
open Derived
open Inductive

let print_bool_result b = print_endline (string_of_bool b)

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
  let () = reset () |> Result.get_ok in
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
    ∀P. P Zero ==> (∀n0. P n0 ==> P (Suc n0)) ==> ∀x. P x
    |}]

(* Test 2: Polymorphic type - list *)
let%expect_test "list_induction" =
  let () = reset () |> Result.get_ok in
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
    ∀P. P Nil ==> (∀n0. ∀n1. P n1 ==> P (Cons n0 n1)) ==> ∀x. P x
    |}]

(* Test 3: Multiple base cases *)
let%expect_test "bool_like_induction" =
  let () = reset () |> Result.get_ok in
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
  let () = reset () |> Result.get_ok in
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
    ∀P. P Leaf ==> (∀n0. ∀n1. ∀n2. P n1 ==> P n2 ==> P (Node n0 n1 n2)) ==> ∀x. P x
    |}]

(* Test 5: Constructor with only non-recursive args *)
let%expect_test "option_induction" =
  let () = reset () |> Result.get_ok in
  let a = TyVar "a" in
  let constructors =
    [ { name = "None"; arg_types = [] }; { name = "Some"; arg_types = [ a ] } ]
  in
  let def = define_inductive "option" [ "a" ] constructors in
  print_induction_thm def;
  [%expect
    {|
    ========================================
    ∀P. P None ==> (∀n0. P (Some n0)) ==> ∀x. P x
    |}]

(* Test 6: Verify constructors are registered *)
let%expect_test "constructors_registered" =
  let () = reset () |> Result.get_ok in
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
  let () = reset () |> Result.get_ok in
  let bad_ty = TyCon ("bad", []) in
  let int_ty = TyCon ("int", []) in
  let constructors =
    [ { name = "Bad"; arg_types = [ TyCon ("fun", [ bad_ty; int_ty ]) ] } ]
  in
  let result = define_inductive "bad" [] constructors in
  (match result with
  | Error `NotPositive -> print_endline "Correctly rejected non-positive"
  | Error e -> print_endline ("Wrong error: " ^ show_kernel_error e)
  | Ok _ -> print_endline "ERROR: Should have been rejected!");
  [%expect {| Correctly rejected non-positive |}]

(* Test 8: Reject no base case *)
let%expect_test "reject_no_base_case" =
  let () = reset () |> Result.get_ok in
  let loop_ty = TyCon ("loop", []) in
  let constructors = [ { name = "Loop"; arg_types = [ loop_ty ] } ] in
  let result = define_inductive "loop" [] constructors in
  (match result with
  | Error `NoBaseCase -> print_endline "Correctly rejected no base case"
  | Error e -> print_endline ("Wrong error: " ^ show_kernel_error e)
  | Ok _ -> print_endline "ERROR: Should have been rejected!");
  [%expect {| Correctly rejected no base case |}]

let%expect_test "three_variant_induction" =
  let () = reset () |> Result.get_ok in
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
    ∀P. P Err ==> (∀n0. P (Ok n0)) ==> (∀n0. P n0 ==> P (Pending n0)) ==> ∀x. P x
    |}]

(* Test recursion theorems *)

let print_recursion_thm def =
  match def with
  | Ok d -> print_endline (Printing.pretty_print_thm d.recursion)
  | Error e -> print_endline ("Error: " ^ show_kernel_error e)

(* Test 1: Simple monomorphic type - nat *)
let%expect_test "nat_recursion" =
  let () = reset () |> Result.get_ok in
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
  let () = reset () |> Result.get_ok in
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
  let () = reset () |> Result.get_ok in
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
  let () = reset () |> Result.get_ok in
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
  let () = reset () |> Result.get_ok in
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
  let () = reset () |> Result.get_ok in
  let nat_ty = TyCon ("nat", []) in
  let constructors =
    [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]
  in
  let def = define_inductive "nat" [] constructors in
  print_distinct_thms def;
  [%expect
    {|
    ========================================
    ∀y0. ¬Zero = Suc y0
    |}]

(* Test 2: Two constructors - list *)
let%expect_test "list_distinctness" =
  let () = reset () |> Result.get_ok in
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
  [%expect
    {|
    ========================================
    ∀y0. ∀y1. ¬Nil = Cons y0 y1
    |}]

(* Test 3: Three constructors - result *)
let%expect_test "result_distinctness" =
  let () = reset () |> Result.get_ok in
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
  [%expect
    {|
    ========================================
    ∀y0. ¬Err = Pending y0
    ========================================
    ∀x0. ∀y0. ¬Ok x0 = Pending y0
    ========================================
    ∀x0. ¬Ok x0 = Err
    |}]

(* Test 4: Four constructors - multiple pairs *)
let%expect_test "four_constructor_distinctness" =
  let () = reset () |> Result.get_ok in
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
  [%expect
    {|
    ========================================
    ¬C = D
    ========================================
    ¬B = D
    ========================================
    ¬B = C
    ========================================
    ¬A = D
    ========================================
    ¬A = C
    ========================================
    ¬A = B
    |}]

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
  let () = reset () |> Result.get_ok in
  let nat_ty = TyCon ("nat", []) in
  let constructors =
    [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]
  in
  let def = define_inductive "nat" [] constructors in
  print_injective_thms def;
  [%expect
    {|
    ========================================
    ∀x0. ∀y0. Suc x0 = Suc y0 ==> x0 = y0
    |}]

(* Test 6: Constructor with multiple args - list *)
let%expect_test "list_injectivity" =
  let () = reset () |> Result.get_ok in
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
  [%expect
    {|
    ========================================
    ∀x0. ∀x1. ∀y0. ∀y1. Cons x0 x1 = Cons y0 y1 ==> x0 = y0 ∧ x1 = y1
    |}]

(* Test 7: Constructor with three args - tree *)
let%expect_test "tree_injectivity" =
  let () = reset () |> Result.get_ok in
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
  [%expect
    {|
    ========================================
    ∀x0. ∀x1. ∀x2. ∀y0. ∀y1. ∀y2. Node x0 x1 x2 = Node y0 y1 y2 ==> x0 = y0 ∧ x1 = y1 ∧ x2 = y2
    |}]

(* Test 8: Only nullary constructors - no injectivity theorems *)
let%expect_test "no_injectivity" =
  let () = reset () |> Result.get_ok in
  let constructors =
    [ { name = "True"; arg_types = [] }; { name = "False"; arg_types = [] } ]
  in
  let def = define_inductive "bool_like" [] constructors in
  print_injective_thms def;
  [%expect {||}]

(* let%expect_test "test inductive nats" = *)
(*   (* let () = clear_env () in *) *)
(*   let _ = init_types () in *)
(*   let thm = *)
(*     let* plus_def = plus_def in *)
(*     let nat_ind = Hashtbl.find_opt the_inductives "nat" |> Option.get in *)
(*     let suc = nat_ind.constructors |> List.assoc_opt "Suc" |> Option.get in *)
(*     let zero = nat_ind.constructors |> List.assoc_opt "Zero" |> Option.get in *)
(**)
(*     let* one = make_app suc zero in *)
(**)
(*     let* zcase = conj_left plus_def in *)
(*     let* succase = conj_right plus_def in *)
(**)
(*     let plus_name, plus_ty = *)
(*       the_term_constants |> Hashtbl.to_seq *)
(*       |> Seq.find (fun (n, _) -> n = "plus") *)
(*       |> Option.get *)
(*     in *)
(*     let plus = Const (plus_name, plus_ty) in *)
(**)
(*     (*lets try to prove that 1 + 1 = 2 *) *)
(*     let* inst_suc_case = spec zero succase in *)
(*     let* zcase_applied = ap_thm zcase one in *)
(*     let* zcase_reduc = conv_equality deep_beta zcase_applied in *)
(*     let* suc_both = ap_term suc zcase_reduc in *)
(*     let* applied = ap_thm inst_suc_case one in *)
(*     let* reduc = conv_equality deep_beta applied in *)
(*     let* _t = trans reduc suc_both in *)
(*     (* not so bad *) *)
(**)
(*     (* how about comm? *) *)
(*     (* plus a b = plus b a*) *)
(*     let a = make_var "a" nat_ind.ty in *)
(*     let b = make_var "b" nat_ind.ty in *)
(*     let n = make_var "n" nat_ind.ty in *)
(*     let n' = make_var "n'" nat_ind.ty in *)
(**)
(*     let* plus_a = make_app plus a in *)
(*     let* plus_ab = make_app plus_a b in *)
(**)
(*     let* plus_b = make_app plus b in *)
(*     let* plus_ba = make_app plus_b a in *)
(*     let* _goal = safe_make_eq plus_ab plus_ba in *)
(**)
(*     (*need lemmas*) *)
(*     let* plus_n = make_app plus n in *)
(*     let* plus_nZ = make_app plus_n zero in *)
(*     let* goal = safe_make_eq plus_nZ n in *)
(*     let* induction_inst = make_lam n goal in *)
(*     (* pp_term induction_inst; *) *)
(**)
(*     let type_inst = *)
(*       [ (make_vartype "r", nat_ind.ty) ] |> List.to_seq |> Hashtbl.of_seq *)
(*     in *)
(*     let* typed_induction_thm = inst_type type_inst nat_ind.induction in *)
(*     (* print_endline @@ pretty_print_thm ~with_type:true zcase; *) *)
(*     (* print_endline @@ pretty_print_thm ~with_type:true succase; *) *)
(*     (* print_endline @@ pretty_print_thm ~with_type:true typed_induction_thm; *) *)
(**)
(*     let* inst_induction = spec induction_inst typed_induction_thm in *)
(*     (* pp_thm inst_induction;  *) *)
(*     (* *)
(*       plus Zero Zero = Zero ==>  *)
(*       (∀n0. plus n0 Zero = n0 ==> plus (Suc n0) Zero = Suc n0) ==>  *)
(*       ∀x. plus x Zero = x *)
(*        *) *)
(*     (* start with base case *) *)
(*     let* zz = ap_thm zcase zero in *)
(*     let* rzz = conv_equality deep_beta zz in *)
(*     (*done*) *)
(*     let* first_discharged = mp inst_induction rzz in *)
(*     pp_thm first_discharged; *)
(**)
(*     let* ih_assm = assume @@ imp_left_term (concl first_discharged) in *)
(*     let* specced_ih = spec n' ih_assm in *)
(**)
(*     let ih_term = imp_left_term (concl specced_ih) in *)
(*     let step_term = imp_right_term (concl specced_ih) in *)
(*     pp_term ih_term; *)
(*     pp_term step_term; *)
(*     (* start the proof *) *)
(*     let* assm_ih = assume ih_term in *)
(*     let* this_scase = spec n' succase in *)
(*     pp_thm this_scase; *)
(*     let* ap2 = ap_thm this_scase zero in *)
(*     pp_thm ap2; *)
(*     let* reduc_ap2 = conv_equality deep_beta ap2 in *)
(*     pp_thm reduc_ap2; *)
(**)
(*     let* ap_ih = ap_term suc assm_ih in *)
(*     pp_thm ap_ih; *)
(**)
(*     let* th1 = trans reduc_ap2 ap_ih in *)
(*     pp_thm th1; *)
(**)
(*     let* th1_imp = disch ih_term th1 in *)
(*     pp_thm th1_imp; *)
(**)
(*     let* gen_th1 = gen n' th1_imp in *)
(*     pp_thm gen_th1; *)
(**)
(*     let* th2 = mp first_discharged gen_th1 in *)
(*     pp_thm th2; *)
(**)
(*     (* woohoo *) *)
(*     Ok truth *)
(*   in *)
(**)
(*   print_thm_result thm; *)
(*   [%expect *)
(*     {| *)
(*     ======================================== *)
(*     (∀n0. plus n0 Zero = n0 ==> plus (Suc n0) Zero = Suc n0) ==> ∀x. plus x Zero = x *)
(**)
(*     plus n' Zero = n' *)
(**)
(*     plus (Suc n') Zero = Suc n' *)
(**)
(*     ======================================== *)
(*     plus (Suc n') = (λn. Suc (plus n' n)) *)
(**)
(*     ======================================== *)
(*     plus (Suc n') Zero = (λn. Suc (plus n' n)) Zero *)
(**)
(*     ======================================== *)
(*     plus (Suc n') Zero = Suc (plus n' Zero) *)
(**)
(*     plus n' Zero = n' *)
(*     ======================================== *)
(*     Suc (plus n' Zero) = Suc n' *)
(**)
(*     plus n' Zero = n' *)
(*     ======================================== *)
(*     plus (Suc n') Zero = Suc n' *)
(**)
(*     ======================================== *)
(*     plus n' Zero = n' ==> plus (Suc n') Zero = Suc n' *)
(**)
(*     ======================================== *)
(*     ∀n'. plus n' Zero = n' ==> plus (Suc n') Zero = Suc n' *)
(**)
(*     ======================================== *)
(*     ∀x. plus x Zero = x *)
(**)
(*     ======================================== *)
(*     T *)
(*     |}] *)

(* let prg = *)
(*   {| *)
(* (type list ('a) *)
(*     (Nil) *)
(*     (Cons ('a (list 'a)))) *)
(**)
(* (type nat () *)
(*     (Z) *)
(*     (S (nat))) *)
(**)
(* (fun length (-> (list 'a) nat) *)
(*     ( (Nil) Z) *)
(*     ( ((Cons x xs)) (S (length xs)))) *)
(**)
(* (fun append (-> (list 'a) (-> (list 'a) (list 'a))) *)
(*     ( (Nil l) l) *)
(*     ( ((Cons x xs) l) (Cons x (append xs l)))) *)
(* |} *)
(**)
(* (* *)
(* forall n: 'a, l: list 'a, length (append n l) = S (length l) *)
(*  *) *)
(* let%expect_test "list" = *)
(*   let () = Elaborator.parse_and_elaborate prg in *)
(*   let goal = *)
(*     let a = TyVar "'a" in *)
(*     let list_a = TyCon ("list", [ a ]) in *)
(*     let nat_ty = TyCon ("nat", []) in *)
(**)
(*     let n = make_var "n" a in *)
(*     let l = make_var "l" list_a in *)
(**)
(*     let length_ty = make_fun_ty list_a nat_ty in *)
(*     let length = Const ("length", length_ty) in *)
(**)
(*     let cons_ty = make_fun_ty a (make_fun_ty list_a list_a) in *)
(*     let cons = Const ("Cons", cons_ty) in *)
(**)
(*     let s_ty = make_fun_ty nat_ty nat_ty in *)
(*     let s = Const ("S", s_ty) in *)
(**)
(*     let* cons_n = make_app cons n in *)
(*     let* cons_n_l = make_app cons_n l in *)
(**)
(*     let* lhs = make_app length cons_n_l in *)
(**)
(*     let* length_l = make_app length l in *)
(**)
(*     let* rhs = make_app s length_l in *)
(**)
(*     let* eq = safe_make_eq lhs rhs in *)
(**)
(*     let* pred_lam = make_lam l eq in *)
(**)
(*     let s = Hashtbl.find the_specifications "length" in *)
(*     pp_thm s; *)
(**)
(*     let d = Hashtbl.find the_inductives "list" in *)
(*     let list_induct = d.induction in *)
(*     pp_thm d.induction; *)
(**)
(*     let* specd = spec pred_lam list_induct in *)
(**)
(*     Ok specd *)
(*   in *)
(*   Derived_test.print_thm_result goal; *)
(**)
(*   [%expect *)
(*     {| *)
(*       ======================================== *)
(*       length Nil = Z ∧ (∀x0. ∀x1. length (Cons x0 x1) = S (length x1)) *)
(**)
(*       ======================================== *)
(*       ∀P. P Nil ==> (∀n0. ∀n1. P n1 ==> P (Cons n0 n1)) ==> ∀x. P x *)
(**)
(*       ======================================== *)
(*       length (Cons n Nil) = S (length Nil) ==> (∀n0. ∀n1. length (Cons n n1) = S (length n1) ==> length (Cons n (Cons n0 n1)) = S (length (Cons n0 n1))) ==> ∀x. length (Cons n x) = S (length x) *)
(*       |}] *)
