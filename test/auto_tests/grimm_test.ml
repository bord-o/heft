open Heft
open Grimm
open Tactic
open Auto

let%expect_test "expansion" =
  let%thm goal (a : bool) (b : bool) (c : bool) = a ==> (b ==> (c ==> a)) in
  let root_tac = pick [ gen; intro; assumption ] in
  let f = frontier_of_goal root_tac goal in

  run_proof goal (fun _goal -> search f 20);
  [%expect
    {|
    |}]

(* let%expect_test "expansion" = *)
(*   let%thm goal (a : bool) (b : bool) (c : bool) (d : bool) = *)
(*     ((a || b) && (c || d)) ==> ((a && c) || (a && d) || (b && c) || (b && d)) *)
(*   in *)
(*   let f = frontier_of_goal ctauto goal in *)
(**)
(*   run_proof goal (fun _goal -> *)
(*     search f 200; *)
(*   ); *)
(*   [%expect {| *)
(*       |}] *)

let%expect_test "expansion" =
  let open Kernel in
  let open Derived in
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let goal =
    ( [],
      make_imp
        (make_disj p (make_conj q r))
        (make_conj (make_disj p q) (make_disj p r)) )
  in
  let f = frontier_of_goal ctauto goal in

  run_proof goal (fun _goal -> search f 1000);
  [%expect
    {|
    ========================================
    P ∨ Q ∧ R ==> P ∨ Q ∧ P ∨ R

    Proof Complete!
    with fuel: 1593
    |}]
