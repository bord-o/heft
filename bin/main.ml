open Heft
open Tactic
open Grimm
open Auto

(* let () = *)
(*   let%thm goal (a : bool) (b : bool) (c : bool) = a ==> (b ==> (c ==> a)) in *)
(*   let root_tac = pick [ gen; intro; assumption ] in *)
(*   let f = frontier_of_goal root_tac goal in *)
(**)
(*   let rec loop depth = *)
(*     run_proof goal (fun _goal -> search f depth); *)
(*     ignore @@ read_line (); *)
(*     loop (depth + 1) *)
(*   in *)
(*   loop 0 *)

let () =
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

  let rec loop depth =
    run_proof goal (fun _goal -> search f depth);
    ignore @@ read_line ();
    loop (depth + 1)
  in
  loop 0
