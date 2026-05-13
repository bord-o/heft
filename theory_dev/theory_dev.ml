[@@@warning "-26-27-32-33"]

open Heft
open Kernel
open Tactic
open Auto
open Effect
open Effect.Deep
(* Note, tell me when a theorem doesn't exist when I expect it to (apply_at) *)

let () =
  print_newline ();
  print_newline ()

let test_goal =
  ([], [%term (a : bool) ==> ((a : bool) ==> (b : bool) ==> (b : bool))])

let test_tactic =
  intro @! "ha" >> intro @! "hab" >> apply_at "hab" >> assumption

let test_tactic_l =
  [ intro @! "ha"; intro @! "hab"; apply_at "hab"; assumption ]

let () = run_proof test_goal test_tactic

type 'a peek = Next_goal of ((thm -> 'a peek) * goal) | Done of thm

let peek tac goal =
  match tac goal with
  | effect Subgoal g, k -> Next_goal ((fun (t : thm) -> continue k t), g)
  | v -> Done v

let s = List.fold_left

(*
w1 : h1 * (fun proof_h1 : thm -> thm) which would be the final step
w2 : h2 * ...
w3 : h3 ...


 *)
