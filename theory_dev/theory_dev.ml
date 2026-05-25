[@@@warning "-26-27-32-33"]

open Heft
open Kernel
open Tactic
open Auto
open Rubiks

let () =
  print_newline ();
  print_newline ()

let%def test_match (x : nat option) : nat =
  match x with Some n -> n | None -> 0n

(* let%primrec try_each (choices : 'a list) (f : 'a -> 'b option) : 'b option = *)
(*   match choices with *)
(*   | [] -> None *)
(*   | c :: cs -> ( *)
(*       match ((f c) : 'b option) with *)
(*       | Some r -> Some r *)
(*       | None -> try_each cs f) *)

(* let%def all_moves : move list = [ *)
(*   Move (FaceU, CW); Move (FaceU, CCW); Move (FaceU, Half); *)
(*   Move (FaceD, CW); Move (FaceD, CCW); Move (FaceD, Half); *)
(*   Move (FaceL, CW); Move (FaceL, CCW); Move (FaceL, Half); *)
(*   Move (FaceR, CW); Move (FaceR, CCW); Move (FaceR, Half); *)
(*   Move (FaceF, CW); Move (FaceF, CCW); Move (FaceF, Half); *)
(*   Move (FaceB, CW); Move (FaceB, CCW); Move (FaceB, Half); *)
(* ] *)
(**)
(* let%primrec dfs (depth : nat) (c : cube) : move list option = *)
(*   match depth with *)
(*   | Zero -> *)
(*       if cube_eq c solved_cube then Some [] else None *)
(*   | Succ n -> *)
(*       if cube_eq c solved_cube then Some [] *)
(*       else *)
(*         try_each all_moves (fun (m : move) -> *)
(*           match (dfs n (apply_move m c) : move list option) with *)
(*           | Some ms -> Some (m :: ms) *)
(*           | None -> None) *)
(**)
(* let%primrec iddfs (max_depth : nat) (c : cube) : move list option = *)
(*   match max_depth with *)
(*   | Zero -> dfs Zero c *)
(*   | Succ n -> ( *)
(*       match (iddfs n c : move list option) with *)
(*       | Some ms -> Some ms *)
(*       | None -> dfs (Succ n) c) *)
