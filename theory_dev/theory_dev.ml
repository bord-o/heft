[@@@warning "-26-27-32-33"]

open Heft
open Kernel
open Tactic
open Auto
open Rubiks

let () =
  print_newline ();
  print_newline ()

let%primrec try_each (choices : 'a list) (f : 'a -> 'b option) : 'b option =
  match choices with
  | [] -> None
  | c :: cs -> (
      match ((f c) : 'b option) with
      | None -> try_each cs f
      | Some r -> Some r
      )

let%def all_moves : move list = [
  Move (FaceU, CW); Move (FaceU, CCW); Move (FaceU, Half);
  Move (FaceD, CW); Move (FaceD, CCW); Move (FaceD, Half);
  Move (FaceL, CW); Move (FaceL, CCW); Move (FaceL, Half);
  Move (FaceR, CW); Move (FaceR, CCW); Move (FaceR, Half);
  Move (FaceF, CW); Move (FaceF, CCW); Move (FaceF, Half);
  Move (FaceB, CW); Move (FaceB, CCW); Move (FaceB, Half);
]

let%primrec dfs (depth : nat) (c : cube) : move list option =
  match depth with
  | Zero ->
      if c  = solved_cube then Some [] else None
  | Suc n ->
      if c  = solved_cube then Some []
      else
        try_each all_moves (fun (m : move) ->
          match (dfs n (apply_move m c) : move list option) with
          | None -> None
          | Some ms -> Some (m :: ms)
          )

let%primrec iddfs (max_depth : nat) (c : cube) : move list option =
  match max_depth with
  | Zero -> dfs Zero c
  | Suc n -> (
      match (iddfs n c : move list option) with
      | None -> dfs (Suc n) c
      | Some ms -> Some ms)



let%thm search1 = 
    iddfs 0n (solved_cube) = Some []
and proof = begin
    simp
    >> rewrite_at "refl_eq_true"
    >> simp
end
[@quiet]
  
let%thm search2 = 
    iddfs 0n (move_U solved_cube) = None
and proof = begin
    simp
    >> cond /: ["heqt"; "heqf"]
    >> eq_true_elim_asm /!"heq"
    >> with_first @@ with_rules cube_def.injective (apply_asm)
    >> elim_conj_asm
    >> with_repeat (with_first @@ with_rules corners_def.injective (apply_asm))
    >> with_repeat elim_conj_asm
end

(* [@trace] *)
(* [@quiet] *)
