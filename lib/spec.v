From Stdlib Require Import List.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.
Import ListNotations.

Fixpoint intercalate {X : Type} (sep : X) (l : list X) :=
  match l with
  | [] => []
  | [x] => [x]
  | x::xs => x :: sep :: intercalate sep xs
  end.

Example intercalate_ex1 : intercalate 0 [1; 2; 3]  = [1; 0; 2; 0; 3] .
Proof.
simpl. reflexivity.
Qed.

Theorem intercalate_correct1 {X : Type} (sep : X) (l : list X) 
  : length (intercalate sep l) = length l + (length l - 1).
Proof.
  induction l.
  - simpl. reflexivity.
  - sauto lq:on.
Qed.



(*let rec intercalate sep = function*)
(*    [] -> []*)
(*    | x::xs -> x :: sep :: intercalate sep xs*)
