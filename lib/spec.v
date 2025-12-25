From Stdlib Require Import List.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.
Import ListNotations.
Require Import Nat.
Require Import Lia.

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

(* induction helpers *)
Fixpoint pairs {X : Type} (l: list X) :=
  match l with
  | [] => []
  | x::xs => 
      (let pairs_with_x := List.map (fun y => (x, y)) xs in
      pairs_with_x ++ pairs xs)
  end.

Eval vm_compute in length (pairs [1; 2; 3; 4; 5; 6; 7; 8; 9]).
(* len pairs squared - len pairs over two*)

Example pairs_ex1 : pairs [1; 2; 3] = [(1, 2); (1, 3); (2, 3)].
Proof.
  simpl. reflexivity. 
Qed.

Lemma pairs_cons {X : Type} (l : list X) (x : X)
  : length (pairs (x :: l)) = length l + length (pairs l).
Proof.
  induction l.
  - simpl. auto.
  - simpl. apply f_equal. 
    repeat rewrite length_app.
    repeat rewrite length_map.
    reflexivity.
Qed.
    
Theorem pairs_correct1 {X : Type} (l : list X) 
  : (2 * length (pairs l)) = ((length l) * (length l - 1)) .
Proof.
  induction l.
  - simpl. auto.
  - rewrite pairs_cons.
    simpl.
    rewrite PeanoNat.Nat.sub_0_r.
    destruct (length l) as [|n].
    * simpl in *. exact IHl.
    * simpl. lia.
Qed.



