(* [@@@warning "-26-27-32-33"] *)

open Heft
open Kernel
open Tactic
open Auto
(* open Rubiks *)

let () =
  print_newline ();
  print_newline ()

(*
  lemma assumes p: P
  and pq: "P ⟹ Q"
  and pr: "P ⟹ R"
  and rqs: "R ⟹ Q ⟹ S"
  and st: "S ⟹ T"
shows T
proof -
  presume S
  thus T using st by simp
next
  presume "R ∧ Q"
  thus S using rqs by simp
next
  show "R ∧ Q" using pr pq p by simp
qed
   *)

let%thm lemma (p : bool) (q : bool) (r : bool) (s : bool) (t : bool) =
  p ==> (p ==> q ==> (p ==> r ==> (r ==> (q ==> s) ==> (s ==> t ==> t))))

and proof =
  begin
    intros @: [ "hp"; "hpq"; "hpr"; "hrqs"; "hst" ]
    >> apply_at "hst"
    >> apply_at "hpr" ~target:"hp" @! "hr"
    >> apply_at "hpq" ~target:"hp" @! "hq"
    >> apply_at "hrqs" ~target:"hr" @! "hqs"
    >> apply_at "hqs" ~target:"hq" @! "s"
    >> assumption
  end
  (* [@trace] *)
  [@quiet]

let%primrec list_length (l : 'a list) : nat =
  match l with [] -> 0n | x :: xs -> Suc (list_length xs)

let%def this_length (l : 'a list) : nat = list_length l

let%thm lemma (l : 'a list) = list_length l = this_length l

and proof =
  begin
    noop >> gen >> simp
  end
  [@quiet]
