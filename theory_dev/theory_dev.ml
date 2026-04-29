[@@@warning "-26-27-32-33"]
(* (* [@@@ocamlformat "disable"] *) *)

open Heft
open Tactic
open Auto
open Grimm

let () =
  print_newline ();
  print_newline ()

let () = Printing.print_thm Nats.nat_def.induction

let%thm plus_Suc (m : nat) (n : nat) = plus m (Suc n) = Suc (plus m n)

and proof =
  begin
    noop >> with_rule Nats.nat_def.induction apply
    (* induct >> gen >> simp >> intros >> simp *)
  end
(* [@simp] *)
(* [@quiet] *)
