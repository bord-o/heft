open Heft
open Kernel
open Derived
open Tactic
(* open Auto *)

let () =
  print_newline ();
  print_newline ()

[@@@warning "-26-27-32-33"]
(* [@@@ocamlformat "disable"] *)

let%thm wf_rec (r : 'a -> 'a -> bool) =
  wf r
  ==> forall (fun (h : ('a -> 'b) -> 'a -> 'b) ->
      forall (fun (f : 'a -> 'b) (g : 'a -> 'b) (x : 'a) ->
          forall (fun (z : 'a) -> r z x ==> (f z = g z)) ==> (h f x = h g x))
      ==> exists (fun (f : 'a -> 'b) -> forall (fun (x : 'a) -> f x = h f x)))

and proof =
  begin
    intros_tac @: [ "hwf"; "himp" ] >> sorry_tac
  end
  [@quiet]

let () = ()
