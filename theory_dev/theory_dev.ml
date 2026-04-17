[@@@warning "-26-27-32-33"]

open Heft
open Kernel
open Derived
open Tactic
open Auto

let () =
  print_newline ();
  print_newline ()

(* [@@@ocamlformat "disable"] *)

let%thm wf_rec_rel_elim (r : 'a -> 'a -> bool) (h : ('a -> 'b) -> 'a -> 'b)
    (x : 'a) (v : 'b) =
  wf_rec_rel r h x v
  ==> exists (fun (g : 'a -> 'b) ->
      forall (fun (y : 'a) -> r y x ==> wf_rec_rel r h y (g y)) && v = h g x)

and proof =
  begin
    intros_tac @! "hwf" >> simp_asm_tac
  end
  [@quiet]

(* let%thm wf_rec_rel_functional (r : 'a -> 'a -> bool) *)
(*     (h : ('a -> 'b) -> 'a -> 'b) (x : 'a) (v : 'b) (v' : 'b) = *)
(*   wf r *)
(*   ==> (wf_rec_cong r h *)
(*       ==> (wf_rec_rel r h x v ==> (wf_rec_rel r h x v' ==> (v = v')))) *)
(**)
(* and proof = *)
(*   begin *)
(*     sorry_tac *)
(*   end *)
(*   [@quiet] *)
(**)
(* let%thm wf_rec_rel_total (r : 'a -> 'a -> bool) (h : ('a -> 'b) -> 'a -> 'b) *)
(*     (x : 'a) = *)
(*   wf r ==> exists (fun (v : 'b) -> wf_rec_rel r h x v) *)
(**)
(* and proof = *)
(*   begin *)
(*     sorry_tac *)
(*   end *)
(*   [@quiet] *)
(**)
(* let%thm wf_rec (r : 'a -> 'a -> bool) (h : ('a -> 'b) -> 'a -> 'b) = *)
(*   wf r *)
(*   ==> (wf_rec_cong r h *)
(*       ==> exists (fun (f : 'a -> 'b) -> forall (fun (x : 'a) -> f x = h f x))) *)
(**)
(* and proof = *)
(*   begin *)
(*     sorry_tac *)
(*   end *)
(*   [@quiet] *)
(**)
