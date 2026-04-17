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

let%thm wf_rec_rel_total (r : 'a -> 'a -> bool) (h : ('a -> 'b) -> 'a -> 'b)
    (x : 'a) =
  wf r ==> exists (fun (v : 'b) -> wf_rec_rel r h x v)

and proof =
  begin
    zero_tac >> with_repeat gen_tac >> intro_tac @! "hwf" >> simp_asm_tac
    >> spec_asm_tac
         [%term
           fun (x : 'a) ->
             exists (fun (v : 'b) ->
                 wf_rec_rel
                   (r : 'a -> 'a -> bool)
                   (h : ('a -> 'b) -> 'a -> 'b)
                   x v)]
       @! "hIH"
    >> generalize_tac [%term (x : 'a)]
    >> apply_at_tac "hIH" >> intros_tac @! "hprem"
  end
(* [@trace] *)
(* [@quiet] *)

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
