open Heft
open Kernel
open Derived
open Tactic

let init () = ()

let%def eqb (a : bool) (b : bool) : bool =
  if a then if b then true else false else if b then false else true

let%def andb (a : bool) (b : bool) : bool =
  if a then if b then true else false else if b then false else false

[@@@ocamlformat "disable"]
let%thm eq_true_intro (p : bool) = p ==> (p = true)
and proof =
  begin
    intros_tac >> eq_true_elim_tac >> assumption_tac
  end [@quiet]
