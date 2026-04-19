open Heft
open Kernel
open Derived
open Tactic

let () = print_endline "initializing theory bools"

let%def eqb (a : bool) (b : bool) : bool =
  if a then if b then true else false else if b then false else true

let%def andb (a : bool) (b : bool) : bool =
  if a then if b then true else false else if b then false else false

[@@@ocamlformat "disable"]
let%thm eq_true_intro (p : bool) = p ==> (p = true)
and proof =
  begin
    intros_tac >> eq_true_elim_tac >> assumption
  end [@quiet]

(* Just an alias that uses the lower level axiom *)
let%thm axiom_of_choice (p : 'a -> bool) =
  exists (fun (x : 'a) -> p x) ==> p (choose (fun (y : 'a) -> p y))

and proof =
  begin
    with_first (with_axioms exact_tac)
  end
  [@quiet]
