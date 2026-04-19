open Heft
open Kernel
open Derived
open Tactic

let () = print_endline "initializing theory functions"
let%def twice (f : 'a -> 'a) (arg : 'a) : 'a = f (f arg)
let%def flip (f : 'a -> 'b -> 'c) (x : 'b) (y : 'a) : 'c = f y x
let%def const (value : 'a) : 'b -> 'a = fun (x : 'b) -> value

let%def compose (f : 'a -> 'b) (g : 'c -> 'a) : 'c -> 'b =
 fun (x : 'c) -> f (g x)

let%thm eq_cong (f : 'a -> 'b) (x : 'a) (y : 'a) = x = y ==> (f x = f y)

and proof =
  begin
    intros >> simp
  end
  [@quiet]
