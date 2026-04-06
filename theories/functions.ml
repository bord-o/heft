open Heft
open Kernel

let init () = ()
let%def twice (f : 'a -> 'a) (arg : 'a) : 'a = f (f arg)
let%def flip (f : 'a -> 'b -> 'c) (x : 'b) (y : 'a) : 'c = f y x
let%def const (value : 'a) : 'b -> 'a = fun (x : 'b) -> value

let%def compose (f : 'a -> 'b) (g : 'c -> 'a) : 'c -> 'b =
 fun (x : 'c) -> f (g x)
