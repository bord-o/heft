open Heft
open Kernel

let init () = ()

let%def eqb (a : bool) (b : bool) : bool =
  if a then if b then true else false else if b then false else true

let%def andb (a : bool) (b : bool) : bool =
  if a then if b then true else false else if b then false else false
