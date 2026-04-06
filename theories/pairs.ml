open Heft
open Kernel

let init () = ()

[%%inductive type ('a, 'b) pair = Pair of 'a * 'b]

let%def fst (x : ('a, 'b) pair) : 'a = match x with Pair (l, r) -> l
let _ = fst
let fst = make_const "fst" [] |> Result.get_ok
let%def snd (x : ('a, 'b) pair) : 'a = match x with Pair (l, r) -> r
let _ = snd
let snd = make_const "snd" [] |> Result.get_ok
