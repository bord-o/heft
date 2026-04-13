open Heft
open Kernel

let () = print_endline "initializing theory options"

[%%inductive type 'a option = None | Some of 'a]

let%def default (opt : 'a option) (value : 'a) : 'a =
  match opt with None -> value | Some v' -> v'

let option_def = Hashtbl.find the_inductives "option"
