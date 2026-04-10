open Kernel
(* Tactic uses this to initialize rules with different tactics *)

let definitions : (string * thm list) list ref = ref []
let simps : (string * thm list) list ref = ref []
let proven : (string * thm) list ref = ref []

let add_simp name thm =
  match Rewrite.rules_of_def thm with
  | Ok thms -> simps := (name, thms) :: !simps
  | Error _e -> ()

let add_def name thm =
  match Rewrite.rules_of_def thm with
  | Ok thms -> definitions := (name, thms) :: !definitions
  | Error _e -> ()

let add_proven name thm = proven := (name, thm) :: !proven
let get_proven name = List.assoc_opt name !proven
let get_def name = List.assoc_opt name !definitions
