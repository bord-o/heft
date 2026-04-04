open Kernel
(* Tactic uses this to initialize rules with different tactics *)

(*
Sometimes I want to rewrite with all definitions, other times I want only a certain rewrite or lemma
Should rewrites and lemmas be separate?
*)

let definitions : (string * thm) list ref = ref []
let simps : (string * thm) list ref = ref []
let proven : (string * thm) list ref = ref []
let add_simp name thm = simps := (name, thm) :: !simps
let add_def name thm = definitions := (name, thm) :: !definitions
let add_proven name thm = proven := (name, thm) :: !proven
let get_proven name = List.assoc_opt name !proven
let get_def name = List.assoc_opt name !definitions

(* TODO: 
    make rule bases of type (string * thm list) list ref so that we can preprocess conjunctions and foralls to avoid doing it at the tactic site
 *)
