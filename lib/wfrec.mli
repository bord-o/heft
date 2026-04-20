open Kernel

val prove_wf_measure : name:string -> unit

val prove_wf_rec_existence :
  name:string -> arg_type:hol_type -> ret_type:hol_type -> unit

val introduce_fixpoint : name:string -> unit
val define_wfrec : name:string -> arg_type:hol_type -> ret_type:hol_type -> unit
