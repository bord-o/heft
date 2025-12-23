
let elaborate _ = failwith "TODO"

(* let rec elaborate = function *)
(*   | [] -> Ok () *)
(*   | TypeDef td :: defs -> *)
(*       let* _ = hol_of_type_def td in *)
(*       elaborate defs *)
(*   | Def d :: defs -> *)
(*       let* _ = hol_of_def d in *)
(*       elaborate defs *)
(*   | Fun fd :: defs -> *)
(*       let* _ = hol_of_fun_def fd in *)
(*       elaborate defs *)
(*   | Theorem t :: defs -> *)
(*       let* _ = hol_of_theorem t in *)
(*       elaborate defs *)
