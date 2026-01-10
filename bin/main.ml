open Holinone
open Derived
open Tactic

let () =
  let a = make_var "A" bool_ty in
  let b = make_var "B" bool_ty in
  let goal = make_conj a b in

  let next_tactic =
    next_tactic_of_list
    @@ wrap_all with_no_trace [ conj_tac; assumption_tac; assumption_tac ]
  in
  match prove ([ a; b ], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g
