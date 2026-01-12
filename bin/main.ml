open Holinone
open Derived
open Tactic
open Inductive

let err = Result.get_ok

let () =
  let a = make_var "A" bool_ty in
  let nat_def =
    let nat_ty = TyCon ("nat", []) in
    define_inductive "nat" []
      [
        { name = "Zero"; arg_types = [] };
        { name = "Suc"; arg_types = [ nat_ty ] };
      ]
    |> err
  in
  let x = make_var "x" nat_def.ty in

  let goal = make_forall x (make_imp a a) in

  let next_tactic =
    next_tactic_of_list
      [
        with_first_success_choice induct_tac;
        intro_tac;
        assumption_tac;
        gen_tac;
        intro_tac;
        assumption_tac;
      ]
  in
  match prove ([], goal) next_tactic with
  | Complete thm ->
      print_endline "Proof Complete!";
      Printing.print_thm thm
  | Incomplete (_asms, g) ->
      print_endline "Proof Failed";
      Printing.print_term g
