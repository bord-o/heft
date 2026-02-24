open Heft
open Derived
open Tactic

(* open Effect *)
open Printing

(* Storage for proven lemmas *)
(* let proven = ref [] *)
(* let lemma s = [ List.assoc s !proven ] *)

let run_proof ?(notrace = true) ?(name = "") goal tac =
  let fuel_count = ref 0 in
  let limit = ref 10_000_000 in
  let wrapped =
    (if notrace then with_no_trace ~show_proof:false else Fun.id)
    @@ (with_fuel_limit limit) (with_fuel_counter fuel_count tac)
  in
  match prove ~name goal wrapped with
  | Complete thm ->
      print_thm thm;
      print_endline "Proof Complete!";
      Printf.printf "with fuel: %d\n" !fuel_count
  | Incomplete (asms, c) ->
      List.iter print_term asms;
      print_term c;
      print_endline "Proof Incomplete";
      Printf.printf "with fuel: %d\n" !fuel_count

let () =
  let p = make_var "P" bool_ty in
  let q = make_var "Q" bool_ty in
  let r = make_var "R" bool_ty in
  let goal =
    ( [],
      make_imp
        (make_conj p (make_disj q r))
        (make_disj (make_conj p q) (make_conj p r)) )
  in
  let proof = with_bfs (
  pick_tac
    [
      assumption_tac;
      intro_tac;
      neg_intro_tac;
      gen_tac;
      conj_tac;
      elim_conj_asm_tac;
      elim_disj_asm_tac;
      false_elim_tac;
      neg_elim_tac;
      apply_asm_tac;
      apply_neg_asm_tac;
      mp_asm_tac;
      left_tac;
      right_tac;
    ]
    ) in
  run_proof goal proof;
