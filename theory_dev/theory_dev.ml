[@@@warning "-26-27-32-33"]
(* (* [@@@ocamlformat "disable"] *) *)

open Heft
open Kernel
open Derived
open Tactic
open Auto

let () =
  print_newline ();
  print_newline ()

let%def min_pair (f : (nat, nat) pair -> nat) (p : (nat, nat) pair) : nat =
  match p with
  | Pair (l, r) ->
      if l = 0n || r = 0n then 0n else Suc (f (Pair (pred l, pred r)))

let%def nat_pair_sum (p : (nat, nat) pair) : nat =
  match p with Pair (l, r) -> plus l r

let%def nat_pair_measure : (nat, nat) pair -> (nat, nat) pair -> bool =
  measure nat_pair_sum

(* let () = Printing.print_thm min_pair *)
(* let () = Printing.print_thm nat_pair_measure *)

let%thm nat_pair_measure_wf = wf nat_pair_measure

and proof =
  begin
    zero_tac >> rewrite_at_tac "nat_pair_measure" >> apply_at_tac "wf_measure"
  end
  [@quiet]

let%thm neg_eq_false (p : bool) = p = false = not p

and proof =
  begin
    zero_tac >> intros_tac
    >> with_rule (neg_def |> Result.get_ok) rewrite_tac
    >> beta_tac
    >> eq_iff_tac @: [ "himp"; "heq" ]
    >> eq_false_elim_tac
    >> with_rule (neg_def |> Result.get_ok) rewrite_tac
    >> beta_tac >> assumption_tac >> rewrite_at_tac "heq" >> intros_tac
    >> false_elim_tac
  end
  [@quiet]

let%thm demorgons_eq_false (p : bool) (q : bool) =
  (p || q) = false ==> ((not p) && not q)

and proof =
  begin
    zero_tac >> intros_tac @! "heq"
    >> rewrite_at_tac "neg_eq_false" ~target:"heq"
    >> with_no_automation_trace ctauto_dfs_tac
  end
  [@quiet]

let%thm min_pair_cong = wf_rec_cong nat_pair_measure min_pair

and proof =
  begin
    zero_tac
    >> rewrite_at_tac "wf_rec_cong"
    >> with_repeat beta_tac >> intros_tac @! "hcong"
    (* walking through the definition to get to the measured parts *)
    >> (rewrite_at_tac "min_pair" >> rewrite_at_tac "min_pair"
      >> with_repeat beta_tac
       >> with_term [%term (x : (nat, nat) pair)] destruct_elim_tac
          @: [ ""; "heq" ]
       >> simp_tac
       >> cond_tac @: [ "htrue"; "hfalse" ]
       >> simp_tac >> simp_tac >> apply_at_tac "eq_cong" >> apply_at_tac "hcong"
       )
    (* if ~(a0 = 0 \/ a1 = Zero) then ∃n0. a0 = Suc n0 /\ ∃n1. a1 = Suc a1 *)
    >> (apply_at_tac "demorgons_eq_false" ~target:"hfalse"
       >> elim_conj_asm_tac @: [ "ha0"; "ha0" ]
       >> with_term [%term (a0 : nat)] destruct_elim_tac
          @: [ "ha0Zero"; ""; "ha0Nonzero" ]
       >>> with_term [%term (a1 : nat)] destruct_elim_tac
           @: [ "ha1Zero"; ""; "ha1Nonzero" ]
       >> with_first neg_elim_tac >> with_first neg_elim_tac
       >> with_first neg_elim_tac >> simp_tac
       >> rewrite_at_tac "lt_Suc_or_eq"
       >> left_tac
       >> rewrite_at_tac "lt_Suc_or_eq"
       >> right_tac >> refl_tac)
  end
  [@quiet]

let%thm min_pair_wf_rec =
  exists (fun (f : (nat, nat) pair -> nat) ->
      forall (fun (x : (nat, nat) pair) -> f x = min_pair f x))

and proof =
  begin
    zero_tac
    >> with_specialized ~name:"wf_rec"
         ~specs:[ [%term nat_pair_measure]; [%term min_pair] ]
         apply_tac
    >> with_proven [ "nat_pair_measure_wf" ] exact_tac
    >> with_proven [ "min_pair_cong" ] exact_tac
  end
  [@quiet]

let%def min_pair_chosen : (nat, nat) pair -> nat =
  choose (fun (f : (nat, nat) pair -> nat) ->
      forall (fun (x : (nat, nat) pair) -> f x = min_pair f x))

let () = ()
