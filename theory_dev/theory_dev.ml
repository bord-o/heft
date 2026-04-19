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
    noop_tac >> rewrite_at_tac "nat_pair_measure" >> apply_at_tac "wf_measure"
  end
  [@quiet]

let%thm neg_eq_false (p : bool) = p = false = not p

and proof =
  begin
    noop_tac >> intros_tac
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
    noop_tac >> intros_tac @! "heq"
    >> rewrite_at_tac "neg_eq_false" ~target:"heq"
    >> with_no_automation_trace ctauto_dfs_tac
  end
  [@quiet]

let%thm min_pair_cong = wf_rec_cong nat_pair_measure min_pair

and proof =
  begin
    noop_tac
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
    noop_tac
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

let%thm min_pair_chosen_eq (x : (nat, nat) pair) =
  min_pair_chosen x = min_pair min_pair_chosen x

and proof =
  begin
    noop_tac >> intros_tac >> rewrite_at_tac "min_pair_chosen"
  end
  [@quiet]

let min_pair_spec =
  Inductive.new_specification "min_pair_spec"
    (Rules.get_proven "min_pair_wf_rec" |> Option.get)
  |> Result.get_ok

(* let () = Printing.print_thm min_pair_spec *)

let%thm min_pair_uncurried (x : (nat, nat) pair) =
  min_pair_spec x
  =
  match x with
  | Pair (l, r) ->
      if l = 0n || r = 0n then 0n
      else Suc (min_pair_spec (Pair (pred l, pred r)))

and proof =
  begin
    noop_tac
    >> rewrite_at_tac "min_pair_spec"
    >> beta_tac >> rewrite_at_tac "min_pair" >> beta_tac >> gen_tac >> refl_tac
  end
  [@quiet]

(* let () = List.iter Printing.print_thm Nats.nat_def.distinct *)
let%thm nat_distinct_flip (m : nat) = Suc m = Zero = F

and proof =
  begin
    noop_tac >> intros_tac >> eq_false_elim_tac >> neg_intro_tac >> sym_asm_tac
    >> with_rules Nats.nat_def.distinct (with_first rewrite_asm_tac)
    >> assumption_tac
  end
  [@quiet]

let%thm false_or_false = (false || false) = false

and proof =
  begin
    noop_tac >> eq_false_elim_tac >> neg_intro_tac >> elim_disj_asm_tac
    >>> assumption_tac
  end
  [@quiet]

let%thm refl_eq_true (x : 'a) = x = x = true

and proof =
  begin
    noop_tac >> intros_tac >> eq_true_elim_tac >> refl_tac
  end
  [@quiet]

let%thm t_or_f = (true || false) = true

and proof =
  begin
    noop_tac >> eq_true_elim_tac >> left_tac >> truth_tac
  end
  [@quiet]

let%thm min_pair_test = min_pair_spec (Pair (2n, 3n)) = 2n

and proof =
  begin
    noop_tac
    >> rewrite_at_tac "min_pair_uncurried"
    >> simp_tac ~exclude:[ "min_pair_spec" ]
    >> rewrite_at_tac "nat_distinct_flip"
    >> rewrite_at_tac "nat_distinct_flip"
    >> rewrite_at_tac "false_or_false"
    >> simp_tac ~exclude:[ "min_pair_spec" ]
    >> rewrite_at_tac "min_pair_uncurried"
    >> simp_tac ~exclude:[ "min_pair_spec" ]
    >> rewrite_at_tac "nat_distinct_flip"
    >> rewrite_at_tac "nat_distinct_flip"
    >> rewrite_at_tac "false_or_false"
    >> simp_tac ~exclude:[ "min_pair_spec" ]
    >> rewrite_at_tac "min_pair_uncurried"
    >> simp_tac ~exclude:[ "min_pair_spec" ]
    >> rewrite_at_tac "nat_distinct_flip"
    >> rewrite_at_tac "refl_eq_true"
    >> rewrite_at_tac "t_or_f"
    >> simp_tac ~exclude:[ "min_pair_spec" ]
  end
(* [@quiet] *)

let () = ()
