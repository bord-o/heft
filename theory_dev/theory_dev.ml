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
    noop >> rewrite_at "nat_pair_measure" >> apply_at "wf_measure"
  end
  [@quiet]

let%thm neg_eq_false (p : bool) = p = false = not p

and proof =
  begin
    noop >> intros
    >> with_rule (neg_def |> Result.get_ok) rewrite
    >> beta
    >> eq_iff @: [ "himp"; "heq" ]
    >> eq_false_elim
    >> with_rule (neg_def |> Result.get_ok) rewrite
    >> beta >> assumption >> rewrite_at "heq" >> intros >> false_elim
  end
  [@quiet]

let%thm demorgons_eq_false (p : bool) (q : bool) =
  (p || q) = false ==> ((not p) && not q)

and proof =
  begin
    noop >> intros @! "heq"
    >> rewrite_at "neg_eq_false" ~target:"heq"
    >> with_no_automation_trace ctauto_dfs
  end
  [@quiet]

let%thm min_pair_cong = wf_rec_cong nat_pair_measure min_pair

and proof =
  begin
    noop >> rewrite_at "wf_rec_cong" >> with_repeat beta >> intros @! "hcong"
    (* walking through the definition to get to the measured parts *)
    >> (rewrite_at "min_pair" >> rewrite_at "min_pair" >> with_repeat beta
       >> with_term [%term (x : (nat, nat) pair)] destruct_elim @: [ ""; "heq" ]
       >> simp
       >> cond @: [ "htrue"; "hfalse" ]
       >> simp >> simp >> apply_at "eq_cong" >> apply_at "hcong")
    (* if ~(a0 = 0 \/ a1 = Zero) then ∃n0. a0 = Suc n0 /\ ∃n1. a1 = Suc a1 *)
    >> (apply_at "demorgons_eq_false" ~target:"hfalse"
       >> elim_conj_asm @: [ "ha0"; "ha0" ]
       >> with_term [%term (a0 : nat)] destruct_elim
          @: [ "ha0Zero"; ""; "ha0Nonzero" ]
       >>> with_term [%term (a1 : nat)] destruct_elim
           @: [ "ha1Zero"; ""; "ha1Nonzero" ]
       >> with_first neg_elim >> with_first neg_elim >> with_first neg_elim
       >> simp >> rewrite_at "lt_Suc_or_eq" >> left >> rewrite_at "lt_Suc_or_eq"
       >> right >> refl)
  end
  [@quiet]

let%thm min_pair_wf_rec =
  exists (fun (f : (nat, nat) pair -> nat) ->
      forall (fun (x : (nat, nat) pair) -> f x = min_pair f x))

and proof =
  begin
    noop
    >> with_specialized ~name:"wf_rec"
         ~specs:[ [%term nat_pair_measure]; [%term min_pair] ]
         apply
    >> with_proven [ "nat_pair_measure_wf" ] exact
    >> with_proven [ "min_pair_cong" ] exact
  end
  [@quiet]

let%def min_pair_chosen : (nat, nat) pair -> nat =
  choose (fun (f : (nat, nat) pair -> nat) ->
      forall (fun (x : (nat, nat) pair) -> f x = min_pair f x))

let%thm min_pair_chosen_eq (x : (nat, nat) pair) =
  min_pair_chosen x = min_pair min_pair_chosen x

and proof =
  begin
    noop >> intros >> rewrite_at "min_pair_chosen"
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
    noop >> rewrite_at "min_pair_spec" >> beta >> rewrite_at "min_pair" >> beta
    >> gen >> refl
  end
  [@quiet]

(* let () = List.iter Printing.print_thm Nats.nat_def.distinct *)
let%thm nat_distinct_flip (m : nat) = Suc m = Zero = F

and proof =
  begin
    noop >> intros >> eq_false_elim >> neg_intro >> sym_asm
    >> with_rules Nats.nat_def.distinct (with_first rewrite_asm)
    >> assumption
  end
  [@quiet]

let%thm false_or_false = (false || false) = false

and proof =
  begin
    noop >> eq_false_elim >> neg_intro >> elim_disj_asm >>> assumption
  end
  [@quiet]

let%thm refl_eq_true (x : 'a) = x = x = true

and proof =
  begin
    noop >> intros >> eq_true_elim >> refl
  end
  [@quiet]

let%thm t_or_f = (true || false) = true

and proof =
  begin
    noop >> eq_true_elim >> left >> truth
  end
  [@quiet]

let%thm min_pair_test = min_pair_spec (Pair (2n, 3n)) = 2n

and proof =
  begin
    noop
    >> rewrite_at "min_pair_uncurried"
    >> simp ~exclude:[ "min_pair_spec" ]
    >> rewrite_at "nat_distinct_flip"
    >> rewrite_at "nat_distinct_flip"
    >> rewrite_at "false_or_false"
    >> simp ~exclude:[ "min_pair_spec" ]
    >> rewrite_at "min_pair_uncurried"
    >> simp ~exclude:[ "min_pair_spec" ]
    >> rewrite_at "nat_distinct_flip"
    >> rewrite_at "nat_distinct_flip"
    >> rewrite_at "false_or_false"
    >> simp ~exclude:[ "min_pair_spec" ]
    >> rewrite_at "min_pair_uncurried"
    >> simp ~exclude:[ "min_pair_spec" ]
    >> rewrite_at "nat_distinct_flip"
    >> rewrite_at "refl_eq_true" >> rewrite_at "t_or_f"
    >> simp ~exclude:[ "min_pair_spec" ]
  end
(* [@quiet] *)

let () = ()
