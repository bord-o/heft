[@@@warning "-26-27-32-33"]

open Heft
open Tactic
open Auto

let%def nat_pair_sum (p : (nat, nat) pair) : nat =
  match p with Pair (l, r) -> plus l r

let%wfrec min_pair (p : (nat, nat) pair) : nat =
  match p with
  | Pair (l, r) ->
      if l = 0n || r = 0n then 0n else Suc (min_pair (Pair (pred l, pred r)))

and measure = fun (p : (nat, nat) pair) -> nat_pair_sum p

and proof =
  begin
    noop >> rewrite_at "wf_rec_cong" >> with_repeat beta >> intros @! "hcong"
    >> (rewrite_at "min_pair_functional"
       >> rewrite_at "min_pair_functional"
       >> with_repeat beta
       >> with_term [%term (x : (nat, nat) pair)] destruct_elim @: [ ""; "heq" ]
       >> simp
       >> cond @: [ "htrue"; "hfalse" ]
       >> simp >> simp >> apply_at "eq_cong" >> apply_at "hcong")
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

let%expect_test "min_pair unfolding lemma exists" =
  (match Rules.get_proven "min_pair" with
  | Some thm -> Printing.print_thm thm
  | None -> print_endline "MISSING");
  [%expect
    {|
    ========================================
    ∀p. min_pair_fix p = match_pair p (λl. λr. COND l = Zero ∨ r = Zero Zero (Suc (min_pair_fix (Pair (pred l) (pred r)))))
    |}]

let%wfrec nat_half (n : nat) : nat =
  if n = 0n || pred n = 0n then 0n else Suc (nat_half (pred (pred n)))

and measure = fun (n : nat) -> n
and proof = sorry [@quiet]

let%expect_test "nat_half unfolding lemma exists" =
  (match Rules.get_proven "nat_half" with
  | Some thm -> Printing.print_thm thm
  | None -> print_endline "MISSING");
  [%expect
    {|
    ========================================
    ∀n. nat_half_fix n = COND n = Zero ∨ pred n = Zero Zero (Suc (nat_half_fix (pred (pred n))))
    |}]

let%wfrec nat_to_zero (n : nat) : nat =
  if n = 0n then 0n else nat_to_zero (pred n)

and measure = fun (n : nat) -> n
and proof = sorry [@quiet]

let%expect_test "nat_to_zero unfolding lemma exists" =
  (match Rules.get_proven "nat_to_zero" with
  | Some thm -> Printing.print_thm thm
  | None -> print_endline "MISSING");
  [%expect
    {|
    ========================================
    ∀n. nat_to_zero_fix n = COND n = Zero Zero (nat_to_zero_fix (pred n))
    |}]

let%expect_test "intermediate names registered" =
  let check name getter =
    match getter name with
    | Some _ -> Printf.printf "%s: present\n" name
    | None -> Printf.printf "%s: MISSING\n" name
  in
  check "min_pair_measure_wf" Rules.get_proven;
  check "min_pair_cong" Rules.get_proven;
  check "min_pair_wf_rec" Rules.get_proven;
  check "min_pair" Rules.get_proven;
  check "nat_half_measure_wf" Rules.get_proven;
  check "nat_half_cong" Rules.get_proven;
  check "nat_half_wf_rec" Rules.get_proven;
  check "nat_half" Rules.get_proven;
  check "nat_to_zero_measure_wf" Rules.get_proven;
  check "nat_to_zero_cong" Rules.get_proven;
  check "nat_to_zero_wf_rec" Rules.get_proven;
  check "nat_to_zero" Rules.get_proven;
  [%expect
    {|
    min_pair_measure_wf: present
    min_pair_cong: present
    min_pair_wf_rec: present
    min_pair: present
    nat_half_measure_wf: present
    nat_half_cong: present
    nat_half_wf_rec: present
    nat_half: present
    nat_to_zero_measure_wf: present
    nat_to_zero_cong: present
    nat_to_zero_wf_rec: present
    nat_to_zero: present
    |}]
