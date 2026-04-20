[@@@warning "-26-27-32-33"]
(* (* [@@@ocamlformat "disable"] *) *)

open Heft
open Tactic
open Auto

let () =
  print_newline ();
  print_newline ()

let%def min_pair (f : (nat, nat) pair -> nat) (p : (nat, nat) pair) : nat =
  match p with
  | Pair (l, r) ->
      if l = 0n || r = 0n then 0n else Suc (f (Pair (pred l, pred r)))

(* type ('a, 'b) pair = Pair of 'a * 'b *)
(* type nat = Zero | Suc of nat *)
(* let pred : nat -> nat = function Zero -> Zero | Suc n -> n *)
(* let rec min_pair (p : (nat, nat) pair) : nat = *)
(*   match p with *)
(*   | Pair (l, r) -> *)
(*       if l = Zero || r = Zero then Zero else Suc (min_pair (Pair (pred l, pred r))) *)
(* let rec int_of_nat : nat -> int = function Zero -> 0 | Suc n -> 1 + int_of_nat n *)
(* let rec nat_of_int : int -> nat = fun n -> if n <= 0 then Zero else Suc (nat_of_int (n-1)) *)
(* let _ = min_pair (Pair ((nat_of_int 9), (nat_of_int (-1)))) |> int_of_nat |> print_int *)

let%def nat_pair_sum (p : (nat, nat) pair) : nat =
  match p with Pair (l, r) -> plus l r

let%def nat_pair_measure : (nat, nat) pair -> (nat, nat) pair -> bool =
  measure nat_pair_sum

(* let () = Printing.print_thm min_pair *)
(* let () = Printing.print_thm nat_pair_measure *)

let%thm nat_pair_measure_wf = wf nat_pair_measure

and proof =
  begin
    rewrite_at "nat_pair_measure" >> apply_at "wf_measure"
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
    rewrite_at "min_pair_spec" >> beta >> rewrite_at "min_pair" >> beta >> gen
    >> refl
  end
  [@quiet]

let%def min_pair_unc (l : nat) (r : nat) : nat = min_pair_spec (Pair (l, r))

let%thm min_pair_uncurried_fr (l : nat) (r : nat) =
  min_pair_spec (Pair (l, r))
  = if l = 0n || r = 0n then 0n else Suc (min_pair_unc (pred l) (pred r))

and proof =
  begin
    intros >> rewrite_at "min_pair_spec" >> rewrite_at "min_pair"
    >> with_repeat beta
    >> simp ~exclude:[ "min_pair_spec" ]
  end
  [@quiet]

let%thm min_pair_final (l : nat) (r : nat) =
  min_pair_unc l r
  = if l = 0n || r = 0n then 0n else Suc (min_pair_unc (pred l) (pred r))

and proof =
  begin
    noop >> intros >> rewrite_at "min_pair_unc" >> with_repeat beta
    >> rewrite_at "min_pair_uncurried_fr"
    >> refl
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
    >> rewrite_at "refl_eq_true" >> rewrite_at "true_or_false"
    >> simp ~exclude:[ "min_pair_spec" ]
  end
  [@quiet]

(* What I would like to write:
let%rec min_pair (p : (nat, nat) pair) : nat =
  match p with
  | Pair (l, r) ->
      if l = 0n || r = 0n then 0n else Suc (min_pair (Pair (pred l, pred r)))
and measure = nat_pair_sum
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

need to

take a single parameter definition f(x)
rewrite it into h(f, x), where recursive calls are replaced with f

take a measure function, m', of type 'a -> nat, where f was type 'a -> 'b
generate the proof of wf_m by calling measure m and applying wf_measure

build the congruence goal where we say wf_cong m' h
user proves this goal

System gives a warning for the rejected definition until the proof goes through.

With both proofs we can prove wf_rec automatically

this gives existence theorem. With it we can assert that the fixpoint exists with new_spec, giving g
We can now create an unfolding lemma for normal use by asserting that h g x = the body of the original f

This unfolding lemma will be the only thing in rules after we are done. This will allow for unfolding the recursion without
leaving the intermediate definitions in the system that could cause simp to loop.

So the ppx code generated should
take a hol term from the definition
- fail if there is more than one argument in any recursive calls
- create a term that wraps the body in another argument for f
- replace all recursive calls with this f
Build proof of wf measure using simple unfolding. Here the user would provide their measure like `and measure = (fun p -> ...)` where it will 
wrap the fun in the `measure` definition. Please consult theory_dev.ml 
```
let%thm nat_pair_measure_wf = wf nat_pair_measure

and proof =
  begin
    rewrite_at "nat_pair_measure" >> apply_at "wf_measure"
  end
  [@quiet]

```

Build the goal for wf_cong, simple, just as in theory_dev.ml
User provides goal with `and proof = ...`
The ppx should provide an error in some way if the proof isn't finished so that the user knows that definition isn't sound yet

Now we automate the portion of theory_dev where we call new_specification on the existence theorem provided by wf_rec, after discharging the preconditions
of wf r and wf_cong.

Now we set up the final (for now) unfolding lemma that we will use instead of the intermediate definitions:
where min_pair_spec is the one obtained by the wf_rec existence thm
```
let%thm min_pair_unfold (x : (nat, nat) pair) =
  min_pair_spec x
  =
  match x with
  | Pair (l, r) ->
      if l = 0n || r = 0n then 0n
      else Suc (min_pair_spec (Pair (pred l, pred r)))

and proof =
  begin
    rewrite_at "min_pair_spec" >> beta >> rewrite_at "min_pair" >> beta >> gen
    >> refl
  end
  [@quiet]

```

Later on I plan to handle the currying inside the system so the user can write naturally, but for now lets just work with a single parameter that represents all
arguments through Pairs

*)

let%wfrec merge_wf (p : (nat list, nat list) pair) : nat list =
  match p with
  | Pair (xs, ys) -> (
      match (xs : nat list) with
      | [] -> ys
      | x' :: xs' -> (
          match (ys : nat list) with
          | [] -> xs
          | y' :: ys' ->
              if nat_lt x' y' then x' :: merge_wf (Pair (xs', ys))
              else y' :: merge_wf (Pair (xs, ys'))))

and measure =
 fun (p : (nat list, nat list) pair) ->
  match p with Pair (l, r) -> plus (length l) (length r)

and proof =
  begin
    noop >> rewrite_at "wf_rec_cong" >> with_repeat beta >> intros @! "hcong"
    >> rewrite_at "merge_wf_functional"
    >> rewrite_at "merge_wf_functional"
    >> with_repeat beta
    >> with_term [%term (x : (nat list, nat list) pair)] destruct_elim
       @: [ ""; "heq" ]
    >> simp
    >> with_term [%term (a0 : nat list)] destruct_elim
       @: [ "ha0nil"; ""; ""; "ha0cons" ]
    >> simp >> simp
    >> with_term [%term (a1 : nat list)] destruct_elim
       @: [ "ha1nil"; ""; ""; "ha1cons" ]
    >> simp >> simp
    >> cond @: [ "htrue"; "hfalse" ]
    >> (simp >> apply_at "eq_cong" >> apply_at "hcong" >> rewrite_at "heq"
      >> simp >> rewrite_at "lt_Suc_or_eq" >> right >> refl)
    >> (simp >> apply_at "eq_cong" >> apply_at "hcong" >> rewrite_at "heq"
      >> simp >> rewrite_at "lt_Suc_or_eq" >> right >> refl)
  end
  [@quiet]

(* let () = !Rules.definitions  |> List.iter (fun (n, _) -> print_endline n) *)

let%thm merge_wf_test (xs : nat list)  =
    merge_wf_fix (Pair (xs, [])) = xs
and proof = 
    begin
        noop
        >> gen
        >> rewrite_at "merge_wf"
    end


let () = ()
