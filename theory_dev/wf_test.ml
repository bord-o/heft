[@@@warning "-26-27-32-33"]
(* (* [@@@ocamlformat "disable"] *) *)

open Heft
open Tactic
open Auto
open Grimm

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

let () =
  run_proof ~quiet:true ~simp:true ~name:"eq_true_false"
    (make_goal [%term true = false = false])
    (eq_false_elim >> neg_intro
    >> with_assumptions @@ with_flip_rules rewrite
    >> truth);
  run_proof ~quiet:true ~simp:true ~name:"eq_false_false"
    (make_goal [%term false = false = true])
    (eq_true_elim >> refl);
  run_proof ~quiet:true ~simp:true ~name:"eq_true_true"
    (make_goal [%term true = true = false])
    (eq_true_elim >> refl);
  run_proof ~quiet:true ~simp:true ~name:"eq_false_true"
    (make_goal [%term false = true = false])
    (eq_false_elim >> neg_intro >> simp);
  run_proof ~quiet:true ~simp:true ~name:"neg_false_true"
    (make_goal [%term (not false) = true])
    (eq_true_elim >> neg_intro >> false_elim);
  run_proof ~quiet:true ~simp:true ~name:"neg_true_false"
    (make_goal [%term (not true) = false])
    (eq_false_elim
    >> with_term [%term true] have
    >> truth >> neg_intro >> neg_elim)

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
          @>> with_term [%term (a1 : nat)] destruct_elim
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
       @>> with_term [%term (a1 : nat)] destruct_elim
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

let%thm merge_wf_id_l (xs : nat list) = merge_wf (Pair (xs, [])) = xs

and proof =
  begin
    noop >> gen >> rewrite_at "merge_wf" >> simp
    >> with_term [%term (xs : nat list)] destruct_elim
       @: [ "hnil"; ""; ""; "hcons" ]
    >> simp >> simp
  end
  [@simp] [@quiet]

let%thm merge_wf_id_r (xs : nat list) = merge_wf (Pair ([], xs)) = xs

and proof =
  begin
    noop >> gen >> rewrite_at "merge_wf" >> simp
    >> with_term [%term (xs : nat list)] destruct_elim
       @: [ "hnil"; ""; ""; "hcons" ]
    >> simp >> simp
  end
  [@simp] [@quiet]

let%thm merge_comm (xs : nat list) (ys : nat list) =
  merge_wf (Pair (xs, ys)) = merge_wf (Pair (ys, xs))

and proof =
  begin
    induct
    >>= [
          induct >>= [ simp; intros >> simp ];
          gen >> gen >> intro @! "ih" >> induct
          >>= [
                simp;
                intros @! "heq" >> rewrite_at "merge_wf" >> simp
                >> cond @: [ "htrue"; "hfalse" ]
                >> (simp
                   >> rewrite_at "merge_wf" ~position:1
                   >> simp
                   >> apply_at "nat_lt_antisym" ~target:"htrue"
                   >> simp)
                >> simp
                >> rewrite_at "merge_wf" ~position:1
                >> simp
                >> cond @: [ "htrue2"; "hfalse2" ]
                >> simp >> simp
                >> apply_at "not_lt_bidir" ~target:"hfalse" @! "hprem"
                >> apply_at "hprem" ~target:"hfalse2" @! "hn0eq"
                >> rewrite_at "hn0eq" >> apply_at "eq_cong"
                (* >> rewrite_at "" *);
              ];
        ]
  end
  (* I think I need better induction for this one*)
  [@quiet]

let%thm merge_length_l (x : nat) (xs : nat list) (y : nat) (ys : nat list) =
  length (merge_wf (Pair (Cons (x, xs), Cons (y, ys))))
  = Suc (Suc (plus (length xs) (length ys)))

and proof =
  begin
    noop >> intros >> rewrite_at "merge_wf" >> simp >> cond >> simp
    (* Could finish if I had comm*)
  end
  [@quiet]

(* todo why did it unfold merge_wf_functional? A: its both a def and proven so it will use whatever works *)
let%thm merge_wf_length_bounded (xs : nat list) (ys : nat list) =
  length (merge_wf (Pair (xs, ys))) = plus (length xs) (length ys)

and proof =
  begin
    intros
    >> with_term [%term (xs : nat list)] destruct_elim
       @: [ "hxsnil"; ""; ""; "hxssuc" ]
       @>> with_term [%term (ys : nat list)] destruct_elim
       @: [ "hysnil"; ""; ""; "hyssuc" ]
    >> simp >> simp >> simp >> simp
  end
  [@quiet]
(* [@trace] *)

(* [@trace] *)

let () = ()

let contradict : tactic =
 fun goal ->
  with_grimm
    (pick
       [
         try_ simp >> gen;
         try_ simp >> intro;
         try_ simp >> eq_false_elim;
         try_ simp >> neg_intro;
         try_ simp >> sym_asm;
         try_ simp >> discriminate;
       ])
    goal

let%thm _dist (a : bool) (b : bool) (c : bool) (d : bool) =
  ((a || b) && (c || d)) ==> ((a && c) || (a && d) || (b && c) || (b && d))

and proof =
  begin
    intros >> elim_conj_asm >> elim_disj_asm >> elim_disj_asm >> left >> conj
    >> assumption >> assumption >> right >> left >> conj >> assumption
    >> assumption >> elim_disj_asm >> right >> right >> left >> conj
    >> assumption >> assumption >> right >> right >> right >> conj >> assumption
    >> assumption
  end
(* [@quiet] *)

[%%inductive type 'a list = Nil | Cons of 'a * 'a list]

let%primrec length_aux (l : 'a list) (len : nat) : nat =
  match l with [] -> len | h :: l -> length_aux l (plus len 1n)

let%def length (l : 'a list) : nat = length_aux l 0n
let%def cons (a : 'a) (l : 'a list) : 'a list = a :: l
let%def singleton (a : 'a) : 'a list = [ a ]

let%primrec nth_opt (l : 'a list) (n : nat) : 'a option =
  match l with
  | [] -> None
  | a :: l' -> if n = 0n then Some a else nth_opt l' (sub n 1n)

let%primrec rev_append (l1 : 'a list) (l2 : 'a list) : 'a list =
  match l1 with [] -> l2 | a :: l -> rev_append l (a :: l2)

let%def rev (l : 'a list) : 'a list = rev_append l []

let () =
  let goal = make_goal [%term forall (fun (a : nat) -> sub a 0n = a)] in
  run_proof ~quiet:true ~simp:true ~name:"sub_Zero_r" ~notrace:true goal
    (induct
    >> with_no_automation_trace auto_dfs
    >> with_no_automation_trace auto_dfs)

(* let%def t = Pair (i, Pair (last, f)) *)
let%thm sub_lt_lemma (a : nat) (b : nat) (c : nat) =
  nat_lt b a ==> (nat_le a c ==> nat_lt (sub c a) (sub c b))

and proof =
  begin
    noop >> induct
    >>= [
          induct
          >>= [
                intros >> simp_all >> false_elim;
                intros >> simp_all >> false_elim;
              ];
          gen >> intro @! "hIH" >> induct
          >>= [
                intros >> simp >> apply_at "sub_lt" >> assumption >> assumption;
                intros
                >> with_term [%term (c : nat)] destruct_elim
                   @: [ "hzero"; ""; "hsuc" ]
                >> simp_all >> false_elim >> simp_all >> apply_at "hIH"
                >> assumption >> assumption;
              ];
        ]
  end
  [@quiet]

let%thm suc_is_plus (a : nat) = Suc a = plus a 1n

and proof =
  begin
    gen >> simp
  end
  [@quiet]

let%thm lt_plus (a : nat) (n : nat) = nat_lt 0n n ==> nat_lt a (plus a n)

and proof =
  begin
    induct >> intros
    >> with_term [%term (n : nat)] destruct_elim @: [ "hnzero"; ""; "hnsuc" ]
    >> simp_all >> false_elim >> simp
    >> intros @: [ "hIH"; "hlt" ]
    >> with_term [%term (n : nat)] destruct_elim @: [ "hnzero"; ""; "hnsuc" ]
    >> simp_all >> false_elim >> simp
    >> apply_at "hIH" ~target:"hlt" @! "hIHSpec"
    >> rewrite_at "hnsuc" ~target:"hIHSpec"
    >> simp_all
  end
  [@quiet]

let%wfrec init (p : (nat, (nat, nat -> 'a) pair) pair) : 'a list =
  match p with
  | Pair (i, p2) -> (
      match (p2 : (nat, nat -> 'a) pair) with
      | Pair (last, g) ->
          if nat_lt last i then []
          else if i = last then [ g i ]
          else g i :: g (plus i 1n) :: init (Pair (plus i 2n, Pair (last, g))))

and measure =
 fun (p : (nat, (nat, nat -> 'a) pair) pair) ->
  match p with
  | Pair (i, p2) -> (
      match (p2 : (nat, nat -> 'a) pair) with Pair (last, _g) -> sub last i)

and proof =
  begin
    noop >> rewrite_at "wf_rec_cong" >> with_repeat beta >> intros @! "hcong"
    >> rewrite_at "init_functional"
    >> rewrite_at "init_functional"
    >> with_repeat beta
    >> with_term [%term (x : (nat, (nat, nat -> 'a) pair) pair)] destruct_elim
       @: [ ""; "heqp1" ]
    >> simp
    >> with_term [%term (a1 : (nat, nat -> 'a) pair)] destruct_elim
       @: [ ""; "heqp2" ]
    >> simp >> with_nth_choice 1 cond >> simp >> simp >> cond >> simp >> simp
    >> apply_at "eq_cong" >> apply_at "eq_cong" >> apply_at "hcong" >> simp
    >> apply_at "sub_lt_lemma" >> rewrite_at "suc_is_plus"
    >> rewrite_at "suc_is_plus"
    >> with_proven [ "plus_assoc" ] (with_flip_rules rewrite)
    >> apply_at "lt_plus" >> simp
  end
