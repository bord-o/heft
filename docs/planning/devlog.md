# Dev Log

## Saturday, March 28

While building a proof-of-concept of fuel-based general recursion, I decided that a mergesort implementation would be a good stopping point. Mergesort cannot be written in a structurally recursive way, due the necessity of recursion on a symmetrical split of the list being sorted. In addition to this, the auxilliary function 'merge', used to merge two sorted lists, is also not structurally recursive. So this should be a good test of both a more complex definition and a definition which uses other non-structurally recursive functions in its definition.

While other systems generally set up machinery for proving well-foundedness of a measure function (over the arguments), I was curious if simply defining these functions with a fuel argument could get me the same results. Essentially the goal is to get to an 'unfolding lemma' which allows us to abstract away the fuel based definition by proving that sufficient fuel exists and that using this fuel ensures the function's totality and equality with the body of the fuel-based definition. More concretely for merge, this looks something like the following two proofs.

```ocaml
let%expect_test "merge fuel sufficient" =
  let prg =
    {|
    variable fuel a0 a0': nat
    variable xs ys x a1 a1' x' : list nat
    
    theorem merge_fuel_sufficient :
        forall λfuel.
            forall λxs. forall λys.
                        imp (nat_lt (plus (length xs) (length ys)) fuel)
                            (exists λx.
                                (eq (merge_aux fuel xs ys) (some x)))
    term xs : xs
    term ys : ys
    term consa01 :  (cons a0 a1) 
    term consa01' :  (cons a0' a1') 
    term a1 : a1
    term a1' : a1'
    term x : x
    term wit : (cons a0 x')
    term wit2 :  (cons a0' x')

  |}
  in

  let xs = Elaborator.term_from_string prg "xs" in
  let ys = Elaborator.term_from_string prg "ys" in
  let wit = Elaborator.term_from_string prg "wit" in
  let wit2 = Elaborator.term_from_string prg "wit2" in
  let a1 = Elaborator.term_from_string prg "a1" in
  let a1' = Elaborator.term_from_string prg "a1'" in
  let consa01 = Elaborator.term_from_string prg "consa01" in
  let consa01' = Elaborator.term_from_string prg "consa01'" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac >> intros_tac
    >> simp_tac
    >> with_arbitrary_term xs destruct_tac
    >> elim_disj_asm_tac >> simp_tac
    >> with_arbitrary_term ys exists_tac
    >> refl_tac
    >> with_repeat elim_exists_asm_tac
    >> simp_tac
    >> with_arbitrary_term ys destruct_tac
    >> elim_disj_asm_tac >> simp_tac
    >> with_arbitrary_term consa01 exists_tac
    >> refl_tac
    >> with_repeat elim_exists_asm_tac
    >> simp_tac >> cond_tac >> simp_tac
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_proven [ "length_cons" ] rewrite_asm_tac
    >> with_proven [ "add_suc_l" ] rewrite_asm_tac
    >> with_proven [ "lt_suc_suc" ] rewrite_asm_tac
    >> spec_asm_tac a1 >> spec_asm_tac consa01' >> mp_asm_tac
    >> elim_exists_asm_tac >> simp_tac
    >> with_arbitrary_term wit exists_tac
    >> refl_tac >> simp_tac
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_first (with_assumptions rewrite_asm_tac)
    >> with_proven [ "plus_comm" ] rewrite_asm_tac
    >> with_proven [ "length_cons" ] rewrite_asm_tac
    >> with_proven [ "add_suc_l" ] rewrite_asm_tac
    >> with_proven [ "plus_comm" ] rewrite_asm_tac
    >> with_proven [ "lt_suc_suc" ] rewrite_asm_tac
    >> spec_asm_tac consa01 >> spec_asm_tac a1' >> mp_asm_tac
    >> elim_exists_asm_tac >> simp_tac
    >> with_arbitrary_term wit2 exists_tac
    >> refl_tac
  in
  run_proof ~name:"merge_fuel_sufficient" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀xs. ∀ys. nat_lt (plus (length xs) (length ys)) x ==> ∃x. merge_aux x xs ys = some x

    Proof Complete!
    with fuel: 404
    |}]
```
*where (length xs + length ys) is our 'measure', we say that any fuel greater than our measure results in 'something'*


```ocaml
let%expect_test "merge unfolding lemma" =
  let prg =
    {|
  variable fuel : nat
  variable h y' a0 a0' : nat
  variable xs ys x t ys' a1 a1' witness : list nat

  theorem merge_unfold:
    forall λxs. forall λys.
            (eq (merge xs ys)
                (list_match xs
                    (ys)
                    (λh. λt. 
                        (list_match ys
                            (cons h t)
                            (λy'. λys'.
                                COND (nat_lt h y')
                                    (cons h (merge t (cons y' ys')))
                                    (cons y' (merge (cons h t) ys')))))))
    term xs : xs
    term ys : ys
    term suf : exists (λx. eq  (merge_aux (suc (plus (length a1') (suc (length a1)))) a1' (cons a0 a1)) (some x))
    term suf2 : exists (λx. eq  (merge_aux (suc (plus (length a1') (suc (length a1)))) (cons a0' a1') a1) (some x))

    |}
  in

  let xs = Elaborator.term_from_string prg "xs" in
  let suf = Elaborator.term_from_string prg "suf" in
  let suf2 = Elaborator.term_from_string prg "suf2" in
  let ys = Elaborator.term_from_string prg "ys" in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    intros_tac
    >> with_arbitrary_term xs destruct_tac
    >> with_arbitrary_term ys destruct_tac
    >> with_repeat elim_disj_asm_tac
    >> simp_tac
    >> with_repeat elim_exists_asm_tac
    >> simp_tac
    >> with_repeat elim_exists_asm_tac
    >> simp_tac
    >> with_repeat elim_exists_asm_tac
    >> with_definition [ "merge" ] rewrite_tac
    >> beta_tac
    >> with_first (with_definition [ "merge_aux" ] rewrite_tac)
    >> with_repeat (with_first (with_assumptions rewrite_tac))
    >> simp_tac ~exclude:[ "merge"; "merge_aux" ]
    >> cond_tac
    >> simp_tac ~exclude:[ "merge"; "merge_aux" ]
    >> with_arbitrary_term suf assert_tac
    >> with_proven [ "merge_fuel_sufficient" ] apply_thm_tac
    >> simp_tac >> elim_exists_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "merge"; "merge_aux" ]
    >> with_definition [ "merge" ] rewrite_tac
    >> beta_tac
    >> with_proven [ "length_cons" ] rewrite_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac
    >> simp_tac ~exclude:[ "merge"; "merge_aux" ]
    >> with_arbitrary_term suf2 assert_tac
    >> with_proven [ "merge_fuel_sufficient" ] apply_thm_tac
    >> simp_tac
    >> with_proven [ "plus_suc" ] rewrite_tac
    >> simp_tac >> elim_exists_asm_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "merge"; "merge_aux" ]
    >> with_definition [ "merge" ] rewrite_tac
    >> beta_tac
    >> with_proven [ "length_cons" ] rewrite_tac
    >> with_first (with_proven [ "plus_suc" ] rewrite_asm_tac)
    >> with_first (with_proven [ "plus_comm" ] rewrite_tac)
    >> with_first (with_proven [ "plus_suc" ] rewrite_tac)
    >> with_first (with_proven [ "plus_comm" ] rewrite_tac)
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac
  in
  run_proof ~name:"merge_unfold" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀xs. ∀ys. merge xs ys = list_match xs ys (λh. λt. list_match ys (cons h t) (λy'. λys'. COND (nat_lt h y') (cons h (merge t (cons y' ys'))) (cons y' (merge (cons h t) ys'))))

    Proof Complete!
    with fuel: 1197
    |}]
```
*where the list_match expression is exactly the body of the fuel-based definition, essentially lifting us from using merge_aux to using merge directly*

At this point we could then remove merge_aux from our simplifier and definitions, essentially never using it again and preferring the unfolding lemma instead as if it was defined this way from the start.

---

With the necessary definitions of `merge : list nat -> list nat -> list nat`, `take : nat -> list nat -> list nat`, and drop `drop : nat -> list nat -> list nat` in place, `merge_sort_aux` can be defined as the fuel-based stand in for our eventual `merge_sort`.

```ocaml
    def merge_sort_aux : nat -> list nat -> option (list nat)
    | zero => λxs. none
    | suc n => λxs.
        COND (nat_le (length xs) (suc zero))
            (some xs)
            ((λhalf_length. 
                option_match (merge_sort_aux n (take half_length xs))
                    (none)
                    (λleft. 
                        option_match (merge_sort_aux n (drop half_length xs))
                            (none)
                            (λright. some (merge left right))
                    )
            ) (div (length xs) (suc (suc zero))))
```
*a little ugly without let bindings or numerals, but a fairly standard definition that avoids a dedicated `split` function*

I should also note that I ran into some difficulty when trying to compute with merge_sort_aux on concrete data. For instance, proving `merge_sort_aux 8 [3, 1, 2] = some [1, 2, 3]` required a very specific ordering of rewrites to avoid explosion of unfolding branches that wouldn't end up being relevant: 

```ocaml
  let proof =
    rw_def "merge_sort_aux" >> simp_tac ~exclude
    >> with_repeat @@ rw_def "div"
    >> with_repeat @@ rw_def "div_aux"
    >> simp_tac ~exclude >> rw_def "merge_sort_aux" >> simp_tac ~exclude
    >> rw_def "merge_sort_aux" >> simp_tac ~exclude
    >> with_repeat @@ rw_def "div"
    >> with_repeat @@ rw_def "div_aux"
    >> simp_tac ~exclude >> rw_def "merge_sort_aux" >> simp_tac ~exclude
    >> rw_def "merge_sort_aux" >> simp_tac ~exclude >> rw_thm "merge_unfold"
    >> simp_tac ~exclude >> rw_thm "merge_unfold" >> simp_tac ~exclude
    >> rw_thm "merge_unfold" >> simp_tac ~exclude >> rw_thm "merge_unfold"
    >> simp_tac ~exclude >> rw_thm "merge_unfold" >> simp_tac ~exclude
    >> rw_thm "merge_unfold" >> simp_tac ~exclude
```

I believe that this is a common pattern in HOL light, where the simplifier is quite naive like mine, and there is no generic `compute` for these types of tests.

Now to prove sufficiency and unfolding for this definition:

```ocaml
let%expect_test "merge sort sufficient" =
  let prg =
    {|
    variable fuel n0 : nat
    variable xs x : list nat

    theorem merge_sort_fuel_sufficient:
        forall λfuel.
            forall λxs.
                imp (nat_lt (length xs) fuel)
                    (exists λx.
                        (eq (merge_sort_aux fuel xs) (some x)))

    term xs : xs
    term left :  (take (div (length xs) (suc (suc zero))) xs)
    term right : (drop (div (length xs) (suc (suc zero))) xs)

    term right_oblig : nat_lt (length (drop (div (length xs) (suc (suc zero))) xs)) n0
    term left_oblig :  nat_lt (length (take (div (length xs) (suc (suc zero))) xs)) n0
  |}
  in

  let xs = Elaborator.term_from_string prg "xs" in
  let left = Elaborator.term_from_string prg "left" in
  let right = Elaborator.term_from_string prg "right" in
  (* let left_oblig = Elaborator.term_from_string prg "left_oblig" in *)
  (* let right_oblig = Elaborator.term_from_string prg "right_oblig" in *)
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac >> intros_tac
    >> with_first (with_definition [ "merge_sort_aux" ] rewrite_tac)
    >> beta_tac >> cond_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "merge_sort_aux"; "take"; "drop"; "div"; "merge" ]
    >> with_arbitrary_term xs exists_tac
    >> refl_tac
    >> with_first (with_assumptions rewrite_tac)
    >> simp_tac ~exclude:[ "merge_sort_aux"; "take"; "drop"; "div"; "merge" ]
    >> spec_asm_tac left >> spec_asm_tac right >> sorry_tac
  in
  run_proof ~name:"merge_sort_fuel_sufficient" ~notrace:true goal proof;
  [%expect
    {|
    ========================================
    ∀x. ∀xs. nat_lt (length xs) x ==> ∃x. merge_sort_aux x xs = some x

    Proof Complete!
    with fuel: 100
    |}]
```
*I added an exclusion list to the simplifier to help out until I'm sure I can remove these auxiliary functions from the rule set. Eventually I should only need the unfolding lemma, i.e. merge_unfold but not merge or merge_aux*

This proof is in progress, but requires lemmas around take/drop that I need to backfill. Overall, I think that the fuel-based approach is fine for a smaller number of these types of generally recursive definitions, but requires a meaningfully large proof burden per definition. Long term, well-foundedness is the right move for a ergonomic prover and provides an easier, more automation-friendly obligation.


## Sunday, March 29

I took some time to look into the construction of number systems in a HOL environment. It seems that Harrison does something a bit peculiar in HOL-light, rather than building the number tower in a progressive way, moving from naturals -> integers -> rationals -> reals, he instead builds the real numbers as a [quotient type](https://en.wikipedia.org/wiki/Quotient_type) and get the others through sub-typing.

To inform myself a bit I looked at A.H. Lightstone's ["Symbolic Logic and the Real Number System"](https://archive.org/details/symboliclogicrea0000ahli) and found some interesting symmetries in the construction of integers and rationals that I wasn't aware of. Assuming we start with naturals and pairs as they're defined in my system:

```
inductive nat :=
    | zero : nat
    | suc : nat -> nat

vartype a b
inductive pair := 
    | pair : a -> b -> pair a b
```

We can build integers as a subtype of pairs of naturals where the right and left represent the positive and negative components, respectively. Here it would be something like:

```
variable a b c d : nat
subtype int := pair a b
    where (eq a zero) \/ (eq b zero)
    
```
*(pseudocode as I don't have object syntax for subtypes yet)*

Which gives us a canonical representation to distinguish between (5,3) and (6,4), for instance. 

The symmetry I was referring to is that rationals are defined almost the same way, with a pair, this time representing the numerator and denominator. Here we use an integer numerator to keep the sign, and a natural denominator for simplicity:

```
variable a : int
variable b : nat
subtype rat := pair a b
    where (nat_lt zero b) ∧ (gcd (abs a) b = suc zero)
    
```
*(pseudocode as I don't have object syntax for subtypes yet)*

Which gives us a canonical representation to distinguish between (2,3) and (6,9), for instance. 

This is more obvious when looking more abstractly at their equivalence relations, with addition vs multiplication being the only difference:

```
for integers
(a, b) === (c, d) when a + d = b + c

for rationals
(a, b) === (c, d) when a * d = b * c
```

For my system I will elect to go the more traditional route of the number tower, as I think it will make for a more readable and easily understood formulation at the cost of having some more fiddly definitions for the algebraic laws due to reasoning about these underlying representations directly and respecting normalization at each step. Another benefit to the more traditional approach is that I don't necessarily need to add quotient typing to the system, not that it would be a large addition.
