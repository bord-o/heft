# Dev Log

## Saturday, March 28

While building a proof-of-concept of fuel-based general recursion, I decided that a merge-sort implementation would be a good stopping point. Merge-sort cannot be written in a structurally recursive way, due the necessity of recursion on a symmetrical split of the list being sorted. In addition to this, the auxiliary function 'merge', used to merge two sorted lists, is also not structurally recursive. So this should be a good test of both a more complex definition and a definition which uses other non-structurally recursive functions in its definition.


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

## Wednesday, April 1

One thing that has bothered me about the state of proof assistants today is that the two main approaches of dependent type theory (DTT) and LCF (HOL) have really significant trade-offs, especially from the perspective of someone that is only beginning their journey through the space. Most of what I'll be discussing here is coming from the perspective of someone who knows how to program, and is interested in leveraging formal verification in some way.

On one hand the dominant DTT provers (Rocq, Lean) have tons of good documentation, and Lean specifically has invested heavily in making the onboarding experience as frictionless as possible. Still, these provers ask a lot of the user. To begin proving something outside of a trivial tutorial you must:

1. Be comfortable with functional programming 
1. Understand logic
1. Understand dependent types
1. Learn the tactic DSL

Lean is by far the best in minimizing the burden of these issues, I think largely because of the meta-programming-based tactics system and availability of quality documentation.

The other camp of widely-used proof assistants is the HOL family, including HOL-Light, HOL4, and Isabelle/HOL. These systems take a drastically different approach the core proof assistant's construction, something I might get into another time. The main difference is that these systems don't use dependent types at all, instead embedding a small simply-typed lambda calculus as the 'term language' or sometimes referred to as 'object language' to distinguish from the implementation language (often called the meta-language, hence ML). This term language is far easier to wrap your mind around compared to DTT, but creates a different problem altogether. 

Aside from the cultural issues (smaller user-base, less documentation) with HOL systems that have nothing to do with the incredible implementations that have been created, I see the main issue with usability in these systems being this multiple language stratification that I mentioned above. These systems essentially trade out the technical complexity of DTT for the mental overhead of working in a system with sometimes 4 different languages all mangled together.

The most popular HOL prover, Isabelle/HOL, illustrates my point clearly. To use Isabelle you need to learn this 'shell' language, I'm not sure whats it's called, but it serves as the main interface for creating definitions, types, and setting up proofs. Parts of this shell language are actually quoted pieces of the internal HOL term language, creating a lot of friction just to define a function for example. In addition to these two, we also have a 'tactic mode' for doing proofs manually, and another language, Isar, for structuring proofs to read more like traditional proofs. Each of these 4 languages requires it's own learning process, and the fact that they're so tightly integrated means that you can't really get started without learning a bit about all of them.

I believe that a HOL system is the right call for a widely usable proof system that shields the user from a lot of theory that comes with DTT, and the only missing piece in the current systems is a reasonable usability story.

---

Since my system is based on HOL-Light, I'll go over some of the friction that system has as well. HOL-Light is essentially a stripped-down HOL core, with the kernel famously consisting of only ~700 lines of readable OCaml, the only 'trusted' code in the system as far as I know. Since this is a HOL system we have the same quotation problem, where we often have a need for referencing the term language when defining things, writing proofs, etc. HOL-Light does this with some clever but clunky quoting preprocessing, allowing for quotation of HOL terms with backticks.

HOL-Light handles interactivity by assuming the user will be working on proofs and definitions directly in the OCaml top-level, which is in my experience far less pleasant to use than working in your favorite text editor with LSP-based diagnostics and proof state display.

Until now, I've been using a small domain-specific language (DSL) for writing my HOL definitions, types, and theorems. I have some infrastructure in elaborate.ml for this purpose, as well as a lexer and parser for the language. I've run into a lot of friction using this system, as I don't have quotation like HOL-Light, requiring me to manually construct terms, elaborate them, and then use the OCaml value when specializing an assumption or asserting a intermediate lemma. To get around these issues and retain a text-editor based interactive workflow, I'm exploring OCaml PPXes as my quotation mechanism, combined with leveraging OCaml's speedy compiler to refresh my proof state with `dune build --watch` in another window.

To build HOL terms with a PPX, I will leverage the fact that the term language's semantics are close enough to a subset of OCaml's AST that I can write my HOL definitions, types, and goals as OCaml directly. We'll see how this works in practice but I think it's a really pragmatic path forward to a potentially beginner-friendly proof assistant. The system will then trade out a lot of the traditional proof assistant onboarding process with "just know OCaml", which I think is a far more reasonable ask. The onboarding process would potentially be:

1. Install OCaml
1. `dune init proj my_proofs`
1. Add to `dune-project` the dependencies `heft heft.ppx heft.theories` and `dune pkg lock`
1. Start writing definitions and goals as valid OCaml with ppx_heft as a preprocessor
1. Run `dune build --watch` in another window to see the proof state update on each save

The end user would see something like:

```ocaml
type%heft nat =
    | Zero
    | Suc of nat

let%heft_primrec plus (m : nat) =
    match (m:nat) with
    | Zero -> fun (n:nat) -> (n:nat)
    | Suc (m':nat) -> fun (n:nat) -> Suc (plus (m':nat) (n:nat))

let%heft_goal plus_zero_right =
    forall (fun (m:nat) ->
        plus (m:nat) zero = (m:nat)
    )
```

There are still a few problems to solve here, like how to tell which terms should be variables vs constants for example, since PPX extensions are a purely syntactic transformation, and I don't know how acceptable it is to do things like type inference during the translation. For now I think I can get around this by just requiring all variables to have explicit annotation, matching HOL's internal representation. Also, I still need to think about other edge cases for HOL that could be difficult or confusing to represent as OCaml, subtypes for example.

## Friday, April 3

On my proof assistant, I've finally made the switch to a PPX-based approach to representing my HOL language, compared to the DSL I was using before. Moving to this approach allowed me to remove around 1000 lines of pretty complex elaboration logic, as well as make my definitions and theorems more easily representable, simply as writing OCaml with some restrictions. The new syntax looks like this.

```ocaml

(* Defining types*)
[%%inductive 
type nat = 
    Zero 
    | Suc of nat]


(* Non-recursive definitions *)
let%def pred (n : nat) : nat = match n with Zero -> Zero | Suc m -> m

(* Structurally recursive definitions *)
let%primrec plus (n : nat) (m : nat) : nat =
match n with Zero -> m | Suc n' -> Suc (plus n' m)

(* Proofs *)
let goal =
  make_goal
    [%term forall (fun (xs : 'a list) -> length xs = Zero ==> (xs = Nil))]
in
run_proof goal
  begin
    induct_tac >> intros_tac >> refl_tac >> intros_tac >> simp_asm_tac
    >> sym_asm_tac
    >> with_first (with_rules NatTheory.nat_def.distinct rewrite_asm_tac)
    >> false_elim_tac
  end;
```

The PPX takes a restricted set of syntactically valid OCaml code and transforms it into the equivalent HOL terms, with the addition of calling the inductive and function definition machinery at runtime.

This cut down a lot of noise in my system, and I hope it makes the system more approachable, at least to those comfortable with OCaml.

I still have plans for some dedicated proof syntax and for subtype definitions. Something like:

```ocaml
let%thm length_zero_imp_nil (xs : 'a list) =
    length xs = Zero ==> (xs = Nil),
    begin
      induct_tac >> intros_tac >> refl_tac >> intros_tac >> simp_asm_tac
      >> sym_asm_tac
      >> with_first (with_rules NatTheory.nat_def.distinct rewrite_asm_tac)
      >> false_elim_tac
    end [@simp] [@quiet]
```

Or maybe:

```ocaml
let%thm length_zero_imp_nil (xs : 'a list) =
    length xs = Zero ==> (xs = Nil)
and proof = 
    begin
      induct_tac >> intros_tac >> refl_tac >> intros_tac >> simp_asm_tac
      >> sym_asm_tac
      >> with_first (with_rules NatTheory.nat_def.distinct rewrite_asm_tac)
      >> false_elim_tac
    end [@simp] [@quiet]
```

Where the [@simp] annotations are used in the run_proof call.

## Friday, April 10

I'm looking at adding some more tactics to improve the ergonomics of my prover. I've added a discriminate tactic for goals with distinct constructor equality (`Suc n = Zero`), but I want to improve my contradiction reasoning a bit. Right now I have a contradict_asm_tac which can prove things like `~P |- F` using a subgoal of ` |- P`, but Rocq's contradict tactic is much stronger and handles 3 more distinct  cases in addition to the one that my tactic does.


From Rocq's documentation:

```
A tactic for proof by contradiction. With contradict H,

1    H:~A |- B gives |- A
2    H:~A |- ~B gives H: B |- A
3    H: A |- B gives |- ~A
4    H: A |- ~B gives H: B |- ~A

```
Translating this to my system, I can have exfalso_tac as `assert_tac F >> [subgoal] >> false_elim_tac`

- Case one is just `exfalso >> contradict_asm_tac`
- Case two is `neg_intro` to get `~A, B |- F`, then `contradict_asm_tac` to get `B |- A`
- Case three is just `assert_tac ~A`
- Case four is `neg_intro` to get  `A, B |- F`, then `assert_tac ~A >> [subgoal >> neg_elim_tac` 

Essentially if the goal is a negation we call neg_intro to get it in an assumption, say `A`, then we take a chosen assumption (other than `A`), say `B`. If it's a negation, we contradict_asm, otherwise we just assert its negation (`~B`).

This will help in a variety of cases that are currently pretty tedious with the current negation/false related tactics. 

## Sunday, April 12

I use neovim for development, and after the 0.12 update I was able to clean up my config quite a bit. For my own sanity and for any others that want a clean, minimalist config that includes nearly everything needed to be productive during development I've annotated some of the main parts of the config below. 

```lua
-- Requires: neovim 0.12+, ripgrep (for telescope live_grep), a nerd font (optional)

-- Basic config
vim.opt.tabstop = 4
vim.opt.shiftwidth = 4
vim.opt.ignorecase = true
vim.opt.smartcase = true
vim.opt.autoindent = true
vim.opt.number = true
vim.opt.clipboard = 'unnamedplus'
vim.g.mapleader = " "
vim.g.maplocalleader = '  '
vim.opt.ruler = true
vim.opt.cursorline = true
vim.opt.expandtab = true
vim.opt.scrolloff = 15
vim.opt.relativenumber = true
vim.cmd('dig TS 8866') -- digraph support for ⊢
vim.opt.laststatus = 2 -- Or 3 for global statusline
vim.opt.statusline = " %f %m %= %l:%c of %L ♥ "

-- Plugins
local function gh(repo) return 'https://github.com/' .. repo end
local function cb(repo) return 'https://codeberg.org/' .. repo end

vim.pack.add({
    gh('nvim-lua/plenary.nvim'), -- pretty generic dependency for other plugins
    gh('hrsh7th/nvim-cmp'), -- completion
    gh('hrsh7th/cmp-nvim-lsp'), -- more completion
    gh('nvim-treesitter/nvim-treesitter'), -- supports better syntax highlighting
    gh('nvim-telescope/telescope.nvim'), -- a fuzzy 
    gh('nvim-telescope/telescope-frecency.nvim'), -- a helpful addition for finding files based on both how often and how recently you've opened them
    gh('p00f/alabaster.nvim'), -- theme
    cb('andyg/leap.nvim'), -- for jumping to any word on screen by prefix 
    gh('tpope/vim-surround'), -- for wrapping parens, etc
    gh('tpope/vim-fugitive'), -- simple and clean interface to git for reviewing and modifying diffs
    gh('ellisonleao/gruvbox.nvim'), -- theme
    gh('olimorris/onedarkpro.nvim'), -- theme
    gh('ntk148v/komau.vim'), -- theme
    gh('airblade/vim-gitgutter'), -- show git changes on the side of the buffer
    gh('neovim/nvim-lspconfig'), -- lsp is now built in, but this brings all the configs for different langs as well
    gh('Julian/lean.nvim'), -- lean4 support
    gh('whonore/Coqtail'), -- rocq support
    gh('tomtomjhj/vsrocq.nvim'), -- rocq support
    gh('stevearc/oil.nvim') -- file explorer 
})
vim.api.nvim_create_user_command("PackUpdate", function()
    require("vim.pack").update()
end, { desc = "Update all plugins using vim.pack" })

-- Colorscheme
vim.api.nvim_create_user_command("ToggleBackground", function()
    if vim.o.background == 'dark' then vim.o.background = 'light' else vim.o.background = 'dark' end
end, { desc = "Toggles the vim.opt.background setting" })
vim.opt.background = 'light'
vim.cmd("colorscheme komau")

-- Configure plugins
require('oil').setup()
require('telescope').load_extension('frecency')
require('telescope').setup({
    defaults = {
        path_display = { "smart" }
    }
})
require('lean').setup({
    mappings = true,
})

-- Completion setup (tab to cycle completions, enter to accept them)
local cmp = require('cmp')
cmp.setup({
    sources = {
        { name = 'nvim_lsp' },
    },
    mapping = {
        ['<Tab>'] = cmp.mapping.select_next_item(),
        ['<S-Tab>'] = cmp.mapping.select_prev_item(),
        ['<CR>'] = cmp.mapping.confirm({ select = true }),
        ['<C-Space>'] = cmp.mapping.complete(),
    },
})
-- autoformat on save
local format_on_save = false
vim.api.nvim_create_autocmd("BufWritePre", {
    group = vim.api.nvim_create_augroup("FormatOnSave", { clear = true }),
    callback = function()
        if format_on_save then
            vim.lsp.buf.format()
        end
    end,
})

vim.api.nvim_create_user_command("ToggleFormatOnSave", function()
    format_on_save = not format_on_save
    vim.notify("Format on save: " .. (format_on_save and "enabled" or "disabled"))
end, { desc = "Toggles format on save" })
vim.keymap.set('n', '<leader>ss', ':ToggleFormatOnSave<CR>') 

-- Quickfix
vim.api.nvim_create_autocmd("FileType", {
  pattern = "qf",
  callback = function()
    vim.keymap.set("n", "dd", function()
      local qflist = vim.fn.getqflist()
      local line = vim.fn.line(".") - 1  -- 0-indexed
      table.remove(qflist, line + 1)
      vim.fn.setqflist(qflist)
    end, { buffer = true })
  end,
})

-- Main keybindings

-- Fuzzy
local builtin = require('telescope.builtin')
vim.keymap.set('n', '<leader>ff', builtin.find_files)        -- SPACE f f finds files in the current directory, minus those in gitignore
vim.keymap.set('n', '<leader>fg', builtin.live_grep)         -- SPACE f g finds text inside files in the current directory, minus those in gitignore
vim.keymap.set('n', '<leader>fb', builtin.buffers)           -- SPACE f b finds files currently opened
vim.keymap.set('n', '<leader>fH', builtin.help_tags)         -- SPACE f H looks through the help pages for neovim and plugins
vim.keymap.set('n', '<leader>fh', ':Telescope frecency<CR>') -- SPACE f h looks through files sorted by how often and how recently they've been opened
vim.keymap.set('n', '<leader>fc', builtin.git_commits)       -- SPACE f c looks through git commits and shows the diffs
vim.keymap.set('n', '<leader>fs', builtin.git_status)        -- SPACE f s looks through changed files (from git status)

-- Git
vim.keymap.set('n', '<leader>gb', ':Git blame<CR>')  -- SPACE g b shows an inline git blame for the current file
vim.keymap.set('n', '<leader>gs', ':Git status<CR>') -- SPACE g s shows a quick overview of the git status
vim.keymap.set('n', '<leader>gg', ':Git<CR>')        -- SPACE g g opens a full git fugitive window for managing changes and more
vim.keymap.set('n', ']g', ':GitGutterNextHunk<CR>')  -- ] g goes to the next changed piece of code
vim.keymap.set('n', '[g', ':GitGutterPrevHunk<CR>')  -- [ g goes to the previous changed piece of code

--
vim.keymap.set('n', '<leader>b', ':ToggleBackground<CR>') -- [ g goes to the previous changed piece of code


-- Leap
vim.keymap.set({ 'n', 'x', 'o' }, 's', '<Plug>(leap)') -- s triggers vim leap, to jump to another part of the screen by character tags
vim.keymap.set('n', 'S', '<Plug>(leap-from-window)')   -- S triggers the same but more globally

-- File management
vim.keymap.set('n', '<leader>o', ':Oil<CR>') -- SPACE o opens interactive file explorer with ability to rename/delete/move files as a buffer

-- Treesitter
vim.api.nvim_create_autocmd("FileType", {
    callback = function(ev)
        pcall(vim.treesitter.start, ev.buf)
    end
})

-- Specialized languages
require('rocq')
require('koka')

-- Normal LSP's
vim.lsp.enable('lua_ls')
vim.lsp.enable('ocamllsp')
-- on_init = function(client)
--     client.server_capabilities.semanticTokensProvider = nil
-- end,
vim.lsp.enable('koka')     -- configured separately above
vim.lsp.enable('clangd')
vim.lsp.enable('millet')   -- SML language server
vim.lsp.enable('tinymist') -- typst language server

-- Custom macros for dumb shit

vim.keymap.set('n', '<leader>cc', 'olet goal = make_goal [%term ] in') 
```
