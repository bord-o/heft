# Heft

**An interactive higher-order-logic theorem prover for OCaml, built on algebraic effects.**

Heft is a proof assistant in the [LCF tradition](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions), built on top of a small kernel a la [HOL Light](https://hol-light.github.io). Heft implements a system of proof refinement through algebraic effects, enabling a small uniform tactic DSL, and direct-style code when authoring tactics and automation. In addition, Heft integrates closely with the OCaml language ecosystem, leveraging [PPX](https://ocaml.org/docs/metaprogramming) to allow logical definitions and statements to be written in OCaml syntax directly.


---

## Why build another prover?

Heft started as an exploration on usability in theorem provers, and its initial goal was trying to answer a specific question: 

*Is the stratified and often complex [multi-language user experience](https://bord-o.github.io/0008/index.xml) of HOL based provers a natural inevitability of the LCF architecture, or can a HOL prover be made to integrate cleanly into an existing language ecosystem?*

This question was posed because, though dependent type theory provides a strong foundation for building theorem provers [without a meta-language/object-language distinction](https://lean-lang.org/), it comes with sizable cognitive overhead. Higher order logic provides a more intuitive (arguably) mathematical foundation for programmers without formal methods experience. With strong language ecosystem integration I believe it can enable a stronger user experience and wider adoption.

Part of the [proof assistant stratification problem](https://bord-o.github.io/0008/index.xml) is the need for an object, meta, and tactic language, so solving the language stratification problem amounts to unifying or simplifying the distinction between those three languages. Heft uses OCaml's PPX system to blur the distinction between the object and meta language in a relatively simple and predictable way ([see use in nats.ml](theories/nats/nats.ml)), but for the tactic language we need a different approach. As it turns out, algebraic effects map cleanly onto the control flow patterns of proof refinement in LCF systems, and more importantly, enable a unified API across tactics, meaning there is less of a "language" to learn for end users ([see tactic.ml](lib/tactic.ml)). Outside of a few combinators familiar to users of other provers like [HOL4](https://hol-theorem-prover.org/) or [Rocq](https://rocq-prover.org/), nearly all Heft core tactics take no arguments and have the same type. Tactic questions like 'which term should I use for induction', 'what should I do in case of failure', and 'which rules should I try to rewrite with' are all decided by effect handlers.

---

## Basic Usage

Defining the natural numbers, a recursive function, and proving a theorem about it:

```ocaml
open Heft
open Tactic
open Auto

[%%inductive type nat = Zero | Suc of nat]

let%primrec plus (n : nat) (m : nat) : nat =
  match n with
  | Zero    -> m
  | Suc n'  -> Suc (plus n' m)

(* ∀ x y. plus x y = plus y x *)
let%thm plus_comm (x : nat) (y : nat) = 
    plus x y = plus y x
and proof =
  begin
    induct >>= [ 
        (* Solve the base case with proof search over core tactics *)
        auto_dfs; 

        (* Solve inductive case with proof search, leveraging the inductive hypothesis automatically *)
        with_info_trace auto_dfs  
    ]
  end
  [@quiet]
  (* [@trace] optionally enable tracing to debug proofs. All tactics share an effects-based tracing and tactic registration framework. *)
  (* [@simp] optionally add the finished theorem to the simp set for later proofs. *)
```

Here is the exact same proof, presented in a more manual style that shows some handler stacking to override default behavior. Note that the goal has `x` and `y` swapped now. 

```ocaml
let%thm plus_comm (y : nat) (x : nat) = 
    plus x y = plus y x
and proof =
  begin
    (* [induct] will dispatch the first quantified variable by default, but we can give a specific term if we want *)
    with_term [%term (x:nat)] induct   
    (* in [tac1 @>> tac2] the [@>>] combinator apply tac2 to all subgoals produced by tac1 *)
    @>> with_info_trace @@ with_dfs @@ auto 
  end
  [@quiet]
```


## Building

Requires OCaml 5.4. Build as any dune-based project.

```
opam install . --deps-only
dune build
dune test
```

## Using Heft within your project 

If you want to try to prove some things about a pure function in your codebase, it's quite straightforward to integrate Heft. To write definitions and proofs we'll need two things, the Heft PPX, and the Heft library, which provides tactics, automation, and proof execution primitives. If you have any issues getting a project set up, please see [Hefts own theory development binary](theory_dev/dune) for some context.

Since Heft is not on Opam yet, we will need to first pin it.

```
$ opam pin https://github.com/bord-o/heft.git
```

This will fetch and build the dependencies, then Heft itself. With heft installed, all we need to do is create a new dune binary in our client project.

```
$ mkdir proofs
$ dune init executable proofs ./proofs/ --libs heft,heft.theories.lists --ppx heft.ppx_heft --public
```

This will setup a new executable for proving in batch mode. To run a proof lets edit `proofs.ml`

```ocaml
open Heft
open Tactic
open Auto


[%%inductive type color = Red | Green | Blue]

let myauto = 
    with_no_automation_trace @@ with_dfs' @@ pick [
      induct;
      simp ~with_asms:true;
      or_;
    ]

let%thm test (c : color) = 
    c = Red || c = Green || c = Blue
and proof = 
    begin
        myauto
    end
```

Here we make a new inductive type, write ourselves a targeted proof search for our problem, then dispatch the proof search over our little exhaustiveness goal. When working on batch mode proofs it's nice to have a second terminal with the proof execution output pulled up next to our editor, running the command:

```
$ dune exe proofs -w
```

Which will run the proof each time the file changes, and print out the subgoal/completion information.

```sh
========================================
∀x. x = Red ∨ x = Green ∨ x = Blue

Proof Complete!
with fuel: 335
```

At this point, transferring your code into Heft is just a matter of adding a `let%primrec` instead of `let rec` for recursive functions, `let%def` instead of `let` for non-recursive expressions, and `let%wfrec` for `let rec` in the case of a recursive definition that requires explicit termination reasoning.

For using Heft's built-in lemma libraries like `heft.theories.lists` you'll want to add a line to your dune file for the proofs binary. This will ensure that theory dependencies are linked and executed to ensure proper handling of runtime dependencies in the HOL object language.

```dune
(link_flags (:standard -linkall))
```

## Docs

The auto-generated documentation is hosted [here](https://bord-o.github.io/heft/heft/Heft/index.html).

---

## Limitations

In its current state, Heft supports a pure subset of OCaml, meaning that mutable references, structs, and much of the standard library is not directly expressible in Heft without choosing an encoding. The Heft PPX is also limited in its support of pattern matching, there is clear literature on de-sugaring nested patterns into a term language with concrete eliminators, as the HOL term language has, but this hasn't been implemented yet (take a look at [rubiks.ml](theory_dev/rubiks.ml) to see this limitation in action).

Heft is still in active development. Though it's already possible to prove quite sophisticated results, it lacks a large basis of basic CS/Math lemmas, and even foundational tactics, the rewriting system, and core abstractions might change in the future. 

I intend for Heft to be a place where folks can experiment with LCF provers on top of a clean modern codebase, with clean abstractions for writing proof automation or decision procedures.

### Trust

Heft provides the same trust guarantees as HOL Light, with a couple of exceptions. Due to resource constraints, induction theorems for user provided data types are generated at runtime, after checking that the type doesn't violate some invariants that would lead to unsoundness (strictly positive, base case exists, etc). This code could be completely removed upon deriving induction theorems like HOL Light, this was just skipped for brevity. Other theorems like recursion, distinctness, and injectivity are generated per-type as well, but could be derived a la HOL Light in the future.

## Acknowledgments

Heft's kernel [kernel.ml](lib/kernel.ml) is largely a port of John Harrison's [fusion.ml](https://github.com/jrh13/hol-light/blob/master/fusion.ml) from HOL Light, and the system as a whole borrows many ideas from the larger LCF lineage of proof assistants.
