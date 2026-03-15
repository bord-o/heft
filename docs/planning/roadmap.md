# Roadmap

## Now

- [] Write auto tactic inspired by aesop [../lib/tactic.ml]
    - [] Write aesop pseudocode
    - [] Translate aesop pseudocode to our architecture
    - [] Make safe and fast normalization to be called in between tactic choices
- [] Make full use of available context in priority queue
    - [] Goal x tactic combination analysis
    - [] Are there situations where choice should beat subgoal/resume?
- [] Add more test cases for ctauto and itauto
    - [] Add more benchmarks that show dfs vs best-first comparison directly
- [] Add forward reasoning tactic
- [] Test existing handlers more thoroughly
- [] Write more tests for rewriting [../test/rewrite_test.ml]
- [] Refactor error variants to carry useful information [../lib/kernel.ml]
- [] Clean up [tactic.ml]

## Soon
- [] Set up core theorems and definitions of Set

## Eventually 
- [] ~Let language recurse on arbitrary argument~
- [] Decide if there should be a separate user facing module for tactics and combinators that are pre configured for most use cases.
- [] Create a cli interface around the with_interactive choice handler
    - [] Built on top of an ocaml toplevel, proof of concept that this architecture can match HOL-light

## Done
- [ x ] Transitivity tactic
- [ x ] Add existential tactic
- [ x ] Write a small subsystem for automatically adding proven statements to some sort of state for use in rewrites/applications (this is done manually right now)
- [ x ] Add handlers for with_proven; with_safe; with_definitions; with_only
- [ x ] Upgrade language to not need "over ?x" in definitions
- [ x ] Move proven theorems into theorems.ml if they aren't actually testing edge cases or features (debloat test file)
- [ x ] Refactor tactic tests
- [ x ] Refactor tactics to use handlers rather than arguments where it makes sense
- [ x] Set up core theorems and definitions in theories of Nat, List, Pair
- [ x ] Refactor handlers to always assume they are running under ambient handler [../lib/tactic.ml]
    - [ x ] New modules for foundational tactics system (effect definitions, core tactics, ambient handle), tactic combinators, and search handlers?
- [ x ] Write more combinators for specific choices of terms, theorems, etc to facilitate targeted rewriting [../lib/tactic.ml]
- [ x ] Refactor tracing in search handlers (maybe just keep the whole trace and throw out all but the final successful proof) [../lib/tactic.ml]
- [ x ] Write a simple parser for hol terms
- [ x ] Write a simple parser for hol definitions
- [ x ] Cleanly separate and document safe vs unsafe tactics [../lib/tactic.ml]
- [ x ] Create best-first handler
