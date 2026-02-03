# Roadmap

## Now

- [] Write a small subsystem for automatically adding proven statements to some sort of state for use in rewrites/applications (this is done manually right now)
- [] Refactor tactics to use handlers rather than arguments where it makes sense
- [] Test existing handlers more thoroughly
- [] Set up core theorems and definitions in theories of Nat, List, Pair
- [] Refactor handlers to always assume they are running under ambient handler [../lib/tactic.ml]
    - [] New modules for foundational tactics system (effect definitions, core tactics, ambient handle), tactic combinators, and search handlers?
- [] Write more tests for rewriting [../test/rewrite_test.ml]
- [] Write more combinators for specific choices of terms, theorems, etc to facilitate targeted rewriting [../lib/tactic.ml]
- [] Refactor tracing in search handlers (maybe just keep the whole trace and throw out all but the final successful proof) [../lib/tactic.ml]
- [] Refactor error variants to carry useful information [../lib/kernel.ml]

## Soon
- [] Set up core theorems and definitions of Set
- [] Cleanly separate and document safe vs unsafe tactics [../lib/tactic.ml]
- [] Write auto tactic inspired by aesop [../lib/tactic.ml]
    - [] Create best-first handler

## Stretch Goals
- [] Decide if there should be a separate user facing module for tactics and combinators that are pre configured for most use cases.
- [] Create a cli interface around the with_interactive choice handler
    - [] Built on top of an ocaml toplevel, proof of concept that this architecture can match HOL-light
- [] Write a simple parser for hol terms
- [] Write a simple parser for hol definitions
