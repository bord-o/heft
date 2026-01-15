# Tactics

## Traditional LCF Approach

## Motivation

Tactics are inherently inflexible. For one, they are usually stratified from the surface language of the ITP, relegated to the confines of a meta-language that the user may or may not know how to use. Other ITPs opt to keep them in the surface language, but still face friction through the learning curve of DSL's (Rocq) or complex meta-programming (Lean4).

Tactics are often built in a monolithic fashion, where decisions about how to carry out the tactic are configured within the tactic itself, with the goal of functioning well across a potentially wide range of use cases. These 'decisions' include:
    - Which rule to try first
    - Which rule to apply if multiple are applicable
    - Where in the goal should we apply the rule
    - Should I fail or retry
    - How much data should I report back to the user
    - What search strategy should I use

## Concept : Tactic Handlers

todo

## Effectful Tactic Combinators

todo

## Searching with Tactic Handlers

todo


