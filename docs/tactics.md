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
## Rewriting
  need to match the lhs of the chosen rule with our goal and get theta

  say we have
    add 0 n = n
  as a rule

  and our goal is 
    add 0 2 = add 1 1

  we should be able to use this tactic to rewrite to
    2 = add 1 1
  by
    term match lhs goal with rule to get n->2
    inst the rule to get add 0 2 = 2
    now we have
      add 0 2 = 2 : thm
      add 0 2 = add 1 1 : term
    so we can just use the rhs of the instantiated rule instead of our
    goal's original lhs, giving
      2 = add 1 1

    when we solve this subgoal we will get it as a thm
      2 = add 1 1 : thm
    with which we can use sym and trans of equality to build our original thm.
    again we need to get from
      2 = add 1 1 : thm
    to
      goal := add 0 2 = add 1 1 :thm
    with
      add 0 2 = 2 : thm
    using
      trans irule subthm

