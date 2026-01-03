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



```ocaml
type _ Effect.t += Subgoal : goal -> thm Effect.t
type _ Effect.t += Fail : unit Effect.t

let conj_tac : goal -> thm = fun (asms, concl) ->
    let l, r = destruct_conj concl |> Result.value ~default:(perform Fail) in
    let lthm = perform (Subgoal (asms, l) in
    let rthm = perform (Subgoal (asms, r) in
    conj lthm rthm


type proof_state = Incomplete of goal | Complete of thm

let rec prove g = function
    | [] -> Incomplete g
    | tactic::tactics ->
        (match tactic g with
            | effect (Fail), k -> Incomplete g
            | effect (Subgoal g'), k ->
                (match prove g' tactics with
                    | Complete thm -> Complete (continue k thm)
                    | incomplete -> incompleteA)
            | thm -> Complete thm)
```
