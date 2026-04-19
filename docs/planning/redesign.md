# Tactic Architecture

## Core Principle

Single `prove` function as ambient handler. Tactics compose via combinators. Search is a combinator that handles `Choose` and `Subgoal`. Tactics must either succeed, make progress, or fail.

## Effects

| Effect        | Meaning                       |
|---------------|-------------------------------|
| `Subgoal g`   | "Prove g to continue"         |
| `Choose xs`   | "Pick one of these"           |
| `Fail`        | "I don't apply / no progress" |
| `Trace`       | Logging                       |
| `Burn n`      | Consume n fuel                |
| `Rules ()`    | "Give me rewrite/apply rules" |
| `Rank xs`     | "Sort these by heuristic"     |

## Tactic Contract

- **Fail when:** tactic doesn't apply or makes no progress
- **Subgoal when:** tactic made progress, needs subgoal proved
- **Never:** produce `Subgoal g` where `g = goal` (no progress)
- **Tactics never handle effects**, only perform them

## Combinator Layers

### Layer 1: Sequencing (handle Subgoal)
```ocaml
val ( >> ) : tactic -> tactic -> goal -> Kernel.thm
```

### Layer 2: Iteration (handle Fail, check progress)
```ocaml
val try_ : tactic_combinator
val with_repeat : tactic_combinator
```

### Layer 3: Choice (performs Choose)
```ocaml
val pick : tactic list -> tactic
```

### Layer 4: Search (handle Choose + Subgoal)
```ocaml
(* BFS uses queue instead of stack *)
(* Best-first uses priority queue *)
(* DFS uses call stack *)
val with_dfs : tactic_combinator

```

### Layer 5: Effect Providers
```ocaml
val with_fuel_limit : int ref -> tactic_combinator
val with_no_trace : ?show_proof:bool -> tactic_combinator
val with_rules : Kernel.thm list -> tactic_combinator
val with_proven : string list -> tactic_combinator
```

### Layer 6: Ambient Handler
```ocaml
(* Prove handles all effects with a naive implementation and optionally
    saves finished proofs to the rule set *)
val prove : ?name:string -> goal -> tactic -> proof_state
```

## Bubbling Rules

| Layer      | Handles                        | Bubbles Up               |
|------------|--------------------------------|--------------------------|
| Tactics    | nothing                        | everything               |
| Sequencing | Subgoal                        | Choose, Fail, Trace, ... |
| Iteration  | Fail, Subgoal (progress check) | Choose, Trace, ...       |
| Search     | Choose, Subgoal                | Fail, Trace, Burn, ...   |
| Providers  | their effect                   | everything else          |
| Ambient    | everything                     | nothing                  |

## Usage Patterns

### Manual Proof
```ocaml
prove goal (
  intro >>
  (conj  >>
    assumption >>
    intro >> assumption
  ])
)
```

### Automation
```ocaml
let auto tacs = pick tacs

prove goal (
  with_dfs (auto [intro; conj; assumption])
)
```

### Hybrid
```ocaml
prove goal (
  intro >>
  conj >> 
    with_dfs (auto structurals) >>
    assumption
)
```

### With Iteration
```ocaml
prove goal (
  with_dfs (
    repeat simp_step >> 
    auto [intro; conj; assumption]
  )
)
```

### With Providers
```ocaml
prove goal (
  with_proven "add_comm" (
      with_dfs (auto [simp; apply; assumption])
    )
)
```

## Key Insights

1. **Tactics must progress or fail** - never `Subgoal g` where `g = goal`
2. **Search owns Choose + Subgoal** - controls backtracking and recursion
3. **repeat checks progress** - safe under search handlers
4. **One prove, many strategies** - composition via combinators
5. **Providers are largely orthogonal** - wrap at any level


# New design for bfs

What if I could construct a lazy sequence of proofs in their entirety by saving
the continuations at each step. This would give me total control of the exploration
and make the most use of my architecture. 

I could design it with an interactive element to begin, sort of like
best first search, but the user is in the loop to decide what is best.

I would need some way to say:

starting with a tactic and a goal, what are all the reachable states from this?
I would need to run the tactic, and collect all of the continuations for either
choice or subgoal.

I could then pick which one to continue.

I should be able to jump from anywhere on the tree to any other point and
continue from there.

If any node solves the goal completely I should be able to fold up the continuations
leading up to that node in order to solve the original goal.

Right now this is all implicit in the DFS implementation, where the 
"tree" i'm talking about is just the call stack. 

I need to identify what the call stack looks like during dfs, and find a way to model
it by saving its parent continuations

If I pull this off it will be a totally search strategy agnostic system,
I shouldn't even need separate implementations for bfs/dfs, just a way to choose between
the different continuations

I think i did this ^
