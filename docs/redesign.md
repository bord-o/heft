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
val pick_tac : tactic list -> tactic
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
  intro_tac >>
  (conj_tac  >>
    assumption_tac >>
    intro_tac >> assumption_tac
  ])
)
```

### Automation
```ocaml
let auto tacs = pick_tac tacs

prove goal (
  with_dfs (auto [intro_tac; conj_tac; assumption_tac])
)
```

### Hybrid
```ocaml
prove goal (
  intro_tac >>
  conj_tac >> 
    with_dfs (auto structural_tacs) >>
    assumption_tac
)
```

### With Iteration
```ocaml
prove goal (
  with_dfs (
    repeat simp_step >> 
    auto [intro_tac; conj_tac; assumption_tac]
  )
)
```

### With Providers
```ocaml
prove goal (
  with_proven "add_comm" (
      with_dfs (auto [simp_tac; apply_tac; assumption_tac])
    )
)
```

## Key Insights

1. **Tactics must progress or fail** - never `Subgoal g` where `g = goal`
2. **Search owns Choose + Subgoal** - controls backtracking and recursion
3. **repeat checks progress** - safe under search handlers
4. **One prove, many strategies** - composition via combinators
5. **Providers are largely orthogonal** - wrap at any level
