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
(* Apply tac2 to subgoal from tac1 *)
let (>>) tac1 tac2 goal =
  match tac1 goal with
  | effect Subgoal g, k -> continue k (tac2 g)
  | v -> v

(* Apply tactics to subgoals in order *)
let thenl tac1 tacs goal =
  let remaining = ref tacs in
  let rec handler f =
    match f () with
    | effect Subgoal g, k ->
        match !remaining with
        | [] -> fail ()
        | t :: ts ->
            remaining := ts;
            let thm = t g in
            handler (fun () -> continue k thm)
    | v -> v
  in
  handler (fun () -> tac1 goal)

(* Apply same tactic to all subgoals *)
let then_all tac1 tac2 goal =
  let rec handler f =
    match f () with
    | effect Subgoal g, k ->
        let thm = tac2 g in
        handler (fun () -> continue k thm)
    | v -> v
  in
  handler (fun () -> tac1 goal)
```

### Layer 2: Iteration (handle Fail, check progress)
```ocaml
(* Try tactic, pass through if fails *)
let try_ tac goal =
  match tac goal with
  | effect Fail, _ -> perform (Subgoal goal)
  | v -> v

(* Repeat while making progress, fail when done *)
let rec repeat tac goal =
  match tac goal with
  | effect Fail, _ -> fail ()
  | effect Subgoal g, k when g = goal -> fail ()
  | effect Subgoal g, k -> continue k (repeat tac g)
  | v -> v
```

### Layer 3: Choice (performs Choose)
```ocaml
(* Pick first tactic that applies *)
let first tacs goal =
  let tac = perform (Choose (Tactic tacs)) in
  tac goal
```

### Layer 4: Search (handle Choose + Subgoal)
```ocaml
let with_dfs tac goal =
  let rec handler f =
    match f () with
    | effect Choose choices, k ->
        let r = Multicont.Deep.promote k in
        let rec try_each = function
          | [] -> fail ()
          | c :: cs ->
              match handler (fun () -> Multicont.Deep.resume r c) with
              | effect Fail, _ -> try_each cs
              | thm -> thm
        in
        try_each (as_chosen_list choices)
    | effect Subgoal g, k ->
        let thm = handler (fun () -> tac g) in
        handler (fun () -> continue k thm)
    | effect Fail, _ -> fail ()
    | v -> v
  in
  handler (fun () -> tac goal)

(* BFS uses queue instead of stack *)
let with_bfs tac goal = ...

(* Best-first uses priority queue *)
let with_best_first cost_fn tac goal = ...
```

### Layer 5: Effect Providers
```ocaml
let with_rewrites rw tac goal =
  match tac goal with
  | effect Rewrites (), k -> continue k rw
  | v -> v

let with_lemmas lems tac goal =
  match tac goal with
  | effect Lemmas (), k -> continue k lems
  | v -> v

let with_fuel limit tac goal =
  match tac goal with
  | effect Burn n, k ->
      limit := !limit - n;
      if !limit < 0 then fail () else continue k ()
  | v -> v
```

### Layer 6: Ambient Handler
```ocaml
let prove goal tac =
  let rec ambient f =
    match f () with
    | effect Trace (_, msg), k -> print_endline msg; continue k ()
    | effect Burn _, k -> continue k ()
    | effect Rank r, k -> continue k (as_ranked_list r)
    | effect Rewrites (), k -> continue k !Lemmas.simp_rules
    | effect Lemmas (), k -> continue k !Lemmas.safe_lemmas
    | effect Choose c, k -> continue k (List.hd (as_chosen_list c))
    | effect Subgoal _, _ -> None
    | effect Fail, _ -> None
    | thm -> Some thm
  in
  ambient (fun () -> tac goal)
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
  (conj_tac |> thenl [
    assumption_tac;
    intro_tac >> assumption_tac
  ])
)
```

### Automation
```ocaml
let auto tacs = first tacs

prove goal (
  with_dfs (auto [intro_tac; conj_tac; assumption_tac])
)
```

### Hybrid
```ocaml
prove goal (
  intro_tac >>
  (conj_tac |> thenl [
    with_dfs (auto structural_tacs);
    assumption_tac
  ])
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
  with_rewrites my_rules (
    with_lemmas my_lemmas (
      with_dfs (auto [simp_tac; apply_tac; assumption_tac])
    )
  )
)
```

## Key Insights

1. **Tactics must progress or fail** - never `Subgoal g` where `g = goal`
2. **Search owns Choose + Subgoal** - controls backtracking and recursion
3. **repeat checks progress** - safe under search handlers
4. **One prove, many strategies** - composition via combinators
5. **Providers are orthogonal** - wrap at any level
