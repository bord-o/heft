# Practical Proof Guide for Heft

A guide for writing proofs in Heft's tactic system, aimed at someone familiar with Coq/Lean who wants to understand how things work (and where they don't yet).

## Key Differences from Coq/Lean

### No Unification-Based Application

Coq's `apply` unifies the conclusion of a hypothesis with the goal and instantiates universally quantified variables automatically. Heft's `apply_asm` only works on bare implications `P ==> Q` where `Q` literally matches the goal. It does **not** handle `∀x. P x ==> Q x` — the forall must be stripped first.

`apply_thm` (used with `with_assumptions` or `with_proven`) does strip foralls and uses `match_term`, but it operates on theorems provided via the `Rules` effect, not directly on assumptions. So to "apply" a universally quantified assumption:

```ocaml
(* Wrong — apply_asm won't match ∀n. P n ==> Q n *)
apply_asm

(* Right — convert assumptions to Rules, then apply_thm does matching *)
with_assumptions (with_first (apply_thm >> assumption))
```

The `with_first` is often necessary because `apply_thm` will try each theorem via `Choose`, and without `with_first` it just takes the first one (which may not be the right one).

### No `destruct` on Free Variables

In Coq you can `destruct n` on any variable in scope. Heft's `cases` and `induct` require the goal to start with `∀x. ...`. If `x` appears free in assumptions and the goal, you need `destruct`:

```ocaml
(* n is free in assumptions and goal *)
with_arbitrary_term n destruct >> induct >> ...
```

`destruct` works by:
1. Discharging all assumptions mentioning the variable into the goal as implications
2. Wrapping with `∀var. ...`
3. Firing a subgoal for the generalized goal
4. After the subgoal returns, spec'ing the variable back and mp'ing to recover assumptions

The consequence: after `destruct >> induct`, each case has extra `==>` from the discharged assumptions. You need `intros` to recover them.

### Subgoal Sequencing with `>>`

`>>` is `then_one` — it applies the second tactic to the **first** subgoal only. Remaining subgoals bubble up. This means:

```ocaml
induct >> base_case >> step_case
```

This works because `induct >> base_case` solves the base case (first subgoal), then `>> step_case` handles the step case (which is now the first remaining subgoal).

For explicit control, use `>>=` (then_each):

```ocaml
induct >>= [
  base_case;     (* applied to first subgoal *)
  step_case;     (* applied to second subgoal *)
]
```

And `@>>` (then_all) applies the same tactic to all subgoals.

### `simp` vs `simp_asm`

- `simp` simplifies the **goal** using definition unfolding rules
- `simp_asm ~with_asms:false` simplifies **assumptions** using definition unfolding
- `simp ~with_asms:true` additionally uses assumptions as rewrite rules for the goal

Beware: `simp` does **not** handle conditional rewrites (like `P ==> x = y`). If an assumption is `∀n. P n ==> Q n`, simp won't use it to rewrite `Q t` to `T`.

### Deriving Contradiction from `T = F`

There is no `discriminate` tactic. If you reduce an absurd premise to `T = F` in the assumptions, the incantation is:

```ocaml
sym_asm >> eq_true_elim_asm >> false_elim
```

This works because:
1. `sym_asm` flips `T = F` to `F = T`
2. `eq_true_elim_asm` converts `F = T` to `F` (since `P = T` yields `P`)
3. `false_elim` closes any goal when `F` is in assumptions

### Boolean Encoding

Heft uses HOL-style encoding where propositions are boolean terms. `sorted l` is a term of type `bool`, not `Prop`. Equality is `=`, implication is `==>`, and everything evaluates to `T` or `F`.

Pattern-matching definitions (like `sorted`, `insert`) expand into `COND` (if-then-else) and `list_match`/`nat_match` terms. After `simp`, you'll often see raw COND expressions:

```
COND (nat_le n0 n) (cons n0 (insert n1 n)) (cons n (cons n0 n1))
```

Use `cond` to case-split on the condition, or `with_arbitrary_term expr cases` for a specific boolean expression.

## Common Proof Patterns

### Double Induction (e.g., properties of `nat_le`)

When you need to induct on two variables, keep both universally quantified and chain inductions:

```ocaml
induct >>= [
  (* base case for first variable *)
  ...;
  (* step case — intro IH, then induct on second variable *)
  gen >> intro >> induct >>= [
    (* base of second *) ...;
    (* step of second *) ...;
  ];
]
```

### Case Splitting on Booleans Mid-Proof

When the goal contains `COND b ...`, use:

```ocaml
cond   (* auto-finds COND conditions and splits *)
```

Or for a specific expression:

```ocaml
with_arbitrary_term (nat_le x y) cases
```

This adds `nat_le x y = T` or `nat_le x y = F` to assumptions in each branch.

### Using Proven Lemmas

```ocaml
(* Use registered lemma as rewrite rule *)
with_proven ["lemma_name"] rewrite

(* Use registered lemma for simplification *)
with_proven ["lemma_name"] simp

(* Apply lemma to goal (strips foralls, matches conclusion) *)
with_proven ["lemma_name"] apply_thm
```

Lemmas are registered via `run_proof ~name:"lemma_name" goal proof`.

### Keeping Variables Generalized

A general principle: don't intro universally quantified variables unless you need to. Keeping `∀n. P n` as the goal lets `induct` work directly. If you intro `n` and it becomes free, you'll need `destruct` to generalize it back, which creates a more complex goal.

In Coq terms: prefer `induction n` on `∀n. P n` over `intros n; destruct n` when possible.

## Tactic Quick Reference

| Tactic | Effect | Analogue |
|--------|--------|----------|
| `intro` | Intro one `==>` | `intro` (implication only) |
| `gen` | Intro one `∀` | `intro` (universal only) |
| `intros` | Repeat intro/gen | `intros` |
| `assumption` | Exact match in asms | `assumption` |
| `refl` | Prove `x = x` | `reflexivity` |
| `simp` | Unfold + rewrite goal | `simp` |
| `simp_asm` | Simplify assumptions | `simp at h` |
| `induct` | Structural induction | `induction` (needs `∀`) |
| `cases` | Case split | `cases` (needs `∀` or bool) |
| `destruct` | Case split free var | `destruct` |
| `cond` | Split on COND expr | `destruct (decide ...)` |
| `conj` | Split `∧` goal | `split` |
| `left` / `right` | Choose `∨` side | `left` / `right` |
| `apply_asm` | Apply `P ==> Q` asm | `apply` (no unification) |
| `apply_thm` | Apply theorem w/ matching | `apply` (with unification) |
| `mp_asm` | Modus ponens in asms | `specialize` + `apply` |
| `rewrite` | Rewrite goal with rules | `rewrite` |
| `rewrite_asm` | Rewrite assumption with rules | `rewrite ... in h` |
| `false_elim` | Close goal from `F` | `contradiction` (literal F only) |
| `neg_elim` | Contradiction from P, ¬P | `contradiction` |
| `truth` | Prove `T` | `trivial` |
| `ccontr` | Classical contradiction | `by_contra` |

## Combinators Quick Reference

| Combinator | Meaning |
|-----------|---------|
| `tac1 >> tac2` | Apply tac2 to first subgoal of tac1 |
| `tac1 @>> tac2` | Apply tac2 to all subgoals of tac1 |
| `tac >>= [t1; t2]` | Apply t1 to first subgoal, t2 to second |
| `with_first tac` | Try all choices, take first success |
| `with_dfs tac` | Depth-first search over choices |
| `with_arbitrary_term t tac` | Force term choice (bypass Choose) |
| `with_term t tac` | Force term choice (must be in choices) |
| `with_assumptions tac` | Provide assumptions as Rules |
| `with_proven ["x"] tac` | Provide named theorems as Rules |
| `with_flip_rules tac` | Reverse direction of rewrite Rules |
| `with_repeat tac` | Repeat until fixpoint or failure |
| `with_nth_choice n tac` | Select nth option at Choose |
| `solve tac` | Fail if subgoals remain |

## Missing Tactics (Wish List)

### `discriminate`
Derive `F` from absurd equalities like `T = F`, `zero = suc n`, `nil = cons x xs`. Currently requires the manual `sym_asm >> eq_true_elim_asm >> false_elim` dance, which only works for `T = F` — constructor inequalities for inductives aren't handled at all.

### `spec_asm`
Specialize a universally quantified assumption `∀x. P x` with a specific term to get `P t`. Currently you have to go through `with_assumptions apply_thm`, which is indirect and sometimes fragile. A direct `spec_asm t` that finds `∀x. ...` in assumptions and adds the specialized version would be very useful.

### `injection`
From `cons x xs = cons y ys`, derive `x = y` and `xs = ys`. Constructor injectivity isn't directly exploitable right now.

### `subst`
Given `x = t` in assumptions, substitute `t` for `x` everywhere (in other assumptions and the goal). This would clean up many proof states that are cluttered with equalities.

## Debugging Tips

- **Use `>>=` early**: When a proof isn't working with `>>` chains, switch to `>>=` to handle each subgoal explicitly. This makes it clear which branch is failing.
- **Stop the proof early**: Replace the rest of a tactic chain with nothing to see the intermediate goal state in the expect output. The "Proof Incomplete" output shows you the current assumptions and goal.
- **Watch the fuel count**: If fuel increases but the proof stays incomplete, your tactics are making progress on one branch but failing on another.
- **`simp_asm ~with_asms:false` before `simp`**: Simplify assumptions first so they're in normal form, then simplify the goal. Using `~with_asms:true` on simp can then use the simplified assumptions.
- **Check what `Choose` returns**: Many tactics use `Choose` internally. If a tactic silently fails, it might be choosing the wrong term. Wrap with `with_first` to try all options, or `with_nth_choice n` to pick a specific one.
