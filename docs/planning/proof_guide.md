# Practical Proof Guide for Heft

A guide for writing proofs in Heft's tactic system, aimed at someone familiar with Coq/Lean who wants to understand how things work (and where they don't yet).

## Key Differences from Coq/Lean

### No Unification-Based Application

Coq's `apply` unifies the conclusion of a hypothesis with the goal and instantiates universally quantified variables automatically. Heft's `apply_asm_tac` only works on bare implications `P ==> Q` where `Q` literally matches the goal. It does **not** handle `∀x. P x ==> Q x` — the forall must be stripped first.

`apply_thm_tac` (used with `with_assumptions` or `with_proven`) does strip foralls and uses `match_term`, but it operates on theorems provided via the `Rules` effect, not directly on assumptions. So to "apply" a universally quantified assumption:

```ocaml
(* Wrong — apply_asm_tac won't match ∀n. P n ==> Q n *)
apply_asm_tac

(* Right — convert assumptions to Rules, then apply_thm_tac does matching *)
with_assumptions (with_first (apply_thm_tac >> assumption))
```

The `with_first` is often necessary because `apply_thm_tac` will try each theorem via `Choose`, and without `with_first` it just takes the first one (which may not be the right one).

### No `destruct` on Free Variables

In Coq you can `destruct n` on any variable in scope. Heft's `cases_tac` and `induct_tac` require the goal to start with `∀x. ...`. If `x` appears free in assumptions and the goal, you need `destruct_tac`:

```ocaml
(* n is free in assumptions and goal *)
with_arbitrary_term n destruct_tac >> induct_tac >> ...
```

`destruct_tac` works by:
1. Discharging all assumptions mentioning the variable into the goal as implications
2. Wrapping with `∀var. ...`
3. Firing a subgoal for the generalized goal
4. After the subgoal returns, spec'ing the variable back and mp'ing to recover assumptions

The consequence: after `destruct_tac >> induct_tac`, each case has extra `==>` from the discharged assumptions. You need `intros_tac` to recover them.

### Subgoal Sequencing with `>>`

`>>` is `then_one` — it applies the second tactic to the **first** subgoal only. Remaining subgoals bubble up. This means:

```ocaml
induct_tac >> base_case_tac >> step_case_tac
```

This works because `induct_tac >> base_case_tac` solves the base case (first subgoal), then `>> step_case_tac` handles the step case (which is now the first remaining subgoal).

For explicit control, use `>>=` (then_each):

```ocaml
induct_tac >>= [
  base_case_tac;     (* applied to first subgoal *)
  step_case_tac;     (* applied to second subgoal *)
]
```

And `>>>` (then_all) applies the same tactic to all subgoals.

### `simp_tac` vs `simp_asm_tac`

- `simp_tac` simplifies the **goal** using definition unfolding rules
- `simp_asm_tac ~with_asms:false` simplifies **assumptions** using definition unfolding
- `simp_tac ~with_asms:true` additionally uses assumptions as rewrite rules for the goal

Beware: `simp_tac` does **not** handle conditional rewrites (like `P ==> x = y`). If an assumption is `∀n. P n ==> Q n`, simp won't use it to rewrite `Q t` to `T`.

### Deriving Contradiction from `T = F`

There is no `discriminate` tactic. If you reduce an absurd premise to `T = F` in the assumptions, the incantation is:

```ocaml
sym_asm_tac >> eq_true_elim_asm_tac >> false_elim_tac
```

This works because:
1. `sym_asm_tac` flips `T = F` to `F = T`
2. `eq_true_elim_asm_tac` converts `F = T` to `F` (since `P = T` yields `P`)
3. `false_elim_tac` closes any goal when `F` is in assumptions

### Boolean Encoding

Heft uses HOL-style encoding where propositions are boolean terms. `sorted l` is a term of type `bool`, not `Prop`. Equality is `=`, implication is `==>`, and everything evaluates to `T` or `F`.

Pattern-matching definitions (like `sorted`, `insert`) expand into `COND` (if-then-else) and `list_match`/`nat_match` terms. After `simp_tac`, you'll often see raw COND expressions:

```
COND (nat_le n0 n) (cons n0 (insert n1 n)) (cons n (cons n0 n1))
```

Use `cond_tac` to case-split on the condition, or `with_arbitrary_term expr cases_tac` for a specific boolean expression.

## Common Proof Patterns

### Double Induction (e.g., properties of `nat_le`)

When you need to induct on two variables, keep both universally quantified and chain inductions:

```ocaml
induct_tac >>= [
  (* base case for first variable *)
  ...;
  (* step case — intro IH, then induct on second variable *)
  gen_tac >> intro_tac >> induct_tac >>= [
    (* base of second *) ...;
    (* step of second *) ...;
  ];
]
```

### Case Splitting on Booleans Mid-Proof

When the goal contains `COND b ...`, use:

```ocaml
cond_tac   (* auto-finds COND conditions and splits *)
```

Or for a specific expression:

```ocaml
with_arbitrary_term (nat_le x y) cases_tac
```

This adds `nat_le x y = T` or `nat_le x y = F` to assumptions in each branch.

### Using Proven Lemmas

```ocaml
(* Use registered lemma as rewrite rule *)
with_proven ["lemma_name"] rewrite_tac

(* Use registered lemma for simplification *)
with_proven ["lemma_name"] simp_tac

(* Apply lemma to goal (strips foralls, matches conclusion) *)
with_proven ["lemma_name"] apply_thm_tac
```

Lemmas are registered via `run_proof ~name:"lemma_name" goal proof`.

### Keeping Variables Generalized

A general principle: don't intro universally quantified variables unless you need to. Keeping `∀n. P n` as the goal lets `induct_tac` work directly. If you intro `n` and it becomes free, you'll need `destruct_tac` to generalize it back, which creates a more complex goal.

In Coq terms: prefer `induction n` on `∀n. P n` over `intros n; destruct n` when possible.

## Tactic Quick Reference

| Tactic | Effect | Analogue |
|--------|--------|----------|
| `intro_tac` | Intro one `==>` | `intro` (implication only) |
| `gen_tac` | Intro one `∀` | `intro` (universal only) |
| `intros_tac` | Repeat intro/gen | `intros` |
| `assumption` | Exact match in asms | `assumption` |
| `refl_tac` | Prove `x = x` | `reflexivity` |
| `simp_tac` | Unfold + rewrite goal | `simp` |
| `simp_asm_tac` | Simplify assumptions | `simp at h` |
| `induct_tac` | Structural induction | `induction` (needs `∀`) |
| `cases_tac` | Case split | `cases` (needs `∀` or bool) |
| `destruct_tac` | Case split free var | `destruct` |
| `cond_tac` | Split on COND expr | `destruct (decide ...)` |
| `conj_tac` | Split `∧` goal | `split` |
| `left_tac` / `right_tac` | Choose `∨` side | `left` / `right` |
| `apply_asm_tac` | Apply `P ==> Q` asm | `apply` (no unification) |
| `apply_thm_tac` | Apply theorem w/ matching | `apply` (with unification) |
| `mp_asm_tac` | Modus ponens in asms | `specialize` + `apply` |
| `rewrite_tac` | Rewrite goal with rules | `rewrite` |
| `rewrite_asm_tac` | Rewrite assumption with rules | `rewrite ... in h` |
| `false_elim_tac` | Close goal from `F` | `contradiction` (literal F only) |
| `neg_elim_tac` | Contradiction from P, ¬P | `contradiction` |
| `truth` | Prove `T` | `trivial` |
| `ccontr_tac` | Classical contradiction | `by_contra` |

## Combinators Quick Reference

| Combinator | Meaning |
|-----------|---------|
| `tac1 >> tac2` | Apply tac2 to first subgoal of tac1 |
| `tac1 >>> tac2` | Apply tac2 to all subgoals of tac1 |
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

### `discriminate_tac`
Derive `F` from absurd equalities like `T = F`, `zero = suc n`, `nil = cons x xs`. Currently requires the manual `sym_asm_tac >> eq_true_elim_asm_tac >> false_elim_tac` dance, which only works for `T = F` — constructor inequalities for inductives aren't handled at all.

### `spec_asm_tac`
Specialize a universally quantified assumption `∀x. P x` with a specific term to get `P t`. Currently you have to go through `with_assumptions apply_thm_tac`, which is indirect and sometimes fragile. A direct `spec_asm_tac t` that finds `∀x. ...` in assumptions and adds the specialized version would be very useful.

### `injection_tac`
From `cons x xs = cons y ys`, derive `x = y` and `xs = ys`. Constructor injectivity isn't directly exploitable right now.

### `subst_tac`
Given `x = t` in assumptions, substitute `t` for `x` everywhere (in other assumptions and the goal). This would clean up many proof states that are cluttered with equalities.

## Debugging Tips

- **Use `>>=` early**: When a proof isn't working with `>>` chains, switch to `>>=` to handle each subgoal explicitly. This makes it clear which branch is failing.
- **Stop the proof early**: Replace the rest of a tactic chain with nothing to see the intermediate goal state in the expect output. The "Proof Incomplete" output shows you the current assumptions and goal.
- **Watch the fuel count**: If fuel increases but the proof stays incomplete, your tactics are making progress on one branch but failing on another.
- **`simp_asm_tac ~with_asms:false` before `simp_tac`**: Simplify assumptions first so they're in normal form, then simplify the goal. Using `~with_asms:true` on simp_tac can then use the simplified assumptions.
- **Check what `Choose` returns**: Many tactics use `Choose` internally. If a tactic silently fails, it might be choosing the wrong term. Wrap with `with_first` to try all options, or `with_nth_choice n` to pick a specific one.
