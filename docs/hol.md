# HOL Light Cheat Sheet

## Part 1: The 10 Primitive Rules (Intuitive Explanations)

HOL Light has only 10 primitive inference rules. Every theorem in the system—no matter how complex—ultimately traces back to applications of just these 10 rules. This is what makes the system trustworthy: the "trusted kernel" is tiny.

### 1. REFL (Reflexivity)
```
REFL t   returns   ⊢ t = t
```

**Intuition**: Anything equals itself. This is your "free theorem generator"—you can always get `⊢ x = x` for any term `x`.

**Example**:
```ocaml
# REFL `x + 1`;;
val it : thm = |- x + 1 = x + 1
```

### 2. TRANS (Transitivity)
```
From  ⊢ s = t   and   ⊢ t = u   returns   ⊢ s = u
```

**Intuition**: Chain equalities together. If `a = b` and `b = c`, then `a = c`. This is how you "walk" from one term to another through a sequence of rewrites.

**Example**:
```ocaml
# TRANS (ARITH_RULE `1 + 3 = 4`) (ARITH_RULE `4 = 2 + 2`);;
val it : thm = |- 1 + 3 = 2 + 2
```

### 3. MK_COMB (Congruence for Application)
```
From  ⊢ f = g   and   ⊢ x = y   returns   ⊢ f(x) = g(y)
```

**Intuition**: If two functions are equal, and two arguments are equal, then applying those functions to those arguments gives equal results. This is how equality "propagates through" function application.

**Why it matters**: Since almost everything in HOL is built from function application (even `a + b` is `((+) a) b`), this rule lets you transform deep inside terms.

**Example**:
```ocaml
# let th1 = ASSUME `(+) 2 = (+) (1 + 1)`;;
# let th2 = ARITH_RULE `3 = 1 + 2`;;
# MK_COMB (th1, th2);;
val it : thm = (+) 2 = (+) (1 + 1) |- 2 + 3 = (1 + 1) + (1 + 2)
```

### 4. ABS (Congruence for Abstraction)
```
From  ⊢ s = t   returns   ⊢ (λx. s) = (λx. t)
```

**Intuition**: If `s = t`, then the functions `λx. s` and `λx. t` are equal. You can "wrap" an equality inside a lambda.

**Restriction**: `x` must not be free in the hypotheses of the theorem. (Otherwise you'd be illegally generalizing over a variable that might have constraints on it.)

**Example**:
```ocaml
# ABS `x:num` (ARITH_RULE `x + 0 = x`);;
val it : thm = |- (\x. x + 0) = (\x. x)
```

### 5. BETA (Beta Reduction)
```
BETA `(λx. t) x`   returns   ⊢ (λx. t) x = t
```

**Intuition**: Applying a function `λx. t` to `x` just gives you `t`. This is the computational heart of lambda calculus.

**Note**: The primitive rule only handles the case where the argument is exactly the bound variable. The derived `BETA_CONV` handles the general case.

**Example**:
```ocaml
# BETA `(\x. x + 1) x`;;
val it : thm = |- (\x. x + 1) x = x + 1
```

### 6. ASSUME (Assumption)
```
ASSUME p   returns   {p} ⊢ p
```

**Intuition**: You can always assume something is true—but it goes into your hypotheses. This is the "suppose P" move in a proof.

**Example**:
```ocaml
# ASSUME `x < y`;;
val it : thm = x < y |- x < y
```

### 7. EQ_MP (Modus Ponens for Equality)
```
From  ⊢ p = q   and   ⊢ p   returns   ⊢ q
```

**Intuition**: If `p` equals `q` (as propositions), and `p` is true, then `q` is true. This bridges equality and truth.

**Why it's so important**: HOL defines all logical connectives in terms of equality, so EQ_MP is the workhorse for logical reasoning.

**Example**:
```ocaml
# let eq_th = TAUT `(p /\ T) = p`;;
# let p_th = ASSUME `p /\ T`;;
# EQ_MP eq_th p_th;;
val it : thm = p /\ T |- p
```

### 8. DEDUCT_ANTISYM_RULE (Double Implication to Equality)
```
From  {p} ⊢ q   and   {q} ⊢ p   returns   ⊢ p = q
```

**Intuition**: If assuming `p` lets you prove `q`, AND assuming `q` lets you prove `p`, then `p` and `q` are equal (logically equivalent). This is how you prove `p ⇔ q`.

**Why it's central**: This is the fundamental rule for establishing propositional equivalences. Combined with EQ_MP, it gives you implication reasoning.

**Example**:
```ocaml
# let th1 = ASSUME `p:bool`;;   (* {p} ⊢ p *)
# let th2 = ASSUME `p:bool`;;   (* {p} ⊢ p *)
# DEDUCT_ANTISYM_RULE th1 th2;;
val it : thm = |- p <=> p
```

### 9. INST (Instantiate Term Variables)
```
INST [t1,x1; t2,x2; ...] th
```

Substitutes terms for free variables in a theorem.

**Intuition**: If you've proved `⊢ P(x)` with `x` free, you can substitute any term for `x` to get a more specific theorem.

**Example**:
```ocaml
# let th = ARITH_RULE `x + 0 = x`;;
# INST [`5`, `x:num`] th;;
val it : thm = |- 5 + 0 = 5
```

### 10. INST_TYPE (Instantiate Type Variables)
```
INST_TYPE [ty1,α1; ty2,α2; ...] th
```

Substitutes types for type variables in a theorem.

**Intuition**: If you've proved something polymorphically (for all types α), you can specialize it to any concrete type.

**Example**:
```ocaml
# let th = REFL `x:A`;;   (* |- x = x, polymorphic *)
# INST_TYPE [`:num`, `:A`] th;;
val it : thm = |- x = x   (* now x has type num *)
```

---

## Part 2: The Key Insight

**HOL Light has NO primitive rules for ∀, ∃, ⇒, ∧, ∨, ¬, T, F!**

All of these logical connectives are *defined* in terms of equality and lambda abstraction. Then derived rules are built to manipulate them. For example:

- **T** (truth) is defined as `(λp. p) = (λp. p)`
- **∀** (for all) is defined as `∀ = λP. (P = λx. T)`
- **∧** (and) is defined via a clever equality involving pairs
- **⇒** (implies) is defined as `p ⇒ q  ≡  p ∧ q = p`

This is why bool.ml and equal.ml exist—they bootstrap all of propositional and predicate logic from those 10 primitive rules!

---

## Part 3: Worked Example of a Derived Rule

Let's trace through **SYM** (symmetry of equality), which proves `⊢ t = s` from `⊢ s = t`.

### The Code
```ocaml
let SYM th =
  let tm = concl th in
  let l,r = dest_eq tm in
  let lth = REFL l in
  EQ_MP (MK_COMB(AP_TERM (rator (rator tm)) th, lth)) lth;;
```

### Step-by-Step Trace

Let's trace through with `th = ASSUME `l:num = r``:

**Input**: `l = r |- l = r`

**Step 1**: Get the conclusion and break it apart
```ocaml
let tm = concl th       (* tm = `l = r` *)
let l,r = dest_eq tm    (* l = `l`, r = `r` *)
```

**Step 2**: Create a reflexive theorem for the left side
```ocaml
let lth = REFL l        (* lth = |- l = l *)
```

**Step 3**: Extract the equality constant
```ocaml
rator (rator tm)        (* This is `(=)` - the equality constant *)
```

**Step 4**: Use AP_TERM to apply `(=)` to both sides of our theorem
```ocaml
AP_TERM `(=)` th        
(* From th: l = r |- l = r
   Get:     l = r |- (=) l = (=) r
   
   Think: if l = r, then "(=) l" equals "(=) r" 
   (partially applied equality) *)
```

**Step 5**: Use MK_COMB to apply these to the reflexive theorem
```ocaml
MK_COMB(AP_TERM `(=)` th, lth)
(* From:  l = r |- (=) l = (=) r   and   |- l = l
   Get:   l = r |- ((=) l) l = ((=) r) l
   i.e.:  l = r |- (l = l) = (r = l)
   
   Think: we're applying both sides to l *)
```

**Step 6**: Use EQ_MP to "cross over"
```ocaml
EQ_MP (MK_COMB ...) lth
(* From:  l = r |- (l = l) = (r = l)   and   |- l = l
   Get:   l = r |- r = l
   
   Think: since (l = l) is true, and (l = l) = (r = l), 
          therefore (r = l) is true! *)
```

**Final result**: `l = r |- r = l`  ✓

### The Trick

The clever insight is that `(l = l) = (r = l)` follows from `l = r` by congruence:
- Start with `l = r`
- Apply `(=)` to both sides: `(=) l = (=) r`
- Apply both sides to `l`: `(l = l) = (r = l)`

Then since `l = l` is trivially true (REFL), we can use EQ_MP to conclude `r = l`.

---

## Part 4: Another Example - PROVE_HYP

Here's a simpler but very useful derived rule:

```ocaml
let PROVE_HYP ath bth =
  if exists (aconv (concl ath)) (hyp bth)
  then EQ_MP (DEDUCT_ANTISYM_RULE ath bth) ath
  else bth;;
```

**What it does**: Given `⊢ A` and `{A} ⊢ B`, it returns `⊢ B` (i.e., discharges the hypothesis A using the proof of A).

**How it works**:
1. Check if the conclusion of `ath` appears in the hypotheses of `bth`
2. If so, use DEDUCT_ANTISYM_RULE to get `⊢ A = B` (since `{A} ⊢ B` and we can trivially get `{B} ⊢ A` from `⊢ A`)
3. Use EQ_MP with `⊢ A` to get `⊢ B`

Wait, that's not quite right! Let me re-examine...

Actually, DEDUCT_ANTISYM_RULE on `⊢ A` and `{A} ⊢ B` gives:
- From `⊢ A`: this is `{} ⊢ A`, so `{B} ⊢ A` (B goes away because it's not in the hypotheses)
- From `{A} ⊢ B`: the A gets removed because it's the conclusion of the first theorem
- Result: `{} ⊢ A = B`, i.e., `⊢ A = B`

Then `EQ_MP (⊢ A = B) (⊢ A)` gives `⊢ B`.

---

## Part 5: Tips for Building Derived Rules

1. **Think in terms of equality**: Almost everything in HOL is about equality. Even `p ⇒ q` is just `p ∧ q = p`.

2. **MK_COMB is your friend**: When you need to transform deep inside a term, you're usually chaining MK_COMB applications.

3. **The AP_TERM / AP_THM pattern**: 
   - `AP_TERM f (⊢ x = y)` gives `⊢ f x = f y` (apply f to both sides)
   - `AP_THM (⊢ f = g) x` gives `⊢ f x = g x` (apply both to x)
   
4. **DEDUCT_ANTISYM_RULE for ⇔**: If you need to prove `p ⇔ q`, prove `{p} ⊢ q` and `{q} ⊢ p` separately.

5. **EQ_MP to "rewrite" propositions**: If you have `⊢ p = q` and `⊢ p`, use EQ_MP to get `⊢ q`.

6. **Read bool.ml carefully**: It shows exactly how all the familiar logical operations are bootstrapped. The definitions of CONJ, DISJ, IMP_TRANS, etc. are all there.

---

## Part 6: Quick Reference

| Rule | From | To |
|------|------|-----|
| REFL | term t | ⊢ t = t |
| TRANS | ⊢ s = t, ⊢ t = u | ⊢ s = u |
| MK_COMB | ⊢ f = g, ⊢ x = y | ⊢ f x = g y |
| ABS | ⊢ s = t | ⊢ (λx.s) = (λx.t) |
| BETA | term (λx.t)x | ⊢ (λx.t)x = t |
| ASSUME | prop p | {p} ⊢ p |
| EQ_MP | ⊢ p = q, ⊢ p | ⊢ q |
| DEDUCT_ANTISYM_RULE | {p}⊢q, {q}⊢p | ⊢ p = q |
| INST | substitution, thm | thm with vars replaced |
| INST_TYPE | type subst, thm | thm with types replaced |

