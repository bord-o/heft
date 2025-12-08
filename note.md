# OneHOL

## Roadmap

**Essential Reading (in order):**

1. Harrison, *Handbook of Practical Logic and Automated Reasoning* — chapters 1-6, then chapter on HOL
2. Taha & Sheard, "MetaML and multi-stage programming with explicit annotations" (1997)
3. HOL Light source code — `fusion.ml` (the kernel)

**Secondary (when relevant):**

4. Davies & Pfenning, "A modal analysis of staged computation" (2001) — theoretical foundations for reflection typing
5. Harrison, "Towards Self-verification of HOL Light" (2006)

---

## System Overview

A higher-order logic proof assistant where terms, proofs, and tactics exist in a single language through reflected types that allow programs to manipulate syntax as data.

**Core components:**

- Standard HOL logic (simple types, polymorphism, classical)
- quote (g:goal) results in g:reflect_goal for quotation
- splice (g:reflect_goal) results in g:goal for symmetry
- Pattern matching on quoted terms (reflect_* types)
- Tactics are functions `goal → thm`, but use quotation on the input and splicing on the output, operating on the reflection types instead
- External FFI for ambitious automation (solvers, ML models)
- Small kernel checks all proof terms regardless of source just like HOL light, all reflection is happening in a thin runtime layer

---

## Open Questions (in priority order)

1. **Binding representation:** How do you represent and match on `λ` inside `Code`? (de Bruijn, HOAS, nominal?)

1. **Typing rules for quotation:** What are the precise rules for `⌜_⌝` and splice? How do free variables interact with quotation?

## Syntax

### Keywords

```
theorem 
def 
type

fn
let
in
case
of
end
if
then
else

forall
exists

terminating
by

splice
quote
```

### Tree

```ocaml



```
