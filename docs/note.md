# OneHOL

Profoundly discoverable.

You shouldn't have to know the name of some incantation for a proof.

All tactics and existing lemmas should be discoverable naturally.

## Roadmap

**Essential Reading (in order):**

1. Harrison, *Handbook of Practical Logic and Automated Reasoning* — chapters 1-6, then chapter on HOL
2. Taha & Sheard, "MetaML and multi-stage programming with explicit annotations" (1997)
3. HOL Light source code — `fusion.ml` (the kernel)

**Secondary (when relevant):**

4. Davies & Pfenning, "A modal analysis of staged computation" (2001) — theoretical foundations for reflection typing
5. Harrison, "Towards Self-verification of HOL Light" (2006)

---

## Heuristics for Usability
- Visibility of system status
- Match between system and real proofs
- User control and freedom
- consistency
- error prevention
- recognition > recall
- flexibility and efficiency of use
- aesthetic and minimal design
- error recovery
- documentation

## TODOs
- Fix hashtable weirdness in the kernel
- Rewrite elaborator with clear mind
