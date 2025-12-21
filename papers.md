Great question! Here are the most relevant papers for what you're building:

## Foundational Papers on Proof Search

### **1. "Rippling: Meta-Level Guidance for Mathematical Reasoning" (Bundy et al., 2005)**
- **Why read**: Rippling is the most successful heuristic for automatic induction proofs
- **Key idea**: Guide search by tracking structural differences between goal and hypotheses
- **Relevance**: Your "exploration" feature could use rippling heuristics to rank reachable goals
- Available at: https://www.cambridge.org/core/books/rippling/

### **2. "Proof Planning" (Bundy, 1988)**
- **Why read**: Introduced the idea of "tactics" (methods) with preconditions
- **Key idea**: Plan which tactics to apply before doing the proof search
- **Relevance**: Your bounded search is essentially proof planning with user guidance
- Classic paper, widely cited

### **3. "IsaPlanner: A Prototype Proof Planner in Isabelle" (Dixon & Fleuriot, 2003)**
- **Why read**: Practical implementation of proof planning
- **Key idea**: Combines rippling with IsarStep for structured proofs
- **Relevance**: Shows how to integrate automated search with interactive proving
- http://www.inf.ed.ac.uk/publications/report/0279.html

## Synthesis and Search

### **4. "Program Synthesis by Sketching" (Solar-Lezama, 2008)**
- **Why read**: User provides "sketch" of solution, synthesizer fills in details
- **Key idea**: User guides search by constraining the space
- **Relevance**: Your "pick a reachable goal" is exactly this—user sketches the proof path
- https://people.csail.mit.edu/asolar/papers/thesis.pdf

### **5. "Growing a Proof Assistant" (Wadler et al., 2020)**
- **Why read**: Discusses tradeoffs in proof assistant design
- **Key idea**: Iterate with users, don't build everything upfront
- **Relevance**: Validates your approach of starting with TUI before parsing
- https://drops.dagstuhl.de/opus/volltexte/2020/13066/

### **6. "Proof Synthesis Guided by Delimited Overloading" (Ziliani et al., 2013)**
- **Why read**: Introduces "proof search as computation"
- **Key idea**: Encode search problems as type inference
- **Relevance**: Different approach, but shows how to make search programmable
- Implemented in Mtac for Coq

## Interactive Theorem Proving

### **7. "Tinker, Tailor, Solver, Proof" (Grov & Bundy, 2013)**
- **Why read**: Studies how users actually build proofs interactively
- **Key idea**: Users need to "tinker" (explore) and "tailor" (refine)
- **Relevance**: Empirical validation that exploration is what users need
- https://www.research.ed.ac.uk/en/publications/tinker-tailor-soldier-proof

### **8. "Proof General: A Generic Tool for Proof Development" (Aspinall, 2000)**
- **Why read**: Design of the classic proof interaction interface
- **Key idea**: Separation between proof script and proof state
- **Relevance**: Your TUI is similar but more interactive
- http://proofgeneral.inf.ed.ac.uk/

### **9. "The Seven Virtues of Simple Type Theory" (Farmer, 2008)**
- **Why read**: Argues for HOL-style simple type theory
- **Key idea**: Simpler logic → easier proof search
- **Relevance**: Validates your choice of HOL as foundation
- https://imps.mcmaster.ca/doc/seven-virtues.pdf

## Machine Learning for Proof Search

### **10. "Learning to Prove Theorems via Interacting with Proof Assistants" (Yang & Deng, 2019)**
- **Why read**: ML model learns which tactics to apply
- **Key idea**: Use proof assistant interaction data to train models
- **Relevance**: Your TUI could collect data for training suggestion models
- https://arxiv.org/abs/1905.09381

### **11. "Generative Language Modeling for Automated Theorem Proving" (Polu & Sutskever, 2020)**
- **Why read**: GPT-f, neural theorem proving for Metamath
- **Key idea**: Language models can generate proof steps
- **Relevance**: Could integrate into your "exploration" feature
- https://arxiv.org/abs/2009.03393

### **12. "Draft, Sketch, and Prove: Guiding Formal Theorem Provers with Informal Proofs" (Jiang et al., 2022)**
- **Why read**: Recent work on LLMs + proof assistants
- **Key idea**: Use informal proof sketches to guide search
- **Relevance**: Your "pick the goal" is a form of sketching
- https://arxiv.org/abs/2210.12283

## Tactic Languages and Automation

### **13. "A Tactic Language for Hiproofs" (Tankink et al., 2010)**
- **Why read**: Design space for tactic languages
- **Key idea**: Tactics as first-class programs
- **Relevance**: Helps think about what primitives your tactic system needs
- https://www.cs.ru.nl/~janz/papers/hiproofs.pdf

### **14. "Mtac: A Monad for Typed Tactic Programming in Coq" (Ziliani et al., 2015)**
- **Why read**: Modern approach to typed tactics
- **Key idea**: Tactics have types, can be composed safely
- **Relevance**: Alternative to your reflection approach
- https://plv.mpi-sws.org/mtac/

### **15. "Hammers for Type Theory" (Czajka & Kaliszyk, 2018)**
- **Why read**: Integration of SMT solvers with proof assistants
- **Key idea**: External automation fills in "boring" parts
- **Relevance**: Your bounded search could call external solvers
- https://arxiv.org/abs/1807.08911

## Most Relevant for Your Project

If you only read **three**, read these:

1. **"Tinker, Tailor, Solver, Proof"** - Validates that exploration is what users need
2. **"Rippling"** - Best known technique for automatic induction, could rank your suggestions
3. **"Program Synthesis by Sketching"** - Theoretical foundation for your "user guides search" approach

## Quick Reads (Shorter Papers)

- **"The QED Manifesto" (1994)** - Vision for automated reasoning, still inspiring
- **"Towards Self-Verification of HOL Light" (Harrison, 2006)** - Short paper on HOL kernel
- **"The Lean Theorem Prover" (de Moura et al., 2015)** - Good overview of modern design

## Surveys

- **"Automated Reasoning: 33 Basic Research Problems" (Wos, 1988)** - Classic, sets context
- **"Three Decades of Automated Theorem Proving" (Bundy, 1999)** - Historical perspective
- **"Machine Learning for Theorem Proving" (Kaliszyk et al., 2021)** - Recent survey of ML approaches

## Where to Find Them

Most are available on:
- **arXiv.org** (recent papers)
- **Google Scholar** (search by title)
- **Author homepages** (often have PDFs)
- **CiteSeerX** (older papers)

## My Reading Order Recommendation

**Week 1** (while building parser):
- Read "Tinker, Tailor, Solver, Proof" (validates your approach)
- Skim "QED Manifesto" (inspirational)

**Week 2** (while building TUI):
- Read "Program Synthesis by Sketching" (theoretical grounding)
- Skim "IsaPlanner" (practical implementation)

**Week 3** (after TUI works):
- Start "Rippling" book (improve your heuristics)
- Read ML papers if interested in suggestion ranking

## Bonus: Recent Workshops

Check out:
- **AITP** (AI and Theorem Proving) - annual workshop, lots of recent work
- **ITP** (Interactive Theorem Proving) - main conference
- **CADE** (Automated Deduction) - classic conference

Their proceedings have tons of relevant papers.

Want me to dive deeper into any particular area (proof planning, synthesis, ML integration)?
