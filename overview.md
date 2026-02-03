# Overview

The (preliminary) course plan:

Week | Part / Focus | Concepts & Techniques | Tools / Languages | AI Learning / AI Component
-----|--------------|---------------------|-----------------|---------------------------
1 | Introduction / Lecture Only | Formal methods overview, motivation, safety, correctness; specifications, deductive reasoning, invariants; verification techniques overview | Lean, Haskell, TLA+, SMT solvers, Rocq, PRISM | Introduce AI as a future assistant for proof guidance, verification, and analysis
Part 1 – Specification & Deductive Verification
2 | Formal Specification | TLA+, Z, Alloy; writing precise system specifications | TLA+, SMT solvers | AI-assisted specification validation; automated consistency checks
3 | Deductive Verification | Hoare logic, pre/postconditions, weakest preconditions | SMT solvers, Lean | AI-guided automated proof suggestions; invariant hints
4 | Part 1 Application | E.g. Protocol verification: safety & liveness | TLA+, Lean | AI-generated counterexamples; invariant suggestions for protocols
Part 2 – Static Analysis & Model Checking
5 | Static Analysis | Abstract interpretation, termination, dataflow analysis | Lean, SMT solvers | ML-based bug prediction; AI heuristics for prioritizing program paths
6 | Model Checking | LTL, CTL, safety vs liveness, state-space exploration | TLA+, SPIN, UPPAAL | AI-guided state-space exploration and pruning for efficiency
7 | Part 2 Application | E.g. Hardware verification: CPU / memory modules | TLA+, SMT solvers | AI-assisted synthesis and verification of hardware constraints
Part 3 – Proof Assistants
8 | Interactive Theorem Proving | Lean / Rocq basics, proof strategies, automation | Lean, Rocq | AI proof search assistance; automated hint generation
9 | Advanced Proof Techniques | Dependent types, monads, category theory | Lean, Haskell | Neural-symbolic reasoning for compositional proofs; AI-guided verification of software
10 | Part 3 Application | Neural network verification: robustness / bounded outputs | Rocq, Lean | AI-assisted formal safety proofs for neural networks
Part 4 – Probabilistic Programming & Formal Methods
11 | Probabilistic Programming | Monads for probability, stochastic systems | Haskell, Lean | AI policy modeling with probabilistic monads; probabilistic program abstraction
12 | Probabilistic Verification | Probabilistic model checking, expected outcomes, invariants | Haskell, PRISM, Lean | AI safety and reliability guarantees; probabilistic reasoning in RL agents
13 | Part 4 Application | Integrate probabilistic reasoning | Haskell, Lean, PRISM | Verify randomized distributed algorithms or AI policies; AI-guided counterexamples
14 | Conclusion & Project Presentations | Synthesis of all parts. Discussion and further work on chapters | All course tools | 
