# Proof and verification in Lean

```{note}
**Chapter roles (Spring 2026)**  
Author: Kalin Richardson · Reviewer: Nayeli Castro  
See [Chapter assignments](0-chapter-assignments.md).
```

This chapter introduces **Lean 4** as a dependently typed proof assistant and programming language. We'll explore how dependent types enable us to write programs that are *provably correct by construction*—a fundamental shift from testing to verification.

**Quick Link:** [Lean Language Website](https://lean-lang.org/)

## Goals

- Understand **dependent types** and why they matter for correctness.
- Build intuition through **small, concrete examples** you can run yourself.
- See how **proofs and programs coexist** in the same language.
- Know where to go next (Mathlib, community resources, certified programming projects).
 
## Introduction
 
### The Problem with Testing
 
Traditional software development follows this cycle:
 
1. Write code
2. Test it (hope you found all the bugs)
3. Deploy
4. Fix bugs found in production
This approach has served us well, but it has fundamental limits. Testing can show the presence of bugs, not their absence. As Edsger Dijkstra famously said: "Program testing can be a very effective way to show the presence of bugs, but it is hopelessly inadequate for showing their absence."
 
Consider a simple function:
 
```lean
def divide (a b : Nat) : Nat := a / b
```
 
We can test this with `divide 10 2 = 5` all day long. But what happens when someone calls `divide 10 0`? In traditional languages, this crashes. We *could* add a test for it, but we can't test every possible input. There will always be edge cases we miss.
 
### The Promise of Formal Verification
 
What if we could prove our code is correct *before* it runs? Not just test it, but mathematically guarantee it works?
 
That's where **Lean** comes in. Lean is a proof assistant: **a tool that lets you write programs and simultaneously write proofs that those programs satisfy their specifications.** The proofs aren't optional comments; they're enforced by the type system.
 
With Lean, the function above becomes:
 
```lean
def safe_divide (a b : Nat) (h : b ≠ 0) : Nat := a / b
```
 
Now the type signature says: "To call `safe_divide`, you must provide a *proof* that `b ≠ 0`." If you try to call it with `b = 0`, Lean won't let you. Not at runtime, but at compile time. The bug is impossible.
 
### Historical Context: From λ-Calculus to Lean
 
Lean didn't appear out of nowhere. It's built on decades of research:
 
- **1930s:** Alonzo Church develops **λ-calculus** (lambda calculus), showing that computation and logic are deeply connected.
- **1972:** Per Martin-Löf develops **intuitionistic type theory**, which formalized the idea that proofs and programs are the same thing (the Curry-Howard correspondence).
- **1984:** Thierry Coquand and Gérard Huet create **Coq**, the first practical proof assistant based on dependent types.
- **2016:** Leonardo de Moura and team release **Lean 3**, making theorem proving more accessible.
- **2021:** **Lean 4** launches with a focus on practical programming + verification.
Each step made it easier to write formal proofs. Lean 4 is the result: a language designed from day one to be both a programming language *and* a theorem prover.
 
---
 
## Why Lean? Why Dependent Types?
 
### The Core Insight
 
In a normal type system, types are static. A list has type `List Int`, and that's all the type system knows. It doesn't know the list's length, whether it's sorted, or anything else.
 
**Dependent types change this.** A dependent type can depend on a *value*. So you can have:
 
- A type for "lists of exactly length 3"
- A type for "sorted lists"
- A type for "non-zero natural numbers"
When a type depends on a value, the type system becomes a proof system. To construct a value of that type, you must provide proof that the value satisfies the constraint.
 
### Example: Vectors with Known Length
 
In a normal language:
 
```lean
def my_list : List Int := [1, 2, 3]
-- The type doesn't say how long it is
#eval my_list.length  -- We have to check at runtime
```
 
In Lean with dependent types:
 
```lean
def my_vector : {n : Nat // n = 3} := ⟨3, rfl⟩
-- The type itself guarantees the value is 3
```
 
Better yet, we can use a dependent pair to couple a list with a proof of its length:
 
```lean
def my_list_with_proof (lst : List α) : {n : Nat // n = lst.length} := by
  exact ⟨lst.length, rfl⟩
```
 
This function takes a list and returns a number *bundled with a proof* that the number equals the list's length. The proof is `rfl` (reflexivity), which just says "it's true by definition."
 
---
 
## Dependent Types Explained
 
Let's build up from simple to complex examples.
 
### Example 1: Safe Division (Proof as a Requirement)
 
The most straightforward use of dependent types:
 
```lean
def safe_divide (a b : Nat) (h : b ≠ 0) : Nat := a / b
```
 
**What's happening:**
- `a` and `b` are the numerator and denominator
- `h : b ≠ 0` is not just a variable—it's a *proof* that `b ≠ 0`
- Lean requires this proof before the function can be called
**Using it:**
 
```lean
#eval safe_divide 10 2 (by decide)  -- ✅ Works (2 ≠ 0 is decidable)
-- #eval safe_divide 10 0 (by decide)  -- ❌ Won't compile (can't prove 0 ≠ 0)
```
 
The error happens at compile time, not runtime. You can't accidentally divide by zero.
 
### Example 2: Dependent Pairs (Data + Proof)
 
Sometimes you want to return both a computation result and proof of its properties:
 
```lean
def add_with_proof (x y : Nat) : {z : Nat // z = x + y} := by
  exact ⟨x + y, rfl⟩
```
 
**What's happening:**
- `{z : Nat // z = x + y}` is a **dependent pair**: a natural number `z` paired with a proof that `z = x + y`
- The angle brackets `⟨·, ·⟩` construct the pair
- `.val` extracts the value, `.property` extracts the proof
**Using it:**
 
```lean
#eval (add_with_proof 3 4).val       -- 7
-- The proof is available but hidden:
-- (add_with_proof 3 4).property : 7 = 3 + 4
```
 
### Example 3: Function Specifications
 
You can write a function and *prove* it satisfies a spec:
 
```lean
def double_with_proof (n : Nat) : {m : Nat // m = 2 * n} := by
  exact ⟨2 * n, rfl⟩
```
 
This function computes `2 * n` and proves the result is exactly `2 * n`. Not "probably," not "we tested it"—*provably*.
 
---
 
## Working Examples: From Simple to Complex
 
### Example 1: List Length Certification
 
**The Problem:** How do we certify that a computed length is correct?
 
**The Solution:**
 
```lean
def list_length_certified (lst : List α) : {n : Nat // n = lst.length} := by
  exact ⟨lst.length, rfl⟩
```
 
**How it works:**
1. Take a list `lst`
2. Compute its length
3. Return the length bundled with a proof that it equals `lst.length`
4. The proof is `rfl` (reflexivity)—Lean checks it automatically
**Testing:**
 
```lean
#eval (list_length_certified [1, 2, 3]).val
-- Output: 3
 
#eval (list_length_certified [1, 2, 3, 4, 5]).val
-- Output: 5
```
 
### Example 2: Proving List Append is Associative
 
A classic theorem from algebra: `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)`
 
**In Lean:**
 
```lean
theorem append_assoc (xs ys zs : List α) : 
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => 
    -- Base case: xs = []
    -- Then: ([] ++ ys) ++ zs = [] ++ (ys ++ zs)
    -- Both sides simplify to ys ++ zs
    rfl
  | cons x xs' ih =>
    -- Inductive case: xs = x :: xs'
    -- ih is the inductive hypothesis:
    --   (xs' ++ ys) ++ zs = xs' ++ (ys ++ zs)
    -- We need to show:
    --   (x :: xs' ++ ys) ++ zs = x :: (xs' ++ (ys ++ zs))
    simp [ih]
```
 
**What's happening:**
1. **Induction on lists:** We prove the theorem by induction on `xs`
2. **Base case (`nil`):** When `xs = []`, both sides equal `ys ++ zs` by definition, so `rfl` (reflexivity) proves it
3. **Inductive case (`cons`):** Assume the theorem holds for `xs'`. We show it holds for `x :: xs'` using that assumption (`ih`)
**Why this matters:** This isn't a test. Lean verifies *every step* of the proof. If you make a logical error, Lean catches it immediately. Once it compiles, the theorem is *proven for all lists of all types*.
 
### Example 3: Computing Factorials (Recursion + Type Safety)
 
```lean
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
 
#eval factorial 5
-- Output: 120
```
 
**What's happening:**
1. Pattern match on `n`: if it's 0, return 1
2. Otherwise, return `n * factorial (n-1)`
3. Lean verifies the recursion terminates (structural recursion on `Nat`)
**Type Safety:**
- `factorial` only works on `Nat` (non-negative integers)
- You can't accidentally pass a negative number
- The type system enforces this
---
 
## Tactic Mode vs Term Mode: Two Ways to Write Proofs
 
Lean lets you write proofs two ways:
 
### Tactic Mode (Step-by-Step)
 
Most readable for beginners. You give Lean step-by-step instructions:
 
```lean
def add_proof_tactic (x y : Nat) : {z : Nat // z = x + y} := by
  exact ⟨x + y, rfl⟩
```
 
**How to read it:**
- `by` means "switch to tactic mode"
- `exact ⟨x + y, rfl⟩` says "the proof is exactly this dependent pair"
### Term Mode (Direct)
 
More concise. You write the proof term directly:
 
```lean
def add_proof_term (x y : Nat) : {z : Nat // z = x + y} :=
  ⟨x + y, rfl⟩
```
 
**Both are equivalent.** Choose tactic mode when you're building the proof step-by-step, term mode when you know the answer directly.
 
---
 
## Common Tactics: Building Blocks of Proofs
 
When you write proofs in tactic mode, you use **tactics**—commands that transform your goal. Here are the most important ones:
 
### `exact` — Provide the exact answer
 
```lean
example : 2 + 2 = 4 := by exact rfl
```
 
Say "the proof is exactly this term."
 
### `rfl` — Reflexivity (true by definition)
 
```lean
example : 3 = 3 := by rfl
```
 
Use when both sides are identical by definition.
 
### `simp` — Simplify
 
```lean
example (n : Nat) : n + 0 = n := by simp
```
 
Simplify both sides using known lemmas until they match (or the goal is proven).
 
### `induction` — Prove by induction
 
```lean
theorem sum_n (n : Nat) : sum (range n) = n * (n - 1) / 2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]
```
 
Prove a property holds for all natural numbers.
 
### `decide` — Compute the proof
 
```lean
example : 2 + 2 = 4 := by decide
```
 
For decidable propositions (like arithmetic), just evaluate it.
 
---
 
## Pattern Matching: Handling Different Cases
 
Lean lets you handle different cases cleanly:
 
```lean
def head_or_zero : List Nat → Nat
  | [] => 0           -- Case 1: empty list → return 0
  | x :: _ => x       -- Case 2: non-empty → return first element
 
#eval head_or_zero []           -- Output: 0
#eval head_or_zero [5, 10, 15]  -- Output: 5
```
 
**Why this matters:** You *must* handle all cases. If you forget the empty list case, Lean won't let you compile. The pattern matcher is exhaustive.
 
---
 
## The Lean Ecosystem
 
### Mathlib: The Standard Library
 
[Mathlib](https://github.com/leanprover-community/mathlib4) is a massive library of formalized mathematics—thousands of theorems, lemmas, and definitions.
 
**Some examples:**
- `List.length_append`: proves `(xs ++ ys).length = xs.length + ys.length`
- `Nat.add_comm`: proves `m + n = n + m` for all natural numbers
- `Finset.sum`: defines finite sums with proofs about their properties
Instead of proving everything from scratch, you import Mathlib and use pre-proven lemmas.
 
### Lean Community
 
- **[Lean Zulip Chat](https://leanprover.zulipchat.com/)** — Ask questions, get help instantly
- **[Lean Game Server](https://adam.math.hhu.de/)** — Interactive puzzles to learn Lean
- **[Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)** — Search lemmas by name or type
---
 
## Real-World Applications: Certified Programming
 
Dependent types aren't just theoretical. They're used in practice:
 
### 1. **Compiler Verification**
Formally verify that a compiler produces correct output. Companies like Amazon and Huawei have used Lean for this.
 
### 2. **Cryptography**
Prove that cryptographic implementations are correct. Formal verification catches subtle bugs that testing misses.
 
### 3. **Safety-Critical Systems**
Autonomous vehicles, medical devices, and aviation systems use formal methods to guarantee correctness.
 
### 4. **Mathematical Proofs**
Mathematicians use Lean to formalize proofs. The Four Color Theorem and parts of the Perfectoid Spaces project have been formalized in Lean.
 
---
 
## Key Insights: Why This Matters
 
### 1. **Correctness is Computable**
With dependent types, correctness isn't an after-thought. It's built into the type system.
 
### 2. **The Curry-Howard Correspondence**
Proofs and programs are the same thing. A proof of a theorem *is* a program of the corresponding type.
 
### 3. **Zero-Cost Abstraction**
Proofs are erased at runtime. Your verified code runs as fast as unverified code.
 
### 4. **Composability**
If function `f` has type `A → B` and function `g` has type `B → C`, you can compose them to get `A → C`. The types guarantee the composition is valid.
 
---
 
## Getting Started
 
### Try Interactive Puzzles (No Setup)
- [Lean Game Server](https://adam.math.hhu.de/) — Play puzzle games to learn Lean syntax
### Install Lean Locally
 
**On macOS / Linux:**
 
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake new my_first_project
cd my_first_project
lake build
```
 
**On Windows:**
 
```powershell
# Download and run the Windows installer
curl -O https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
.\elan-init.ps1
lake new my_first_project
cd my_first_project
lake build
```
 
Or use **Chocolatey** (if installed):
```powershell
choco install lean
```
 
**All platforms:** After installation, verify with:
```bash
elan --version
lean --version
```
 
### Learn from Official Resources
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) — Official tutorial
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) — Learn pure FP in Lean
- [Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025) — What this course uses
### Join the Community
Ask questions in the [Lean Zulip](https://leanprover.zulipchat.com/) — it's friendly and welcoming.
 
---
 
## Summary: The Journey
 
We've gone from:
 
- **The problem:** Testing can't guarantee correctness
- **The vision:** Write programs with built-in proofs
- **The tool:** Lean, a practical programming language + theorem prover
- **The insight:** Dependent types let you encode correctness in types
- **The examples:** List length, append associativity, safe division
- **The ecosystem:** Mathlib, Lean Game Server, community resources
Lean represents a paradigm shift in how we think about programming. Instead of:
 
```
Write Code → Test → Hope for the Best
```
 
We can now do:
 
```
Write Code → Write Proof → Guarantee Correctness
```
 
This isn't theoretical. It's practical. It's usable. And it's the future of safety-critical software.
 
---
 
## References & Further Reading
 
**Official Resources:**
- [Lean Language Website](https://lean-lang.org/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
**Learning & Community:**
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)
- [Lean Game Server](https://adam.math.hhu.de/)
- [Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
**Theoretical Foundations:**
- [Lambda Calculus](https://en.wikipedia.org/wiki/Lambda_calculus)
- [Curry-Howard Correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence)
- [Dependent Types](https://en.wikipedia.org/wiki/Dependent_type)
- [Intuitionistic Type Theory](https://en.wikipedia.org/wiki/Intuitionistic_type_theory)
**Historical Context:**
- Per Martin-Löf: *Intuitionistic Type Theory* (1984)
- Thierry Coquand & Gérard Huet: *The Calculus of Constructions* (1988)
- Leonardo de Moura: *Lean: A Proof Assistant* (2016)
---
 
## Conclusion
 
Lean is more than a tool—it's a new way of thinking about code. By combining programming and proving, it lets you write software that is not just tested but *proven correct*. 
 
The journey from "bugs in production" to "proofs before deployment" is transforming how we build reliable systems. Whether you're interested in formal methods, pure mathematics, or safe software engineering, Lean provides the language and community to explore these ideas.
 
Start small, prove simple theorems, and gradually build your confidence. The Lean community is here to help. Welcome to the world of correct-by-construction programming.