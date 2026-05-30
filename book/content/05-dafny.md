# Program analysis in Dafny

```{note}
**Chapter roles (Spring 2026)**  
Author: Khoa Nguyen · Reviewer: Kaye Galang  
See [Chapter assignments](0-chapter-assignments.md).
```

This chapter introduces **Dafny** for specifying and verifying imperative and functional programs with automated theorem proving.

## Introduction

**Dafny** is a "verification-aware programming language". "Verification-aware" means that the language is designed to incorporate formal verfication directly into their development and runtime operations. This is particularly useful when a system is needed to be "provably correct", i.e. mathematically proven to be correct, and not just "probably correct". **Dafny** natively support recording specifications and integrates static program verfifier. It empowers developers to write provably correct code with respect to their specifications through combining sophisticated automated reasoning with familiar programming idioms and tools. It compiles to popular coding languages such as C#, Java, JavaScript, Go, and Python, allowing integration with existing workflows [[1]](#ref1).

**Dafny** was created by K. Rustan M. Leino at Microsoft Research, building on his earlier work on ESC/Modula-3, ESC/Java, and Spec#. Leino latter moved to Amazon Web Services, where his team applied **Dafny** to security-critical infrastructure, including the AWS Encryption SDK and the Cedar policy engine [[2]](#ref2)-[[3]](#ref3). He is no longer working at AWS.

Under the hood, **Dafny** translates programs to the Boogie intermediate verification language and then dispatches proof obligations to the Z3 SMT (Satisfiability Modulo Theories) solver. If Z3 can construct a proof, the program is verified. If not, **Dafny** reports a counterexample directly in the editor, enabling immediate feedback much like a type-checker does today [[2]](#ref2),[[4]](#ref4).

For more information about Z3 and SMT solving, checkout this [book](https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/content/04-smt-solving-z3.html). 

### Why Use Dafny?

#### From Testing to Proof
Conventional testing checks behaviour on a finite set of inputs. Formal verification proves behaviour over all possible inputs. **Dafny** makes rigorous verification an integral part of development, thus reducing costly late-stage bugs that testing alone may miss.

#### Integrated with Developer-Friendly Workflow

Unlike standalone theorem provers such as Coq, now known as Rocq, or Isabelle/HOL, **Dafny** embeds specifications directly into the source code. The VSCode extension applies the verifier continuously in the background, flagging problems as the programmer types. Specifications and ghost constructs are stripped out at compile time, so they carry zero runtime overhead.

For more information on Rocq, check out chapter [8](https://leap-at-chapman.github.io/CPSC-570-From-Bugs-to-Proofs/rocq/) of the current book. Check out this [book](https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/content/08-higher-order-logic-isabelle.html) for more information about Isabelle and Higher Order Logic.
 
#### Compile to Real Languages

Because **Dafny** compiles to C#, Java, JavaScript, Go, and Python, teams do not need to abandon their existing technology stacks. The verified **Dafny** source becomes a trustworthy blueprint whose compiled output can be dropped into production systems.

## Hoare-style Reasoning

Hoare logic, or Floyd-Hoare Logic or Hoare-rules, serves as the foundation for **Dafny** logic. The central idea was the Hoare Triple:

``` { P } C { Q } ```

`P` is the precondition, describing the state of the world. `C` is the command to be executed. `Q` is the postcondition, describing the state of the world after command is executed. A Hoare Triple is valid if `P` holds before `C` runs and `C` terminates, then `Q` is guaranteed to hold after `C`.
Hoare logic is essential for mathematically proving program correctness, ensuring that if prerequisites are met, a program's execution produces the desired results. **Dafny** integrates Hoare logic directly in its syntax. Under the hood, **Dafny** translates Hoare-style specifications into Boogie's intermidiate language, then hands the proof obligations to the Z3 SMT solver. 

The preconditions are the ``requires`` clauses, using the ``requires`` keyword. A ``requires`` clause states what must be true for a method to be called correctly. If a caller violates the precondition, Dafny will report a verfication error at the call site, not inside the method. This seperates caller obligations from implementer guarantees. The commands exist within the curly brackets, indicating what the method does, similar to other programming languages that also utilize curly brackets to indicate code blocks. 
```
  method Divide(a: int, b: int) returns (result: int)
    requires b != 0
  {
    result := a / b;
  }
```
It is never correct to divide a number by zero (0), or rather the answer is undefined if a division by zero occured. In the above example, since we are dividing ``a`` by ``b``, we must require that ``b`` cannot be zero (0).

The postconditions are indicated by the ``ensures`` keyword. An ``ensures`` clause states what a method promises to deliver. **Dafny** proves that every return path of the method satisfies the postcondition, given the preconditions hold. 
```
  method Abs(x: int) returns (y: int)
    ensures y >= 0
    ensures (x >= 0 ==> y == x) && (x < 0 ==> y == -x)
  {
    if x < 0 { y := -x; } else { y := x; }
  }
```
In the case of absolute value, any number can satisfy the operation or any number can have an absolute value, so preconditions are not required. However, we must ensures that if the input is positive, the output must be equal to the input and if the input is negative, the output must be equal to the opposite of the input. This way, we can guarantee that the method is mathematically correct. 

**Dafny** supports proofs of imperative programs based on the ideas of Hoare logic, where loop invariants and loop variants are supplied via invariant and decreases clauses respectively. An invariant, or loop invariant, is a condition that is always true before and after a loop iteration is executed. The treatment of loop invariants in **Dafny** differs subtly from traditional Hoare logic. Variable mutated in a loop having any prior facts about them are discarded at loop entry, so all necessary information must be written explicity in the invariant, using the ``invariant`` keyword. An invariant must satisfy three properties: 
- It is implied by the precondition.
- It is presevered by each iteration of the loop body.
- Together with the negated loop condition, it implies the postcondition.

To prove total correctness (the program terminates and is correct), **Dafny** requires a ``decreases`` clause, using the ``decreases`` keyword. This expression is bounded below and strictly decreases with each loop iteration or recursive call. This prevents infinite loops by construction. **Dafny** can often infer simple decreases clauses automatically.

Sometimes proving termination is either impossible or beside the point. Consider a stream processor intended to run forever, or a loop whose termination depends on an unsolved mathematical conjecture. For these cases, **Dafny** provides an escape hatch: the special annotation ``decreases *``, which instructs the verifier to skip the termination check entirely for that loop or method. All other correctness properties,preconditions, postconditions, loop invariants, are still fully verified.

The canonical illustration is the Collatz conjecture (also known as the hailstone sequence). Starting from any positive integer ``N``, the rule is simple: if ``N`` is even, halve it; if ``N`` is odd, multiply by 3 and add 1. The conjecture, one of the most famous unsolved problems in mathematics, holds that this process always eventually reaches 1, but no proof exists. **Dafny** captures this perfectly:

```
  method hail(N: nat)
    decreases *
  {
    var n := N;
    while 1 < n
      decreases *
    {
      n := if n % 2 == 0 then n / 2 else n * 3 + 1;
    }
  }
```
This program terminates if and only if the Collatz conjecture is true, which, as of 2026, remains an open problem in mathematics. Rather than pretending the question is settled, **Dafny** provides an honest mechanism: ``decreases *`` acknowledges that termination is either unknown or intentionally unbounded, while still enforcing every other correctness property. A method containing a loop marked ``decreases *`` must itself be marked ``decreases *``, propagating the disclaimer up the call chain so no caller can silently depend on termination.

This distinction between partial correctness (the program does the right thing if it terminates) and total correctness (the program does the right thing and terminates) is one Hoare logic makes explicit, and **Dafny** exposes it squarely to the programmer. Most production code should carry full termination proofs. But ``decreases *`` is the right tool when you are modelling a reactive system, exploring an algorithm whose convergence is not yet understood, or deliberately writing an infinite server loop [[12]](#ref12).

## Walkthrough with Binary Search

Binary search is one of computer science's most celebrated algorithms, one where many programmers leanr in their Algorithm and Data Structures classes, yet it is notorious for hiding subtle bugs. **Dafny** eliminates an entire class of these bugs by using mathematical (unbounded) integers, and its verifier catches logical errors that testing rarely finds.

### Specification
Before writing a single line of implementation, we state what binary search should do:
- Input (Precondition): a sorted sequence of integers and a key to search for.
- Output (Postcondition): an index in the sequence, or -1 if the key is not present.
- Correctness: if a valid index is returned, the element at that index equals the key. If -1 is returned, the key is absent from the entire sequence.

In **Dafny**, the precondition and postcondition capture these requirements precisely:
```
  predicate Sorted(q: seq<int>)
  {
    forall i, j :: 0 <= i < j < |q| ==> q[i] <= q[j]
  }
```
A predicate is a function that returns a boolean. In this example, it is checking that every elements in the list or sequence passed into the function is sorted in ascending order.  

```
  method BinarySearch(q: seq<int>, key: int) returns (index: int)
    requires Sorted(q)
    ensures index == -1 ==> forall i :: 0 <= i < |q| ==> q[i] != key
    ensures index != -1 ==> 0 <= index < |q| && q[index] == key
```

### Implementation

The method ``BinarySearch`` takes 2 arguments, a sequence of integer and a key to search[[5]](#ref5).

The iterative body maintains two pointers, ``lo`` and ``hi``, narrowing the search window with each iteration:

```
method BinarySearch(q: seq<int>, key: int) returns (index: int)
  requires Sorted(q)
  ensures index == -1 ==> forall i :: 0 <= i < |q| ==> q[i] != key
  ensures index != -1 ==> 0 <= index < |q| && q[index] == key
{
  var lo := 0;
  var hi := |q|;
  index := -1;
  while lo < hi
    invariant 0 <= lo <= hi <= |q|
    invariant forall i :: 0 <= i < lo ==> q[i] < key
    invariant forall i :: 0 <= i < |q| ==> q[i] > key
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if q[mid] == key {
      index := mid;
      return;
    } else if q[mid] < key {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
}
```

### Invariants and Decreases

Each of the three loop invariants plays a distinct role:

```
invariant 0 <= lo <= hi <= |q|
```
This invariant guarantees that ``lo`` and ``hi`` never escape the valid index range. Without it, **Dafny** cannot prove that the midpoint computation and the array accesses are safe. It ensures that, before the loop, ``lo = 0`` and ``hi = |q|`` holds and is preserved because each branch either increases ``lo`` or decreases ``hi`` within the window.

```
invariant forall i :: 0 <= i < lo ==> q[i] < key
```
Everything to the left of ``lo`` has already been ruled out, i.e. strictly smaller than the key. Because the sequence is sorted, once we move ``lo`` past position ``mid``, every element before ``lo`` is known to be less than ``key``.

```
invariant forall i :: 0 <= i < |q| ==> q[i] > key
```
Symmetrically, everything at or beyond ``hi`` is strictly greater. When ``lo`` and ``hi`` converge, invariants 2 and 3 together state that the key cannot be anywhere in the sequence, justifying the return of -1.

```
decreases hi - lo
```
The quantity ``hi - lo`` is a non-negative integer (by invariant 1) that strictly decreases every iteration. If the ``key`` is not found, ``mid`` is strictly between ``lo`` and ``hi``, so advancing ``lo`` or retreating ``hi`` always shrinks the window by at least 1. **Dafny** verifies this automatically.

### A Note on Overflow 

A notorious real-world bug in many binary search implementation is integer overflow in computing the midpoint. In languages with bounded integers, ``(lo + hi) / 2`` can overflow when ``lo`` and ``hi`` are large. **Dafny** uses mathematical integers that never overflow, so this entire class of bugs is excluded by the language's type system. **Dafny** verfier verifies that ``(lo + hi) / 2`` is used correctly without any explicit annotation from the programmer.

### What Dafny Checks

When this method is submitted to **Dafny**, the verifier checks all of the following automatically:

- The precondition Sorted is satisfied at every call site.
- Each loop invariant holds before the loop.
- Each loop invariant is preserved by the loop body.
- The decreases clause is strictly decreased each iteration.
- Both postconditions hold when the method returns, for every possible return path.
- All array/sequence accesses are within bound.
If any check fails, **Dafny** returns a counterexample, i.e. a specific assignment of values that witnesses the failure, rather than just a generic error message.

## Exploration - Dafny, Game Development, and Industries Applications

Game development is an unlikely candidate for formal verification. It is known for rapid prototyping, shifting requirements, and a tolerance for imperfection. In other words, it suffers from the notorious "good enough for games" ethos. As a result, since many modern games are enormous software systems, bugs escape into shipping code, causing genuine harm to player experience, competitive fairness, and studio reputation.

Not every part of a game engine is a suitable target for **Dafny**, but several subsystems are excellent candidates:

### Game Rule Engines

Many games system are defined by discrete, precisely-stated rules. A rules engine in **Dafny** could carry formal proofs that:
- Inventory or resource counts never go negative.
- Win conditions are triggered if and only if the formal win predicate is satisfied.
- The game state is always reachable from the initial state by a valid sequence of moves.

Such proofs would be particularly valuable for competitive or ranked games, where rule-engine bugs can create exploits that affect real player rankings.

### Collision Detection Logic

Collision detection bugs, where objects clip through walls or hit-boxes mismatch visual geometry, are among the most common and costly bugs in game development. Collision responses of the category "two objects intersect and the physics engine does not handle it correctly" are a well-documented class of failures in shipped games [[6]](#ref6).

Physical laws do not exist in the virtual world by default. They must be computationally modelled and programmed carefully. **Dafny** could specify and verify the invariants of a collision detection subsystem, for instance

```
// Invariant: no two solid objects ever occupy the same cell
predicate NoOverlap(objects: seq<GameObject>)
{
  forall i, j :: 0 <= i <j < |objects|
    ==> !Intersects(objects[i].bounds, objects[j].bounds)
}
```
A verified collision response method would carry a proof that the post-collision state satisfies NoOverlap, eliminating clipping bugs by construction rather than by testing [[7]](#ref7).

### Procedural Generation Guarantees

Procedural content generation, like dungeons, maps, quest graphs, relies on algorithms that must satisfy structural invariants. A procedurally generated dungeon should always be fully connected; a quest dependency graph should always be acyclic. These are precisely the kinds of properties that **Dafny** excels at verifying. A verified dungeon generator could carry formal proof that every generated level has at least one path from entrance to exit.

### Save-State Serialisation

Save files are a form of persistent state that must round-trip faithfully: 
```
serialize(deserialize(s)) == s and deserialize(serialize(g)) == g. 
```

These are natural **Dafny** postconditions. Bugs in save-state serialisation are notoriously hard to find with random testing, since they often manifest only with unusual game-state combinations. A formally verified serialiser would eliminate this class of bugs entirely.

### Networking and Determinism

Multiplayer games with rollback netcode (such as GGPO) require that game logic be perfectly deterministic: the same inputs must always produce the same state. A **Dafny**-verified simulation kernel could carry a formal proof of determinism, ruling out floating-point non-determinism, hash-map iteration-order bugs, and other subtle sources of desynchronisation that cause players to see different game states.

### Limitations
Formal verification is not a silver bullet, and applying **Dafny** to game development carries real costs. Writing specifications takes time and skill. The verifier can fail to discharge proofs automatically, requiring hand-crafted lemmas. And a formally verified program is only as correct as its specification: if the specification is wrong, the proof proves the wrong thing.

Nevertheless, for the parts of a game that most resemble the safety-critical software **Dafny** already excels at: deterministic simulation kernels, rule engines, serialisation. The cost of specification is likely lower than the cost of shipping bugs. The game industry's growing interest in competitive integrity and live-service reliability creates a natural home for these techniques.

### Industries Adoptation

**Dafny** is used in many areas in real-world industries. For example, at AWS, Leino's team used it to produce a formally verified implementation of the AWS Encryption SDK and to formally verify the Cedar authorization engine. In Leino's own words: "What's exciting is that we have moved the needle from using **Dafny** in research projects to using it in projects with industrial impact." The client-side encryption library for .NET was implemented and formally proved in **Dafny**, proving mathematical guarantees about cryptographic correctness that testing alone cannot supply [[8]](#ref8)

Here is a list of some notable examples of real-world **Dafny** deployments:
- Ethereum Virtual Machine Sematincs (ConsenSys): The Trustworthy Smart Contracts team at ConsenSys built a formal, executable semantics of the EVM in **Dafny**, enabling bytecode-level verification of smart contracts. A single vulnerability in a smart contract can cause catastrophic financial losses, making this a natural home for formal proof [[9]](#ref9).
- Railway Interlocking Logic (Fondazione Bruno Kessler): Researchers at FBK used **Dafny** to verify a generic interlocking logic controlling train movements in railway stations, safety-critical infrastructure where a verification failure could mean a collision [[10]](#ref10).
- Railway Protection Systems: Independent work at CAV 2025 demonstrated automated, parameterized verification of a Railway Protection System using **Dafny**, showing the approach scales to the variety of station configurations found in real deployments[[11]](#ref11).

## References
- <a id="ref1"></a>[1] https://dafny.org/dafny
- <a id="ref2"></a>[2] https://en.wikipedia.org/wiki/Dafny 
- <a id="ref3"></a>[3] https://www.amazon.science/working-at-amazon/rustan-leino-provides-proof-that-software-is-bug-free
- <a id="ref4"></a>[4] https://en.wikipedia.org/wiki/Hoare_logic
- <a id="ref5"></a>[5] https://dafny.org/latest/OnlineTutorial/guide
- <a id="ref6"></a>[6] https://link.springer.com/article/10.1007/s10270-024-01253-2
- <a id="ref7"></a>[7] https://www.kth.se/social/files/5ad8a6e356be5b8d377ba851/DGI%2018%20Collision%20detection%20Fangkai.pdf
- <a id="ref8"></a>[8] https://www.amazon.science/working-at-amazon/rustan-leino-provides-proof-that-software-is-bug-free
- <a id="ref9"></a>[9] https://dafny.org/blog/2025/06/24/evm-bytecode/
- <a id="ref10"></a>[10] https://arxiv.org/pdf/2403.00087
- <a id="ref11"></a>[11] https://www.researchgate.net/publication/393948025_Automated_Parameterized_Verification_of_a_Railway_Protection_System_with_Dafny
- <a id="ref12"></a>[12] https://dafny.org/latest/OnlineTutorial/Termination
