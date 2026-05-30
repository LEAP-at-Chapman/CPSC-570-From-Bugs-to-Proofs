# Program extraction with Rocq

```{note}
**Chapter roles (Spring 2026)**  
Author: Nayeli Castro · Reviewer: Khoa Nguyen  
See [Chapter assignments](0-chapter-assignments.md).
```

This chapter introduces **Rocq** (formerly known as Coq) with emphasis on constructive proofs and extracting runnable programs.

## Goals

- Motivate program extraction: how a constructive proof that an object *exists* can be turned into executable code (e.g. via Rocq’s extraction to OCaml or Haskell), and why that matters for building correct-by-construction components rather than treating the prover as a black box.
- Show a minimal development ending in extracted code or a verified function.
- Explore a further aspect depending on your interest.
- Link to Rocq / Coq documentation and community-maintained learning paths.

## Background

**Rocq** (formerly known as Coq) is a program developed to provide interactive and computational proof assistance to users developing their own theorems. Rocq works as an interactive theorem prover through machine-assisted and machine-augmented proof checking, and it is often used by developers to find formal proofs through proof automation, express and check mathematical insertions, and perform program extraction through proving the existence of a mathematical object in its formal specification. As a program that has existed and been used since 1989, Rocq has established itself as an important computational tool available to developers and mathematicians that are in need of proving complex theorems or extracting code that may be difficult or impossible through human-performed techniques.[^1]

## Basic Theory and Syntax Basics

Rocq differs from other unique programming langauges as it is mainly used for proof assistance. Due to that, its language is formatted in such a way that it would make it easier to write theorems. The Rocq Language itself contains features such as implicit arguments and notations, which are then translated into the the core language, **CoC** , into a definition that the **Rocq Kernel** can read and interpret. CoC, or Calculus of Constructions, is a type theory that may serve as both a programming language and mathematical framework. It has the ability to define functions from terms to terms, terms to types, types to types, and types to terms. CoC was developed alongside Rocq and became the main theory that the interactive theorem prover follows.[^2][^3]

The Rocq Kernel itself is the most important part of Rocq, as it serves as being the smaller critical component of the entire system that focuses on checking important CoC concepts such as **terms** and **types** that are written within the program.[^2]

**Terms** are the basic expressions used in Rocq. They may be used to represent proofs, mathematical expressions, propositions, and even executable programs and program types. Every term needs to be associated wih a type. **Types** in Rocq represent logical propositions as well as the program that is the proof of those propositions, therefore making all types be terms, but not all terms are types. The Rocq Kernel checks whether a term has an associated type and if that type follows a certain *typing rule*.[^4]

**Terms** are declared using commands such as *Definition*, *FixPoint*, *Theorem*, *Compute*, and *Check*.[^5]

- *Definition* gives a name to a value, function, or proof term. They are used for *non-recursive* function.

```rocq
(* Definitions, as well as other terms, follow this basic syntax:
Definition name : type := body.
*)

(* An example of a Definition *)
Definition reference_add_two (n : nat) : nat :=
  n + 2.
```

- *Fixpoint* gives a name to a *recursive* function. Recursive functions recurse within a subpart of their input due to recursive functions being structurally smaller. 

```rocq
(* Fixpoints follow this basic syntax: 
Fixpoint name (x : type) : result_type :=
      match x with
      | ...
      end.
*)

(* An example of a Fixpoint *)
Fixpoint reference_length {A : Type} (xs : list A) : nat :=
  match xs with
  | [] => 0
  | _ :: rest => S (reference_length rest)
  end.
```

- *Theorem* starts a proof obligation and contains a proposition that is proven within *Proof*, which makes Rocq go into Proof Mode, and *Qed*, which terminates Proof Mode. In Proof Mode and within the boundaries of *Proof* and *Qed*, *tactics* specify how to transform the current *proof state* (an unproven goal or proposition) in order eventually generate a complete proof. The list of tactics available in Rocq is found in the [Tactic Index](https://rocq-prover.org/doc/V9.2.0/refman/rocq-tacindex.html#tactic-index).

```rocq
(* Theorems follow this basic syntax:
Theorem name : proposition.
    Proof.
      ...
    Qed.
*)

(* An example of a Theorem *)
Theorem reference_add_two_zero :
    reference_add_two 0 = 2. (* The proposition we want to prove is that 'reference_add_two_zero' equals 2 when it takes in 0. *)
Proof. (* Begin the proof, go into Proof Mode *)
  reflexivity. (* The specified tactic method that will be used to reach the goal of the proposed theorem *)
Qed (* Terminate the proof, Exit Proof Mode *).
```

- *Compute* is used to evaluate an expression and is often used for checking the output of an expression for testing purposes. It is not a proof by itself.

```rocq
(* An example of how to use Compute *)
Compute reference_add_two 5.
Compute reference_length [true; false; true].
```

- *Check* is used to check the type or name of an expression. This term is often used to inspect what Rocq thinks the meaning or properties of an expression is.

```rocq
(* An example of how to use Check *)
Check reference_add_two.
Check reference_length.
Check reference_add_two_zero.
```

**Types** are used to construct logical foundations of mathematics by using foundations from *"type theory"* rather than the standard *"set theory"* due to Rocq's fundamental usage of CoC. Types may be seen as sets that contain terms, and a type that has at least one term is referred to an inhabited type. Types may also contain other types that apply to it. Due to the strict rule of terms needing an associated type, the Rocq Kernel always verifies that the rule is followed as well as making sure that the term and type are associated via one or several *typing rules*.[^4] 

**Typing rules** exist as a way to make terms follow *type discipline*, in which they then are verified within a *global environment* with a *local context*. Typing rules are set in order to:

1. Ensure the Proposed Logic and Operation is Correct and Makes Sense.

2. Ensure that Terms Match the Proposition Being Proven to Prevent Contradictions.

3. Verify the Correctness of Properties, Algorithms, and Specifications.

4. Ensure that Programs are Well-Defined and Contain No Logical Issues Before Program Extractions.

The relationship between terms and types are one of the fundamental aspects of Rocq as it is tied to CoC theory and its format for performing proofs. A proposition must have a consistent structure for the relationships between its terms and types in order to be able to have a valid proof.

## Introduction to Program Extraction with Rocq

Although Rocq is mainly seen as an interactive proof asistant program, it also functions as a programming language. Due to this dual role, Rocq is able to convert its theorems into executable programs. The theory behind turning theorems into programs assumes that proofs contain computational content and that building blocks from both proofs and programs correspond to each other, such as propositions corresponding to types, proof simplification corresponding to program evaluation, and proofs states corresponding to functions within a program. This theory is referred to as the *Curry-Howard correspondence*.[^6]

The ability to perform program extraction is one of the most important and unique traits of Rocq, and also the reason many choose Rocq as their program of choice for representing proposed designs in code. Extraction matters due to the methodology of *Correct by Construction (CbC)*, in which mathematical models are built before design coding.[^7] The aim of the methodology of CbC is to catch any possible defects in the design of a proposed model before the time and effort is put on building the final component that the model will be presented in. For example, one typically writes pseudo code to lay out the foundation of a proposed solution to a problem or within smaller blocks like functions that have yet to be written as a way to have a "template" of what the function is supposed to do. Using the CbC methodology with Rocq goes into even lower levels of code, down to the fundamentals of a proposed mathematical or algorithmic design. The combination of CoC and CbC, as well as Rocq being built to support both methodologies, makes proving correctness of a design quicker and more organized than a human doing it by hand at a higher level. 

The extraction targets of Rocq are *OCaml* and *Haskell* due to their compatibility of all being functional languages. Rocq being a functional language is important to its usage as it makes functions more mathematical and immutable, makes computation be expression-based, and makes use of heavy recursion; all which are sought after when proving complicated theorems and verifying lower-level design proposals. Haskell and OCaml in particular match Rocq's internal presentations of containing expressive type systems and pattern matching. 

While Rocq is mainly designed to prove theorems at its most basic level, extraction to Ocaml or Haskell makes it possible to transfer lower-leveled designs written in Rocq into higher-level programs that can compile, run as applications, and most importantly, be able to be integrated into larger or different systems of code. The main idea of extraction is to start from the basics of a design with Rocq, make sure its components are able to be proven, and then extract that design to Ocaml or Haskell, where the design is able to evolve into being part of a bigger and more complete program.

## How to Perform Program Extraction

The basic workflow for program extraction in Rocq is simple. All that is needed is to load Rocq's extraction framework onto any kind of definition or proposition written within the Rocq kernel, with either Ocaml or Haskell chosen as the output language.

```rocq
Definition add_one (n : nat) : nat :=
  n + 1.
```

This is a simple definition written in *Gallina*, Rocq's functional programming language framework. **add_one** takes a natural number and adds **1** to it. Gallina specifically enforces the rule that all programs must terminate, which ensures that all programs that are written are *well-typed* and free from errors and contradictions.[^2] This is valuable to the process of extracting content from Rocq to executable source code, as it makes it necessary for the lower-level *logic* to make sense and be functional.

```rocq
Require Extraction.
Extraction Language Haskell.
Extraction "add_one.hs" add_one.
```
**Require Extraction** is what loads Rocq's extraction system. **Extraction Language** defines the language (in this example, it would be Haskell) that will used to represent the translation of Rocq's logic into usable executable code. **"add_one.hs"** is the name of the output file for the extraction. The **add_one** after the output file is telling the extraction system that we will want to extract the contents of **add_one** onto the Haskell output file named **add_one.hs**.[^8]

Once the extraction is ran, the definition written inside Rocq will be automatically translated into the selected extraction language.

```haskell
add_one :: Nat -> Nat
add_one n =
  add n (S O)
```
The original definition in Rocq has been extracted into executable Haskell code.

## Real World Usage of Rocq Extraction

The **Compcert C Compiler** is a compiler for the C programming language, a fundamental programming language used in many computational components. The Compcert C Compiler was designed to be intended to be used for life-critical and mission-critical software for systems that need precision, such as systems for rockets and medical equipment. The compiler is trusted by many developers due to being formally verified through it's lowest level of mathematical proofs, making it completely excempt from miscompilation issues that are common in other C compilers. The developers of the Compcert C compiler verified the compiler's core logic through Rocq and extracted the Rocq definitions into OCaml code, which was later increased in size and complexity through C code.[^9] In the end, Rocq is a very valuable program that made itself crucial to the machine-assisted development of several kinds of theorems and systems by being both accurate and malleable enough to "grow" into larger and more complex executable instructions.

## References

[^1]: Introduction and Contents from The Rocq Prover Reference Manual. (Link)[https://rocq-prover.org/doc/V9.2.0/refman/index.html]

[^2]: Core Language from The Rocq Prover Reference Manual. (Link)[https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html]

[^3]: Calculus of Constructions Wikipedia Page. (Link)[https://en.wikipedia.org/wiki/Calculus_of_constructions]

[^4]: Basic Notions and Conventions from The Rocq Prover Reference Manual. (Link)[https://rocq-prover.org/doc/V9.2.0/refman/language/core/basic.html#term-term]

[^5]: From Bugs to Proofs tutorial_01_basics_love_01_04.v Github file. (Link)[https://github.com/LEAP-at-Chapman/CPSC-570-From-Bugs-to-Proofs/blob/main/rocq/tutorial_01_basics_love_01_04.v]

[^6]: Curry-Howard Correspondence Wikipedia Page. (Link)[https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence]

[^7]: Correct by Construction Wikipedia Page. (Link)[https://en.wikipedia.org/wiki/Correct_by_Construction]

[^8]: Program Extraction from The Rocq Prover Reference Manual. (Link)[https://rocq-prover.org/doc/V9.2.0/refman/addendum/extraction.html]

[^9]: The Compcert C Compiler Official Website. (Link)[https://compcert.org/compcert-C.html]
