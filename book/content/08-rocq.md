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

## Draft

**Rocq** (formerly known as Coq) is a program developed to provide interactive and computational proof assistance to users developing their own theorems. Rocq works as an interactive theorem prover through machine-assisted and machine-augmented proof checking, and it is often used by developers to find formal proofs through proof automation, express and check mathematical insertions, and perform program extraction through proving the existence of a mathematical object in its formal specification. As a program that has existed and been used since 1989, Rocq has established itself as an important computational tool available to developers and mathematicians that are in need of proving complex theorems that may be difficult or impossible through human-performed techniques. 
