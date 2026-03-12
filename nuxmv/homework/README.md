# Homework: Railroad Crossing Controller in nuXmv

## Overview

In this homework you will model a **railroad crossing controller** — a safety-critical system where a gate must protect cars from an oncoming train — and use nuXmv to verify its properties with CTL and LTL.

This builds on the mutual exclusion demo from lecture. Both systems prevent dangerous concurrent states: in mutex, two processes must not be in the critical section simultaneously; here, the train must not be crossing while the gate is up. The same verification patterns apply — safety, liveness, fairness — but now in a **controller-environment** setting rather than peer-to-peer.

You will build the verification incrementally across three parts:

| Part | Topic | You will learn | File |
|------|-------|----------------|------|
| 1 | **Modeling** | nuXmv state machines, transitions | [RailroadCrossing_Part1.smv](RailroadCrossing_Part1.smv) |
| 2 | **LTL** | Linear-time properties, LTLSPEC keyword | [RailroadCrossing_Part2.smv](RailroadCrossing_Part2.smv) |
| 3 | **CTL + Fairness** | Branching-time properties, FAIRNESS | [RailroadCrossing_Part3.smv](RailroadCrossing_Part3.smv) |

Each part builds on the previous one. Complete them in order.

---

## The System

A train approaches a crossing. A gate must lower before the train arrives and raise after it leaves.

```
  Train lifecycle:                Gate lifecycle:

  absent ──► approaching          up ──► lowering
    ▲            │                  ▲        │
    │            ▼                  │        ▼
  leaving ◄── crossing            raising ◄── down
       ▲        │
       │        ▼
       └───── near
```

The train passes through five states: `absent → approaching → near → crossing → leaving → absent`. The intermediate `near` state gives the gate time to lower before the train arrives at the crossing.

The gate responds to the train: it begins lowering when the train approaches, and begins raising when the train leaves.

The key guarantee: **the gate is down whenever a train is crossing.**

---

## Part 1: Modeling — [RailroadCrossing_Part1.smv](RailroadCrossing_Part1.smv)

**Goal:** Complete the state machine for the gate controller.

The template provides:
- Variable declarations for `train` and `gate`
- Complete train transitions (the environment)
- Gate `init` (given) and `next` skeleton (TODO)

**Your task:**
1. Fill in `next(gate)` so the gate responds correctly to the train
2. Fill in the `DEFINE` section (`safe` and `train_present`)
3. Uncomment the SPEC at the bottom to verify your model

**What to observe:** Does `AG safe` pass? If not, inspect the counterexample to find your bug.

---

## Part 2: LTL — [RailroadCrossing_Part2.smv](RailroadCrossing_Part2.smv)

**Goal:** Write LTL specifications that capture safety and response properties.

The model from Part 1 is included (with the same TODOs — complete Part 1 first). Your task is to translate English properties into LTL formulas using the `LTLSPEC` keyword.

**Your task:** Write LTL formulas for three properties (described in the file).

**LTL quick reference:**

| Operator (nuXmv notation) | Operator (LTL notation) | Meaning |
|----------|---------|---------|
| `G p` | $\square p$ | p holds globally |
| `F p` | $\lozenge p$ | p holds eventually |
| `X p` | $\bigcirc p$ | p holds in the next state |
| `p U q` | $p \mathbf{U} q$ | p holds until q becomes true |

**What to observe:** Do all your properties pass? If not, inspect the counterexample.

---

## Part 3: CTL + Fairness — [RailroadCrossing_Part3.smv](RailroadCrossing_Part3.smv)

**Goal:** Write CTL specifications and add fairness constraints to ensure liveness.

The model from Parts 1–2 is included (with the same TODOs — complete Part 1 first). Your LTL specs from Part 2 are referenced for comparison. Your task is to add CTL specifications and a FAIRNESS constraint.

**Your task:**
1. Write CTL formulas for five properties (described in the file)
2. Run **without** the FAIRNESS constraint — note which properties fail
3. Add the FAIRNESS constraint, re-run — note which now pass
4. Explain: why does fairness matter for this model?

**CTL quick reference:**

| Operator (nuXmv notation) | Operator (LTL notation) | Meaning |
|---------|---------|---------|
| `AG p` | $\forall \square p$ | On all paths, p holds globally |
| `AF p` | $\forall \lozenge p$ |On all paths, p holds eventually |
| `EF p` | $\exists \lozenge p$ |On some path, p holds eventually |
| `EG p` | $\exists \square p$ | On some path, p holds globally |
| `AX p` | $\forall \bigcirc p$ | In all next states, p holds |
| `A[p U q]` | $\forall (p \mathbf{U} q)$ |On all paths, p holds until q |

**What to observe:** Which CTL properties fail without fairness? What counterexample does nuXmv produce? How does `FAIRNESS` fix this? Compare with your LTL specs from Part 2 — which CTL formulas correspond to which LTL formulas?

---

## Running nuXmv

### Batch mode (simplest)
```bash
nuXmv RailroadCrossing_Part1.smv
```

### Interactive mode
```bash
nuXmv -int
> read_model -i RailroadCrossing_Part1.smv
> go
> check_ctlspec
> check_ltlspec
> quit
```

Interactive mode lets you check CTL and LTL separately and inspect results incrementally.

### Installation
- Download from [https://nuxmv.fbk.eu/](https://nuxmv.fbk.eu/)
- Or use the Docker image: `docker run -v $(pwd):/work -w /work nuxmv/nuxmv model.smv`

---

## Deliverables

1. **Part 1:** Completed `RailroadCrossing_Part1.smv` with gate transitions and defines
2. **Part 2:** Completed `RailroadCrossing_Part2.smv` with LTL specifications
3. **Part 3:** Completed `RailroadCrossing_Part3.smv` with CTL specifications and fairness
4. **Short writeup** (1/2–1 page): For each part, describe what you observed when running nuXmv. In particular:
   - Does the safety property hold? If not during development, what was the counterexample?
   - Which LTL properties pass and why?
   - Which CTL properties fail without fairness? What changes with fairness?
   - Compare one LTL property with its CTL equivalent — are they checking the same thing?

---

## Tips

- Read counterexample traces carefully — they show the exact sequence of states that violates a property
- Start by tracing the model on paper: write out 6–8 states of the train/gate lifecycle to build intuition
- If a property fails unexpectedly, check whether the issue is a modeling bug or a missing fairness constraint
- Compare with the lecture mutex example: `G mutex` ↔ `G safe`, `AG mutex` ↔ `AG safe`, fairness on `turn` ↔ fairness on the train
- The nuXmv documentation is at [https://nuxmv.fbk.eu/](https://nuxmv.fbk.eu/)
