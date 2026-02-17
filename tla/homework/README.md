# Homework: Two-Phase Commit in PlusCal / TLA+

## Overview

In this homework you will model **Two-Phase Commit (2PC)** — a fundamental protocol for distributed transactions — and use the TLC model checker to verify its properties.

2PC is used in real systems like PostgreSQL, MySQL, and MongoDB to ensure that a group of participants either **all commit** or **all abort** a transaction. This atomicity guarantee is safety-critical: a violation could mean one bank debits money while another fails to credit it.

You will build the model incrementally across three parts:

| Part | Topic | You will learn | File |
|------|-------|----------------|------|
| 1 | **Concurrency** | Process interleaving, nondeterminism | [TwoPhaseCommit_Part1.tla](TwoPhaseCommit_Part1.tla) |
| 2 | **Liveness** | Fairness conditions, termination | [TwoPhaseCommit_Part2.tla](TwoPhaseCommit_Part2.tla) |
| 3 | **Safety** | Invariants, atomicity | [TwoPhaseCommit_Part3.tla](TwoPhaseCommit_Part3.tla) |

Each part builds on the previous one. Complete them in order.

---

## The Protocol

Two-Phase Commit coordinates a **coordinator** and **N participants**:

```
        Coordinator                    Participants
        ───────────                    ────────────
  Phase 1:  Send PREPARE ──────────────>  Receive PREPARE
            Wait for votes  <──────────  Vote YES or NO

  Phase 2:  If all YES:    ──── COMMIT ──>  Commit
            If any NO:     ──── ABORT ───>  Abort
            Wait for acks  <──────────────  Acknowledge
```

The key guarantee: **all participants reach the same outcome**.

---

## Part 1: Concurrency — [TwoPhaseCommit_Part1.tla](TwoPhaseCommit_Part1.tla)

**Goal:** Model the coordinator and participants as concurrent PlusCal processes.

The template provides:
- Variable declarations (`coordPhase`, `partPhase`, `partVote`)
- Helper predicates (`AllVoted`, `AllYes`, `AllDecided`)
- Process skeletons with `skip` placeholders

**Your task:** Replace each `skip` with the correct PlusCal statements. Key constructs:

- **`when <condition>`** — blocks until the condition is true
- **`with v \in S do ... end with`** — nondeterministic choice from set S
- **`either ... or ... end either`** — nondeterministic branching

After completing the PlusCal, translate it (Ctrl+T in VSCode with the TLA+ extension, or "Translate PlusCal Algorithm" in the Toolbox) and run TLC to explore the state space.

**What to observe:** With `NumParticipants = 3`, how many distinct states does TLC find? What happens when participants vote in different orders?

---

## Part 2: Liveness — [TwoPhaseCommit_Part2.tla](TwoPhaseCommit_Part2.tla)

**Goal:** Add fairness so that the protocol is guaranteed to terminate.

Without fairness, TLA+'s specification allows behaviors where a process is forever stuck — even when it *could* act. For example, a participant might never vote, leaving the coordinator waiting forever. This is not a bug in the protocol; it is the absence of a progress assumption.

**Your task:** Fill in:
- `CoordinatorActions` / `ParticipantActions(self)` — group the actions
- `LSpec` — extend Part 1's `Spec` with `WF_vars(...)` for each group
- `LTermination` — `<>(all processes done)`

Run TLC with `LSpec` as the specification and `LTermination` as a property to check.

**What to observe:** Does `LTermination` hold under `Spec` (without fairness)? Under `LSpec` (with fairness)?

---

## Part 3: Safety — [TwoPhaseCommit_Part3.tla](TwoPhaseCommit_Part3.tla)

**Goal:** Express and verify the atomicity guarantee of 2PC.

Safety says "something bad never happens." The core safety property of 2PC is:

> **No participant is in state "committed" while another is in state "aborted."**

**Your task:** Fill in:
- `TypeInvariant` — variables stay in valid domains
- `Atomicity` — no split commit/abort outcome
- `CoordinatorParticipantsAgree` — coordinator decision matches participant states

Run TLC with `LSpec` as the specification and `Invariants` as an invariant.

**What to observe:** Do all invariants hold? Try deliberately introducing a bug (e.g., let a participant commit without checking the coordinator's decision) and see what counterexample TLC produces.

---

## Running TLC

### In the TLA+ Toolbox
1. File > Open Spec, root module = `TwoPhaseCommit_Part3.tla`
2. Create a new model
3. Set constant: `NumParticipants = 3`
4. Behavior spec: `LSpec`
5. Invariants: `Invariants`
6. Properties: `LTermination`
7. Run

### In VSCode (TLA+ extension)
1. Open `TwoPhaseCommit_Part3.tla`
2. Create a `.cfg` file or use the TLC command palette
3. Set `NumParticipants` to 3

### Command line
```bash
java -jar tla2tools.jar -config MyConfig.cfg TwoPhaseCommit_Part3
```

---

## Deliverables

1. **Part 1:** Completed `TwoPhaseCommit_Part1.tla` with translated PlusCal
2. **Part 2:** Completed `TwoPhaseCommit_Part2.tla` with fairness and termination
3. **Part 3:** Completed `TwoPhaseCommit_Part3.tla` with invariants
4. **Short writeup** (1/2-1 page): For each part, describe what you observed when running TLC. In particular:
   - How many states did TLC explore?
   - What happens without fairness?
   - What counterexample does TLC produce if you break atomicity?

---

## Tips

- Start with `NumParticipants = 2` for a smaller state space while developing
- Increase to 3 once your model works — observe how the state space grows
- Read TLC's output carefully: counterexample traces show you the exact interleaving that violates a property
- The PlusCal reference is at [https://lamport.azurewebsites.net/tla/p-manual.pdf](https://lamport.azurewebsites.net/tla/p-manual.pdf)
