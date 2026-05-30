# Timed model checking with UPPAAL

```
**Chapter roles (Spring 2026)**
Author: Ethan Tapia · Reviewer: Jake Triester
See [Chapter assignments](0-chapter-assignments.md).
```

This chapter introduces UPPAAL for modeling timed automata and verifying timed temporal properties. By the end, you should be able to read a UPPAAL `.xml` model, understand what clocks and guards mean operationally, and write queries that distinguish properties that hold from properties that *almost* hold but break under a specific timing.

## Goals

- Explain timed automata networks and clock constraints in practical terms.
- Walk through a small model (the train-gate from class) and write a reachability and a time-bounded property against it.
- Show how a property can be repaired by tightening it with a clock constraint.
- Point to the UPPAAL GUI documentation and case-study repositories.

## From untimed to timed model checking

Earlier chapters covered tools like nuXmv where time is *abstract* — transitions happen one after another with no notion of "how long." That's enough to reason about ordering ("eventually `q`," "always `p`," "`p` until `q`"), but not enough to reason about deadlines. If you want to ask "can the gate close within 5 seconds of a train approaching?" you need clocks.

UPPAAL adds real-valued clocks to finite-state automata, giving you **timed automata**. A clock is a variable that increases continuously at rate 1 while time passes in a location, and can be reset to 0 on a transition. Guards on edges and invariants on locations are constraints over these clocks (`x >= 10`, `x < 20`, etc.). The semantics are simple in spirit:

- Time passes only in locations whose invariant still holds.
- An edge can fire only when its guard is true.
- Firing an edge can reset clocks and update integer variables.

A **network of timed automata** is just several of these running in parallel, synchronizing on channels (think Promela/CSP-style `chan!` / `chan?` handshakes). UPPAAL adds some practical extras on top: integer variables, broadcast channels, urgent and committed locations, and arrays — all of which you'll see in the example below.

The property language is a subset of **Timed Computation Tree Logic (TCTL)**, written in a compact ASCII syntax. TCTL is an extension of CTL — the branching-time logic with path quantifiers `A` and `E` introduced in the [previous chapter on model checking with nuXmv](TODO-link-to-CTL-section) — augmented with the ability to write clock constraints inside formulas. So the path quantifiers and modalities are the ones you've already seen; what's new is that the atomic propositions can now be things like `x >= 10` where `x` is a real-valued clock.

UPPAAL's verifier accepts the following operators:

- `A[] P` — invariantly P on all paths (safety / AG)
- `E<> P` — P is reachable (EF)
- `A<> P` — P holds eventually on every path (AF)
- `E[] P` — there exists a path where P holds always (EG)
- `P --> Q` — leads-to: every state satisfying P is eventually followed by Q

Clocks and integer variables can appear directly inside `P` and `Q`, which is the whole point — it's what makes the logic *timed*.

## A worked example: the train-gate model

The running example for the homework assignment is a classic: several trains approach a gate that can only admit one train at a time. Each train has its own clock `x`. The gate maintains a FIFO queue of trains waiting to cross.

The skeleton of each train is four locations:

- `Safe` — not near the gate
- `Appr` — approaching (synchronizes `appr[id]!` with the gate, resets `x`)
- `Stop` — has been told to wait (entered if the gate is occupied)
- `Cross` — crossing (synchronizes `leave[id]!` when done)

![Figure 1: The Train template in the UPPAAL editor, showing the four locations and the guards and synchronizations on each edge.](figures/uppaal-train-template.png)

The interesting timing constraints:

- A train in `Appr` can take the `Appr → Cross` edge only when `x >= 10` (it needs time to actually arrive).
- A train that's been stopped and then released can go `Start → Cross` only when `x >= 7`.
- The gate can fire `stop[id]?` only while `x <= 10` — i.e. you can only stop a train *before* it would have crossed on its own.

That last constraint is the load-bearing one, and it makes the model interesting to query.

### Writing a property that holds

The first property is a **queue invariant** — by which I mean a safety property that constrains the relationship between the gate's queue state and the locations of the trains. The whole protocol revolves around the queue, so it's a natural place to look for invariants that should hold across every reachable state.

```
A[] forall (i : id_t) Train(i).Cross imply Gate.len >= 1
```

In English: whenever any train is in `Cross`, the gate's queue contains at least one entry. This is satisfied, and the reason traces back to the protocol. A train can only reach `Cross` through one of two paths:

1. `Appr → Cross` directly — but this requires the gate to have handled the train's `appr[id]?`, which is the same transition that enqueues it (`Free → Occ` with `enqueue(e)`).
2. `Start → Cross` after being released — which requires the gate to have sent `go[front()]!`, and `front()` only exists if the train was enqueued.

Either way, *enqueuing happens before crossing.* Dequeuing only happens when the gate observes `leave[front()]?`, which fires on the train's `Cross → Safe` transition — so the train is already out of `Cross` by the time it's removed. The window where a train is in `Cross` is strictly contained within the window where it's in the queue, so `Gate.len >= 1` is forced.

### Writing a property that *almost* holds

Now a property that looks reasonable but isn't:

```
A[] Train(0).Appr imply forall (i : id_t) (i == 0 or not Train(i).Cross)
```

In English: whenever Train(0) is approaching, no other train is crossing. UPPAAL finds a counterexample. The scenario is straightforward:

- Train(1) approaches first and enters its own `Appr` with the queue containing just itself.
- Train(1)'s clock advances past 10, so it transitions `Appr → Cross`.
- *Now* Train(0) calls `appr[0]!` and enters `Appr`.

At this moment, Train(1) is in `Cross` while Train(0) is in `Appr`. The property fails.

![Figure 2: The UPPAAL Verifier pane with the failing query selected, showing the red status indicator and the option to open the diagnostic trace in the Simulator.](figures/uppaal-verifier-fail.png)

### Repairing the property with a clock constraint

The fix is to tighten the property using Train(0)'s own clock:

```
A[] (Train(0).Appr and Train(0).x > 10) imply forall (i : id_t) (i == 0 or not Train(i).Cross)
```

This *does* hold. The reasoning is worth walking through carefully because it's the kind of argument that makes timed model checking feel powerful.

The `stop[id]?` transition has the guard `x <= 10`. So once Train(0)'s clock exceeds 10, that transition is permanently disabled for Train(0). The only way Train(0) is still in `Appr` past `x = 10` is that no `stop` was ever sent to it. A `stop` is only sent when a train approaches while the gate is already occupied. If the gate never stopped Train(0), then when Train(0) called `appr[0]!` the gate was `Free` — meaning it took the `Free → Occ` transition with `len == 0` and just enqueued Train(0). At that moment, Train(0) is the only entry in the queue.

That's the key fact. If the queue was empty when Train(0) arrived, then no train was currently between "enqueued" and "dequeued," which means **no train was in `Cross` at that moment.** And since the FIFO ordering puts any later approaching train *behind* Train(0) in the queue, no later train can reach `Cross` until Train(0) has been dequeued — which requires Train(0) to have crossed and left, which hasn't happened yet (Train(0) is still in `Appr`).

So Train(0) being in `Appr` with `x > 10` carries a hidden guarantee about the gate's history: it was free when Train(0) arrived, the queue is now headed by Train(0), and no other train has crossed since. The property holds.

![Figure 3: The Verifier pane with the repaired query, showing the green "Property is satisfied" indicator.](figures/uppaal-verifier-pass.png)

## Further exploration: where this scales

The train-gate example is small, but the pattern generalizes. A few directions worth knowing about if you want to dig deeper:

**Statistical model checking (UPPAAL SMC).** When the state space is too big for exhaustive verification or the system is stochastic, UPPAAL SMC simulates runs and gives you probabilistic estimates of properties [2]. It has been applied to performance analysis of real-time scheduling, mixed criticality systems, sensor networks, energy-aware systems, and systems biology [3]. The query syntax extends naturally — `Pr[<=100](<> P)` asks for the probability that `P` becomes true within 100 time units.

**Strategy synthesis (UPPAAL Stratego).** Instead of just checking whether a property holds, you can ask UPPAAL to *synthesize a controller* that makes it hold. This is the realm of timed games — useful when part of the system is controllable (your code) and part is adversarial (the environment).

**Source-code bridges.** There's active research on connecting real source code to UPPAAL's engine — recent work develops a bridge between LLVM intermediate representation and the UPPAAL engine, which is one path toward applying timed model checking to actual implementations rather than only abstract models [4].

**Industrial case studies.** UPPAAL has been applied to real protocols: automotive systems verification using the FlexRay communication protocol [5], voting protocols such as Prêt à Voter [6], and contract-based middleware [7]. The patterns are similar to what you saw in the train-gate: identify the agents, give each one a clock, encode the handshake as channel synchronizations, and write the safety property as `A[]`.

## Getting started with UPPAAL

The official toolset is at [uppaal.org](https://uppaal.org/). The GUI has three panes you'll use constantly:

- **Editor** — drawing locations, edges, guards, and clock declarations.
- **Simulator** — stepping through executions by hand to sanity-check your model before verification.
- **Verifier** — running queries and inspecting counterexamples (which UPPAAL replays back into the simulator).

When a property fails, the verifier hands you a trace. Loading that trace into the simulator and stepping through it is, in my experience, the single most useful debugging move — much more useful than staring at the model and trying to reason about why your guards aren't tight enough.

The standard introduction is Behrmann, David, and Larsen's "A Tutorial on UPPAAL" [1], which works through the train-gate model and several others. The repository for this course ships the homework `train-gate-hw.xml` model and its three queries — building variations of those queries is a good way to develop intuition for when timing constraints buy you something and when they don't.

## Summary

The shift from untimed model checking to timed model checking is mostly a shift in what questions you can ask. The tools are similar in spirit — you write a model, you write a property, the checker either says "verified" or hands you a trace. What's new is that your properties can mention *when* things happen, not just *whether* and *in what order*. The train-gate example shows the smallest interesting version of this: two queries that look almost identical, one fails, the other holds, and the only difference is a clock constraint that encodes a hidden fact about the gate's history.

## References

[1] G. Behrmann, A. David, and K. G. Larsen. "A Tutorial on UPPAAL." In *Formal Methods for the Design of Real-Time Systems (SFM-RT 2004)*, LNCS vol. 3185, pp. 200–236. Springer, 2004. Available at <https://uppaal.org/texts/new-tutorial.pdf>.

[2] A. David, K. G. Larsen, A. Legay, M. Mikučionis, and D. B. Poulsen. "UPPAAL SMC Tutorial." *International Journal on Software Tools for Technology Transfer*, 17(4):397–415, 2015. Available at <https://uppaal.org/texts/uppaal-smc-tutorial.pdf>.

[3] A. David, K. G. Larsen, A. Legay, M. Mikučionis, and D. B. Poulsen. "UPPAAL-SMC: Statistical Model Checking for Priced Timed Automata." arXiv:1207.1272, 2012. <https://arxiv.org/abs/1207.1272>.

[4] M. Kulczynski, D. Nowotka, A. Legay, and D. B. Poulsen. "Analysis of Source Code Using UPPAAL." arXiv:2108.02963, 2021. <https://arxiv.org/abs/2108.02963>.

[5] X. Guo, H.-H. Lin, K. Yatake, and T. Aoki. "An UPPAAL Framework for Model Checking Automotive Systems with FlexRay Protocol." In *Formal Techniques for Safety-Critical Systems (FTSCS 2013)*, CCIS vol. 419, pp. 60–75. Springer, 2014.

[6] W. Jamroga, D. Kim, D. Mestel, P. Y. A. Ryan, S. Schneider, S. Srivatsa, M. Volkamer, and Z. Xia. "Model Checkers Are Cool: How to Model Check Voting Protocols in Uppaal." arXiv:2007.12412, 2020. <https://arxiv.org/abs/2007.12412>.

[7] D. Basile. "Formal Analysis of the Contract Automata Runtime Environment with Uppaal: Modelling, Verification and Testing." arXiv:2501.12932, 2025. <https://arxiv.org/abs/2501.12932>.

[8] UPPAAL official website and documentation. <https://uppaal.org/>.

[9] LEAP-at-Chapman. *CPSC 570: From Bugs to Proofs* — UPPAAL homework and `train-gate-hw.xml` model. <https://github.com/LEAP-at-Chapman/CPSC-570-From-Bugs-to-Proofs/tree/main/upaal>.
