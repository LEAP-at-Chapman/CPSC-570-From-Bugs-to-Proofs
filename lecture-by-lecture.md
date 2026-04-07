# Lecture by lecture



* L1.1: Introduction
* L1.2: [TLA+](https://lamport.azurewebsites.net/tla/tla.html)
* L2.1: [TLA+ toolbox](https://lamport.org/tla/toolbox.html) and examples ([clock](tla/DAsyncInterface.tla), [interface](tla/DClock.tla))
* L2.2: Introduction to concurrency and temporal paradigms using [PlusCal](https://docs.tlapl.us/learning:pluscal) and using the [TLC model checker](https://docs.tlapl.us/using:tlc:start) ([wire](tla/DWire.tla), [PlusCal traffic light](tla/CTraffic.tla))
* L3.1: Concurrency, safety, and liveness in TLA+ and PlusCal. Announce [HW1](tla/homework/README.md).
* L4.1: [Alloy](https://alloytools.org/): [tutorial](https://haslab.github.io/formal-software-design/overview/index.html), [docs](https://alloy.readthedocs.io/), [Alloy4Fun](http://alloy4fun.inesctec.pt/), [relational logic](https://haslab.github.io/formal-software-design/relational-logic/index.html)
* L4.2: More Alloy
  * Demos: [Trash](alloy/trash.als), [File structure](alloy/struct.als)
  * [Exercises](https://haslab.github.io/formal-software-design/structural-design/index.html#exercises) (containing HW 2)
* L5.2: Model checking I
  * Linear temporal logic (LTL) I: [Wikipedia](https://en.wikipedia.org/wiki/Linear_temporal_logic), [Lecture notes](CPSC-570%20Notes.pdf)
* L6.1: Model checking II
  * [LTL](https://hackmd.io/4Mhc2FywRF2mYqDprcJMAA?view), [Transition systems](https://hackmd.io/ZHM1i5WiSTyq1QHuv8UkKQ)
  * [nuXmv](https://nuxmv.fbk.eu/)
  * Demo: mutex ([model](nuxmv/mutex_v1_model.smv), [LTL](nuxmv/mutex_v2_ltl.smv))
  * HW 3: railroad crossing ([readme](nuxmv/homework/README.md))
* L6.2: Model Checking III
  * [CTL](https://hackmd.io/vaBO9pmiThSi89fTy3_4rw?view)
* L7.1: Model Checking IV
  * Semantics of [CTL](https://hackmd.io/vaBO9pmiThSi89fTy3_4rw?view#Semantics-of-CTL)
  * Part 3 from railroad crossing ([readme](nuxmv/homework/README.md))
* L7.2: Model Checking V
  * [CTL vs. LTL](https://hackmd.io/ut28s3cAQiiq3IYFqTjuXw?both)
  * Preview of timed model checking and [UPAAL](https://uppaal.org/) (see [Timed Automata](https://uppaal.org/texts/by-lncs04.pdf) and [UPAAL Tutorial](https://uppaal.org/texts/new-tutorial.pdf))
* L8.1: Model Checking VI
  * [UPAAL](https://uppaal.org/) (see [Timed Automata](https://uppaal.org/texts/by-lncs04.pdf) and [UPAAL Tutorial](https://uppaal.org/texts/new-tutorial.pdf))
  * [UPAAL: HW](upaal/hw.md)
* L9.1: [Dafny](https://dafny.org/), for tutorials see: [general](https://dafny.org/), [termination](https://dafny.org/latest/OnlineTutorial/Termination), [lemmas](https://dafny.org/latest/OnlineTutorial/Lemmas)
  * [Lecture tutorial](dafny/tutorial.dfy), [HW: Readme](dafny/homework/transactional-inventory/README.md), [HW: Code](dafny/homework/transactional-inventory/homework-transactions.dfy)


