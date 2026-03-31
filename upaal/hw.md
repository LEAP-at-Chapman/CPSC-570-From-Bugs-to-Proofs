# UPPAAL Homework 1: The Train-Gate Model

## Overview

This assignment uses the **train-gate** model, a classic example of a real-time system modeled in UPPAAL. The system consists of 6 trains sharing a single-track bridge, controlled by a gate with a FIFO queue.

Open `train-gate-hw.xml` in UPPAAL. Familiarize yourself with the two templates:

- **Train**: Each train cycles through locations Safe, Appr (approaching), Cross (crossing the bridge), and potentially Stop and Start (if the gate holds it). Each train has a local clock `x` that is reset at various transitions. Note the invariants and guards on each location and transition.

- **Gate**: Manages access to the bridge using a queue. It has two main states: Free (no train crossing) and Occ (bridge occupied). When a train approaches and the gate is occupied, the train is enqueued and told to stop. When the crossing train leaves, the gate signals the next train in the queue.

The file includes several pre-verified example properties for reference. Your task is to write three new properties in the `===== HW` section at the bottom of the query list.

## Questions

### Q1: Queue Invariant (CTL)

Write a safety property (using `A[]`) that expresses: **whenever any train is crossing the bridge, the gate's queue contains at least one entry** (i.e., `Gate.len >= 1`).

Verify it. Briefly explain why this property holds by describing when trains are enqueued and dequeued in the gate protocol.

### Q2: Approaching Implies No One Crossing? (TCTL — expected to fail)

Write a safety property that expresses: **whenever Train(0) is in the Appr location, no other train is in Cross**.

Verify it. It should **not** be satisfied. Describe a scenario (a sequence of events) that produces a counterexample. Which trains are in which locations, and why does the gate protocol allow this?

### Q3: Adding a Clock Constraint (TCTL — fix Q2)

Modify your Q2 property by adding the constraint `Train(0).x > 10` to the left-hand side. That is: **whenever Train(0) is in Appr _and_ its clock x exceeds 10, no other train is in Cross**.

Verify it. It should now be **satisfied**. Explain:

1. What does `Train(0).x > 10` tell you about Train(0)'s history? Look at the guard on the Appr-to-Stop transition.
2. What does that imply about the state of the gate when Train(0) first approached?
3. Why does this guarantee no other train can be crossing?

## Submission

Submit your completed `.xml` file and a short write-up (PDF or text) with your explanations for each question.
