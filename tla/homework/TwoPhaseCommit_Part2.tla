----------------------------- MODULE TwoPhaseCommit_Part2 -----------------------------
(*
  Part 2: Liveness
  
  HOMEWORK: Add fairness so that the protocol eventually terminates.
  
  BACKGROUND:
  - Without fairness, TLC allows behaviors where a process never takes a step,
    even when it could. For example, a participant might never vote.
  - Weak fairness WF_vars(A) means: if action A stays continuously enabled,
    it must eventually execute.
  - Strong fairness SF_vars(A) means: if action A is enabled infinitely often
    (even intermittently), it must eventually execute.
  
  YOUR TASK:
  1. Define CoordinatorActions and ParticipantActions(self) as the disjunction
     of the relevant actions from Part 1.
  
  2. Define LSpec that extends Part 1's Spec with fairness conditions:
     - Weak fairness on the coordinator actions
     - Weak fairness on each participant's actions
  
  3. Define LTermination as a temporal property asserting that
     all processes eventually reach pc = "Done".
  
  HINTS:
  - LSpec should be: Spec /\ WF_vars(...) /\ \A p \in Participants: WF_vars(...)
  - LTermination uses the <> (eventually) operator
  - Think about WHY weak fairness is sufficient here (vs strong fairness)
*)
EXTENDS TwoPhaseCommit_Part1

\* TODO: Define CoordinatorActions as the disjunction of coordinator actions
CoordinatorActions == FALSE  \* Replace FALSE

\* TODO: Define ParticipantActions(self) as the disjunction of participant actions
ParticipantActions(self) == FALSE  \* Replace FALSE

\* TODO: Define LSpec extending Part 1's Spec with weak fairness
\*       for the coordinator and for each participant
LSpec == Spec  \* Add fairness conjuncts

\* TODO: Define LTermination: eventually all processes are Done
LTermination == TRUE  \* Replace with temporal formula

=============================================================================
