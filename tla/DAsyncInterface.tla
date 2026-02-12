-------------------------- MODULE DAsyncInterface --------------------------

EXTENDS Naturals

CONSTANT Data

VARIABLES val, rdy, ack

TypeInvariant ==
    /\ (val \in Data)
    /\ (rdy \in {0,1})
    /\ (ack \in {0,1})
    
Init ==
    /\ (rdy \in {0,1})
    /\ (rdy = ack)
    /\ (val \in Data)
    
Send ==
    /\ rdy = ack      \* Precondition
    /\ (val' \in Data)  \* Postcondition
    /\ rdy' = 1 - rdy \* rdy' # rdy \* Postcondition
    /\ UNCHANGED ack \* Postcondition
    
Rcv ==
    /\ (rdy # ack) \* Precondition
    /\ (ack' = 1 - ack)    \* Postcondition
    /\ (UNCHANGED <<val, rdy>>)   \* Postcondition
    
 
Next == Send \/ Rcv

Spec == Init /\ [][Next]_<<val, rdy, ack>>

THEOREM Spec => []TypeInvariant

    




=============================================================================
\* Modification History
\* Last modified Mon Feb 09 18:18:24 PST 2026 by jon
\* Created Wed Feb 04 18:33:27 PST 2026 by jon
