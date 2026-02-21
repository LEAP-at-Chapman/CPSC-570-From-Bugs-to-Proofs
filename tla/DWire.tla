------------------------------- MODULE DWire -------------------------------

EXTENDS Integers

\* Wire transfer between two people: sender, receiver
\* wire > 0
\* success: deduct and add the money accordingly 
\* fail: accounts unchanged
\* condition: must not have negative balance
\* can make payments in parallel

(*--algorithm wire

variables
    people = {"alice", "bob"},
    acc = [ p \in people |->  5];

define
    NoOverdrafts == (\A p \in people : (acc[p] >= 0))
    EventuallyConsistent == <>[](acc["alice"] + acc["bob"] = 10)
end define;

process Wire \in 1..2
    variables
          sender = "alice",
          receiver = "bob",
            amount \in 1..acc[sender];
            
begin
    CheckAndWithdrawFunds:
        if amount <= acc[sender] then
            acc[sender] := acc[sender] - amount;
        Deposit:
            acc[receiver] := acc[receiver] + amount;
        end if;
end process;

end algorithm;    
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e8a60c23" /\ chksum(tla) = "3932022")
VARIABLES people, acc, pc

(* define statement *)
NoOverdrafts == (\A p \in people : (acc[p] >= 0))
EventuallyConsistent == <>[](acc["alice"] + acc["bob"] = 10)

VARIABLES sender, receiver, amount

vars == << people, acc, pc, sender, receiver, amount >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ acc = [ p \in people |->  5]
        (* Process Wire *)
        /\ sender = [self \in 1..2 |-> "alice"]
        /\ receiver = [self \in 1..2 |-> "bob"]
        /\ amount \in [1..2 -> 1..acc[sender[CHOOSE self \in  1..2 : TRUE]]]
        /\ pc = [self \in ProcSet |-> "CheckAndWithdrawFunds"]

CheckAndWithdrawFunds(self) == /\ pc[self] = "CheckAndWithdrawFunds"
                               /\ IF amount[self] <= acc[sender[self]]
                                     THEN /\ acc' = [acc EXCEPT ![sender[self]] = acc[sender[self]] - amount[self]]
                                          /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                          /\ acc' = acc
                               /\ UNCHANGED << people, sender, receiver, 
                                               amount >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ acc' = [acc EXCEPT ![receiver[self]] = acc[receiver[self]] + amount[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << people, sender, receiver, amount >>

Wire(self) == CheckAndWithdrawFunds(self) \/ Deposit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: Wire(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Mon Feb 16 18:16:06 PST 2026 by jon
\* Created Wed Feb 11 18:27:30 PST 2026 by jon
