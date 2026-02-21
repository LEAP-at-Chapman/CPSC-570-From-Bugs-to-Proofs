------------------------------ MODULE CTraffic ------------------------------

NextColor(c) == CASE c = "red" -> "green"
                  [] c = "green" -> "red"
                     
(**--algorithm traffic

variables
    at_light = TRUE;
    light = "red";
    
fair process light = "light"
begin
    Cycle:
      while at_light do
        light := NextColor(light);  
    end while;
end process;

fair+ process car = "car"
begin
    Drive:
    when light = "green";
    at_light := FALSE;
end process;

end algorithm;*)                     
\* BEGIN TRANSLATION (chksum(pcal) = "10e15a9a" /\ chksum(tla) = "626ff956")
\* Process light at line 12 col 6 changed to light_
VARIABLES at_light, light, pc

vars == << at_light, light, pc >>

ProcSet == {"light"} \cup {"car"}

Init == (* Global variables *)
        /\ at_light = TRUE
        /\ light = "red"
        /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Cycle"
                                        [] self = "car" -> "Drive"]

Cycle == /\ pc["light"] = "Cycle"
         /\ IF at_light
               THEN /\ light' = NextColor(light)
                    /\ pc' = [pc EXCEPT !["light"] = "Cycle"]
               ELSE /\ pc' = [pc EXCEPT !["light"] = "Done"]
                    /\ light' = light
         /\ UNCHANGED at_light

light_ == Cycle

Drive == /\ pc["car"] = "Drive"
         /\ light = "green"
         /\ at_light' = FALSE
         /\ pc' = [pc EXCEPT !["car"] = "Done"]
         /\ light' = light

car == Drive

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == light_ \/ car
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(light_)
        /\ SF_vars(car)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Feb 16 18:35:24 PST 2026 by jon
\* Created Mon Feb 16 18:23:20 PST 2026 by jon
