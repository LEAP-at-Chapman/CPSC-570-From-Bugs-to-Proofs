------------------------------- MODULE DClock -------------------------------
EXTENDS Naturals
VARIABLES hr

HCInit == hr \in {1 .. 12}
HCNext == (hr' = IF hr # 12 THEN hr + 1 ELSE 1)

Spec == HCInit /\ [][HCNext]_hr
=============================================================================
\* Modification History
\* Last modified Wed Feb 04 18:26:24 PST 2026 by jon
\* Created Wed Feb 04 17:28:04 PST 2026 by jon
