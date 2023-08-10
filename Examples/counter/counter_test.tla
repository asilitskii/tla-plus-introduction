-------------------------------- MODULE counter_test --------------------------------
EXTENDS Integers, TLC

VARIABLE x

Add(v) == v' = v + 1

Init == x = 4

Next == Add(x)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

LessThan10Invariant == x < 10
Liveness == <>(x = 2)
=============================================================================
\* Modification History
\* Last modified Sat Aug 05 16:01:32 NOVT 2023 by andrey
\* Created Fri Aug 04 00:19:30 NOVT 2023 by andrey
