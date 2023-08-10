----------------------------- MODULE stack_test -----------------------------
VARIABLE seq

Stack == INSTANCE stack WITH stack <- seq, StackType <- {1, 2}

Init == seq = <<>>

Next == \/ /\ seq = <<>>
           /\ Stack!Push(2)
        \/ /\ seq # <<>>
           /\ Stack!Pop

Spec == Init /\ [][Next]_seq

Refinement == Stack!Spec

=============================================================================
\* Modification History
\* Last modified Sun Aug 06 20:31:36 NOVT 2023 by andrey
\* Created Sun Aug 06 16:26:04 NOVT 2023 by andrey
