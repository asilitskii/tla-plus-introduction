----------------------------- MODULE stack -----------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
CONSTANT StackType
VARIABLE stack

Push(value) == stack' = Append(stack, value)

Pop == stack' = SubSeq(stack, 1, Len(stack) - 1) 

Next == \/ Pop
        \/ \E x \in StackType:
           Push(x)
Spec == [][Next]_stack

=============================================================================
\* Modification History
\* Last modified Sun Aug 06 20:12:58 NOVT 2023 by andrey
\* Created Sun Aug 06 16:21:18 NOVT 2023 by andrey
