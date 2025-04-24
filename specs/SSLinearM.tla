----------------------------- MODULE SSLinearM -----------------------------

EXTENDS SSLinear, FiniteSets

LInitM == LInit

ApplyMultipleReads ==
    \E s \in SUBSET {k : k \in 1..Len(ops)} :
        /\ Cardinality(s) >= 1
        /\ \A i \in s :
            /\ ops[i].type = "Read"
            /\ ops[i].status = "Pending"
            /\ ~\E j \in 1..Len(h) : h[j] = i 
        /\ \E seq \in {sq \in [1..Cardinality(s) -> s] :
            /\ \A x,y \in 1..Cardinality(s): sq[x] = sq[y] => x = y} :
            /\ h' = h \o seq
        /\ UNCHANGED ops

ApplyMultipleReadsWithWrite ==
    \E s \in SUBSET {k : k \in 1..Len(ops)} :
        /\ Cardinality(s) >= 1
        /\ \A i \in s :
            /\ ops[i].type = "Read"
            /\ ops[i].status = "Pending"
            /\ ~\E j \in 1..Len(h) : h[j] = i
        /\ \E w \in 1..Len(ops) :
            /\ ops[w].type = "Write"
            /\ ops[w].status = "Pending"
            /\ ~\E j \in 1..Len(h) : h[j] = w     
            /\ \E seq \in {sq \in [1..Cardinality(s)+1 -> s \union {w}] :
                /\ \A x,y \in 1..Cardinality(s)+1: sq[x] = sq[y] => x = y} :
                /\ h' = h \o seq
            /\ UNCHANGED ops


LNextM == \/ LNext
          \/ ApplyMultipleReads
          \/ ApplyMultipleReadsWithWrite

LSpecM == LInitM /\ [][LNextM]_<<ops, h>>

=============================================================================
\* Modification History
\* Last modified Tue Apr 08 18:13:24 IST 2025 by Kotikala Raghav
\* Created Thu Apr 03 11:37:53 IST 2025 by Kotikala Raghav
