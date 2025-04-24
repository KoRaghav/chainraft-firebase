------------------------------ MODULE SSLinear ------------------------------
(* Single Server Linear Spec *)

EXTENDS Naturals, Sequences

CONSTANT Nil, Val

VARIABLE ops,   \* Stores externally visible operations
         h    \* Stores the sequence of operations applied on the object
         
LOCAL Operation ==
    [type : {"Read"}, status : {"Pending"}] \union
    [type : {"Read"}, status : {"Done"}, val: Val \union {Nil}] \union
    [type : {"Write"}, status : {"Pending", "Done"}, val: Val \union {Nil}]         
         
LTypeOK ==
    /\ ops \in Seq(Operation)
    /\ h \in Seq(Nat)

LInit ==
    /\ ops = << >>
    /\ h = << >>


LOCAL Min(S) == CHOOSE x \in S : \A y \in S : x <= y
LOCAL Max(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : y <= x

-----------------------------------------------------------------------------

\* Return the value applied by the last Write before index i
GetObjValBefore(i) ==
    LET appliedWrites == {j \in 1..i : ops[h[j]].type = "Write"}
    IN IF appliedWrites = {} THEN Nil
       ELSE ops[h[Max(appliedWrites)]].val

-----------------------------------------------------------------------------

IssueRead ==
    /\ ops' = Append(ops, [type   |-> "Read",
                           status |-> "Pending"])
    /\ UNCHANGED h
    
IssueWrite ==
    \E v \in Val:
        /\ ops' = Append(ops, [type   |-> "Write",
                               val    |-> v,
                               status |-> "Pending"])
        /\ UNCHANGED h
        
ApplyRead ==
    \E i \in 1..Len(ops):
        /\ ops[i].type = "Read"
        /\ ops[i].status = "Pending"
        /\ ~\E j \in 1..Len(h) : h[j] = i
        /\ h' = Append(h, i)
        /\ UNCHANGED ops

ApplyWrite ==
    \E i \in 1..Len(ops):
        /\ ops[i].type = "Write"
        /\ ops[i].status = "Pending"
        /\ ~\E j \in 1..Len(h) : h[j] = i
        /\ h' = Append(h, i)
        /\ UNCHANGED ops

AckRead ==
    \E i \in 1..Len(ops):
        /\ ops[i].type = "Read"
        /\ ops[i].status = "Pending"
        /\ \E j \in 1..Len(h) :
            /\ h[j] = i
            /\ ops' = [ops EXCEPT ![i] = [type   |-> "Read",
                                          val    |-> GetObjValBefore(j),
                                          status |-> "Done"]]
        /\ UNCHANGED h

AckWrite ==
    \E i \in 1..Len(ops):
        /\ ops[i].type = "Write"
        /\ ops[i].status = "Pending"
        /\ \E j \in 1..Len(h) :
            /\ h[j] = i
            /\ ops' = [ops EXCEPT ![i].status = "Done"]
        /\ UNCHANGED h

LNext == \/ IssueRead
         \/ IssueWrite
         \/ ApplyRead
         \/ ApplyWrite
         \/ AckRead
         \/ AckWrite

LSpec == LInit /\ [][LNext]_<<ops, h>>
=============================================================================
\* Modification History
\* Last modified Mon Apr 21 17:27:11 IST 2025 by Kotikala Raghav
\* Created Thu Jan 09 19:31:07 IST 2025 by Kotikala Raghav
