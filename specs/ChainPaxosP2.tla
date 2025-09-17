---------------------------- MODULE ChainPaxosP2 ----------------------------

EXTENDS ChainPaxos

VARIABLE curVal

LOCAL MAX(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : y <= x

CPInitP == CPInit /\ curVal = Nil

CPTypeOKP == /\ CPTypeOK
             /\ curVal \in Val \union {Nil}

RecvAcceptP(s) ==
    /\ buf[s] # << >>
    /\ LET m == Head(buf[s])
           nAcpt == IF m.ni \in DOMAIN log[s] /\ log[s][m.ni].na >=  m.na
                    THEN MAX({m.nAcpt+1, log[s][m.ni].nAcpt})
                    ELSE m.nAcpt+1
       IN /\ m.type = "Accept"
          /\ IF /\ IsQuorum(nAcpt, Len(chain[s]))
                /\ m.val \in Val
                /\ ops[m.id].status = "Pending"
             THEN curVal' = m.val
             ELSE UNCHANGED curVal
    /\ RecvAccept(s)

CommitRead(i) ==
    /\ ops[i].type = "Read"
    /\ ops[i].status = "Pending"
    /\ ops' = [ops EXCEPT ![i] = [type |-> "Read", status |-> "Committed", val |-> curVal]]
    /\ UNCHANGED <<msgs, serverVars, hisVars, curVal>>


\* Allow client receiving a read only if it was correctly predicted
ClientRecvReadP(m) ==
    /\ m.type = "ReadResponse"
    /\ ops[m.id].status = "Committed"
    /\ ops[m.id].val = m.val
    /\ ClientRecvRead(m)
    /\ UNCHANGED curVal

CPNextP ==
    \* Client actions
    \/ \E v \in Val : ClientSendWrite(v) /\ UNCHANGED curVal
    \/ ClientSendRead /\ UNCHANGED curVal
    \/ \E m \in msgs : ClientRecvWrite(m) /\ UNCHANGED curVal
    \/ \E m \in msgs : ClientRecvReadP(m)

    \* Server actions
    \/ \E s \in Server : LeaderSendNoOP(s) /\ UNCHANGED curVal
    \/ \E s \in Server : LeaderRecvAcceptAck(s) /\ UNCHANGED curVal
    \/ \E s \in Server : RecvAcceptP(s)
    \/ \E s \in Server : \E m \in msgs : LeaderRecvWrite(s, m) /\ UNCHANGED curVal
    \/ \E s \in Server : \E m \in msgs : RecvRead(s, m) /\ UNCHANGED curVal

    \* FT actions
    \/ \E s \in Server : SuspectNextNode(s) /\ UNCHANGED curVal
    \/ \E s \in Server: AddNewNode(s) /\ UNCHANGED curVal
    \/ \E s \in Server : \E m \in msgs : RecvStateTransfer(s, m) /\ UNCHANGED curVal
    \/ \E s \in Server : Restart(s) /\ UNCHANGED curVal
    
    \/ \E i \in DOMAIN ops : CommitRead(i)

CPvarsP == <<CPvars, curVal>>
        
CPSpecP == CPInitP /\ [][CPNextP]_CPvarsP

INSTANCE SSLinear

THEOREM CPSpecP => LSpec

=============================================================================
\* Modification History
\* Last modified Thu Aug 21 19:05:39 IST 2025 by jay
\* Last modified Thu Aug 21 17:25:38 IST 2025 by Kotikala Raghav
\* Created Thu Aug 14 17:55:56 IST 2025 by Kotikala Raghav