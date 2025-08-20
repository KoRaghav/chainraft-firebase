---------------------------- MODULE ChainPaxosP2 ----------------------------

EXTENDS ChainPaxos

VARIABLE curVal, returnVal

CPInitP == CPInit /\ curVal = Nil /\ returnVal = << >>

CPTypeOKP == /\ CPTypeOK
             /\ curVal \in Val \union {Nil}
             /\ \A i \in DOMAIN returnVal :
                /\ i \in DOMAIN ops
                /\ returnVal[i] \in Val \union {Nil}

RecvAcceptP(s) ==
    /\ buf[s] # << >>
    /\ LET m == Head(buf[s])
       IN /\ m.type = "Accept"
          /\ IF /\ IsQuorum(m.nAcpt + 1, Len(chain[s]))
                /\ ~IsQuorum(m.nAcpt, Len(chain[s]))
                /\  m.val \in Val
                /\ ops[m.id].status = "Pending"
             THEN curVal' = m.val
             ELSE UNCHANGED curVal
    /\ RecvAccept(s)
    /\ UNCHANGED returnVal

CommitRead(i) ==
    /\ ops[i].type = "Read"
    /\ ops[i].status = "Pending"
    /\ i \notin DOMAIN returnVal
    /\ ops' = [ops EXCEPT ![i] = [type |-> "Read", status |-> "Committed", val |-> curVal]]
    /\ returnVal' = returnVal @@ (i :> curVal)
    /\ UNCHANGED <<msgs, orgVars, logVars, leaderVars, buf, readQueue, state, hisVars, curVal>>


\* Allow client receiving a read only if it was correctly predicted
ClientRecvReadP(m) ==
    /\ m.type = "ReadResponse"
    /\ ops[m.id].status = "Committed"
    /\ m.id \in DOMAIN returnVal
    /\ returnVal[m.id]  = m.val
    /\ ClientRecvRead(m)
    /\ UNCHANGED <<curVal, returnVal>>

CPNextP ==
    \* Client actions
    \/ \E v \in Val : ClientSendWrite(v) /\ UNCHANGED <<curVal, returnVal>>
    \/ ClientSendRead /\ UNCHANGED <<curVal, returnVal>>
    \/ \E m \in msgs : ClientRecvWrite(m) /\ UNCHANGED <<curVal, returnVal>>
    \/ \E m \in msgs : ClientRecvReadP(m)

    \* Server actions
    \/ \E s \in Server : LeaderRecvAcceptAck(s) /\ UNCHANGED <<curVal, returnVal>>
    \/ \E s \in Server : RecvAcceptP(s)
    \/ \E s \in Server : \E m \in msgs : LeaderRecvWrite(s, m) /\ UNCHANGED <<curVal, returnVal>>
    \/ \E s \in Server : \E m \in msgs : RecvRead(s, m) /\ UNCHANGED <<curVal, returnVal>>

    \* FT actions
    \/ \E s \in Server : SuspectNextNode(s) /\ UNCHANGED <<curVal, returnVal>>
    \/ \E s \in Server: AddNewNode(s) /\ UNCHANGED <<curVal, returnVal>>
    \/ \E s \in Server : \E m \in msgs : RecvStateTransfer(s, m) /\ UNCHANGED <<curVal, returnVal>>
    \* \/ \E s \in Server : Restart(s) /\ UNCHANGED <<curVal, returnVal>>
    
    \/ \E i \in DOMAIN ops : CommitRead(i)

CPvarsP == <<CPvars, curVal, returnVal>>
        
CPSpecP == CPInitP /\ [][CPNextP]_CPvarsP

INSTANCE SSLinear

\* THEOREM CPSpecP => LSpec

=============================================================================
\* Modification History
\* Last modified Wed Aug 20 16:42:25 IST 2025 by jay
\* Last modified Sun Aug 17 16:22:50 IST 2025 by Kotikala Raghav
\* Created Thu Aug 14 17:55:56 IST 2025 by Kotikala Raghav