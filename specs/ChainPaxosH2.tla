---------------------------- MODULE ChainPaxosH2 ----------------------------

EXTENDS ChainPaxos
LOCAL INSTANCE ChainPaxosDefs

VARIABLE w, r

CPTypeOKH == /\ CPTypeOK
             /\ w \in Seq(DOMAIN ops)
             /\ DOMAIN r \subseteq DOMAIN ops
             /\ \A i \in DOMAIN r :
                r[i] <= Len(w)

CPInitH == /\ CPInit
           /\ w = << >>
           /\ r = << >>

RecvAcceptH(s) ==
    /\ RecvAccept(s)
    /\ LET m == Head(buf[s])
           nAcpt == IF m.ni \in DOMAIN log[s] /\ ~isNpGreaterThan(m.na,log[s][m.ni].na)
                    THEN MAX({m.nAcpt+1, log[s][m.ni].nAcpt})
                    ELSE m.nAcpt+1 
           decided == IsQuorum(nAcpt, Len(chain[s]))
        
       IN /\ IF /\ decided
                /\ m.val \in Val
                \* /\ ops[m.id].status = "Pending"
                /\ ~\E i \in DOMAIN w: w[i] = m.id
             THEN w' = Append(w, m.id)
             ELSE UNCHANGED w
    /\ UNCHANGED r
    
ClientSendReadH ==
    /\ ClientSendRead
    /\ r' = r @@ (Len(ops) + 1 :> Len(w))
    /\ UNCHANGED w

UC == UNCHANGED <<w, r>>
    
CPNextH ==
    \* Client actions
    \/ \E v \in Val : ClientSendWrite(v) /\ UC
    \/ ClientSendReadH
    \/ \E m \in msgs : ClientRecvWrite(m) /\ UC
    \/ \E m \in msgs : ClientRecvRead(m) /\ UC
  
    \* Server actions
    \/ \E s \in Server : LeaderSendNoOP(s) /\ UC
    \/ \E s \in Server : LeaderRecvAcceptAck(s) /\ UC
    \/ \E s \in Server : RecvAcceptH(s)
    \/ \E s \in Server : \E m \in msgs : LeaderRecvWrite(s, m) /\ UC
    \/ \E s \in Server : \E m \in msgs : RecvRead(s, m) /\ UC
    
    \* FT actions
    \/ \E s \in Server : SuspectNextNode(s) /\ UC
    \/ \E s \in Server : AddNewNode(s) /\ UC
    \/ \E s \in Server : \E m \in msgs : RecvStateTransfer(s, m) /\ UC
    \/ \E s \in Server : Fail(s) /\ UC

    \/ \E s \in Server : TryToBecomeLeader(s) /\ UC
    \/ \E s \in Server : \E m \in msgs : RecvPrepare(s, m) /\ UC
    \/ \E s \in Server : \E m \in msgs : RecvPrepareOk(s, m) /\ UC
        
        
CPSpecH == CPInitH /\ [][CPNextH]_<<CPvars, w, r>>

-----------------------------------------------------------------------------

CaughtUpReads ==
    \A i \in DOMAIN ops :
        (ops[i].type = "Read" /\ ops[i].status = "Done") =>
            \/ r[i] = 0 /\ ops[i].val = Nil
            \/ (\E j \in Max({r[i], 1})..Len(w) : ops[i].val = ops[w[j]].val)

=============================================================================
\* Modification History
\* Last modified Wed Sep 17 16:03:57 IST 2025 by Kotikala Raghav
\* Last modified Wed Sep 03 16:25:12 IST 2025 by jay
\* Created Thu Aug 14 12:25:37 IST 2025 by Kotikala Raghav