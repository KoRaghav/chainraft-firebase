----------------------------- MODULE ChainPaxosNoAnim -----------------------

EXTENDS ChainPaxos

Init == CPInit
vars == CPvars
Next ==
    \* Client actions
    \/ \E v \in Val : ClientSendWrite(v)
    \/ ClientSendRead
    \/ \E m \in msgs : ClientRecvWrite(m)
    \/ \E m \in msgs : ClientRecvRead(m)
  
    \* Server actions
    \/ \E s \in Server : LeaderSendNoOP(s)
    \/ \E s \in Server : LeaderRecvAcceptAck(s)
    \/ \E s \in Server : RecvAccept(s)
    \/ \E s \in Server : \E m \in msgs : LeaderRecvWrite(s, m)
    \/ \E s \in Server : \E m \in msgs : RecvRead(s, m)
    
    \* FT actions
    \/ \E s \in Server : SuspectNextNode(s)
    \/ \E s \in Server : AddNewNode(s)
    \/ \E s \in Server : \E m \in msgs : RecvStateTransfer(s, m)
    \/ \E s \in Server : Fail(s)
    
    \/ \E s \in Server : TryToBecomeLeader(s)
    \/ \E s \in Server : \E m \in msgs : RecvPrepare(s, m)
    \/ \E s \in Server : \E m \in msgs : RecvPrepareOk(s, m)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Tue May 06 13:25:47 IST 2025 by Kotikala Raghav
\* Last modified Wed Apr 23 22:54:06 IST 2025 by jay
\* Created Wed Mar 26 18:10:34 IST 2025 by Kotikala Raghav