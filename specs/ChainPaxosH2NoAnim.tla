----------------------------- MODULE ChainPaxosH2NoAnim -----------------------

EXTENDS ChainPaxosH2

Init == CPInitH
vars == CPvars
Next ==
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

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Tue May 06 13:25:47 IST 2025 by Kotikala Raghav
\* Last modified Wed Apr 23 22:54:06 IST 2025 by jay
\* Created Wed Mar 26 18:10:34 IST 2025 by Kotikala Raghav