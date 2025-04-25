---------------------------- MODULE ChainPaxosP ----------------------------

EXTENDS ChainPaxos

VARIABLE h, \* Stores linearized operations
         p  \* predicts the upcoming sequence of maxAcks in Accept messages

CPInitP == /\ CPInit
           /\ h = << >>
           /\ p = <<0>>

CPTypeOKP == /\ CPTypeOK 
             /\ h \in Seq(Nat)
             /\ \A i \in 1..Len(h) :
                  h[i] <= Len(ops)
             /\ p \in Seq(Nat)


LeaderRecvWriteP(s, m) ==
    /\ LeaderRecvWrite(s, m)
    /\ \/ /\ maxAck[s] = Head(p)
          /\ UNCHANGED p
       \/ /\ Len(p) >= 2
          /\ maxAck[s] = p[2]
          /\ p' = Tail(p)
    /\ UNCHANGED h

LeaderRecvAcceptAckP(s) ==
    /\ buf[s] # << >>
    /\ LET m == Head(buf[s])
       IN /\ m.type = "AcceptAck"
          /\ Len(p) >= 2 => m.ni <= p[2]
    /\ LeaderRecvAcceptAck(s)
    /\ UNCHANGED <<h, p>>

RecvAcceptP(s) ==
    /\ buf[s] # << >>
    /\ LET m == Head(buf[s])
       IN /\ m.type = "Accept"
          /\ IF IsQuorum(m.nAcpt + 1) /\ ~IsQuorum(m.nAcpt)
             THEN \E bool \in BOOLEAN :
                LET r == UNION { {id \in UNION {readQueue[srv][i] : i \in {k \in DOMAIN readQueue[srv] : k <= m.ni}} :
                                    ~\E j \in DOMAIN h : h[j] = id} :
                                    srv \in {s_ \in Server : s_ = 1}}
                        \union
                        UNION { {id \in UNION {readQueue[srv][j] : j \in {k \in DOMAIN readQueue[srv] : k <= m.mAck}} :
                                        ~\E j \in DOMAIN h : h[j] = id} :
                                    srv \in {s_ \in Server : s_ >= s}}
                        \union
                        IF bool
                        THEN UNION { {id \in UNION {readQueue[srv][j] : j \in {k \in DOMAIN readQueue[srv] : k <= m.ni}} :
                                        ~\E j \in DOMAIN h : h[j] = id} :
                                    srv \in {s_ \in Server : s_ < s /\ s_ # 1}}
                        ELSE {}
                        
                IN \E seq \in {sq \in [1..Cardinality(r) -> r] :
                    /\ \A x,y \in 1..Cardinality(r): sq[x] = sq[y] => x = y} :
                  /\ h' = Append(h, m.id) \o seq
                  /\ IF bool THEN p' = Append(p, m.ni) ELSE UNCHANGED p
             ELSE UNCHANGED <<h, p>>
    /\ RecvAccept(s)
    
CPNextP ==
    \/ \E v \in Val : ClientSendWrite(v) /\ UNCHANGED <<h, p>>
    \/ ClientSendRead /\ UNCHANGED <<h, p>>
    \/ \E s \in Server : LeaderRecvAcceptAckP(s)
    \/ \E s \in Server : RecvAcceptP(s)
    \/ \E s \in Server : \E m \in msgs : LeaderRecvWriteP(s, m)
    \/ \E s \in Server : \E m \in msgs : RecvRead(s, m) /\ UNCHANGED <<h, p>>
    \/ \E m \in msgs : ClientRecvWrite(m) /\ UNCHANGED <<h, p>>
    \/ \E m \in msgs : ClientRecvRead(m) /\ UNCHANGED <<h, p>>

CPvarsP == <<CPvars, h, p>>
        
CPSpecP == CPInitP /\ [][CPNextP]_CPvarsP

 INSTANCE SSLinearM

\* THEOREM CPSpecP => LSpecM

=============================================================================
\* Modification History
\* Last modified Fri Apr 25 08:51:46 IST 2025 by Kotikala Raghav
\* Created Mon Apr 14 12:07:02 IST 2025 by Kotikala Raghav
