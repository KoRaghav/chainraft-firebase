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

DecidedReads(s, mAck) ==
    LET r ==  {id \in UNION {readQueue[s][j] : 
                                    j \in {k \in DOMAIN readQueue[s] : k <= mAck}} :
                                            ~\E j \in DOMAIN h : h[j] = id}
        seq == CHOOSE sq \in [1..Cardinality(r) -> r] : 
                                \A x,y \in 1..Cardinality(r): sq[x] = sq[y] => x = y
    IN  seq

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
          /\ IF IsSelfRemv(s, m.val)
        \*   /\ IF FALSE
             THEN UNCHANGED <<h,p>>
             ELSE IF /\ IsQuorum(m.nAcpt + 1, Len(chain[s]))
                     /\ ~IsQuorum(m.nAcpt, Len(chain[s]))
                     \* Have to pass updated chain for AddNode
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
                        /\ IF m.id = Nil \/ \E j \in DOMAIN h : h[j] = m.id
                            THEN h' = h \o seq
                            ELSE h' = Append(h, m.id) \o seq
                        /\ IF bool THEN p' = Append(p, m.ni) ELSE UNCHANGED p
             ELSE /\ h' = h \o DecidedReads(s, m.mAck)
                  /\ UNCHANGED p
            \*  ELSE UNCHANGED <<h,p>>
    
    /\ RecvAccept(s)
    
CPNextP ==
    \* Client actions
    \/ \E v \in Val : ClientSendWrite(v) /\ UNCHANGED <<h, p>>
    \/ ClientSendRead /\ UNCHANGED <<h, p>>
    \/ \E m \in msgs : ClientRecvWrite(m) /\ UNCHANGED <<h, p>>
    \/ \E m \in msgs : ClientRecvRead(m) /\ UNCHANGED <<h, p>>

    \* Server actions
    \* \/ \E s \in Server : LeaderSendNoOPP(s) /\ UNCHANGED <<h, p>>
    \/ \E s \in Server : LeaderRecvAcceptAckP(s)
    \/ \E s \in Server : RecvAcceptP(s)
    \/ \E s \in Server : \E m \in msgs : LeaderRecvWriteP(s, m)
    \/ \E s \in Server : \E m \in msgs : RecvRead(s, m) /\ UNCHANGED <<h, p>>

    \* FT actions
    \/ \E s \in Server : SuspectNextNode(s) /\ UNCHANGED <<h, p>>
    \/ \E s \in Server : AddNewNode(s) /\ UNCHANGED <<h, p>>
    \/ \E s \in Server : \E m \in msgs : RecvStateTransfer(s, m) /\ UNCHANGED <<h, p>>
    \* \/ \E s \in Server : Restart(s) /\ UNCHANGED <<h,p>>

CPvarsP == <<CPvars, h, p>>
        
CPSpecP == CPInitP /\ [][CPNextP]_CPvarsP

 INSTANCE SSLinearM

\* THEOREM CPSpecP => LSpecM

=============================================================================
\* Modification History
\* Last modified Sat Jun 28 16:19:14 IST 2025 by jay
\* Last modified Fri Apr 25 08:51:46 IST 2025 by Kotikala Raghav
\* Created Mon Apr 14 12:07:02 IST 2025 by Kotikala Raghav