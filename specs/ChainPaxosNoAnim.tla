----------------------------- MODULE ChainPaxosNoAnim -----------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT C,     \* Number of servers
         Val,   \* Set of values an object can take
         Nil    \* MV
 
Server == 1..C

-----------------------------------------------------------------------------
(* Messages *)

RemoveNode == [type : {"RemoveNode"}, srv : Server]
AddNode == [type : {"AddNode"}, srv : Server]

Message ==
    [type : {"Accept"},
     ni   : Nat,
     ldr  : Server,
     na   : Server,
     id   : Nat \union {Nil}, \* Nil for RemoveNode
     val  : Val \union RemoveNode,
     nAcpt: Nat,
     mAck : Nat] \union
    [type : {"AcceptAck"},
     ni   : Nat]

ClientMessage ==
    [type : {"WriteRequest"},
     id   : Nat,
     val  : Val] \union
    [type : {"WriteResponse"},
     id   : Nat] \union
    [type : {"ReadRequest"},
     id   : Nat] \union
    [type : {"ReadResponse"},
     id   : Nat,
     val  : Val]
     
-----------------------------------------------------------------------------
(* Client-Side Variables *)

LOCAL Operation ==
    [type : {"Read"}, status : {"Pending"}] \union
    [type : {"Read"}, status : {"Done"}, val: Val \union {Nil}] \union
    [type : {"Write"}, status : {"Pending", "Done"}, val: Val \union {Nil}]


VARIABLE ops,       \* sequence of operations from client (client state)
         msgs       \* Client-Server messages
         
clientVars == <<ops, msgs>> 

TypeClientVars == /\ ops \in Seq(Operation)
                  /\ msgs \subseteq ClientMessage \union RemoveNode

InitClientVars == /\ ops = << >>
                  /\ msgs = {}

-----------------------------------------------------------------------------
(* Organization Variables *)

VARIABLE cnextok,
         csleader,
         marked,
         chain
         
orgVars == <<cnextok, csleader, marked, chain>>

TypeOrgVars == /\ cnextok \in [Server -> Server]
               /\ csleader \in [Server -> Server]
               /\ marked \in [Server -> SUBSET Server]
               /\ chain \in [Server -> Seq(Server)]

InitOrgVars == /\ cnextok = [s \in Server |-> IF s = C THEN 1 ELSE s+1]
               /\ csleader = [s \in Server |-> 1]
               /\ marked = [s \in Server |-> {}]
               /\ chain = [s \in Server |-> [s_ \in 1..C |-> s_]]

-----------------------------------------------------------------------------
(* Log Variables *)
         
VARIABLE log,
         np,
         maxAck
         
logVars == <<log, np, maxAck>>

TypeLogVars ==
    /\ \A s \in Server :
        /\ DOMAIN log[s] \subseteq Nat
        /\ \A i \in DOMAIN log[s] :
            log[s][i] \in [id : Nat, val : Val,
                           nAcpt : Nat, decided : BOOLEAN]
    /\ np \in [Server -> Nat]
    /\ maxAck \in [Server -> Nat]
    
InitLogVars == /\ log = [s \in Server |->  << >>]
               /\ np = [s \in Server |-> 1]
               /\ maxAck = [s \in Server |-> 0]

-----------------------------------------------------------------------------
(* Leader Variables *)       

VARIABLE maxAcpt,
         pending
         
leaderVars == <<maxAcpt, pending>>

TypeLeaderVars == /\ maxAcpt \in [Server -> Nat]
                  /\ pending \in [Server -> SUBSET Nat]

InitLeaderVars == /\ maxAcpt = [s \in Server |-> 0]
                  /\ pending = [s \in Server |-> {}]
  
-----------------------------------------------------------------------------
(* All Server Variables *)      

VARIABLE buf,
         readQueue
         
serverVars == <<buf, readQueue, orgVars, logVars, leaderVars>>
                  
InitServerVars ==
    /\ buf = [s \in Server |-> << >>]
    /\ readQueue = [s \in Server |-> << >>]
    /\ InitOrgVars
    /\ InitLogVars
    /\ InitLeaderVars
    
TypeServerVars ==
    /\ C \in Nat
    /\ buf \in [Server -> Seq(Message)]
    /\ \A s \in Server : \A i \in DOMAIN readQueue[s] :
        /\ i \in Nat
        /\ readQueue[s][i] \subseteq Nat
    /\ TypeOrgVars
    /\ TypeLogVars
    /\ TypeLeaderVars
    /\ Val \intersect RemoveNode = {}

-----------------------------------------------------------------------------
(* History Variables *)

VARIABLE noopLog,
         removeNodeLog 

TypeHisVars == /\ noopLog \in Seq(Nat) \* Log indices of noop operations
               /\ removeNodeLog \in Seq(Server) \* Servers to be removed 

InitHisVars == /\ noopLog = << >>
               /\ removeNodeLog = << >>

hisVars == <<noopLog, removeNodeLog>>

-----------------------------------------------------------------------------

vars == <<clientVars, serverVars, hisVars>>

Init == InitClientVars /\ InitServerVars /\ InitHisVars

CPTypeOK == TypeClientVars /\ TypeServerVars /\ TypeHisVars

-----------------------------------------------------------------------------

SendMsg(m) ==
    msgs' = msgs \union {m}

RemoveMsg(m) ==
    msgs' = msgs \ {m}

PopMsg(s) ==
    buf' = [buf EXCEPT ![s] = Tail(@)]

Reply(s, t, m) ==
    buf' = [buf EXCEPT ![s] = Tail(@), ![t] = Append(@, m)]

MIN(S) == CHOOSE x \in S : \A y \in S : x <= y
MAX(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : y <= x


NextNodeNotMarked(s, chain_, marked_) ==
    LET nonMarked == chain_ \ marked_
        rightNodes == {t \in nonMarked : t > s}
    IN IF rightNodes = {} THEN MIN(nonMarked) ELSE MIN(rightNodes)


IsQuorum(nAcpt) == nAcpt + nAcpt > C

-----------------------------------------------------------------------------
(* Client Operations *)   

ClientSendWrite(v) ==
    /\ SendMsg([type |-> "WriteRequest",
                val  |-> v,
                id   |-> Len(ops) + 1])
    /\ ops' = Append(ops, [type   |-> "Write",
                           val    |-> v,
                           status |-> "Pending"])
    /\ UNCHANGED <<serverVars, hisVars>>

ClientRecvWrite(m) ==
    /\ m.type = "WriteResponse"
    /\ ops[m.id].status = "Pending"
    /\ ops' = [ops EXCEPT ![m.id].status = "Done"]
    /\ RemoveMsg(m)
    /\ UNCHANGED <<serverVars, hisVars>>
        
ClientSendRead ==
    /\ SendMsg([type |-> "ReadRequest",
                id   |-> Len(ops) + 1])
    /\ ops' = Append(ops, [type   |-> "Read",
                           status |-> "Pending"])
    /\ UNCHANGED <<serverVars, hisVars>>

ClientRecvRead(m) ==
    /\ m.type = "ReadResponse"
    /\ ops[m.id].status = "Pending"
    /\ ops' = [ops EXCEPT ![m.id] = [type |-> "Read", status |-> "Done", val |-> m.val]]
    /\ RemoveMsg(m)
    /\ UNCHANGED <<serverVars, hisVars>>

-----------------------------------------------------------------------------
(* Server Operations *)

\* Leader receives a write message (and starts instance)
LeaderRecvWrite(s, m) ==
    /\ s = csleader[s]
    /\ \/ m.type = "WriteRequest"
       \/ m.type = "RemoveNode"
    /\ RemoveMsg(m)
    /\ maxAcpt' = [maxAcpt EXCEPT ![s] = @ + 1]
       \* Append Accept message to the front of buffer 
    /\ buf' = [buf EXCEPT ![s] = 
              <<[type   |-> "Accept",
                 ni     |-> maxAcpt[s] + 1,
                 ldr    |-> s,
                 na     |-> np[s],
                 id     |-> IF m \notin RemoveNode THEN m.id ELSE Nil,
                 val    |-> IF m \notin RemoveNode THEN m.val ELSE m,
                 nAcpt  |-> 0,
                 mAck   |-> maxAck[s]]>> \o @]
    /\ pending' = [pending EXCEPT ![s] = @ \union
                    IF m \notin RemoveNode THEN {m.id} ELSE {}]
    /\ UNCHANGED <<ops, readQueue, orgVars, logVars, hisVars>>  

SetToSeqAsc(set) ==
    LET n == Cardinality(set)
    IN CHOOSE sq \in [1..n -> set] :
                \A x, y \in 1..n :
                    x < y => sq[x] < sq[y] 

SeqToSet(seq) ==
    {seq[i] : i \in DOMAIN seq}

UpdateOrgVars(s, leader, term, val, decided) ==
    /\ IF np[s] < term
       THEN /\ np' = [np EXCEPT ![s] = term]
            /\ csleader' = [csleader EXCEPT ![s] = leader]
       ELSE UNCHANGED <<np, csleader>>
    
    /\ IF val \in RemoveNode 
       THEN LET prevMarked == IF np[s] >= term THEN marked[s] ELSE {}
                markedNodes == prevMarked \union IF ~decided THEN {val.srv} ELSE {} 
            IN /\ marked' = [marked EXCEPT ![s] = markedNodes]
               /\ chain' = [chain EXCEPT ![s] = IF ~decided THEN @
                                ELSE SetToSeqAsc({@[i] : i \in DOMAIN @} \ {val.srv}) ]
               /\ cnextok' = [cnextok EXCEPT ![s] =
                        NextNodeNotMarked(s, {chain[s][t] : t \in DOMAIN chain[s]}, markedNodes)]
       
       ELSE /\ marked' = IF np[s] < term THEN [marked EXCEPT ![s] = {}] ELSE marked
            /\ IF val \in AddNode
               THEN TRUE \* TODO
               ELSE UNCHANGED <<chain, cnextok>>

RecvAccept(s) ==
    /\ buf[s] # << >>
    /\ LET m == Head(buf[s])
       IN /\ m.type = "Accept"
          /\ np[s] <= m.na
          \* Remove all entries waiting on maxAck upto m.mAck from read queue
          /\ readQueue' = [readQueue EXCEPT ![s] =
                              [i \in {j \in DOMAIN @ : j > m.mAck} |-> @[i]]] 
          /\ LET nAcpt == IF m.ni \in DOMAIN log[s]
                          THEN MAX({m.nAcpt+1, log[s][m.ni].nAcpt})
                          ELSE m.nAcpt+1 
                 decided == IsQuorum(nAcpt)
                 mAck == m.mAck
             IN /\ maxAck' = [maxAck EXCEPT ![s] = mAck]
                /\  IF m.val \notin RemoveNode
                    THEN pending' = [pending EXCEPT ![s] =
                        IF np[s] < m.na THEN {}
                        ELSE IF decided THEN @ \ {m.id}
                                ELSE @]
                    ELSE UNCHANGED pending             
                /\ UpdateOrgVars(s, m.ldr, m.na, m.val, decided)
                /\ log' = [log EXCEPT ![s] = @ @@ (m.ni :>
                                  [id        |-> m.id,
                                   val       |-> m.val,
                                   nAcpt     |-> nAcpt,
                                   decided   |-> decided])]
                /\ LET latestCommittedInst == MAX({i \in DOMAIN log[s] :
                            log[s][i].decided} \union {m.mAck})
                       latestCommittedVal ==
                            IF decided /\ m.ni > latestCommittedInst
                            THEN m.val 
                            ELSE log[s][latestCommittedInst].val
                       readResponses ==
                            {[type |-> "ReadResponse", id |-> i,
                               val |-> latestCommittedVal] :
                                i \in UNION {readQueue[s][j] :
                                 j \in {k \in DOMAIN readQueue[s] : k <= m.mAck}}}
                       writeResponse == [type |-> "WriteResponse",
                                         id   |-> m.id]
                   IN IF /\ IsQuorum(m.nAcpt + 1)
                         /\ ~IsQuorum(m.nAcpt)
                         /\ m.val \notin RemoveNode 
                      THEN msgs' = msgs \union readResponses \union {writeResponse}
                      ELSE msgs' = msgs \union readResponses
                /\ IF cnextok[s] = csleader[s]
                   THEN Reply(s, csleader[s],
                              [type |-> "AcceptAck",
                               ni   |-> m.ni])
                   ELSE Reply(s, cnextok[s],
                              [type |-> "Accept",
                               ni   |-> m.ni,
                               ldr  |-> m.ldr,
                               na   |-> m.na,
                               id   |-> m.id,
                               val  |-> m.val,
                               nAcpt|-> nAcpt,
                               mAck |-> mAck])
          /\ UNCHANGED <<ops, maxAcpt, hisVars>>

LeaderRecvAcceptAck(s) ==
    /\ s = csleader[s] 
    /\ buf[s] # << >>
    /\ LET m == Head(buf[s])
       IN /\ m.type = "AcceptAck"
          /\ PopMsg(s)
          /\ maxAck' = [maxAck EXCEPT ![s] = m.ni]
          /\ log' = [log EXCEPT ![s] =
                            [i \in DOMAIN log[s] |->
                                IF i <= m.ni
                                THEN [log[s][i] EXCEPT !.decided = TRUE]
                                ELSE log[s][i]]]
          /\ readQueue' = [readQueue EXCEPT ![s] =
                                [i \in {j \in DOMAIN @ : j > m.ni} |-> @[i]]]
          /\ LET latestCommittedInst == MAX({i \in DOMAIN log[s] :
                                                log[s][i].decided}
                                                    \union {m.ni})
                 latestCommittedVal == log[s][latestCommittedInst].val
                 readResponses ==
                    {[type |-> "ReadResponse", id |-> i, val |-> latestCommittedVal] :
                            i \in UNION {readQueue[s][j] :
                            j \in {k \in DOMAIN readQueue[s] : k <= m.ni}}}
             IN msgs' = msgs \union readResponses
          /\ LET logEntry == log[s][m.ni]
             IN IF logEntry.val \in RemoveNode
                THEN LET newChain == SetToSeqAsc(SeqToSet(chain[s]) \ {logEntry.val.srv})
                     IN /\ marked' = [marked EXCEPT ![s] = @ \ {logEntry.val.srv}]
                        /\ chain' = [chain EXCEPT ![s] = newChain]
                        /\ cnextok' = [cnextok EXCEPT ![s] =
                            NextNodeNotMarked(s, SeqToSet(newChain), marked[s] \ {logEntry.val.srv})]
             ELSE UNCHANGED <<marked, chain>>
    /\ UNCHANGED <<ops, csleader, np, leaderVars, hisVars>>

RecvRead(s, m) ==
    /\ m.type = "ReadRequest"
    /\ RemoveMsg(m)
    /\ LET nextInst == MAX(DOMAIN log[s]) + 1
       IN readQueue' = [readQueue EXCEPT ![s] =
                            IF nextInst \in DOMAIN @
                            THEN [@ EXCEPT ![nextInst] = @ \union {m.id}]
                            ELSE @ @@ (nextInst :> {m.id})]
    /\ UNCHANGED <<ops, buf, orgVars, logVars, leaderVars, hisVars>>

\* Node s suspects that node s+1 has failed
SuspectNextNode(s) ==
    /\ cnextok[s] # csleader[s] \* Cannot suspect leader
    /\ SendMsg([type |-> "RemoveNode", srv |-> s+1])
    /\ removeNodeLog' = Append(removeNodeLog, s+1)
    /\ UNCHANGED <<ops, serverVars, noopLog>>

-----------------------------------------------------------------------------

Next ==
    \/ \E v \in Val : ClientSendWrite(v)
    \/ ClientSendRead
    \/ \E s \in Server : LeaderRecvAcceptAck(s)
    \/ \E s \in Server : RecvAccept(s)
    \/ \E s \in Server : \E m \in msgs : LeaderRecvWrite(s, m)
    \/ \E s \in Server : \E m \in msgs : RecvRead(s, m)
    \/ \E m \in msgs : ClientRecvWrite(m)
    \/ \E m \in msgs : ClientRecvRead(m)  
    
    \/ \E s \in Server : SuspectNextNode(s)      
        
\* CPSpec == CPInit /\ [][CPNext]_CPvars

-----------------------------------------------------------------------------

maxCommit(s) == MAX({i \in DOMAIN log[s] : log[s][i].decided} \union {maxAck[s]})

CommitIdxInv == /\ maxCommit(3) >= maxCommit(4)
                /\ maxCommit(4) >= maxCommit(2)

MaxAckInv == /\ maxAck[4] <= maxAck[3]
             /\ maxAck[3] <= maxAck[2]

LogInv == \A s \in Server :
        /\ maxAck[s] <= maxCommit(s)
        /\ maxCommit(s) <= MAX(DOMAIN log[s])

=============================================================================
\* Modification History
\* Last modified Tue May 06 13:25:47 IST 2025 by Kotikala Raghav
\* Last modified Wed Apr 23 22:54:06 IST 2025 by jay
\* Created Wed Mar 26 18:10:34 IST 2025 by Kotikala Raghav
