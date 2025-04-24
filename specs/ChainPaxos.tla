----------------------------- MODULE ChainPaxos -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT C,     \* Number of servers
         Val,   \* Set of values an object can take
         Nil    \* MV
 
Server == 1..C

-----------------------------------------------------------------------------
(* Messages *)

RemoveNode == [type : {"RemoveNode"}, srv : Server]

Message ==
    [type : {"Accept"},
     ni   : Nat,
     ldr  : Server,
     na   : Server,
     id   : Nat,
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
                  /\ msgs \subseteq ClientMessage

InitClientVars == /\ ops = << >>
                  /\ msgs = {}

-----------------------------------------------------------------------------
(* Organization Variables *)

VARIABLE cnextok,
         csleader,
         marked
         
orgVars == <<cnextok, csleader, marked>>

TypeOrgVars == /\ cnextok \in [Server -> Server]
               /\ csleader \in [Server -> Server]
               /\ marked \in [Server -> SUBSET Server]

InitOrgVars == /\ cnextok = [s \in Server |-> IF s = C THEN 1 ELSE s+1]
               /\ csleader = [s \in Server |-> 1]
               /\ marked = [s \in Server |-> {}]

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

vars == <<clientVars, serverVars>>

CPInit == InitClientVars /\ InitServerVars

CPTypeOK == TypeClientVars /\ TypeServerVars

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


NextNodeNotMarked(s) ==
    LET nodes == {t \in Server : t > s}
    IN IF nodes = {} THEN MIN(Server) ELSE MIN(nodes)


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
    /\ UNCHANGED serverVars

ClientRecvWrite(i) ==
    /\ \E m \in msgs :
        /\ m.type = "WriteResponse"
        /\ m.id = i
        /\ RemoveMsg(m)
        /\ ops[i].status = "Pending"
        /\ ops' = [ops EXCEPT ![i].status = "Done"]
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED serverVars
        
ClientSendRead ==
    /\ SendMsg([type |-> "ReadRequest",
                id   |-> Len(ops) + 1])
    /\ ops' = Append(ops, [type   |-> "Read",
                           status |-> "Pending"])
    /\ UNCHANGED serverVars

ClientRecvRead(i) ==
    /\ \E m \in msgs :
        /\ m.type = "ReadResponse"
        /\ m.id = i
        /\ RemoveMsg(m)
        /\ ops[i].status = "Pending"
        /\ ops' = [ops EXCEPT ![i] = [type |-> "Read", status |-> "Done", val |-> m.val]]
        /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* Server Operations *)

\* Leader receives a write message (and starts instance)
LeaderRecvWrite(s, m) ==
    /\ s = csleader[s]
    /\ m.type = "WriteRequest"
    /\ RemoveMsg(m)
    /\ maxAcpt' = [maxAcpt EXCEPT ![s] = @ + 1]
    /\ buf' = [buf EXCEPT ![s] = Append(@,
                [type   |-> "Accept",
                 ni     |-> maxAcpt[s] + 1,
                 ldr    |-> s,
                 na     |-> np[s],
                 id     |-> m.id,
                 val    |-> m.val,
                 nAcpt  |-> 0,
                 mAck   |-> maxAck[s]])]
    /\ UNCHANGED <<ops, readQueue, orgVars, logVars, pending>>  

UpdateLeaderInfo(s, leader, na, val) ==
    /\ IF np[s] < na
       THEN /\ pending' = [pending EXCEPT ![s] = {}]
            /\ csleader' = [csleader EXCEPT ![s] = leader]
            /\ np' = [np EXCEPT ![s] = na]
            /\ marked' = [marked EXCEPT ![s] = IF val \in RemoveNode THEN {val.srv} ELSE {}]
            /\ cnextok' = [cnextok EXCEPT ![s] = NextNodeNotMarked(s)]
       ELSE UNCHANGED <<pending, orgVars, np>>
            
RecvAccept(s) ==
    /\ buf[s] # << >>
    /\ LET m == Head(buf[s])
       IN /\ m.type = "Accept"
          /\ np[s] <= m.na
          /\ UpdateLeaderInfo(s, m.ldr, m.na, m.val)
          /\ readQueue' = [readQueue EXCEPT ![s] =
                              [i \in {j \in DOMAIN @ : j > m.mAck} |-> @[i]]]
          /\ LET nAcpt == IF m.ni \in DOMAIN log[s]
                          THEN MAX({m.nAcpt+1, log[s][m.ni].nAcpt})
                          ELSE m.nAcpt+1 
                 decided == IsQuorum(nAcpt)
                 mAck == MAX({m.mAck, maxAck[s]})
             IN /\ maxAck' = [maxAck EXCEPT ![s] = mAck]
                /\ log' = [log EXCEPT ![s] = @ @@ (m.ni :>
                                  [id        |-> m.id,
                                   val       |-> m.val,
                                   nAcpt     |-> nAcpt,
                                   decided   |-> decided])]
                /\ LET latestCommittedInst == MAX({i \in DOMAIN log[s] : log[s][i].decided} \union {m.mAck})
                       latestCommittedVal == IF decided /\ m.ni > latestCommittedInst
                                             THEN m.val 
                                             ELSE log[s][latestCommittedInst].val
                       readResponses == {[type |-> "ReadResponse", id |-> i, val |-> latestCommittedVal] :
                                              i \in UNION {readQueue[s][j] : j \in {k \in DOMAIN readQueue[s] : k <= m.mAck}}}
                       writeResponse == [type |-> "WriteResponse",
                                         id   |-> m.id]
                   IN IF IsQuorum(m.nAcpt + 1) /\ ~IsQuorum(m.nAcpt)
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
          /\ UNCHANGED <<ops, maxAcpt>>

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
          /\ LET latestCommittedInst == MAX({i \in DOMAIN log[s] : log[s][i].decided} \union {m.ni})
                 latestCommittedVal == log[s][latestCommittedInst].val
                 readResponses == {[type |-> "ReadResponse", id |-> i, val |-> latestCommittedVal] :
                                        i \in UNION {readQueue[s][j] : j \in {k \in DOMAIN readQueue[s] : k <= m.ni}}}
             IN msgs' = msgs \union readResponses
    /\ UNCHANGED <<ops, orgVars, np, leaderVars>>

RecvRead(s, m) ==
    /\ m.type = "ReadRequest"
    /\ RemoveMsg(m)
    /\ LET nextInst == MAX(DOMAIN log[s]) + 1
       IN readQueue' = [readQueue EXCEPT ![s] =
                            IF nextInst \in DOMAIN @
                            THEN [@ EXCEPT ![nextInst] = @ \union {m.id}]
                            ELSE @ @@ (nextInst :> {m.id})]
    /\ UNCHANGED <<ops, buf, orgVars, logVars, leaderVars>>

-----------------------------------------------------------------------------

CPNext ==
    \/ \E v \in Val : ClientSendWrite(v)
    \/ ClientSendRead
    \/ \E s \in Server : LeaderRecvAcceptAck(s)
    \/ \E s \in Server : RecvAccept(s)
    \/ \E s \in Server : \E m \in msgs : LeaderRecvWrite(s, m)
    \/ \E s \in Server : \E m \in msgs : RecvRead(s, m)
    \/ \E i \in DOMAIN ops : ClientRecvWrite(i)
    \/ \E i \in DOMAIN ops : ClientRecvRead(i)
        
        
CPSpec == CPInit /\ [][CPNext]_vars

=============================================================================
\* Modification History
\* Last modified Thu Apr 24 21:44:21 IST 2025 by Kotikala Raghav
\* Last modified Wed Apr 23 22:54:06 IST 2025 by jay
\* Created Wed Mar 26 18:10:34 IST 2025 by Kotikala Raghav
