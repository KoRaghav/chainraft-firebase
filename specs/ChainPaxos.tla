----------------------------- MODULE ChainPaxos -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT C,     \* Number of servers
         Val,   \* Set of values an object can take
         Nil    \* MV
 
Server == 1..C
MinQuoromSize == (C \div 2) + 1

-----------------------------------------------------------------------------
(* Messages *)

NoOP == [type : {"NoOP"}]
RemoveNode == [type : {"RemoveNode"}, srv : Server]
AddNode == [type : {"AddNode"}, srv : Server]

Message ==
    [type : {"Accept"},
     ni   : Nat,
     ldr  : Server,
     na   : Server,
     id   : Nat \union {Nil}, \* Nil for RemoveNode
     val  : Val \union NoOP \union RemoveNode,
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
     val  : Val \union {Nil}]
     
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
            log[s][i] \in [id  : Nat \union {Nil},
                           val : Val \union RemoveNode \union AddNode,
                           na  : Server, nAcpt : Nat, decided : BOOLEAN]
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

CPvars == <<clientVars, serverVars, hisVars>>

CPInit == InitClientVars /\ InitServerVars /\ InitHisVars

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

SetToSeqAsc(set) ==
    LET n == Cardinality(set)
    IN CHOOSE sq \in [1..n -> set] :
                \A x, y \in 1..n :
                    x < y => sq[x] < sq[y] 

SeqToSet(seq) ==
    {seq[i] : i \in DOMAIN seq}

NextNodeNotMarked(s, chain_, marked_) ==
    LET nonMarked == chain_ \ marked_
        rightNodes == {t \in nonMarked : t > s}
    IN IF rightNodes = {} THEN MIN(nonMarked) ELSE MIN(rightNodes)

IsQuorum(nAcpt, chainSize) == 
    LET quoromSize == IF (chainSize \div 2) + 1 <= MinQuoromSize 
                      THEN MinQuoromSize
                      ELSE (chainSize \div 2)
    \* LET quoromSize == chainSize \div 2
    IN  nAcpt >= quoromSize

IsRemoved(s) == \/ s \in marked[s]
                \/ ~\E i \in DOMAIN chain[s] : s = chain[s][i]

IsSelfRemv(s, val) == val \in RemoveNode /\ val.srv = s

IsFunctioning(s) == Cardinality(DOMAIN chain[s]) >= MinQuoromSize
IsNoOP(val) == val \in NoOP
IsRemvNo(val) == val \in RemoveNode
IsAddNo(val) == val \in AddNode

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

\* Leader Sends the periodic NoOP (and starts instance)
LeaderSendNoOP(s) == 
    /\ IsFunctioning(s)
    /\ s = csleader[s]
    /\ maxAcpt' = [maxAcpt EXCEPT ![s] = @ + 1]
    /\ buf' = [buf EXCEPT ![s] = Append(@,
                [type   |-> "Accept",
                 ni     |-> maxAcpt[s] + 1,
                 ldr    |-> s,
                 na     |-> np[s],
                 id     |-> Nil,
                 val    |-> [type |-> "NoOP"],
                 nAcpt  |-> 0,
                 mAck   |-> maxAck[s]])]
    /\ noopLog' = Append(noopLog, maxAcpt[s] + 1)
    /\ UNCHANGED <<ops, msgs, readQueue, orgVars, logVars, removeNodeLog, pending>>

\* Leader receives a write message (and starts instance)
LeaderRecvWrite(s, m) ==
    /\ IsFunctioning(s)
    /\ s = csleader[s]
    /\ \/ m.type = "WriteRequest"
       \/ m.type = "RemoveNode"
    /\ RemoveMsg(m)
    /\ maxAcpt' = [maxAcpt EXCEPT ![s] = @ + 1]
       \* Append Accept message to the ~front~ BACK of buffer 
    /\ buf' = [buf EXCEPT ![s] = @ \o
              <<[type   |-> "Accept",
                 ni     |-> maxAcpt[s] + 1,
                 ldr    |-> s,
                 na     |-> np[s],
                 id     |-> IF m \notin RemoveNode THEN m.id ELSE Nil,
                 val    |-> IF m \notin RemoveNode THEN m.val ELSE m,
                 nAcpt  |-> 0,
                 mAck   |-> maxAck[s]]>>]
    /\ pending' = [pending EXCEPT ![s] = @ \union
                    IF m \notin RemoveNode THEN {m.id} ELSE {}]
    /\ UNCHANGED <<ops, readQueue, orgVars, logVars, hisVars>>  

-----------------------------------------------------------------------------
(* Helper Functions *) 

GetDecidedOrgVars(s, term, mAck) == 
    LET decidedRemovals == {log[s][i].val.srv : 
                                i \in {j \in DOMAIN log[s] : 
                                    /\ j <= mAck 
                                    /\ log[s][j].val \in RemoveNode 
                                    /\ ~log[s][j].decided}}
        decidedAdds == {log[s][i].val.srv :
                            i \in {j \in DOMAIN log[s] : 
                                /\ j <= mAck 
                                /\ log[s][j].val \in AddNode 
                                /\ ~log[s][j].decided}}
 
        decidedMarked == IF np[s] >= term THEN marked[s] \ decidedRemovals ELSE {}

        decidedChain == (SeqToSet(chain[s]) \union decidedAdds) \ (decidedRemovals)

    IN << decidedMarked, decidedChain >>

GetNewOrgVars(s, val, decided, decidedMarked, decidedChain) == 
    LET newMarked == decidedMarked \union IF IsRemvNo(val) /\ ~decided THEN {val.srv} ELSE {}

        toBeRemoved == IF IsRemvNo(val) /\ decided THEN {val.srv} ELSE {}
        toBeAdded == IF IsAddNo(val) /\ decided THEN {val.srv} ELSE {}

        newChain == (decidedChain \union toBeAdded) \ (toBeRemoved)

    IN << newMarked, SetToSeqAsc(newChain), NextNodeNotMarked(s, newChain, newMarked) >>

UpdateOrgVars(s, leader, term, val, decided, mAck) ==
    LET decidedVars == GetDecidedOrgVars(s, term, mAck)
        newVars == GetNewOrgVars(s, val, decided, decidedVars[1], decidedVars[2])

    IN  /\ marked'  = [marked EXCEPT ![s] = newVars[1]]
        /\ chain'   =  [chain EXCEPT ![s] = newVars[2]]
        /\ cnextok' = [cnextok EXCEPT ![s] = newVars[3]]

UpdateLeaderInfo(s, leader, term, id, decided) ==
    /\  IF np[s] < term
        THEN /\ np' = [np EXCEPT ![s] = term]
             /\ csleader' = [csleader EXCEPT ![s] = leader]
        ELSE UNCHANGED <<np, csleader>>

    /\ pending' = [pending EXCEPT ![s] =
                    IF np[s] < term THEN {}
                    ELSE IF decided THEN pending[s] \ {id}
                         ELSE @]

UpdateLogVars(s, ni, inst, mAck) ==
    /\  maxAck' = [maxAck EXCEPT ![s] = mAck]
    /\  LET updLog == [i \in DOMAIN log[s] |-> 
                        IF i <= mAck
                        THEN [log[s][i] EXCEPT !.decided = TRUE]
                        ELSE log[s][i]] \* Deciding all the acked entries
        IN log' = [log EXCEPT ![s] = 
                    IF inst.val = Nil \/ IsNoOP(inst.val)
                    THEN updLog
                    ELSE IF ni \in DOMAIN log[s]
                         THEN [updLog EXCEPT ![ni].nAcpt = inst.nAcpt, ![ni].decided = inst.decided]
                    ELSE updLog @@ (ni :> inst)]

SendReadAndWriteResponse(s, id, ni, val, m, decided, mAck, isMid) ==
    LET latestCommittedInst == MAX({i \in DOMAIN log[s] : /\ log[s][i].val \in Val
                                                          /\ i <= mAck \/ log[s][i].decided })
        latestCommittedVal == IF /\ val \in Val
                                 /\ decided
                                 /\ ni > latestCommittedInst
                              THEN val 
                              ELSE IF latestCommittedInst = 0 THEN Nil
                              ELSE log[s][latestCommittedInst].val
        readResponses ==
            {[type |-> "ReadResponse", id |-> i,
                val |-> latestCommittedVal] :
                i \in UNION {readQueue[s][j] :
                    j \in {k \in DOMAIN readQueue[s] : k <= mAck}}}
        writeResponse == [type |-> "WriteResponse",
                          id   |-> id]
    IN  IF isMid
        THEN msgs' = msgs \union readResponses \union {writeResponse}
        ELSE msgs' = msgs \union readResponses

MsgToFwd(s, d, ni, inst, mAck) ==
    \* Leader could also change here
    \* do conisder that case as well
    \* when term change be careful about inst.na can consist old term
    IF d = csleader[s]
    THEN [type |-> "AcceptAck",
          ni   |-> ni]
    ELSE [type   |-> "Accept",
          ni     |-> ni,
          ldr    |-> csleader[s],
          na     |-> inst.na,
          id     |-> inst.id,
          val    |-> inst.val,
          nAcpt  |-> inst.nAcpt,
          mAck   |-> mAck]

Forward(s, newNextOk, ni, inst, mAck) ==

    \* When Forwarding the Accpet messsage: mAck = m.mAck
    \* When Re-propagate the instances: mAck = maxAck[s]
    \* It could possible that, \/ m.mAck >= maxAck[s]
    \*                         \/ m.mAck <= maxAck[s] (Only for s=1 and if AccpetAck are appended in the front of buf)
    LET newBuf == IF s = cnextok[s]
                  THEN [buf EXCEPT ![s]=Append(Tail(@), MsgToFwd(s, s, ni, inst, mAck))]
                  ELSE [buf EXCEPT 
                            ![s] = Tail(@),
                            ![cnextok[s]] = Append(@, MsgToFwd(s, cnextok[s], ni, inst, mAck))]

    IN IF cnextok[s] = newNextOk \* Nothing happened
       THEN buf' = newBuf
       ELSE IF s = newNextOk THEN buf' = [newBuf EXCEPT ![s]=Append(@, MsgToFwd(s, s, ni, inst, mAck))]
       ELSE LET maXAck == MAX({mAck, maxAck[s]})
                instsIdx == SetToSeqAsc({i \in DOMAIN log[s] : i > maXAck})
                insts == [j \in 1..Len(instsIdx) |-> 
                            MsgToFwd(s, newNextOk, instsIdx[j], log[s][instsIdx[j]], maxAck[s])]

            IN buf' = [newBuf EXCEPT ![newNextOk] = @ \o Append(insts, MsgToFwd(s, newNextOk, ni, inst, mAck))]
            \* IN buf' = [newBuf EXCEPT ![newNextOk] = Append(@, MsgToFwd(s, newNextOk, ni, inst, mAck))]

-----------------------------------------------------------------------------

RecvAccept(s) ==
    /\ IsFunctioning(s) \* Should've MinQuoromSize nodes
    /\ buf[s] # << >>
    /\ LET m == Head(buf[s])
       IN /\ m.type = "Accept"
          /\ np[s] <= m.na \* Rejecting all the messages of older term

          /\ LET nAcpt == IF m.ni \in DOMAIN log[s]
                          THEN MAX({m.nAcpt+1, log[s][m.ni].nAcpt})
                          ELSE m.nAcpt+1
                 mAck == MAX({m.mAck, maxAck[s]})

                 \* Apply all Membership Change upto mAck
                 decidedOrgVars == GetDecidedOrgVars(s, m.na, mAck)

                 \* Decide the current instance based on decided chain
                 decided == IsQuorum(nAcpt, Cardinality(decidedOrgVars[2]) )

                 \* New Org Variables
                 newOrgVars == GetNewOrgVars(s, m.val, decided, decidedOrgVars[1], decidedOrgVars[2])
                 newCnextok == newOrgVars[3]

                 instance == [id      |-> m.id,
                              val     |-> m.val,
                              na      |-> m.na,
                              nAcpt   |-> nAcpt,
                              decided |-> decided]
             IN 
                \* UpdateLeaderINFO(ldr, np) & MarkForRemoval(r)           
                /\ marked'  = [marked EXCEPT ![s] = newOrgVars[1]]
                /\ chain'   = [chain EXCEPT ![s] = newOrgVars[2]]
                /\ cnextok' = [cnextok EXCEPT ![s] = newCnextok]
                /\ UpdateLeaderInfo(s, m.ldr, m.na, m.id, decided)

                \* DECIDEANDGCUPTO(mAck)
                /\ UpdateLogVars(s, m.ni, instance, mAck)

                \* Should the node recieving it's own RemoveNode send a write response??
                \* Not Sending the ReadResponse of the reads that are in the Removed node.
                /\ IF \/ IsRemoved(s)
                      \/ IsSelfRemv(s, m.val)
                   THEN UNCHANGED <<readQueue, msgs>>
                   ELSE \* Remove all entries waiting on maxAck upto m.mAck from read queue
                        /\ readQueue' = [readQueue EXCEPT ![s] =
                            [i \in {j \in DOMAIN @ : j > m.mAck} |-> @[i]]] 
                        /\ LET isMid == /\ IsQuorum(m.nAcpt + 1, Cardinality(DOMAIN newOrgVars[2]))
                                        /\ ~IsQuorum(m.nAcpt, Cardinality(DOMAIN newOrgVars[2]))
                                        /\ m.val \in Val
                           IN SendReadAndWriteResponse(s, m.id, m.ni, m.val, m, decided, mAck, isMid)

                \* FORWARD(m)
                \* IF RemoveNode of self got then don't forward it
                \* Have to fix for adding Node when only Leader is there
                \* Also the STATE TRANSFER
                /\ IF IsSelfRemv(s, m.val)
                   THEN buf' = [buf EXCEPT ![s]=Tail(@)]
                   ELSE Forward(s, newCnextok, m.ni, instance, m.mAck)

          /\ UNCHANGED <<ops, maxAcpt, hisVars>>

LeaderRecvAcceptAck(s) ==
    /\ IsFunctioning(s)
    /\ s = csleader[s] 
    /\ buf[s] # << >>
    /\ LET m == Head(buf[s])
           mAck == MAX({m.ni, maxAck[s]})
       IN /\ m.type = "AcceptAck"
          /\ PopMsg(s)
          /\ UpdateLogVars(s, m.ni, [ val |-> Nil], mAck)

          /\ readQueue' = [readQueue EXCEPT ![s] =
                                [i \in {j \in DOMAIN @ : j > mAck} |-> @[i]]]
          /\ SendReadAndWriteResponse(s, Nil, Nil, Nil, m, TRUE, mAck, FALSE)

          /\ UpdateOrgVars(s, s, np[s], Nil, FALSE, mAck)
          /\ pending' = [pending EXCEPT ![s] = 
                            IF m.ni \in DOMAIN log[s] 
                            THEN @ \ { log[s][m.ni].id} 
                            ELSE @]
    /\ UNCHANGED <<ops, np, csleader, maxAcpt, hisVars>>

RecvRead(s, m) ==
    /\ IsFunctioning(s)
    /\ m.type = "ReadRequest"
    /\ RemoveMsg(m)
    /\ LET nextInst == MAX(DOMAIN log[s]) + 1
       IN readQueue' = [readQueue EXCEPT ![s] =
                            IF nextInst \in DOMAIN @
                            THEN [@ EXCEPT ![nextInst] = @ \union {m.id}]
                            ELSE @ @@ (nextInst :> {m.id})]
    /\ UNCHANGED <<ops, buf, orgVars, logVars, leaderVars, hisVars>>

\* Node s suspects that node cnextok[s] has failed
SuspectNextNode(s) ==
    /\ IsFunctioning(s)
    /\ cnextok[s] # csleader[s] \* Cannot suspect leader
    /\ ~IsRemoved(s)
    /\ SendMsg([type |-> "RemoveNode", srv |-> cnextok[s]])
    /\ removeNodeLog' = Append(removeNodeLog, cnextok[s])
    /\ UNCHANGED <<ops, serverVars, noopLog>>

-----------------------------------------------------------------------------

CPNext ==
    \/ \E v \in Val : ClientSendWrite(v)
    \/ ClientSendRead
    \/ \E s \in Server : LeaderSendNoOP(s)
    \/ \E s \in Server : LeaderRecvAcceptAck(s)
    \/ \E s \in Server : RecvAccept(s)
    \/ \E s \in Server : \E m \in msgs : LeaderRecvWrite(s, m)
    \/ \E s \in Server : \E m \in msgs : RecvRead(s, m)
    \/ \E m \in msgs : ClientRecvWrite(m)
    \/ \E m \in msgs : ClientRecvRead(m)  
    
    \/ \E s \in Server : SuspectNextNode(s)      
        
CPSpec == CPInit /\ [][CPNext]_CPvars

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
\* Last modified Sat Jun 28 14:53:49 IST 2025 by jay
\* Last modified Tue May 06 18:06:03 IST 2025 by Kotikala Raghav
\* Created Wed Mar 26 18:10:34 IST 2025 by Kotikala Raghav
