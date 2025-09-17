----------------------------- MODULE ChainPaxos -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT C,     \* Number of servers
         MaxC,  \* Maximum Numbers of Servers
         Val,   \* Set of values an object can take
         Nil    \* MV

Server == 1..MaxC
MinQuoromSize == (C \div 2) + 1
     
-----------------------------------------------------------------------------
(* Client-Side Variables *)

LOCAL Operation ==
    [type : {"Read"}, status : {"Pending"}] \union
    [type : {"Read"}, status : {"Done"}, val: Val \union {Nil}] \union
    [type : {"Write"}, status : {"Pending", "Done"}, val: Val]


VARIABLE ops,       \* sequence of operations from client (client state)
         msgs       \* Client-Server messages
         
clientVars == <<ops, msgs>> 

NoOP == [type : {"NoOP"}]
RemoveNode == [type : {"RemoveNode"}, srv : Server]
AddNode == [type : {"AddNode"}, srv : Server]
PrepareNum == [seqn : Nat, srv : Server]

LogEntry == [id  : DOMAIN ops \union {Nil},
             val : Val \union RemoveNode \union AddNode \union NoOP,
             na  : PrepareNum, nAcpt : 0..MaxC, decided : BOOLEAN]
StateTransfer == [type   : {"StateTransfer"},
                  dest   : Server,
                  ldr    : Server,
                  chain  : Seq(Server),
                  log    : Seq(LogEntry),
                  term   : Nat,
                  mAck   : Nat]

Message ==
    [type : {"Accept"},
     ni   : Nat,
     ldr  : Server,
     na   : PrepareNum,
     id   : Nat \union {Nil}, \* Nil for RemoveNode/AddNode/NoOP
     val  : Val \union NoOP \union RemoveNode \union AddNode,
     nAcpt: 0..MaxC,
     mAck : Nat] \union

    [type : {"AcceptAck"},
     ni   : Nat]

ClientMessage ==
    [type : {"WriteRequest"},
     id   : DOMAIN ops,
     val  : Val] \union
    [type : {"WriteResponse"},
     id   : DOMAIN ops] \union
    [type : {"ReadRequest"},
     id   : DOMAIN ops] \union
    [type : {"ReadResponse"},
     id   : DOMAIN ops,
     val  : Val \union {Nil}]

TypeClientVars == /\ ops \in Seq(Operation)
                  /\ msgs \subseteq ClientMessage \union RemoveNode \union AddNode \union StateTransfer

InitClientVars == /\ ops = << >>
                  /\ msgs = {}

-----------------------------------------------------------------------------
(* Organization Variables *)

VARIABLE cnextok,
         csleader,
         marked,
         chain,
         state
         
orgVars == <<cnextok, csleader, marked, chain, state>>


TypeOrgVars == /\ cnextok \in [Server -> Server]
               /\ csleader \in [Server -> Server]
               /\ marked \in [Server -> SUBSET Server]
               /\ chain \in [Server -> Seq(Server)]
               /\ state \in [Server -> {"IDLE", "JOINING", "ACTIVE", "FAILED"}]

InitOrgVars == /\ cnextok = [s \in Server |-> IF s >= C THEN 1 ELSE s+1]
               /\ csleader = [s \in Server |-> 1]
               /\ marked = [s \in Server |-> {}]
               /\ chain = [s \in Server |-> [s_ \in 1..C |-> s_]]
               /\ state = [s \in Server |-> IF s <= C THEN "ACTIVE" ELSE "IDLE"] 

-----------------------------------------------------------------------------
(* Log Variables *)
         
VARIABLE log,
         np,
         maxAck
         
logVars == <<log, np, maxAck>>

TypeLogVars ==
    /\ log \in [Server -> Seq(LogEntry)]
    /\ np \in [Server -> PrepareNum]
    /\ maxAck \in [Server -> Nat]
    
InitLogVars == /\ log = [s \in Server |->  << >>]
               /\ np = [s \in Server |-> [seqn |-> 0, srv |-> 1]]
               /\ maxAck = [s \in Server |-> 0]

-----------------------------------------------------------------------------
(* Leader Variables *)       

VARIABLE maxAcpt,
         pending
         
leaderVars == <<maxAcpt, pending>>

TypeLeaderVars == /\ maxAcpt \in [Server -> Nat]
                  /\ pending \in [Server -> SUBSET DOMAIN ops]

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
         removeNodeLog,
         addNodeLog,
         numFails

TypeHisVars == /\ noopLog \in Seq(Nat)          \* Log indices of noop operations
               /\ removeNodeLog \in Seq(Server) \* Servers to be removed 
               /\ addNodeLog \in Seq(Server)    \* Servers to be added 
               /\ numFails \in Nat           \* Number of restarts possible

InitHisVars == /\ noopLog = << >>
               /\ removeNodeLog = << >>
               /\ addNodeLog = << >>
               /\ numFails = 0

hisVars == <<noopLog, removeNodeLog, addNodeLog, numFails>>

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

MAX(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : y <= x

SeqToSet(seq) ==
    {seq[i] : i \in DOMAIN seq}

RECURSIVE RecNextOK(_, _, _)

RecNextOK(chain_, marked_, i) ==
    IF i > Len(chain_) THEN RecNextOK(chain_, marked_, 1)
    ELSE IF chain_[i] \in marked_ THEN RecNextOK(chain_, marked_, i+1)
    ELSE chain_[i]

NextNodeNotMarked(s, chain_, marked_, ldr) ==
    LET idx == CHOOSE x \in DOMAIN chain_ : chain_[x] = s
    IN IF idx >= Len(chain_) THEN ldr
       ELSE RecNextOK(chain_, marked_, idx+1)

IsQuorum(nAcpt, chainSize) == 
    LET quoromSize == IF (chainSize \div 2) + 1 <= MinQuoromSize 
                      THEN MinQuoromSize
                      ELSE (chainSize \div 2) + 1
    IN  nAcpt >= quoromSize

isNpGreaterThan(np1, np2) ==
    \/ np1.seqn > np2.seqn
    \/ /\ np1.seqn = np2.seqn
       /\ np1.srv > np2.srv

IsEnoughSrvs(s) == Cardinality(DOMAIN chain[s]) >= MinQuoromSize

IsSelfRemv(s, val) == val \in RemoveNode /\ val.srv = s

IsNoOP(val) == val \in NoOP
IsRemNode(val) == val \in RemoveNode
IsAddNode(val) == val \in AddNode

-----------------------------------------------------------------------------
(* Client Actions *)   

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
    /\ ops[m.id].status # "Done"
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
    /\ ops[m.id].status # "Done"
    /\ ops' = [ops EXCEPT ![m.id] = [type |-> "Read", status |-> "Done", val |-> m.val]]
    /\ RemoveMsg(m)
    /\ UNCHANGED <<serverVars, hisVars>>

-----------------------------------------------------------------------------
(* Server Actions *)

\* Leader Sends the periodic NoOP (and starts instance)
LeaderSendNoOP(s) == 
    /\ s = csleader[s]
    /\ IsEnoughSrvs(s)

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
    /\ UNCHANGED <<ops, msgs, readQueue, orgVars, logVars, removeNodeLog, pending, addNodeLog, numFails>>

\* Leader receives a write/RemoveNode/AddNode message (and starts instance)
LeaderRecvWrite(s, m) ==
    /\ s = csleader[s]
    /\ IsEnoughSrvs(s)
    /\ m.type \in {"WriteRequest", "RemoveNode", "AddNode"}

    /\ RemoveMsg(m)
    /\ maxAcpt' = [maxAcpt EXCEPT ![s] = @ + 1]
    /\ buf' = [buf EXCEPT ![s] = @ \o
              <<[type   |-> "Accept",
                 ni     |-> maxAcpt[s] + 1,
                 ldr    |-> s,
                 na     |-> np[s],
                 id     |-> IF IsRemNode(m) \/ IsAddNode(m) THEN Nil ELSE m.id,
                 val    |-> IF IsRemNode(m) \/ IsAddNode(m) THEN m ELSE m.val,
                 nAcpt  |-> 0,
                 mAck   |-> maxAck[s]]>>]
    /\ pending' = [pending EXCEPT ![s] = @ \union
                    IF m \notin (RemoveNode \union AddNode) THEN {m.id} ELSE {}]
    /\ UNCHANGED <<ops, readQueue, orgVars, logVars, hisVars>>  

-----------------------------------------------------------------------------
(* Helper Functions *) 

RECURSIVE UpdatedOrgVars(_, _,_)
RECURSIVE RmvSrv(_, _, _)

RmvSrv(ch, r, i) ==
    IF i = 0 \/ ch = << >> THEN << >>
    ELSE IF ch[i] \in r THEN RmvSrv(ch, r, i-1)
    ELSE Append(RmvSrv(ch,r,i-1), ch[i])

UpdatedOrgVars(s, logIdx, newLog) ==
    (* Returns tuple of (newChain, newMarked) *)
    IF logIdx = {} THEN <<marked[s], chain[s]>>
    ELSE LET i == MAX(logIdx)
             inst == newLog[i]
             recVal == UpdatedOrgVars(s, logIdx \ {i}, newLog)

         IN IF IsRemNode(inst.val)
            THEN <<recVal[1] \ {inst.val.srv}, RmvSrv(recVal[2], {inst.val.srv}, Len(recVal[2]))>>
            ELSE IF inst.val.srv \notin SeqToSet(recVal[2])
            THEN <<recVal[1], Append(recVal[2], inst.val.srv)>>
            ELSE recVal

GetUpdatedOrgVars(s, ldr, term, val, decided, ni, newLog) ==
    LET insts == {i \in DOMAIN newLog : /\ IsRemNode(newLog[i].val) \/ IsAddNode(newLog[i].val)
                                        /\ newLog[i].decided
                                        /\ i \in DOMAIN log[s] => ~log[s][i].decided}

        newOrgVars == UpdatedOrgVars(s, insts, newLog)

        newMarked == IF isNpGreaterThan(term, np[s]) THEN {}
                     ELSE IF IsRemNode(val) /\ ~decided THEN newOrgVars[1] \union {val.srv}
                     ELSE newOrgVars[1]

    IN  IF IsSelfRemv(s,val) THEN << newMarked, newOrgVars[2], cnextok[s] >>
        ELSE << newMarked, newOrgVars[2], NextNodeNotMarked(s, newOrgVars[2], newMarked, ldr) >>

UpdateLeaderInfo(s, leader, term, id, decided) ==
    IF isNpGreaterThan(term, np[s])
    THEN /\ np' = [np EXCEPT ![s] = term]
         /\ csleader' = [csleader EXCEPT ![s] = leader]
    ELSE UNCHANGED <<np, csleader>>

GetUpdatedLog(s, ni, inst, mAck) ==
    LET updLog == [i \in DOMAIN log[s] |-> 
                    IF maxAck[s] < i /\ i <= mAck
                    THEN [log[s][i] EXCEPT !.decided = TRUE]
                    ELSE log[s][i]] \* Deciding all the acked entries
        newLog == IF inst.val = Nil THEN updLog
                  ELSE IF ni \in DOMAIN log[s]
                       THEN [updLog EXCEPT ![ni] = inst]
                  ELSE updLog @@ (ni :> inst)
    IN newLog

Responses(s, id, mAck, isMid, newLog) ==
    LET latestCommittedInst == MAX({i \in DOMAIN newLog : /\ newLog[i].val \in Val
                                                          /\ i <= mAck \/ newLog[i].decided })
        latestCommittedVal == IF latestCommittedInst = 0 THEN Nil
                              ELSE newLog[latestCommittedInst].val
        readResponses ==
            {[type |-> "ReadResponse", id |-> i,
                val |-> latestCommittedVal] :
                i \in UNION {readQueue[s][j] :
                    j \in {k \in DOMAIN readQueue[s] : k <= mAck}}}
        writeResponse == [type |-> "WriteResponse",
                          id   |-> id]
    IN  IF isMid
        THEN readResponses \union {writeResponse}
        ELSE readResponses

MsgToFwd(s, d, ldr, ni, inst, mAck) ==
    IF d = ldr
    THEN [type |-> "AcceptAck",
          ni   |-> ni]
    ELSE [type   |-> "Accept",
          ni     |-> ni,
          ldr    |-> ldr,
          na     |-> inst.na,
          id     |-> inst.id,
          val    |-> inst.val,
          nAcpt  |-> inst.nAcpt,
          mAck   |-> mAck]

Forward(s, ldr, newNextOk, ni, inst, mAck) ==

    \* When Forwarding the Accept messsage: mAck = m.mAck
    \* When Re-propagate the instances: mAck = maxAck[s]
    \* It could possible that, \/ m.mAck >= maxAck[s]
    \*                         \/ m.mAck <= maxAck[s] (Only for s=1 and if AccpetAck are appended in the front of buf)
    LET newBuf == [buf EXCEPT 
                        ![s] = Tail(@),
                        ![cnextok[s]] = Append(@, MsgToFwd(s, cnextok[s], ldr, ni, inst, mAck))]

    IN IF cnextok[s] = newNextOk \* Nothing happened
       THEN buf' = newBuf
       ELSE IF s = newNextOk THEN buf' = [newBuf EXCEPT ![s]=Append(@, MsgToFwd(s, s, ldr, ni, inst, mAck))]
       ELSE LET maXAck == MAX({mAck, maxAck[s]})
                insts == [j \in {i \in DOMAIN log[s] : i > maXAck} |-> 
                            MsgToFwd(s, newNextOk, ldr, j, log[s][j], maxAck[s])]

            IN buf' = [newBuf EXCEPT ![newNextOk] = @ \o Append(insts, MsgToFwd(s, newNextOk, ldr, ni, inst, mAck))]

-----------------------------------------------------------------------------

RecvAccept(s) ==
    /\ state[s] = "ACTIVE"
    /\ IsEnoughSrvs(s) \* Should've MinQuoromSize nodes
    /\ buf[s] # << >>
    /\ LET m == Head(buf[s])
       IN /\ m.type = "Accept"
          /\ ~isNpGreaterThan(np[s], m.na) \* Rejecting all the messages of older term

          /\ LET nAcpt == IF m.ni \in DOMAIN log[s] /\ ~isNpGreaterThan(m.na,log[s][m.ni].na)
                          THEN MAX({m.nAcpt+1, log[s][m.ni].nAcpt})
                          ELSE m.nAcpt+1

                 mAck == MAX({m.mAck, maxAck[s]})
                 decided == IsQuorum(nAcpt, Len(chain[s]))

                 instance == [id      |-> m.id,
                              val     |-> m.val,
                              na      |-> m.na,
                              nAcpt   |-> nAcpt,
                              decided |-> decided]
                 newLog == GetUpdatedLog(s, m.ni, instance, mAck)

                 \* New Org Variables
                 newOrgVars == GetUpdatedOrgVars(s, m.ldr, m.na, m.val, decided, m.ni, newLog)
                 newCnextok == newOrgVars[3]

                \*  isMid == /\ IsQuorum(m.nAcpt + 1, Len(newOrgVars[2]))
                \*           /\ ~IsQuorum(m.nAcpt, Len(newOrgVars[2]))
                 isMid == /\ IsQuorum(m.nAcpt + 1, Len(chain[s]))
                          /\ ~IsQuorum(m.nAcpt, Len(chain[s]))

                 stateTransfer == [type   |-> "StateTransfer",
                                   dest   |-> m.val.srv,
                                   ldr    |-> m.ldr,
                                   chain  |-> newOrgVars[2],
                                   log    |-> newLog,
                                   term   |-> m.na,
                                   mAck   |-> mAck]
             IN /\ IF IsRemNode(m.val) /\ m.val.srv = s THEN state' = [state EXCEPT ![s] = "FAILED"]
                   ELSE UNCHANGED state

                \* Update Org and leader vars
                /\ marked'  = [marked EXCEPT ![s] = newOrgVars[1]]
                /\ chain'   = [chain EXCEPT ![s] = newOrgVars[2]]
                /\ cnextok' = [cnextok EXCEPT ![s] = newCnextok]
                /\ UpdateLeaderInfo(s, m.ldr, m.na, m.id, decided)

                \* Update Log vars
                /\ maxAck' = [maxAck EXCEPT ![s] = mAck]
                /\ log' = [log EXCEPT ![s] = newLog]

                \* Send the write & read resonses to client
                /\ IF IsSelfRemv(s, m.val)
                   THEN UNCHANGED <<readQueue, msgs>>
                   ELSE /\ readQueue' = [readQueue EXCEPT ![s] = [i \in {j \in DOMAIN @ : j > mAck} |-> @[i]]]
                        /\ LET newMsg == IF /\ isMid
                                            /\ IsAddNode(m.val)
                                            /\ m.ni \in DOMAIN log[s] => ~log[s][m.ni].decided
                                         THEN msgs \union {stateTransfer}
                                         ELSE msgs
                           IN msgs' = newMsg \union Responses(s, m.id, mAck, isMid /\ m.val \in Val, newLog)

                \* FORWARD(m)
                \* What happens when we recieve AddNode(s) of itself??
                /\ IF IsSelfRemv(s, m.val) THEN PopMsg(s)
                   ELSE IF /\ IsAddNode(m.val)
                           /\ m.val.srv = newCnextok
                   THEN buf' = [buf EXCEPT 
                                ![s] = Tail(@),
                                ![newCnextok] = Append(@, MsgToFwd(s, newCnextok, m.ldr, m.ni, instance, mAck))]
                   ELSE Forward(s, m.ldr, newCnextok, m.ni, instance, m.mAck)

          /\ UNCHANGED <<ops, leaderVars, hisVars>>

LeaderRecvAcceptAck(s) ==
    /\ state[s] = "ACTIVE"
    /\ IsEnoughSrvs(s)
    /\ s = csleader[s] 
    /\ buf[s] # << >>

    /\ LET m == Head(buf[s])
           mAck == MAX({m.ni, maxAck[s]})
           newLog == GetUpdatedLog(s, m.ni, [val |-> Nil], mAck)
       IN /\ m.type = "AcceptAck"
          /\ PopMsg(s)

          \* Update Org and leader vars
          /\ LET newVars == GetUpdatedOrgVars(s, s, np[s], Nil, TRUE, m.ni, newLog)
             IN /\ marked'  = [marked EXCEPT ![s] = newVars[1]]
                /\ chain'   =  [chain EXCEPT ![s] = newVars[2]]
                /\ cnextok' = [cnextok EXCEPT ![s] = newVars[3]]
          /\ pending' = [pending EXCEPT ![s] = IF m.ni \notin DOMAIN log[s] THEN @
                                               ELSE @ \ {log[s][m.ni].id}]

          \* Update Log vars
          /\ maxAck' = [maxAck EXCEPT ![s] = mAck]
          /\ log' = [log EXCEPT ![s] = newLog]
          
          \* Send the read resonses to client
          /\ readQueue' = [readQueue EXCEPT ![s] = [i \in {j \in DOMAIN @ : j > mAck} |-> @[i]]]
          /\ msgs' = msgs \union Responses(s, Nil, mAck, FALSE, newLog)

    /\ UNCHANGED <<ops, np, csleader, maxAcpt, hisVars, state>>

RecvRead(s, m) ==
    /\ state[s] = "ACTIVE"
    /\ IsEnoughSrvs(s)
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
    /\ state[s] = "ACTIVE"
    /\ IsEnoughSrvs(s)
    /\ cnextok[s] # csleader[s] \* Cannot suspect leader

    /\ SendMsg([type |-> "RemoveNode", srv |-> cnextok[s]])
    /\ removeNodeLog' = Append(removeNodeLog, cnextok[s])
    /\ UNCHANGED <<ops, serverVars, noopLog, addNodeLog, numFails>>

Fail(s) ==
    /\ s # csleader[s]

    \* Restarts the server s
    /\ buf' = [buf EXCEPT ![s] = << >>]
    /\ readQueue' = [readQueue EXCEPT ![s] = << >>]

    \* orgVars
    /\ cnextok' = [cnextok EXCEPT ![s] = 1]
    /\ csleader' = [csleader EXCEPT ![s] = 1]
    /\ marked' = [marked EXCEPT ![s] = {}]
    /\ chain' = [chain EXCEPT ![s] = << >>]

    \* logVars
    /\ log' = [log EXCEPT ![s] = << >>]
    /\ maxAck' = [maxAck EXCEPT ![s] = 0]

    /\ numFails' = numFails + 1
    /\ state' = [state EXCEPT ![s] = "FAILED"]
    
    /\ msgs' = msgs \ {m \in msgs : /\ m.type = "StateTransfer"
                                    /\ m.dest = s}

    /\ UNCHANGED <<np, leaderVars, ops, noopLog, removeNodeLog, addNodeLog>>

AddNewNode(s) ==
    /\ state[s] = "IDLE"
    /\ state' = [state EXCEPT ![s] = "JOINING"]
    /\ SendMsg([type |-> "AddNode", srv |-> s])
    /\ addNodeLog' = Append(addNodeLog, s)
    /\ UNCHANGED <<ops, noopLog, removeNodeLog, numFails, buf, readQueue, cnextok, csleader, marked, chain, logVars, leaderVars>>

RecvStateTransfer(s, m) ==
    /\ m.type = "StateTransfer"
    /\ m.dest = s
    /\ state[s] = "JOINING"
    /\ LET mAck == MAX({m.ni, maxAck[s]})
       IN /\ RemoveMsg(m)

          \* orgVars
          /\ cnextok'  = [cnextok EXCEPT ![s] = NextNodeNotMarked(s, m.chain, {}, m.ldr)]
          /\ csleader' = [csleader EXCEPT ![s] = m.ldr]
          /\ chain'    = [chain EXCEPT ![s] = m.chain]

          \* logVars
          /\ log'    = [log EXCEPT ![s] = m.log]
          /\ np'     = [np EXCEPT ![s] = m.term]
          /\ maxAck' = [maxAck EXCEPT ![s] = m.mAck]
          
          /\ state' = [state EXCEPT ![s] = "ACTIVE"]

          /\ UNCHANGED <<ops, marked, leaderVars, buf, readQueue, hisVars>>

-----------------------------------------------------------------------------

CPNext ==
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
    
CPSpec == CPInit /\ [][CPNext]_CPvars

=============================================================================
\* Modification History
\* Last modified Wed Sep 17 16:18:46 IST 2025 by jay
\* Last modified Wed Sep 03 16:19:44 IST 2025 by Kotikala Raghav
\* Created Wed Mar 26 18:10:34 IST 2025 by Kotikala Raghav