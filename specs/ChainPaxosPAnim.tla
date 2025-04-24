----------------------------- MODULE ChainPaxosPAnim ------------------------

EXTENDS ChainPaxosP

\* Merge two records
Merge(r1, r2) == 
    LET D1 == DOMAIN r1 D2 == DOMAIN r2 IN
    [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

SVGElem(_name, _attrs, _children, _innerText) == [name |-> _name, attrs |-> _attrs, children |-> _children, innerText |-> _innerText ]

Text(x, y, text, attrs) == 
    (**************************************************************************)
    (* Text element.'x' and 'y' should be given as integers, and 'text' given *)
    (* as a string.                                                           *)
    (**************************************************************************)
    LET svgAttrs == [x |-> x, 
                     y |-> y] IN
    SVGElem("text", Merge(svgAttrs, attrs), <<>>, text) 

\* Circle element. 'cx', 'cy', and 'r' should be given as integers.
Circle(cx, cy, r, attrs) == 
    LET svgAttrs == [cx |-> cx, 
                     cy |-> cy, 
                     r  |-> r] IN
    SVGElem("circle", Merge(svgAttrs, attrs), <<>>, "")

\* Rectangle element. 'x', 'y', 'w', and 'h_' should be given as integers.
Rect(x, y, w, h_, attrs) == 
    LET svgAttrs == [x      |-> x, 
                     y      |-> y, 
                     width  |-> w, 
                     height |-> h_] IN
    SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

Image(x, y, width, height, href, attrs) == 
    LET svgAttrs == ("xlink:href" :> href @@
                     "x"         :> x @@
                     "y"         :> y @@
                     "width"     :> width @@
                     "height"    :> height) IN
    SVGElem("image", Merge(svgAttrs, attrs), <<>>, "")

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Establish a fixed mapping to assign an ordering to elements in these sets.
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)

----------------------------------------
\* Animation view definition.
c1 == Circle(10, 10, 5, [fill |-> "red"])
c2 == Circle(20, 10, 5, [fill |-> "red"])

----------------------------------------
\* Offsets

Spacing == 38

\* General bases
XBase == 20
YBase == 33

\* Client bases
CXBase == XBase + 15
CYBase == YBase - 29

----------------------------------------
\* Client Symbol

client == Group(<<
            Circle(CXBase, CYBase + 9 , 12, ("stroke" :> "black" @@ "fill" :> "pink")),
            Text(CXBase, CYBase + 12, "Client", ("fill" :> "black" @@ "text-anchor" :> "middle" @@ "font-size" :> "8px"))>>,
            [h_ \in {} |-> {} ])

----------------------------------------
\* Client-Server messages Elements

msgsReq(m) == IF m.type = "WriteRequest" THEN "WReq"
                ELSE IF m.type = "WriteResponse" THEN "WRes"
                ELSE IF m.type = "ReadRequest" THEN "RReq"
                ELSE "RRes"

msgsVal(m) == IF m.type = "WriteRequest" \/ m.type = "ReadResponse"
                THEN ToString(m.id) \o " | " \o ToString(m.val) 
                ELSE IF m.type = "ReadRequest" THEN ToString(m.id) \o " | " \o "?"
                ELSE ToString(m.id)

msgsFill(m) == IF m.type = "WriteRequest" \/ m.type = "ReadRequest"
                 THEN "lightgray"
                 ELSE "lightgray"

msgsText(m) == IF m.type = "WriteRequest" \/ m.type = "ReadRequest"
                 THEN "black"
                 ELSE "black"

msgsStroke(m) ==  IF m.type = "WriteRequest" \/ m.type = "ReadRequest"
                    THEN "orange"
                    ELSE "green"

msgsReqEntry(xbase, ybase, m) == Group(<<Rect(xbase + 1, ybase, 28, 10, ("fill" :> msgsFill(m) @@ "stroke" :> msgsStroke(m))), 
                                   Text(xbase + 15, ybase + 8, msgsReq(m), ("fill" :> msgsText(m) @@ "text-anchor" :>  "middle") @@ "font-size" :> "8px")>>, [h_ \in {} |-> {}])
msgsValEntry(xbase, ybase, m) == Group(<<Rect(xbase + 1, ybase + 10, 28, 10, ("fill" :> msgsFill(m) @@ "stroke" :> msgsStroke(m))), 
                                   Text(xbase + 15, ybase + 18, msgsVal(m), ("fill" :> msgsText(m) @@ "text-anchor" :>  "middle") @@ "font-size" :> "8px")>>, [h_ \in {} |-> {}])

msgsEntry(xbase, ybase, m) == Group(<<msgsReqEntry(xbase, ybase, m), msgsValEntry(xbase, ybase, m)>>, [h_ \in {} |-> {}])
msgsElems ==  LET msgSeq == SetToSeq(msgs)
              IN [ind \in DOMAIN msgSeq |-> msgsEntry(CXBase - (30 * (ind-1)) - 45, CYBase, msgSeq[ind])]

----------------------------------------
\* Client Operations Elements

opsReq(ind) == IF ops[ind].type = "Write" THEN "Write"
               ELSE "Read"

opsVal(ind) == IF ops[ind].type = "Write" \/ ops[ind].status = "Done"
               THEN ToString(ind) \o " | " \o ToString(ops[ind].val) 
               ELSE ToString(ind) \o " | " \o "?"

opsFill(ind) == IF ops[ind].status = "Done"
                THEN "green"
                ELSE "yellow"

opsText(ind) == IF ops[ind].status = "Done"
                THEN "lightgreen"
                ELSE "black"

opsReqEntry(ind, xbase, ybase) == Group(<<Rect(xbase + 1, ybase, 28, 10, ("fill" :> opsFill(ind) @@ "stroke" :> "black")), 
                                   Text(xbase + 15, ybase + 8, opsReq(ind), ("fill" :> opsText(ind) @@ "text-anchor" :>  "middle") @@ "font-size" :> "8px")>>, [h_ \in {} |-> {}])
opsValEntry(ind, xbase, ybase) == Group(<<Rect(xbase + 1, ybase + 10, 28, 10, ("fill" :> opsFill(ind) @@ "stroke" :> "black")), 
                                   Text(xbase + 15, ybase + 18, opsVal(ind), ("fill" :> opsText(ind) @@ "text-anchor" :>  "middle") @@ "font-size" :> "8px")>>, [h_ \in {} |-> {}])

opsEntry(ind, xbase, ybase) == Group(<<opsReqEntry(ind, xbase, ybase), opsValEntry(ind, xbase, ybase)>>, [h_ \in {} |-> {}])
opsElems ==  [ind \in DOMAIN ops |-> opsEntry(ind, CXBase + 30 * (ind-1) + 15, CYBase )]

----------------------------------------
\* Read Queue Elements

RECURSIVE ConcatSeq(_)

ConcatSeq(seq) == IF Len(seq) = 0 THEN << >>
                  ELSE IF Len(seq) = 1 THEN Head(seq)
                  ELSE Head(seq) \o ConcatSeq(Tail(seq))

readSeq(s) == 
    LET logIdxSeq == SetToSeq(DOMAIN readQueue[s])
        indivSeq == [i \in 1..Len(logIdxSeq) |-> SetToSeq({[id |-> j, logIdx |-> logIdxSeq[i]] : j \in readQueue[s][logIdxSeq[i]]})]
    IN ConcatSeq(indivSeq)

readqIDText(id) == IF readQueue[id] = <<>> THEN ""
                 ELSE "id:"

readqLogText(id) == IF readQueue[id] = <<>> THEN ""
                 ELSE "logIdx:"

readqReqEntry(id, xbase, ybase) == Group(<<Rect(xbase + 1, ybase, 10, 10, ("fill" :> "lightgray" @@ "stroke" :> "black")), 
                                   Text(xbase + 6, ybase + 8, ToString(id), ("fill" :> "black" @@ "text-anchor" :>  "middle" @@ "font-size" :> "8px"))>>, [h_ \in {} |-> {}])
readqValEntry(logIdx, xbase, ybase) == Group(<<Rect(xbase + 1, ybase + 10, 10, 10, ("fill" :> "lightgray" @@ "stroke" :> "black")), 
                                   Text(xbase + 6, ybase + 18, ToString(logIdx), ("fill" :> "black" @@ "text-anchor" :>  "middle" @@ "font-size" :> "8px"))>>, [h_ \in {} |-> {}])

readqEntry(id, logIdx, xbase, ybase) == Group(<<readqReqEntry(id, xbase, ybase), readqValEntry(logIdx, xbase, ybase)>>, [h_ \in {} |-> {}])
readqElem(id, xbase, ybase) ==  LET rSeq == readSeq(id) IN
                                Group([ind \in DOMAIN rSeq |-> readqEntry(rSeq[ind].id, rSeq[ind].logIdx, xbase+(12 * ind), ybase)], [h_ \in {} |-> {}])
readqlabels(id, xbase, ybase) == Group(<<Text(xbase + 6, ybase + 8, readqIDText(id), ("fill" :> "black" @@ "text-anchor" :>  "end" @@ "font-size" :> "8px")),
                       Text(xbase + 6, ybase + 18, readqLogText(id), ("fill" :> "black" @@ "text-anchor" :>  "end" @@ "font-size" :> "8px"))>>, 
                [h_ \in {} |-> {}])

readqElems ==  [i \in Server |-> 
                    Group(<<readqElem(i, XBase + 100, YBase + (i-1) * Spacing + 12), 
                            readqlabels(i, XBase + 105, YBase + (i-1) * Spacing + 12)>>, 
                    [h_ \in {} |-> {}])]

----------------------------------------
\* Buffer Elements

bufReq(id,ind) == IF buf[id][ind].type = "Accept" THEN "Acpt"
               ELSE "AcAck"

bufVal(id,ind) == IF buf[id][ind].type = "Accept"
               THEN ToString(buf[id][ind].mAck) \o " | " \o ToString(buf[id][ind].ni) 
               ELSE ToString(buf[id][ind].ni)

bufReqEntry(id, xbase, ybase, ind) == Group(<<Rect(xbase + 1, ybase, 28, 10, ("fill" :> "lightgray" @@ "stroke" :> "black")), 
                                   Text(xbase + 15, ybase + 8, bufReq(id,ind), ("text-anchor" :>  "middle") @@ "font-size" :> "8px")>>, [h_ \in {} |-> {}])
bufValEntry(id, xbase, ybase, ind) == Group(<<Rect(xbase + 1, ybase + 10, 28, 10, ("fill" :> "lightgray" @@ "stroke" :> "black")), 
                                   Text(xbase + 15, ybase + 18, bufVal(id,ind), ("text-anchor" :>  "middle") @@ "font-size" :> "8px")>>, [h_ \in {} |-> {}])

bufEntry(id, xbase, ybase, ind) == Group(<<bufReqEntry(id, xbase, ybase, ind), bufValEntry(id, xbase, ybase, ind)>>, [h_ \in {} |-> {}])
bufElem(id, xbase, ybase) == Group([ind \in DOMAIN buf[id] |-> bufEntry(id, xbase-(30 * ind), ybase, ind)], [h_ \in {} |-> {}])
bufElems ==  [i \in Server |-> bufElem(i, XBase, YBase + (i-1) * Spacing + 12)]

----------------------------------------
\* Log Elements

logEntryFill(id,ind) == IF ind <= maxAck[id] THEN "lightgreen"
                          ELSE IF log[id][ind].decided THEN "orange"
                          ELSE "lightgray"
                          
logEntry(id, xbase, ybase, ind) == Group(<<Rect(xbase + 30, ybase, 10, 10, [fill |-> logEntryFill(id,ind), stroke |-> "black"]), 
                                   Text(xbase + 33, ybase + 8, ToString(log[id][ind].val), ("text-anchor" :>  "start") @@ "font-size" :> "8px")>>, [h_ \in {} |-> {}])
logElem(id, xbase, ybase) == Group([ind \in DOMAIN log[id] |-> logEntry(id, xbase + 12 * (ind-1), ybase, ind)], [h_ \in {} |-> {}])
logElems ==  [i \in Server |-> logElem(i, XBase, YBase + (i-1) * Spacing + 12)]

----------------------------------------
\* mAcks Elements

mAckElem(id, xbase, ybase) == Group(<<Rect(xbase + 10, ybase, 10, 10, ("fill" :> "skyblue" @@ "stroke" :> "black")), 
                                 Text(xbase + 13, ybase + 8, ToString(maxAck[id]), ("text-anchor" :>  "start") @@ "font-size" :> "8px")>>, [h_ \in {} |-> {}])
mAcks == [i \in Server |-> mAckElem(i, XBase, YBase + (i-1) * Spacing + 27)]

----------------------------------------
\* Server Elements

TextFill(i) == IF i \in marked[i] THEN "white"
               ELSE IF csleader[i] = i THEN "black" 
               ELSE "lightgray"

cs == [i \in Server |-> 
        LET id == ToString(i) IN
        Group(<<
            Circle(XBase + 15, YBase + (i-1) * Spacing + 17, 9, 
            [stroke |-> "black", fill |->
                IF i \in marked[i] THEN "red"
                ELSE IF csleader[i] = i THEN "gold" 
                ELSE "gray"]),
            Text(XBase + 15, YBase + (i-1) * Spacing + 20, id, ("fill" :> TextFill(i) @@ "text-anchor" :> "middle" @@ "font-size" :> "9px"))>>,
            [h_ \in {} |-> {} ])] \* Change the color of the text when deleting any server

line == Rect(XBase -80, YBase-2, 200, 1, ("fill" :> "white" @@ "stroke" :> "black"))

extras == <<line>>
clientAnim == <<client>> \o opsElems \o msgsElems
serverAnim == cs \o mAcks \o logElems \o bufElems \o readqElems

AnimView == Group(serverAnim \o clientAnim \o extras, [i \in {} |-> {}])

-----------------------------------------------------------------------------

Init == CPInitP

Next ==
    \/ \E v \in Val : ClientSendWrite(v) /\ UNCHANGED <<h, p>>
    \/ ClientSendRead /\ UNCHANGED <<h, p>>
    \/ \E s \in Server : LeaderRecvAcceptAckP(s)
    \/ \E s \in Server : RecvAcceptP(s)
    \/ \E s \in Server : \E m \in msgs : LeaderRecvWriteP(s, m)
    \/ \E s \in Server : \E m \in msgs : RecvRead(s, m) /\ UNCHANGED <<h, p>>
    \/ \E i \in DOMAIN ops : ClientRecvWrite(i) /\ UNCHANGED <<h, p>>
    \/ \E i \in DOMAIN ops : ClientRecvRead(i) /\ UNCHANGED <<h, p>>

=============================================================================
\* Modification History
\* Last modified Wed Apr 23 22:54:06 IST 2025 by jay
\* Last modified Mon Apr 21 18:43:16 IST 2025 by Kotikala Raghav
\* Created Wed Mar 26 18:10:34 IST 2025 by Kotikala Raghav