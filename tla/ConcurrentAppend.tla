\* 1) no ordering and concurrent access guarantee the same result (through compare-and-swap approach)

------------------------------ MODULE ConcurrentAppend ------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANT NodesCount


(*********
--algorithm ConcurrentAppend { 
  variables 
  states = [s \in 1..NodesCount |-> [value |-> s, signatures |-> {s}]],
  receiverNodeState = [value |-> -1, signatures |-> {NodesCount + 1}],  
  chan = [n \in 1..NodesCount+1 |-> <<>>];  \* FIFO channels 

    \* network functions 
    macro send(des, msg) {
        chan[des] := Append(chan[des], msg);
    }

    macro receive(msg) {
        await Len(chan[self]) > 0;
        msg := Head(chan[self]);
        chan[self] := Tail(chan[self]);
    }

    process (receiverNode \in {NodesCount + 1}) \* process receive signatures + value - we compare it and apply to local state
    variables  
    msg = <<>>,
    { 
    
        RA: while(TRUE) { 
           RB: receive(msg);
            RC:
                if (receiverNodeState.value < msg.value){
                  RD:  receiverNodeState.value := msg.value;
                  RE:  receiverNodeState.signatures := msg.signatures \union {self}; 
                } else if (receiverNodeState.value = msg.value){
                   RF: receiverNodeState.signatures := msg.signatures \union receiverNodeState.signatures; 
                };                
       }
    }
    
    process (senderNode \in 1..NodesCount)
    variables
        receiverNodeId = NodesCount + 1;
    {
    
    SA: with(iv \in 1..NodesCount){        
           send(receiverNodeId, [value |-> states[self].value, signatures |-> states[self].signatures, orig |-> self]);
           };
        }
  
}
*********)
\* BEGIN TRANSLATION (chksum(pcal) = "47f65360" /\ chksum(tla) = "ead7631f")
VARIABLES states, receiverNodeState, chan, pc, msg, receiverNodeId

vars == << states, receiverNodeState, chan, pc, msg, receiverNodeId >>

ProcSet == ({NodesCount + 1}) \cup (1..NodesCount)

Init == (* Global variables *)
        /\ states = [s \in 1..NodesCount |-> [value |-> s, signatures |-> {s}]]
        /\ receiverNodeState = [value |-> -1, signatures |-> {NodesCount + 1}]
        /\ chan = [n \in 1..NodesCount+1 |-> <<>>]
        (* Process receiverNode *)
        /\ msg = [self \in {NodesCount + 1} |-> <<>>]
        (* Process senderNode *)
        /\ receiverNodeId = [self \in 1..NodesCount |-> NodesCount + 1]
        /\ pc = [self \in ProcSet |-> CASE self \in {NodesCount + 1} -> "RA"
                                        [] self \in 1..NodesCount -> "SA"]

RA(self) == /\ pc[self] = "RA"
            /\ pc' = [pc EXCEPT ![self] = "RB"]
            /\ UNCHANGED << states, receiverNodeState, chan, msg, 
                            receiverNodeId >>

RB(self) == /\ pc[self] = "RB"
            /\ Len(chan[self]) > 0
            /\ msg' = [msg EXCEPT ![self] = Head(chan[self])]
            /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
            /\ pc' = [pc EXCEPT ![self] = "RC"]
            /\ UNCHANGED << states, receiverNodeState, receiverNodeId >>

RC(self) == /\ pc[self] = "RC"
            /\ IF receiverNodeState.value < msg[self].value
                  THEN /\ pc' = [pc EXCEPT ![self] = "RD"]
                  ELSE /\ IF receiverNodeState.value = msg[self].value
                             THEN /\ pc' = [pc EXCEPT ![self] = "RF"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "RA"]
            /\ UNCHANGED << states, receiverNodeState, chan, msg, 
                            receiverNodeId >>

RD(self) == /\ pc[self] = "RD"
            /\ receiverNodeState' = [receiverNodeState EXCEPT !.value = msg[self].value]
            /\ pc' = [pc EXCEPT ![self] = "RE"]
            /\ UNCHANGED << states, chan, msg, receiverNodeId >>

RE(self) == /\ pc[self] = "RE"
            /\ receiverNodeState' = [receiverNodeState EXCEPT !.signatures = msg[self].signatures \union {self}]
            /\ pc' = [pc EXCEPT ![self] = "RA"]
            /\ UNCHANGED << states, chan, msg, receiverNodeId >>

RF(self) == /\ pc[self] = "RF"
            /\ receiverNodeState' = [receiverNodeState EXCEPT !.signatures = msg[self].signatures \union receiverNodeState.signatures]
            /\ pc' = [pc EXCEPT ![self] = "RA"]
            /\ UNCHANGED << states, chan, msg, receiverNodeId >>

receiverNode(self) == RA(self) \/ RB(self) \/ RC(self) \/ RD(self)
                         \/ RE(self) \/ RF(self)

SA(self) == /\ pc[self] = "SA"
            /\ \E iv \in 1..NodesCount:
                 chan' = [chan EXCEPT ![receiverNodeId[self]] = Append(chan[receiverNodeId[self]], ([value |-> states[self].value, signatures |-> states[self].signatures, orig |-> self]))]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << states, receiverNodeState, msg, receiverNodeId >>

senderNode(self) == SA(self)

Next == (\E self \in {NodesCount + 1}: receiverNode(self))
           \/ (\E self \in 1..NodesCount: senderNode(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Jul 30 18:21:57 MSK 2022 by zyeve
\* Created Thu Jul 14 21:32:05 MSK 2022 by zyeve
