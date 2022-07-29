\* 1) consensus is possible when minimal connections links >= quorum (also should include liveness and safety)
\* 2) the sync between nodes is possible even without direct connection
\* 3) no ordering guarantee the same result (through compare-and-swap approach)


\* there should be at least f+1 connections for each node

------------------------------ MODULE ConcurrentAppend ------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANT NodesCount


(*********
--algorithm ConcurrentAppend { 
  variables 
  states = [s \in 1..NodesCount |-> [value |-> s, signatures |-> {s}]],
  maxNumber = CHOOSE x \in 1..NodesCount : \A y \in 1..NodesCount : y <= x, \* move to invariants
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
        m = <<>>, 
        i = 1, 
        receiverNodeId = NodesCount + 1;
    {
    
    sd: with(iv \in 1..NodesCount){        
           send(receiverNodeId, [value |-> states[self].value, signatures |-> states[self].signatures, orig |-> self]);
          \* receive(m);
           i := i + 1;
           };
        }
  
}
*********)
\* BEGIN TRANSLATION (chksum(pcal) = "2163a3fa" /\ chksum(tla) = "2445079f")
VARIABLES states, maxNumber, receiverNodeState, chan, pc, msg, m, i, 
          receiverNodeId

vars == << states, maxNumber, receiverNodeState, chan, pc, msg, m, i, 
           receiverNodeId >>

ProcSet == ({NodesCount + 1}) \cup (1..NodesCount)

Init == (* Global variables *)
        /\ states = [s \in 1..NodesCount |-> [value |-> s, signatures |-> {s}]]
        /\ maxNumber = (CHOOSE x \in 1..NodesCount : \A y \in 1..NodesCount : y <= x)
        /\ receiverNodeState = [value |-> -1, signatures |-> {NodesCount + 1}]
        /\ chan = [n \in 1..NodesCount+1 |-> <<>>]
        (* Process receiverNode *)
        /\ msg = [self \in {NodesCount + 1} |-> <<>>]
        (* Process senderNode *)
        /\ m = [self \in 1..NodesCount |-> <<>>]
        /\ i = [self \in 1..NodesCount |-> 1]
        /\ receiverNodeId = [self \in 1..NodesCount |-> NodesCount + 1]
        /\ pc = [self \in ProcSet |-> CASE self \in {NodesCount + 1} -> "RA"
                                        [] self \in 1..NodesCount -> "sd"]

RA(self) == /\ pc[self] = "RA"
            /\ pc' = [pc EXCEPT ![self] = "RB"]
            /\ UNCHANGED << states, maxNumber, receiverNodeState, chan, msg, m, 
                            i, receiverNodeId >>

RB(self) == /\ pc[self] = "RB"
            /\ Len(chan[self]) > 0
            /\ msg' = [msg EXCEPT ![self] = Head(chan[self])]
            /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
            /\ pc' = [pc EXCEPT ![self] = "RC"]
            /\ UNCHANGED << states, maxNumber, receiverNodeState, m, i, 
                            receiverNodeId >>

RC(self) == /\ pc[self] = "RC"
            /\ IF receiverNodeState.value < msg[self].value
                  THEN /\ pc' = [pc EXCEPT ![self] = "RD"]
                  ELSE /\ IF receiverNodeState.value = msg[self].value
                             THEN /\ pc' = [pc EXCEPT ![self] = "RF"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "RA"]
            /\ UNCHANGED << states, maxNumber, receiverNodeState, chan, msg, m, 
                            i, receiverNodeId >>

RD(self) == /\ pc[self] = "RD"
            /\ receiverNodeState' = [receiverNodeState EXCEPT !.value = msg[self].value]
            /\ pc' = [pc EXCEPT ![self] = "RE"]
            /\ UNCHANGED << states, maxNumber, chan, msg, m, i, receiverNodeId >>

RE(self) == /\ pc[self] = "RE"
            /\ receiverNodeState' = [receiverNodeState EXCEPT !.signatures = msg[self].signatures \union {self}]
            /\ pc' = [pc EXCEPT ![self] = "RA"]
            /\ UNCHANGED << states, maxNumber, chan, msg, m, i, receiverNodeId >>

RF(self) == /\ pc[self] = "RF"
            /\ receiverNodeState' = [receiverNodeState EXCEPT !.signatures = msg[self].signatures \union receiverNodeState.signatures]
            /\ pc' = [pc EXCEPT ![self] = "RA"]
            /\ UNCHANGED << states, maxNumber, chan, msg, m, i, receiverNodeId >>

receiverNode(self) == RA(self) \/ RB(self) \/ RC(self) \/ RD(self)
                         \/ RE(self) \/ RF(self)

sd(self) == /\ pc[self] = "sd"
            /\ \E iv \in 1..NodesCount:
                 /\ chan' = [chan EXCEPT ![receiverNodeId[self]] = Append(chan[receiverNodeId[self]], ([value |-> states[self].value, signatures |-> states[self].signatures, orig |-> self]))]
                 /\ i' = [i EXCEPT ![self] = i[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << states, maxNumber, receiverNodeState, msg, m, 
                            receiverNodeId >>

senderNode(self) == sd(self)

Next == (\E self \in {NodesCount + 1}: receiverNode(self))
           \/ (\E self \in 1..NodesCount: senderNode(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Jul 29 14:44:54 MSK 2022 by zyeve
\* Created Thu Jul 14 21:32:05 MSK 2022 by zyeve
