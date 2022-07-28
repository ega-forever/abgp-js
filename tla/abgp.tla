\* 1) consensus is possible when minimal connections links >= quorum (also should include liveness and safety)
\* 2) the sync between nodes is possible even without direct connection
\* 3) no ordering guarantee the same result (through compare-and-swap approach)


\* there should be at least f+1 connections for each node

------------------------------ MODULE abgp ------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANT Nodes, Edges, Quorum, Fail


Nbrs(n)  ==  {m \in Nodes : {m,n} \in Edges}
SetNbrs(S)  ==  UNION {Nbrs(n) : n \in S}

RECURSIVE ReachableFrom(_)
  ReachableFrom(S)  ==  LET R == SetNbrs(S)
                        IN  IF R \subseteq S THEN S
                                             ELSE ReachableFrom(R \cup S)

\* all nodes are reachable between each other
ASSUME  \A n \in Nodes: ReachableFrom({n}) = Nodes

\* all nodes have enough connection links for quorum
ASSUME \A n \in Nodes: (Cardinality(SetNbrs({n})) >= Fail + 1) \* todo replace - this doesn't work

ASSUME Quorum > Fail

(*********
--algorithm NoOrderingSync { 
  variables 
  states = [s \in 1..Cardinality(Nodes) |-> [value |-> s, signatures |-> {s}]],
  maxNumber = CHOOSE x \in Nodes : \A y \in Nodes : y <= x, \* move to invariants
  SenderNodeIdRange = 100,
  ReceiverNodeIdRange = 200,
   
  
  senderProcs = {x + SenderNodeIdRange: x \in Nodes},
  receiverProcs = {x + ReceiverNodeIdRange: x \in Nodes},
 
  
  chan = [n \in (senderProcs \union receiverProcs) |-> <<>>];  \* FIFO channels 

    \* network functions 
    macro send(des, msg) {
        chan[des] := Append(chan[des], msg);
    }

    macro receive(msg) {
        await Len(chan[self]) > 0;
        msg := Head(chan[self]);
        chan[self] := Tail(chan[self]);
    }

    process (receiverNode \in receiverProcs) \* process receive signatures + value - we compare it and apply to local state
    variables  
    msg = <<>>, 
    id = self - ReceiverNodeIdRange;    
    { 
    
        RA: while(TRUE) { 
           RB: receive(msg);
           
            RC: \* todo leave only Q signatures
                if (states[id].value < msg.value){
                  RD:  states[id].value := msg.value;
                  RE:  states[id].signatures := msg.signatures \union {id}; 
                } else if (states[id].value = msg.value){
                   RF: states[id].signatures := msg.signatures \union states[id].signatures; 
                };
                
            RG:  send(msg.orig, [type|-> "Ack"]);       
       }
    }
    
    process (senderNode \in senderProcs) \* sender send msg to all edge nodes 
    variables
        m = <<>>, 
        i = 1, 
        id = self - SenderNodeIdRange,
        nbrsNodes = SetNbrs({id}),
        receiverNode = "";
    {
     SA: while(TRUE) {
     
\*        SB: nbrsNodes := SetNbrs({id}); 
     
        SC: while(i <= Cardinality(nbrsNodes)){        
               SD: send(i + ReceiverNodeIdRange, [value |-> states[id].value, signatures |-> states[id].signatures, orig |-> SenderNodeIdRange + id]);
               SE: receive(m);
               SF: i := i + 1;
               };
               SG: i := 1;           
            }
        }
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
\*  fair process (node \in Nodes) 
\*      variables stateSynced = FALSE, highestKVNode = self, highestSignatures = {}, nbrsNodes = SetNbrs({self});
\*      {
      
      \* each node is represented as process and recieve msgs from other processes
      
      \* append happens via mutex process (however, we assume, that on node level, all write access happens as single process, so we don't use it in formal proof)
      \* we don't check here msg delivery fails, since we assume that there is (at least) one non-failed connection between any 2 peers
      \* since nodes exchange with state, we can access state directly here (through "states" variable)      
  
  
 \*           iteration: while (stateSynced = FALSE) {       \* todo use only nodes in edges (like get updates from nodes with direct connection links)              
             
                    \* since each node will process its requests without concurrency, then mutex is used here to simulate this behavior
                   \* lock: await mutex[iterNodes1] = 0;
                   \* mutex[iterNodes1] := 1;
            
            
 \*                   highestKVNode := CHOOSE x \in nbrsNodes : \A y \in nbrsNodes : values[y] <= values[x]; \* the same node can appear over and over for all nodes (like first accurance)
 \*                   highestSignatures := UNION {signatures[s]: s \in { x \in Nodes : values[x] = values[highestKVNode] } };
                    \* filter signatures by highest known value and union them
            
                    \* compare and swap
 \*                   cas: \* todo leave only Q signatures
 \*                   if (values[self] < values[highestKVNode]){
 \*                     appendValue:  values[self] := values[highestKVNode];
 \*                     appendSignature1:  signatures[self] := highestSignatures \union {self}; 
 \*                   } else if (values[self] = values[highestKVNode]){
 \*                      appendSignature2: signatures[self] := highestSignatures \union signatures[self]; 
 \*                   };
                    
                    \*unlock: mutex[iterNodes1] := 0;
                    
                    \* test: values[self] := maxNumber;
                    
                    \* (\A e \in 1..Len(states): states[e].value = 5) /\ (\A e \in 1..Len(states): Cardinality(states[e].signatures) >= Quorum) --todo move to invariants
                    
                    \* todo compare state synced by maxed value. 
                    \* validate: stateSynced := (\A e \in 1..Len(states): states[e].value =< states[iterNodes1].value) /\ 
                    \*validate: stateSynced := (states[self].value = 5) /\ (Cardinality(states[self].signatures) >= Quorum);
                    
                    \*validate: stateSynced := (states[self].value = maxNumber) /\ (Cardinality(states[self].signatures) >= Quorum)
                    
  \*                  validate: stateSynced := (values[self] = maxNumber) /\ (Cardinality(signatures[self]) >= Quorum)                   
  \*            }    
  
  \*         }   
  \*     }
  
}
*********)
\* BEGIN TRANSLATION (chksum(pcal) = "da1d8cb4" /\ chksum(tla) = "c3f39e0a")
\* Process receiverNode at line 56 col 5 changed to receiverNode_
\* Process variable id of process receiverNode at line 59 col 5 changed to id_
VARIABLES states, maxNumber, SenderNodeIdRange, ReceiverNodeIdRange, 
          senderProcs, receiverProcs, chan, pc, msg, id_, m, i, id, nbrsNodes, 
          receiverNode

vars == << states, maxNumber, SenderNodeIdRange, ReceiverNodeIdRange, 
           senderProcs, receiverProcs, chan, pc, msg, id_, m, i, id, 
           nbrsNodes, receiverNode >>

ProcSet == (receiverProcs) \cup (senderProcs)

Init == (* Global variables *)
        /\ states = [s \in 1..Cardinality(Nodes) |-> [value |-> s, signatures |-> {s}]]
        /\ maxNumber = (CHOOSE x \in Nodes : \A y \in Nodes : y <= x)
        /\ SenderNodeIdRange = 100
        /\ ReceiverNodeIdRange = 200
        /\ senderProcs = {x + SenderNodeIdRange: x \in Nodes}
        /\ receiverProcs = {x + ReceiverNodeIdRange: x \in Nodes}
        /\ chan = [n \in (senderProcs \union receiverProcs) |-> <<>>]
        (* Process receiverNode_ *)
        /\ msg = [self \in receiverProcs |-> <<>>]
        /\ id_ = [self \in receiverProcs |-> self - ReceiverNodeIdRange]
        (* Process senderNode *)
        /\ m = [self \in senderProcs |-> <<>>]
        /\ i = [self \in senderProcs |-> 1]
        /\ id = [self \in senderProcs |-> self - SenderNodeIdRange]
        /\ nbrsNodes = [self \in senderProcs |-> SetNbrs({id[self]})]
        /\ receiverNode = [self \in senderProcs |-> ""]
        /\ pc = [self \in ProcSet |-> CASE self \in receiverProcs -> "RA"
                                        [] self \in senderProcs -> "SA"]

RA(self) == /\ pc[self] = "RA"
            /\ pc' = [pc EXCEPT ![self] = "RB"]
            /\ UNCHANGED << states, maxNumber, SenderNodeIdRange, 
                            ReceiverNodeIdRange, senderProcs, receiverProcs, 
                            chan, msg, id_, m, i, id, nbrsNodes, receiverNode >>

RB(self) == /\ pc[self] = "RB"
            /\ Len(chan[self]) > 0
            /\ msg' = [msg EXCEPT ![self] = Head(chan[self])]
            /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
            /\ pc' = [pc EXCEPT ![self] = "RC"]
            /\ UNCHANGED << states, maxNumber, SenderNodeIdRange, 
                            ReceiverNodeIdRange, senderProcs, receiverProcs, 
                            id_, m, i, id, nbrsNodes, receiverNode >>

RC(self) == /\ pc[self] = "RC"
            /\ IF states[id_[self]].value < msg[self].value
                  THEN /\ pc' = [pc EXCEPT ![self] = "RD"]
                  ELSE /\ IF states[id_[self]].value = msg[self].value
                             THEN /\ pc' = [pc EXCEPT ![self] = "RF"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "RG"]
            /\ UNCHANGED << states, maxNumber, SenderNodeIdRange, 
                            ReceiverNodeIdRange, senderProcs, receiverProcs, 
                            chan, msg, id_, m, i, id, nbrsNodes, receiverNode >>

RD(self) == /\ pc[self] = "RD"
            /\ states' = [states EXCEPT ![id_[self]].value = msg[self].value]
            /\ pc' = [pc EXCEPT ![self] = "RE"]
            /\ UNCHANGED << maxNumber, SenderNodeIdRange, ReceiverNodeIdRange, 
                            senderProcs, receiverProcs, chan, msg, id_, m, i, 
                            id, nbrsNodes, receiverNode >>

RE(self) == /\ pc[self] = "RE"
            /\ states' = [states EXCEPT ![id_[self]].signatures = msg[self].signatures \union {id_[self]}]
            /\ pc' = [pc EXCEPT ![self] = "RG"]
            /\ UNCHANGED << maxNumber, SenderNodeIdRange, ReceiverNodeIdRange, 
                            senderProcs, receiverProcs, chan, msg, id_, m, i, 
                            id, nbrsNodes, receiverNode >>

RF(self) == /\ pc[self] = "RF"
            /\ states' = [states EXCEPT ![id_[self]].signatures = msg[self].signatures \union states[id_[self]].signatures]
            /\ pc' = [pc EXCEPT ![self] = "RG"]
            /\ UNCHANGED << maxNumber, SenderNodeIdRange, ReceiverNodeIdRange, 
                            senderProcs, receiverProcs, chan, msg, id_, m, i, 
                            id, nbrsNodes, receiverNode >>

RG(self) == /\ pc[self] = "RG"
            /\ chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)], ([type|-> "Ack"]))]
            /\ pc' = [pc EXCEPT ![self] = "RA"]
            /\ UNCHANGED << states, maxNumber, SenderNodeIdRange, 
                            ReceiverNodeIdRange, senderProcs, receiverProcs, 
                            msg, id_, m, i, id, nbrsNodes, receiverNode >>

receiverNode_(self) == RA(self) \/ RB(self) \/ RC(self) \/ RD(self)
                          \/ RE(self) \/ RF(self) \/ RG(self)

SA(self) == /\ pc[self] = "SA"
            /\ pc' = [pc EXCEPT ![self] = "SC"]
            /\ UNCHANGED << states, maxNumber, SenderNodeIdRange, 
                            ReceiverNodeIdRange, senderProcs, receiverProcs, 
                            chan, msg, id_, m, i, id, nbrsNodes, receiverNode >>

SC(self) == /\ pc[self] = "SC"
            /\ IF i[self] <= Cardinality(nbrsNodes[self])
                  THEN /\ pc' = [pc EXCEPT ![self] = "SD"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "SG"]
            /\ UNCHANGED << states, maxNumber, SenderNodeIdRange, 
                            ReceiverNodeIdRange, senderProcs, receiverProcs, 
                            chan, msg, id_, m, i, id, nbrsNodes, receiverNode >>

SD(self) == /\ pc[self] = "SD"
            /\ chan' = [chan EXCEPT ![(i[self] + ReceiverNodeIdRange)] = Append(chan[(i[self] + ReceiverNodeIdRange)], ([value |-> states[id[self]].value, signatures |-> states[id[self]].signatures, orig |-> SenderNodeIdRange + id[self]]))]
            /\ pc' = [pc EXCEPT ![self] = "SE"]
            /\ UNCHANGED << states, maxNumber, SenderNodeIdRange, 
                            ReceiverNodeIdRange, senderProcs, receiverProcs, 
                            msg, id_, m, i, id, nbrsNodes, receiverNode >>

SE(self) == /\ pc[self] = "SE"
            /\ Len(chan[self]) > 0
            /\ m' = [m EXCEPT ![self] = Head(chan[self])]
            /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
            /\ pc' = [pc EXCEPT ![self] = "SF"]
            /\ UNCHANGED << states, maxNumber, SenderNodeIdRange, 
                            ReceiverNodeIdRange, senderProcs, receiverProcs, 
                            msg, id_, i, id, nbrsNodes, receiverNode >>

SF(self) == /\ pc[self] = "SF"
            /\ i' = [i EXCEPT ![self] = i[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "SC"]
            /\ UNCHANGED << states, maxNumber, SenderNodeIdRange, 
                            ReceiverNodeIdRange, senderProcs, receiverProcs, 
                            chan, msg, id_, m, id, nbrsNodes, receiverNode >>

SG(self) == /\ pc[self] = "SG"
            /\ i' = [i EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "SA"]
            /\ UNCHANGED << states, maxNumber, SenderNodeIdRange, 
                            ReceiverNodeIdRange, senderProcs, receiverProcs, 
                            chan, msg, id_, m, id, nbrsNodes, receiverNode >>

senderNode(self) == SA(self) \/ SC(self) \/ SD(self) \/ SE(self)
                       \/ SF(self) \/ SG(self)

Next == (\E self \in receiverProcs: receiverNode_(self))
           \/ (\E self \in senderProcs: senderNode(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Jul 28 23:21:19 MSK 2022 by zyeve
\* Created Thu Jul 14 21:32:05 MSK 2022 by zyeve
