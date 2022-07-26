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
  variables states = [s \in 1..Cardinality(Nodes) |-> [value |-> s, signatures |-> {s}]],
  mutex = [s \in 1..Cardinality(Nodes) |-> 0],
  maxNumber = CHOOSE x \in Nodes : \A y \in Nodes : y <= x;
  
  
  
  fair process (node \in Nodes) 
      variables stateSynced = FALSE, node = self, iterNodes1 = 1, highestKVNode = self;
      {
      
      \* each node is represented as process and recieve msgs from other processes
      
      \* append happens via mutex process (however, we assume, that on node level, all write access happens as single process, so we don't use it in formal proof)
      \* we don't check here msg delivery fails, since we assume that there is (at least) one non-failed connection between any 2 peers
      \* since nodes exchange with state, we can access state directly here (through "states" variable)      
  
  
            iteration: while (stateSynced = FALSE) {       \* todo use only nodes in edges (like get updates from nodes with direct connection links)              
             
                    \* since each node will process its requests without concurrency, then mutex is used here to simulate this behavior
                   \* lock: await mutex[iterNodes1] = 0;
                   \* mutex[iterNodes1] := 1;
            
            
                    highestKVNode := CHOOSE x \in Nodes : \A y \in Nodes : states[y].value <= states[x].value;
            
                    \* compare and swap
                    cas:
                    if (states[self].value < states[highestKVNode].value){
                     states[self].value := states[highestKVNode].value;
                    
                    
                        if (Cardinality(states[self].signatures) < Quorum){
                            signatures1:  states[self].signatures := states[self].signatures \union states[highestKVNode].signatures;    
                        }
                    
                    
                    } else if (states[self].value = states[highestKVNode].value){
                            signatures2:  states[self].signatures := states[highestKVNode].signatures \union {iterNodes1};
                    };
                    
                    \*unlock: mutex[iterNodes1] := 0;
                    
                    
                    \* (\A e \in 1..Len(states): states[e].value = 5) /\ (\A e \in 1..Len(states): Cardinality(states[e].signatures) >= Quorum) --todo move to invariants
                    
                    \* todo compare state synced by maxed value. 
                    \* validate: stateSynced := (\A e \in 1..Len(states): states[e].value =< states[iterNodes1].value) /\ 
                    \*validate: stateSynced := (states[self].value = 5) /\ (Cardinality(states[self].signatures) >= Quorum);
                    
                    validate: stateSynced := (states[self].value = maxNumber);
              }    
  
           }   
       }
  
}
*********)
\* BEGIN TRANSLATION (chksum(pcal) = "64a9492a" /\ chksum(tla) = "20c3c791")
\* Process node at line 38 col 8 changed to node_
VARIABLES states, mutex, maxNumber, pc, stateSynced, node, iterNodes1, 
          highestKVNode

vars == << states, mutex, maxNumber, pc, stateSynced, node, iterNodes1, 
           highestKVNode >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ states = [s \in 1..Cardinality(Nodes) |-> [value |-> s, signatures |-> {s}]]
        /\ mutex = [s \in 1..Cardinality(Nodes) |-> 0]
        /\ maxNumber = (CHOOSE x \in Nodes : \A y \in Nodes : y <= x)
        (* Process node_ *)
        /\ stateSynced = [self \in Nodes |-> FALSE]
        /\ node = [self \in Nodes |-> self]
        /\ iterNodes1 = [self \in Nodes |-> 1]
        /\ highestKVNode = [self \in Nodes |-> self]
        /\ pc = [self \in ProcSet |-> "iteration"]

iteration(self) == /\ pc[self] = "iteration"
                   /\ IF stateSynced[self] = FALSE
                         THEN /\ highestKVNode' = [highestKVNode EXCEPT ![self] = CHOOSE x \in Nodes : \A y \in Nodes : states[y].value <= states[x].value]
                              /\ pc' = [pc EXCEPT ![self] = "cas"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                              /\ UNCHANGED highestKVNode
                   /\ UNCHANGED << states, mutex, maxNumber, stateSynced, node, 
                                   iterNodes1 >>

cas(self) == /\ pc[self] = "cas"
             /\ IF states[self].value < states[highestKVNode[self]].value
                   THEN /\ states' = [states EXCEPT ![self].value = states[highestKVNode[self]].value]
                        /\ IF Cardinality(states'[self].signatures) < Quorum
                              THEN /\ pc' = [pc EXCEPT ![self] = "signatures1"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "validate"]
                   ELSE /\ IF states[self].value = states[highestKVNode[self]].value
                              THEN /\ pc' = [pc EXCEPT ![self] = "signatures2"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "validate"]
                        /\ UNCHANGED states
             /\ UNCHANGED << mutex, maxNumber, stateSynced, node, iterNodes1, 
                             highestKVNode >>

signatures1(self) == /\ pc[self] = "signatures1"
                     /\ states' = [states EXCEPT ![self].signatures = states[self].signatures \union states[highestKVNode[self]].signatures]
                     /\ pc' = [pc EXCEPT ![self] = "validate"]
                     /\ UNCHANGED << mutex, maxNumber, stateSynced, node, 
                                     iterNodes1, highestKVNode >>

signatures2(self) == /\ pc[self] = "signatures2"
                     /\ states' = [states EXCEPT ![self].signatures = states[highestKVNode[self]].signatures \union {iterNodes1[self]}]
                     /\ pc' = [pc EXCEPT ![self] = "validate"]
                     /\ UNCHANGED << mutex, maxNumber, stateSynced, node, 
                                     iterNodes1, highestKVNode >>

validate(self) == /\ pc[self] = "validate"
                  /\ stateSynced' = [stateSynced EXCEPT ![self] = (states[self].value = maxNumber)]
                  /\ pc' = [pc EXCEPT ![self] = "iteration"]
                  /\ UNCHANGED << states, mutex, maxNumber, node, iterNodes1, 
                                  highestKVNode >>

node_(self) == iteration(self) \/ cas(self) \/ signatures1(self)
                  \/ signatures2(self) \/ validate(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: node_(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node_(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Jul 26 22:45:20 MSK 2022 by zyeve
\* Created Thu Jul 14 21:32:05 MSK 2022 by zyeve
