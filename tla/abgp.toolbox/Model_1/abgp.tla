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
      variables stateSynced = FALSE, highestKVNode = self, highestSignatures = {};
      {
      
      \* each node is represented as process and recieve msgs from other processes
      
      \* append happens via mutex process (however, we assume, that on node level, all write access happens as single process, so we don't use it in formal proof)
      \* we don't check here msg delivery fails, since we assume that there is (at least) one non-failed connection between any 2 peers
      \* since nodes exchange with state, we can access state directly here (through "states" variable)      
  
  
            iteration: while (stateSynced = FALSE) {       \* todo use only nodes in edges (like get updates from nodes with direct connection links)              
             
                    \* since each node will process its requests without concurrency, then mutex is used here to simulate this behavior
                   \* lock: await mutex[iterNodes1] = 0;
                   \* mutex[iterNodes1] := 1;
            
            
                    highestKVNode := CHOOSE x \in Nodes : \A y \in Nodes : states[y].value <= states[x].value; \* the same node can appear over and over for all nodes (like first accurance)
                    highestSignatures := UNION {states[s].signatures: s \in { x \in Nodes : states[x].value = states[highestKVNode].value } };
                    \* filter signatures by highest known value and union them
            
                    \* compare and swap
                    cas: \* todo leave only Q signatures
                    if (states[self].value < states[highestKVNode].value){
                     states[self].value := states[highestKVNode].value;
                     signatures1:  states[self].signatures := (highestSignatures \union {self});
                    } else if (states[self].value = states[highestKVNode].value){
                      signatures2:  states[self].signatures := (states[self].signatures \union highestSignatures);
                    };
                    
                    \*unlock: mutex[iterNodes1] := 0;
                    
                    test: states[self].value := maxNumber;
                    
                    \* (\A e \in 1..Len(states): states[e].value = 5) /\ (\A e \in 1..Len(states): Cardinality(states[e].signatures) >= Quorum) --todo move to invariants
                    
                    \* todo compare state synced by maxed value. 
                    \* validate: stateSynced := (\A e \in 1..Len(states): states[e].value =< states[iterNodes1].value) /\ 
                    \*validate: stateSynced := (states[self].value = 5) /\ (Cardinality(states[self].signatures) >= Quorum);
                    
                    \*validate: stateSynced := (states[self].value = maxNumber) /\ (Cardinality(states[self].signatures) >= Quorum)
                    
                    validate: stateSynced := (\A e \in 1..Len(states): states[e].value = maxNumber);                    
              }    
  
           }   
       }
  
}
*********)
\* BEGIN TRANSLATION (chksum(pcal) = "bc73f02a" /\ chksum(tla) = "c7adc0e4")
VARIABLES states, mutex, maxNumber, pc, stateSynced, highestKVNode, 
          highestSignatures

vars == << states, mutex, maxNumber, pc, stateSynced, highestKVNode, 
           highestSignatures >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ states = [s \in 1..Cardinality(Nodes) |-> [value |-> s, signatures |-> {s}]]
        /\ mutex = [s \in 1..Cardinality(Nodes) |-> 0]
        /\ maxNumber = (CHOOSE x \in Nodes : \A y \in Nodes : y <= x)
        (* Process node *)
        /\ stateSynced = [self \in Nodes |-> FALSE]
        /\ highestKVNode = [self \in Nodes |-> self]
        /\ highestSignatures = [self \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> "iteration"]

iteration(self) == /\ pc[self] = "iteration"
                   /\ IF stateSynced[self] = FALSE
                         THEN /\ highestKVNode' = [highestKVNode EXCEPT ![self] = CHOOSE x \in Nodes : \A y \in Nodes : states[y].value <= states[x].value]
                              /\ highestSignatures' = [highestSignatures EXCEPT ![self] = UNION {states[s].signatures: s \in { x \in Nodes : states[x].value = states[highestKVNode'[self]].value } }]
                              /\ pc' = [pc EXCEPT ![self] = "cas"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                              /\ UNCHANGED << highestKVNode, highestSignatures >>
                   /\ UNCHANGED << states, mutex, maxNumber, stateSynced >>

cas(self) == /\ pc[self] = "cas"
             /\ IF states[self].value < states[highestKVNode[self]].value
                   THEN /\ states' = [states EXCEPT ![self].value = states[highestKVNode[self]].value]
                        /\ pc' = [pc EXCEPT ![self] = "signatures1"]
                   ELSE /\ IF states[self].value = states[highestKVNode[self]].value
                              THEN /\ pc' = [pc EXCEPT ![self] = "signatures2"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "test"]
                        /\ UNCHANGED states
             /\ UNCHANGED << mutex, maxNumber, stateSynced, highestKVNode, 
                             highestSignatures >>

signatures1(self) == /\ pc[self] = "signatures1"
                     /\ states' = [states EXCEPT ![self].signatures = (highestSignatures[self] \union {self})]
                     /\ pc' = [pc EXCEPT ![self] = "test"]
                     /\ UNCHANGED << mutex, maxNumber, stateSynced, 
                                     highestKVNode, highestSignatures >>

signatures2(self) == /\ pc[self] = "signatures2"
                     /\ states' = [states EXCEPT ![self].signatures = (states[self].signatures \union highestSignatures[self])]
                     /\ pc' = [pc EXCEPT ![self] = "test"]
                     /\ UNCHANGED << mutex, maxNumber, stateSynced, 
                                     highestKVNode, highestSignatures >>

test(self) == /\ pc[self] = "test"
              /\ states' = [states EXCEPT ![self].value = maxNumber]
              /\ pc' = [pc EXCEPT ![self] = "validate"]
              /\ UNCHANGED << mutex, maxNumber, stateSynced, highestKVNode, 
                              highestSignatures >>

validate(self) == /\ pc[self] = "validate"
                  /\ stateSynced' = [stateSynced EXCEPT ![self] = (\A e \in 1..Len(states): states[e].value = maxNumber)]
                  /\ pc' = [pc EXCEPT ![self] = "iteration"]
                  /\ UNCHANGED << states, mutex, maxNumber, highestKVNode, 
                                  highestSignatures >>

node(self) == iteration(self) \/ cas(self) \/ signatures1(self)
                 \/ signatures2(self) \/ test(self) \/ validate(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Jul 27 20:56:39 MSK 2022 by zyeve
\* Created Thu Jul 14 21:32:05 MSK 2022 by zyeve
