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
  mutex = [s \in 1..Cardinality(Nodes) |-> 0];
  
  
  
  fair process (node \in Nodes) 
      variables stateSynced = FALSE, iterNodes1 = 1, iterNodes2 = 1;
      {
      
      \* each node is represented as process and recieve msgs from other processes
      
      \* append happens via mutex process (however, we assume, that on node level, all write access happens as single process, so we don't use it in formal proof)
      \* we don't check here msg delivery fails, since we assume that there is (at least) one non-failed connection between any 2 peers
      \* since nodes exchange with state, we can access state directly here (through "states" variable)      
  
           step1: while (stateSynced = FALSE) {
            step2: while (iterNodes1 <= Cardinality(Nodes)) {                     
             step3: while (iterNodes2 <= Cardinality(Nodes)) {                           
             
                    \* since each node will process its requests without concurrency, then mutex is used here to simulate this behavior
                    lock: await mutex[iterNodes1] = 0;
                    mutex[iterNodes1] := 1;
            
                    \* compare and swap
                    if (states[iterNodes1].value < states[iterNodes2].value){
                    cas: states[iterNodes1].value := states[iterNodes2].value;
                    
                    
                        if (Cardinality(states[iterNodes1].signatures) < Quorum){
                            signatures1:  states[iterNodes1].signatures := states[iterNodes1].signatures \union states[iterNodes2].signatures;    
                        }
                    
                    
                    } else if (states[iterNodes1].value = states[iterNodes2].value){
                            signatures2:  states[iterNodes1].signatures := states[iterNodes2].signatures \union {iterNodes1};
                    };
                    
                    unlock: mutex[iterNodes1] := 0;
                    
                    \* todo compare state synced by maxed value. 
                    \* validate: stateSynced := (\A e \in 1..Len(states): states[e].value =< states[iterNodes1].value) /\ 
                    validate: stateSynced := (\A e \in 1..Len(states): states[e].value = 5) /\ 
                     (\A e \in 1..Len(states): Cardinality(states[e].signatures) >= Quorum);
                    iterNodes2 := iterNodes2 + 1;                
                };
                iterNodes1 := iterNodes1 + 1;
                iterNodes2 := 1
            }    
           }
  
           }   
       }
  
}
*********)
\* BEGIN TRANSLATION (chksum(pcal) = "c4f20b4e" /\ chksum(tla) = "ae49712c")
VARIABLES states, mutex, pc, stateSynced, iterNodes1, iterNodes2

vars == << states, mutex, pc, stateSynced, iterNodes1, iterNodes2 >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ states = [s \in 1..Cardinality(Nodes) |-> [value |-> s, signatures |-> {s}]]
        /\ mutex = [s \in 1..Cardinality(Nodes) |-> 0]
        (* Process node *)
        /\ stateSynced = [self \in Nodes |-> FALSE]
        /\ iterNodes1 = [self \in Nodes |-> 1]
        /\ iterNodes2 = [self \in Nodes |-> 1]
        /\ pc = [self \in ProcSet |-> "step1"]

step1(self) == /\ pc[self] = "step1"
               /\ IF stateSynced[self] = FALSE
                     THEN /\ pc' = [pc EXCEPT ![self] = "step2"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << states, mutex, stateSynced, iterNodes1, 
                               iterNodes2 >>

step2(self) == /\ pc[self] = "step2"
               /\ IF iterNodes1[self] <= Cardinality(Nodes)
                     THEN /\ pc' = [pc EXCEPT ![self] = "step3"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "step1"]
               /\ UNCHANGED << states, mutex, stateSynced, iterNodes1, 
                               iterNodes2 >>

step3(self) == /\ pc[self] = "step3"
               /\ IF iterNodes2[self] <= Cardinality(Nodes)
                     THEN /\ pc' = [pc EXCEPT ![self] = "lock"]
                          /\ UNCHANGED << iterNodes1, iterNodes2 >>
                     ELSE /\ iterNodes1' = [iterNodes1 EXCEPT ![self] = iterNodes1[self] + 1]
                          /\ iterNodes2' = [iterNodes2 EXCEPT ![self] = 1]
                          /\ pc' = [pc EXCEPT ![self] = "step2"]
               /\ UNCHANGED << states, mutex, stateSynced >>

lock(self) == /\ pc[self] = "lock"
              /\ mutex[iterNodes1[self]] = 0
              /\ mutex' = [mutex EXCEPT ![iterNodes1[self]] = 1]
              /\ IF states[iterNodes1[self]].value < states[iterNodes2[self]].value
                    THEN /\ pc' = [pc EXCEPT ![self] = "cas"]
                    ELSE /\ IF states[iterNodes1[self]].value = states[iterNodes2[self]].value
                               THEN /\ pc' = [pc EXCEPT ![self] = "signatures2"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "unlock"]
              /\ UNCHANGED << states, stateSynced, iterNodes1, iterNodes2 >>

cas(self) == /\ pc[self] = "cas"
             /\ states' = [states EXCEPT ![iterNodes1[self]].value = states[iterNodes2[self]].value]
             /\ IF Cardinality(states'[iterNodes1[self]].signatures) < Quorum
                   THEN /\ pc' = [pc EXCEPT ![self] = "signatures1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "unlock"]
             /\ UNCHANGED << mutex, stateSynced, iterNodes1, iterNodes2 >>

signatures1(self) == /\ pc[self] = "signatures1"
                     /\ states' = [states EXCEPT ![iterNodes1[self]].signatures = states[iterNodes1[self]].signatures \union states[iterNodes2[self]].signatures]
                     /\ pc' = [pc EXCEPT ![self] = "unlock"]
                     /\ UNCHANGED << mutex, stateSynced, iterNodes1, 
                                     iterNodes2 >>

signatures2(self) == /\ pc[self] = "signatures2"
                     /\ states' = [states EXCEPT ![iterNodes1[self]].signatures = states[iterNodes2[self]].signatures \union {iterNodes1[self]}]
                     /\ pc' = [pc EXCEPT ![self] = "unlock"]
                     /\ UNCHANGED << mutex, stateSynced, iterNodes1, 
                                     iterNodes2 >>

unlock(self) == /\ pc[self] = "unlock"
                /\ mutex' = [mutex EXCEPT ![iterNodes1[self]] = 0]
                /\ pc' = [pc EXCEPT ![self] = "validate"]
                /\ UNCHANGED << states, stateSynced, iterNodes1, iterNodes2 >>

validate(self) == /\ pc[self] = "validate"
                  /\ stateSynced' = [stateSynced EXCEPT ![self] =                         (\A e \in 1..Len(states): states[e].value = 5) /\
                                                                  (\A e \in 1..Len(states): Cardinality(states[e].signatures) >= Quorum)]
                  /\ iterNodes2' = [iterNodes2 EXCEPT ![self] = iterNodes2[self] + 1]
                  /\ pc' = [pc EXCEPT ![self] = "step3"]
                  /\ UNCHANGED << states, mutex, iterNodes1 >>

node(self) == step1(self) \/ step2(self) \/ step3(self) \/ lock(self)
                 \/ cas(self) \/ signatures1(self) \/ signatures2(self)
                 \/ unlock(self) \/ validate(self)

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
\* Last modified Mon Jul 25 22:09:16 MSK 2022 by zyeve
\* Last modified Fri Jul 22 19:47:27 MSK 2022 by zyeve
\* Created Thu Jul 14 21:32:05 MSK 2022 by zyeve
