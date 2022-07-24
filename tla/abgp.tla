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
ASSUME \A e \in Edges: (Cardinality(SetNbrs(e)) >= Fail + 1)

ASSUME Quorum > Fail

(*********
--algorithm NoOrderingSync {
   \*variables states = {[value |-> s, signatures |-> {s}]: s \in Nodes},
   
   variables states = [s \in 1..Cardinality(Nodes) |-> [value |-> s, signatures |-> {s}]],
   
   
  \* [s \in 1..Cardinality(Nodes): [value |-> s, signatures |-> {s}]],
  
  \*{ x * x : x \in 1..4 } { [a |-> 1, b |-> 2], [a |-> 1, b |-> 3] }
 \* variables states = {[s \in 1..Cardinality(Nodes) |-> [value |-> s, signatures |-> {s}]]},
  
  mutex = [s \in 1..Cardinality(Nodes) |-> 0];
  
  
  fair process (node \in Nodes) 
      variables stateSynced = FALSE, iterNodes1 = 1, iterNodes2 = 1, maxValue = -1;
      {
      
      \* each node is represented as process and recieve msgs from other processes
      
      \* append happens via mutex process (however, we assume, that on node level, all write access happens as single process, so we don't use it in formal proof)
      \* we don't check here msg delivery fails, since we assume that there is (at least) one non-failed connection between any 2 peers
      \* since nodes exchange with state, we can access state directly here (through "states" variable)
      
      
      \* we have to implement signautes in order to validate, that concurrency odn't ovveride signatures!
      
        \* compare and swap (CAS)
        \* todo make safe zone (mutex)
        \*  append:
        \*    with (node \in Nodes) {
        \*      call safeAppend(node, KVPerNode[node]);
        \*    }
            
  
  
  \* todo replace with -> while (do while until all records will contain signtures = quorum and have the same value) + insert distributed lock to prevent extra signatures
  
           step1: while (stateSynced = FALSE) {
            step2: while (iterNodes1 <= Cardinality(Nodes)) {                   
             step3:  while (iterNodes2 <= Cardinality(Nodes)) {              
            
                    if (states[iterNodes1].value < states[iterNodes2].value){
                        states[iterNodes1].value := states[iterNodes2].value;
                    };
                    
                     
                    stateSynced := \A e \in 1..Len(states): states[e].value =< states[iterNodes1].value;
                    \*stateSynced := Cardinality({x \in states: states[x].value > states[iterNodes1].value }) = 0;
                    iterNodes1 := iterNodes1 + 1;
                    iterNodes2 := iterNodes2 + 1;                
                }
            }    
           }
  
           }   
       }
  
}
*********)
\* BEGIN TRANSLATION (chksum(pcal) = "23d2bdc3" /\ chksum(tla) = "1a84624a")
VARIABLES states, mutex, pc, stateSynced, iterNodes1, iterNodes2, maxValue

vars == << states, mutex, pc, stateSynced, iterNodes1, iterNodes2, maxValue
        >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ states = [s \in 1..Cardinality(Nodes) |-> [value |-> s, signatures |-> {s}]]
        /\ mutex = [s \in 1..Cardinality(Nodes) |-> 0]
        (* Process node *)
        /\ stateSynced = [self \in Nodes |-> FALSE]
        /\ iterNodes1 = [self \in Nodes |-> 1]
        /\ iterNodes2 = [self \in Nodes |-> 1]
        /\ maxValue = [self \in Nodes |-> -1]
        /\ pc = [self \in ProcSet |-> "step1"]

step1(self) == /\ pc[self] = "step1"
               /\ IF stateSynced[self] = FALSE
                     THEN /\ pc' = [pc EXCEPT ![self] = "step2"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << states, mutex, stateSynced, iterNodes1, 
                               iterNodes2, maxValue >>

step2(self) == /\ pc[self] = "step2"
               /\ IF iterNodes1[self] <= Cardinality(Nodes)
                     THEN /\ pc' = [pc EXCEPT ![self] = "step3"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "step1"]
               /\ UNCHANGED << states, mutex, stateSynced, iterNodes1, 
                               iterNodes2, maxValue >>

step3(self) == /\ pc[self] = "step3"
               /\ IF iterNodes2[self] <= Cardinality(Nodes)
                     THEN /\ IF states[iterNodes1[self]].value < states[iterNodes2[self]].value
                                THEN /\ states' = [states EXCEPT ![iterNodes1[self]].value = states[iterNodes2[self]].value]
                                ELSE /\ TRUE
                                     /\ UNCHANGED states
                          /\ stateSynced' = [stateSynced EXCEPT ![self] = \A e \in 1..Len(states'): states'[e].value =< states'[iterNodes1[self]].value]
                          /\ iterNodes1' = [iterNodes1 EXCEPT ![self] = iterNodes1[self] + 1]
                          /\ iterNodes2' = [iterNodes2 EXCEPT ![self] = iterNodes2[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "step3"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "step2"]
                          /\ UNCHANGED << states, stateSynced, iterNodes1, 
                                          iterNodes2 >>
               /\ UNCHANGED << mutex, maxValue >>

node(self) == step1(self) \/ step2(self) \/ step3(self)

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
\* Last modified Sun Jul 24 21:32:54 MSK 2022 by zyeve
\* Last modified Fri Jul 22 19:47:27 MSK 2022 by zyeve
\* Created Thu Jul 14 21:32:05 MSK 2022 by zyeve
