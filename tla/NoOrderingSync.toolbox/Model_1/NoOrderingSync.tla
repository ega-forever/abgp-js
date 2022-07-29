\* Modification History
\* Last modified Fri Jul 29 13:47:04 MSK 2022 by zyeve
\* Created Fri Jul 29 09:18:14 MSK 2022 by zyeve


\* 1) consensus is possible when minimal connections links >= quorum (also should include liveness and safety)
\* 2) the sync between nodes is possible even without direct connection
\* 3) no ordering guarantee the same result (through compare-and-swap approach)


\* there should be at least f+1 connections for each node

--------------------------- MODULE NoOrderingSync ---------------------------
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
--fair algorithm NoOrderingSync { 
  variables 
  states = [s \in 1..Cardinality(Nodes) |-> [value |-> s, signatures |-> {s}]],
  maxNumber = CHOOSE x \in Nodes : \A y \in Nodes : y <= x; \* move to invariants
  
  
  
  fair process("no_ordering" = 1){
  
  NA: while(~(\A e \in Nodes: Cardinality(states[e].signatures) >= Quorum)) {
  NB:   with (senderNodeI \in Nodes) {              
          with (receiverNodeI \in SetNbrs({senderNodeI})) {       
            if (states[receiverNodeI].value < states[senderNodeI].value){
                  states[receiverNodeI] := [value |-> states[receiverNodeI].value, signatures |-> (states[senderNodeI].signatures \union {receiverNodeI})];
            } else if (states[receiverNodeI].value = states[senderNodeI].value){
                  states[receiverNodeI].signatures := states[senderNodeI].signatures \union states[receiverNodeI].signatures; 
            };         
       };
                                 
     };
     };
     
     
  NC: assert (\A e \in Nodes: states[e].value = maxNumber) /\ (\A e \in Nodes: Cardinality(states[e].signatures) >= Quorum);                                        
    
  
  
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
\* BEGIN TRANSLATION (chksum(pcal) = "969cddc8" /\ chksum(tla) = "44faec1d")
VARIABLES states, maxNumber, pc

vars == << states, maxNumber, pc >>

ProcSet == {1}

Init == (* Global variables *)
        /\ states = [s \in 1..Cardinality(Nodes) |-> [value |-> s, signatures |-> {s}]]
        /\ maxNumber = (CHOOSE x \in Nodes : \A y \in Nodes : y <= x)
        /\ pc = [self \in ProcSet |-> "NA"]

NA == /\ pc[1] = "NA"
      /\ IF ~(\A e \in Nodes: Cardinality(states[e].signatures) >= Quorum)
            THEN /\ pc' = [pc EXCEPT ![1] = "NB"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "NC"]
      /\ UNCHANGED << states, maxNumber >>

NB == /\ pc[1] = "NB"
      /\ \E senderNodeI \in Nodes:
           \E receiverNodeI \in SetNbrs({senderNodeI}):
             IF states[receiverNodeI].value < states[senderNodeI].value
                THEN /\ states' = [states EXCEPT ![receiverNodeI] = [value |-> states[receiverNodeI].value, signatures |-> (states[senderNodeI].signatures \union {receiverNodeI})]]
                ELSE /\ IF states[receiverNodeI].value = states[senderNodeI].value
                           THEN /\ states' = [states EXCEPT ![receiverNodeI].signatures = states[senderNodeI].signatures \union states[receiverNodeI].signatures]
                           ELSE /\ TRUE
                                /\ UNCHANGED states
      /\ pc' = [pc EXCEPT ![1] = "NA"]
      /\ UNCHANGED maxNumber

NC == /\ pc[1] = "NC"
      /\ Assert((\A e \in Nodes: states[e].value = maxNumber) /\ (\A e \in Nodes: Cardinality(states[e].signatures) >= Quorum), 
                "Failure of assertion at line 59, column 7.")
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << states, maxNumber >>

no_ordering == NA \/ NB \/ NC

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == no_ordering
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(no_ordering)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Created Thu Jul 14 21:32:05 MSK 2022 by zyeve
