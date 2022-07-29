\* Modification History
\* Last modified Fri Jul 29 13:47:46 MSK 2022 by zyeve
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
