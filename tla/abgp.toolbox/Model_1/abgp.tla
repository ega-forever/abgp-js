\* 1) consensus is possible when minimal connections links >= quorum (also should include liveness and safety)
\* 2) the sync between nodes is possible even without direct connection
\* 3) no ordering guarantee the same result (through compare-and-swap approach)


\* there should be at least f+1 connections for each node

------------------------------ MODULE abgp ------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANT Nodes, Edges, root, Quorum, Fail, KVPerNode

ASSUME root \in Nodes
         /\ \A e \in Edges : (e \subseteq Nodes)
         

Nbrs(n)  ==  {m \in Nodes : {m,n} \in Edges}
SetNbrs(S)  ==  UNION {Nbrs(n) : n \in S}

RECURSIVE ReachableFrom(_)
  ReachableFrom(S)  ==  LET R == SetNbrs(S)
                        IN  IF R \subseteq S THEN S
                                             ELSE ReachableFrom(R \cup S)

\* all nodes are reachable between each other
ASSUME  ReachableFrom({root}) = Nodes

\* all nodes have enough connection links for quorum
ASSUME \A e \in Edges: (Cardinality(SetNbrs(e)) >= Fail + 1)

ASSUME Quorum > Fail

(*********
--algorithm NoOrderingSync {
  variables states = [s \in 1..Cardinality(Nodes) |-> 0],
  mutex = [s \in 1..Cardinality(Nodes) |-> 0];
  
  procedure safeAppend(index, KV)
  {  
    \*enter:+ await mutex[index] = 0; mutex[index] := 1;
    sc: 
      if (states[index] < KV){
        states[index] := KV;
    };
     \*exit: mutex[index] := 0
  }
  
  
  fair process (node \in Nodes) 
      variables inNodes = Nodes, KVs = KVPerNode;
      {
      
      
        \* compare and swap (CAS)
        \* todo make safe zone (mutex)
        \*  append:
        \*    with (node \in Nodes) {
        \*      call safeAppend(node, KVPerNode[node]);
        \*    }
            
  
           step1: with (node \in inNodes) {       
            with (KVpair \in KVs) {       
            
           \* await mutex[node] = 0; mutex[node] := 1;
            
            if (states[node] < KVpair){
                states[node] := KVpair;
            };
            
           \* mutex[node] := 0;
            
              
            inNodes := inNodes \ {node};     
            KVs := KVs \ {KVpair};                 
            }
           }    
         
         \* append: while (in[self] =< Cardinality(Nodes)) {             
         \*  append1: call safeAppend(in[self], KVPerNode[self]);
         \*  append2: in[self] := in[self] + 1;
           }   
       }
  
}
*********)
\* BEGIN TRANSLATION (chksum(pcal) = "84600cb6" /\ chksum(tla) = "3c79b88b")
CONSTANT defaultInitValue
VARIABLES states, mutex, pc, stack, index, KV, inNodes, KVs

vars == << states, mutex, pc, stack, index, KV, inNodes, KVs >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ states = [s \in 1..Cardinality(Nodes) |-> 0]
        /\ mutex = [s \in 1..Cardinality(Nodes) |-> 0]
        (* Procedure safeAppend *)
        /\ index = [ self \in ProcSet |-> defaultInitValue]
        /\ KV = [ self \in ProcSet |-> defaultInitValue]
        (* Process node *)
        /\ inNodes = [self \in Nodes |-> Nodes]
        /\ KVs = [self \in Nodes |-> KVPerNode]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "step1"]

sc(self) == /\ pc[self] = "sc"
            /\ IF states[index[self]] < KV[self]
                  THEN /\ states' = [states EXCEPT ![index[self]] = KV[self]]
                  ELSE /\ TRUE
                       /\ UNCHANGED states
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << mutex, stack, index, KV, inNodes, KVs >>

safeAppend(self) == sc(self)

step1(self) == /\ pc[self] = "step1"
               /\ \E node \in inNodes[self]:
                    \E KVpair \in KVs[self]:
                      /\ IF states[node] < KVpair
                            THEN /\ states' = [states EXCEPT ![node] = KVpair]
                            ELSE /\ TRUE
                                 /\ UNCHANGED states
                      /\ inNodes' = [inNodes EXCEPT ![self] = inNodes[self] \ {node}]
                      /\ KVs' = [KVs EXCEPT ![self] = KVs[self] \ {KVpair}]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << mutex, stack, index, KV >>

node(self) == step1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: safeAppend(self))
           \/ (\E self \in Nodes: node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Jul 22 19:47:27 MSK 2022 by zyeve
\* Created Thu Jul 14 21:32:05 MSK 2022 by zyeve
