---- MODULE MC ----
EXTENDS abgp, TLC

\* CONSTANT definitions @modelParameterConstants:0root
const_1658508582598644000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:1Edges
const_1658508582598645000 == 
{ {1,2}, {2,3}, {3,5}, {4,5} }
----

\* CONSTANT definitions @modelParameterConstants:3Quorum
const_1658508582598646000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4Fail
const_1658508582598647000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:5Nodes
const_1658508582598648000 == 
{1,2,3,4,5}
----

\* CONSTANT definitions @modelParameterConstants:6KVPerNode
const_1658508582598649000 == 
{4, 7, 5, 3, 8}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1658508582599650000 ==
(\E p \in 1..5: (Cardinality(inNodes[p]) > 0)) \/ 



(\A p \in 1..5: (states[p] = 8 /\ pc[p] = "Done"))
----
=============================================================================
\* Modification History
\* Created Fri Jul 22 19:49:42 MSK 2022 by zyeve
