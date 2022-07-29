---- MODULE MC ----
EXTENDS abgp, TLC

\* CONSTANT definitions @modelParameterConstants:0Edges
const_1659070936976665000 == 
{ {1,2}, {1,3}, {1,5}, {2,3}, {2,5}, {3,5}, {4,5}, {4,2}, {4,3} }
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1659070936976666000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Fail
const_1659070936976667000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Nodes
const_1659070936976668000 == 
{1,2,3,4,5}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1659070936976669000 ==
(\E e \in 1..Cardinality(Nodes): states[e].value = maxNumber)
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1659070936976670000 ==
(\A p \in Nodes: Cardinality(states[p].signatures) >= Quorum) => (\A e \in 1..Cardinality(Nodes): states[e].value = maxNumber)
----
=============================================================================
\* Modification History
\* Created Fri Jul 29 08:02:16 MSK 2022 by zyeve
