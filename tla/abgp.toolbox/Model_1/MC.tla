---- MODULE MC ----
EXTENDS abgp, TLC

\* CONSTANT definitions @modelParameterConstants:0Edges
const_1659040199332653000 == 
{ {1,2}, {1,3}, {1,5}, {2,3}, {2,5}, {3,5}, {4,5}, {4,2}, {4,3} }
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1659040199332654000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Fail
const_1659040199332655000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Nodes
const_1659040199332656000 == 
{1,2,3,4,5}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1659040199333657000 ==
(\A e \in 1..Cardinality(Nodes): states[e].value = maxNumber) => (\A p \in Nodes: Cardinality(states[p].signatures) >= Quorum)
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1659040199333658000 ==
(\E e \in 1..Cardinality(Nodes): states[e].value = maxNumber)
----
=============================================================================
\* Modification History
\* Created Thu Jul 28 23:29:59 MSK 2022 by zyeve
