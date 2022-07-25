---- MODULE MC ----
EXTENDS abgp, TLC

\* CONSTANT definitions @modelParameterConstants:0Edges
const_165877617109067000 == 
{ {1,2}, {1,3}, {1,5}, {2,3}, {2,5}, {3,5}, {4,5}, {4,2}, {4,3} }
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_165877617109068000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Fail
const_165877617109069000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Nodes
const_165877617109070000 == 
{1,2,3,4,5}
----

=============================================================================
\* Modification History
\* Created Mon Jul 25 22:09:31 MSK 2022 by zyeve
