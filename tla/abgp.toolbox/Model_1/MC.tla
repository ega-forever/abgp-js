---- MODULE MC ----
EXTENDS abgp, TLC

\* CONSTANT definitions @modelParameterConstants:0Edges
const_1658944603550271000 == 
{ {1,2}, {1,3}, {1,5}, {2,3}, {2,5}, {3,5}, {4,5}, {4,2}, {4,3} }
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1658944603550272000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Fail
const_1658944603550273000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Nodes
const_1658944603550274000 == 
{1,2,3,4,5}
----

=============================================================================
\* Modification History
\* Created Wed Jul 27 20:56:43 MSK 2022 by zyeve
