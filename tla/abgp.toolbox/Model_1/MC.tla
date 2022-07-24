---- MODULE MC ----
EXTENDS abgp, TLC

\* CONSTANT definitions @modelParameterConstants:0Edges
const_1658687578769787000 == 
{ {1,2}, {2,3}, {3,5}, {4,5} }
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1658687578769788000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Fail
const_1658687578769789000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Nodes
const_1658687578769790000 == 
{1,2,3,4,5}
----

=============================================================================
\* Modification History
\* Created Sun Jul 24 21:32:58 MSK 2022 by zyeve
