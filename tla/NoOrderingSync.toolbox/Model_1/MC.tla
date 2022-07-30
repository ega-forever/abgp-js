---- MODULE MC ----
EXTENDS NoOrderingSync, TLC

\* CONSTANT definitions @modelParameterConstants:0Edges
const_1659194384334790000 == 
{ {1,2}, {1,3}, {1,5}, {2,3}, {2,5}, {3,5}, {4,5}, {4,2}, {4,3} }
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1659194384334791000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Fail
const_1659194384334792000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Nodes
const_1659194384334793000 == 
{1, 2, 3, 4, 5}
----

=============================================================================
\* Modification History
\* Created Sat Jul 30 18:19:44 MSK 2022 by zyeve
