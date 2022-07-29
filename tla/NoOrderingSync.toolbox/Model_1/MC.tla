---- MODULE MC ----
EXTENDS NoOrderingSync, TLC

\* CONSTANT definitions @modelParameterConstants:0Edges
const_1659091628332755000 == 
{ {1,2}, {1,3}, {1,5}, {2,3}, {2,5}, {3,5}, {4,5}, {4,2}, {4,3} }
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1659091628332756000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Fail
const_1659091628332757000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Nodes
const_1659091628332758000 == 
{1, 2, 3, 4, 5}
----

=============================================================================
\* Modification History
\* Created Fri Jul 29 13:47:08 MSK 2022 by zyeve
