---- MODULE MC ----
EXTENDS abgp, TLC

\* CONSTANT definitions @modelParameterConstants:0Edges
const_165873150397322000 == 
{ {1,2}, {1,3}, {1,5}, {2,3}, {2,5}, {3,5}, {4,5}, {4,2}, {4,3} }
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_165873150397323000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Fail
const_165873150397324000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Nodes
const_165873150397325000 == 
{1,2,3,4,5}
----

=============================================================================
\* Modification History
\* Created Mon Jul 25 09:45:03 MSK 2022 by zyeve
