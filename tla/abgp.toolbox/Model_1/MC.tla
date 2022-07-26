---- MODULE MC ----
EXTENDS abgp, TLC

\* CONSTANT definitions @modelParameterConstants:0Edges
const_1658864722998186000 == 
{ {1,2}, {1,3}, {1,5}, {2,3}, {2,5}, {3,5}, {4,5}, {4,2}, {4,3} }
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1658864722998187000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Fail
const_1658864722998188000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Nodes
const_1658864722998189000 == 
{1,2,3,4,5}
----

=============================================================================
\* Modification History
\* Created Tue Jul 26 22:45:22 MSK 2022 by zyeve
