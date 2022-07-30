---- MODULE MC ----
EXTENDS ConcurrentAppend, TLC

\* CONSTANT definitions @modelParameterConstants:0NodesCount
const_1659194561743794000 == 
3
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1659194561744795000 ==
(\A n \in 1..NodesCount: Len(chan) = 0) /\ receiverNodeState.value # 1 => receiverNodeState.value = (CHOOSE x \in 1..NodesCount : \A y \in 1..NodesCount : y <= x)
----
=============================================================================
\* Modification History
\* Created Sat Jul 30 18:22:41 MSK 2022 by zyeve
