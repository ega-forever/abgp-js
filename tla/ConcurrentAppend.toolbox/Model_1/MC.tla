---- MODULE MC ----
EXTENDS ConcurrentAppend, TLC

\* CONSTANT definitions @modelParameterConstants:0NodesCount
const_1659095149675774000 == 
3
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1659095149676775000 ==
(\A n \in 1..NodesCount: Len(chan) = 0) /\ receiverNodeState.value # 1 => receiverNodeState.value = maxNumber
----
=============================================================================
\* Modification History
\* Created Fri Jul 29 14:45:49 MSK 2022 by zyeve
