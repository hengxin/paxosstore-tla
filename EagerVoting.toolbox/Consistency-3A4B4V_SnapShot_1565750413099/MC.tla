---- MODULE MC ----
EXTENDS EagerVoting, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3, v4
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Value
const_1565750390100206000 == 
{v1, v2, v3, v4}
----

\* MV CONSTANT definitions Acceptor
const_1565750390100207000 == 
{a1, a2, a3}
----

\* SYMMETRY definition
symm_1565750390100208000 == 
Permutations(const_1565750390100206000) \union Permutations(const_1565750390100207000)
----

\* CONSTANT definitions @modelParameterConstants:0Quorum
const_1565750390100209000 == 
{{a1, a2}, {a1, a3}, {a2, a3}, {a1, a2, a3}}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1565750390100210000 ==
0 .. 3
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 10:39:50 CST 2019 by hengxin
