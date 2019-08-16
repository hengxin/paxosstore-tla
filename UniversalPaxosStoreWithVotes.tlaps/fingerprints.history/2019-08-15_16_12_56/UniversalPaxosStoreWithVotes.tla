-------------------- MODULE UniversalPaxosStoreWithVotes --------------------
(*
Extend UniversalPaxosStore with an explicit record of votes
that have been accepted by participants.
This is used to demonstrate that UniversalPaxosStore refines EagerVoting.
*)
EXTENDS UniversalPaxosStore, TLAPS
-----------------------------------------------------------------------------
VARIABLE votes

TypeOKV ==
    /\ TypeOK
    /\ votes \in [Participant -> SUBSET (Ballot \X Value)]
-----------------------------------------------------------------------------
InitV ==
    /\ Init
    /\ votes = [p \in Participant |-> {}]
    
PrepareV(p, b) ==
    /\ Prepare(p, b)
    /\ UNCHANGED votes

UpdateStateV(q, p, pp) ==
    /\ UpdateState(q, p, pp)
    /\ IF state[q][q].maxBal <= pp.maxVBal /\ pp.maxVBal # -1 \* accept
       THEN votes' = [votes EXCEPT ![q] = @ \cup {<<pp.maxVBal, pp.maxVVal>>}]
       ELSE UNCHANGED votes

OnMessageV(q) == 
    \E m \in msgs : 
        /\ q \in m.to
        /\ LET p == m.from
           IN  UpdateStateV(q, p, m.state[p]) \* replacing UpdateState
        /\ IF \/ m.state[q].maxBal < state'[q][q].maxBal
              \/ m.state[q].maxVBal < state'[q][q].maxVBal
           THEN Send([from |-> q, to |-> {m.from}, state |-> state'[q]]) 
           ELSE UNCHANGED msgs

AcceptV(p, b, v) ==
    /\ Accept(p, b, v)
    /\ votes' = [votes EXCEPT ![p] = @ \cup {<<b, v>>}] \* accept
-----------------------------------------------------------------------------
NextV == \E p \in Participant : \/ OnMessageV(p)
                                \/ \E b \in Ballot : \/ PrepareV(p, b)
                                                     \/ \E v \in Value : AcceptV(p, b, v)
SpecV == InitV /\ [][NextV]_<<vars, votes>>
-----------------------------------------------------------------------------
THEOREM Invariant == SpecV => []TypeOKV
  OMITTED
-----------------------------------------------------------------------------
(*
UniversalPaxosStore refines EagerVoting.
*)
maxBal == [p \in Participant |-> state[p][p].maxBal]

EV == INSTANCE EagerVoting WITH Acceptor <- Participant

THEOREM SpecV => EV!Spec
  <1>1. InitV => EV!Init
    BY DEF InitV, Init, EV!Init, InitState, maxBal
  <1>2. TypeOKV' /\ [NextV]_<<vars, votes>> => [EV!Next]_<<votes, maxBal>>
    <2>1. UNCHANGED <<state, msgs, votes>> => UNCHANGED <<votes, maxBal>>
      BY DEF maxBal
    <2>2. TypeOKV' /\ NextV => EV!Next \/ UNCHANGED <<votes, maxBal>>
      <3>. USE DEF TypeOK, EV!Ballot, Ballot
      <3>1. ASSUME NEW q \in Participant,
                   OnMessageV(q),
                   <<votes, maxBal>>' # <<votes, maxBal>>
            PROVE  EV!Next
        <4>1. \E p \in Participant, b \in Ballot, v \in Value : EV!VoteFor(p, b, v)                     
          <5> SUFFICES ASSUME NEW m \in msgs,
                              /\ q \in m.to
                              /\ LET p == m.from
                                 IN  UpdateStateV(q, p, m.state[p])
                              (*
                              /\ IF \/ m.state[q].maxBal < state'[q][q].maxBal
                                    \/ m.state[q].maxVBal < state'[q][q].maxVBal
                                 THEN Send([from |-> q, to |-> {m.from}, state |-> state'[q]])
                                 ELSE UNCHANGED msgs
                              *)
                       PROVE  \E p \in Participant, b \in Ballot, v \in Value : EV!VoteFor(p, b, v)
            BY <3>1 DEF OnMessageV
          <5> QED
        <4> QED
          BY <3>1, <4>1 DEF EV!Next
      <3>2. ASSUME NEW p \in Participant,
                   NEW b \in Ballot,
                   PrepareV(p, b)
            PROVE  EV!Next
        <4>1. EV!IncreaseMaxBal(p, b)
          <5>1. b > maxBal[p]
            BY <3>2 DEF maxBal, PrepareV, Prepare
          <5>2. maxBal' = [maxBal EXCEPT ![p] = b]
            BY <3>2 DEF maxBal, PrepareV, Prepare, Ballot
          <5>3. UNCHANGED votes
            BY <3>2 DEF PrepareV
          <5>4. QED
            BY <5>1, <5>2, <5>3 DEF EV!IncreaseMaxBal
        <4>2. QED
          BY <3>2, <4>1 DEF EV!Next
        (*
        BY <3>2 DEF TypeOKV, EV!TypeOK, TypeOK, EV!Next, EV!IncreaseMaxBal, EV!Ballot, PrepareV, Prepare, Ballot, maxBal
        *)
      <3>3. ASSUME NEW p \in Participant,
                   NEW b \in Ballot,
                   NEW v \in Value,
                   AcceptV(p, b, v)
            PROVE  EV!Next \/ UNCHANGED <<votes, maxBal>>
        <4>1. EV!VoteFor(p, b, v)            
        <4>. QED
          BY <3>3, <4>1 DEF EV!Next
      <3>4. QED
        BY <3>1, <3>2, <3>3 DEF NextV
    <2>3. QED
      BY <2>1, <2>2 DEF vars
  <1>3. QED
    BY <1>1, <1>2, Invariant, PTL DEF SpecV, EV!Spec
=============================================================================
\* Modification History
\* Last modified Thu Aug 15 16:12:53 CST 2019 by hengxin
\* Created Wed Aug 14 14:05:06 CST 2019 by hengxin