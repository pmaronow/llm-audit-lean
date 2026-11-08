import SAP.P012b.WH.W1.Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

namespace SAP.P012b.WH.W1

open Finset SAP.P012b.Bridge
noncomputable section

theorem dyad_raw : hNumerator (dyad false true) = -1/2 ∧
    hDenominator (dyad false true) = 1/2 := by
  norm_num [hNumerator, hDenominator, graphDegree, adjacency, z, dyad, s, Finset.filter_singleton]

theorem t17_example :
    Admissible domainB ∧ GraphCompatible domainB commonNeighbourState ∧
    GraphCompatible domainB (dyad false true) ∧
    (∀ i ∈ domainB.sampled,
      graphDegree commonNeighbourState (s i) = 1 ∧
      graphDegree (dyad false true) (s i) = 1 ∧
      graphDegree (induced domainB commonNeighbourState) (s i) = 0 ∧
      graphDegree (induced domainB (dyad false true)) (s i) = 1) ∧
    (induced domainB commonNeighbourState).edges = ∅ ∧
    InducedCompatible domainB (induced domainB commonNeighbourState) ∧
    ¬ GraphCompatible domainB (induced domainB commonNeighbourState) ∧
    GraphCompatible domainB (induced domainB (dyad false true)) := by
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    by unfold InducedCompatible; decide, by decide, by decide⟩

theorem history_examples :
    Admissible starHistory ∧ Admissible chainHistory ∧ Admissible reorderedHistory ∧
    Compatible starHistory historyState ∧ Compatible chainHistory historyState ∧
    Compatible reorderedHistory historyState ∧
    chainHistory = {starHistory with parent := chainHistory.parent} ∧
    reorderedHistory = {starHistory with time := reorderedHistory.time} ∧
    recruitmentEdges starHistory ≠ recruitmentEdges chainHistory ∧
    recruitmentEdges starHistory = recruitmentEdges reorderedHistory ∧
    starHistory.time 2 < starHistory.time 3 ∧
    reorderedHistory.time 3 < reorderedHistory.time 2 ∧
    preferential starHistory historyState = some (-1/12) ∧
    preferential chainHistory historyState = some (1/6) ∧
    preferential reorderedHistory historyState = some (-1/3) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    rfl, rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  all_goals norm_num [preferential, PreferentialDefined, pValue, pSum,
    susceptible, sameSusceptible, nonseeds, starHistory, chainHistory,
    reorderedHistory, historyState, s, u, Bool.beq_eq_decide_eq, Finset.sdiff_singleton_eq_erase, Finset.filter_singleton, Finset.sdiff_insert,
    Finset.filter_insert, Finset.image_insert]

theorem oneLeaf_examples :
    Admissible oneLeafData ∧
    (0 < sampledTraitDegree oneLeafData false ∧ 0 < sampledTraitDegree oneLeafData true) ∧
    oneLeafData.seeds.card < oneLeafData.sampled.card ∧
    (∀ b : Bool, Compatible oneLeafData (oneLeafState b)) ∧
    homophily (oneLeafState false) = some (-1) ∧
    homophily (oneLeafState true) = some (-1/3) ∧
    (∀ b : Bool, preferential oneLeafData (oneLeafState b) = some 0) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro b; cases b <;> decide
  · norm_num [homophily, HomophilyDefined, hValue, hNumerator, hDenominator,
      graphDegree, adjacency, z, oneLeafState, s, u, Finset.filter_insert, Finset.filter_singleton]
  · norm_num [homophily, HomophilyDefined, hValue, hNumerator, hDenominator,
      graphDegree, adjacency, z, oneLeafState, s, u, Finset.filter_insert, Finset.filter_singleton]
  · intro b
    cases b <;> norm_num [preferential, PreferentialDefined, pValue, pSum,
      susceptible, sameSusceptible, nonseeds, oneLeafData, oneLeafState, s, u,
      Bool.beq_eq_decide_eq, Finset.sdiff_singleton_eq_erase, Finset.filter_singleton, Finset.sdiff_insert, Finset.filter_insert, Finset.image_insert]

end
end SAP.P012b.WH.W1
