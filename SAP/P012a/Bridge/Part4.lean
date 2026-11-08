import SAP.P012a.Bridge.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.Bridge

open SAP.P012a Finset
open scoped Classical
noncomputable section

theorem proposal_counterexample :
    Admissible proposalData ∧ Compatible proposalData proposalStart ∧
    replacementPool proposalData proposalStart 1 = ∅ ∧
    (∀ t : Bool, Proposal proposalData false proposalStart (proposalBad t) ∧
      ¬ Compatible proposalData (proposalBad t)) ∧
    homophily proposalStart = some (-1/3) ∧
    preferential proposalData proposalStart = some (-1/2) := by
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.proposal_counterexample)

theorem proposal_counterexample_b :
    Admissible proposalDataB ∧ Compatible proposalDataB proposalStartB ∧
    replacementPool proposalDataB proposalStartB 2 = ∅ ∧
    (∀ t : Bool, Proposal proposalDataB false proposalStartB (proposalBadB t) ∧
      ¬ Compatible proposalDataB (proposalBadB t)) := by
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.proposal_counterexample_b)

theorem cleanup_counterexample :
    Admissible cleanupData ∧ Compatible cleanupData cleanupStart ∧
    Proposal cleanupData false cleanupStart (cleanup cleanupData false cleanupStart) ∧
    ¬ Compatible cleanupData (cleanup cleanupData false cleanupStart) ∧
    homophily cleanupStart = some (-1) ∧ preferential cleanupData cleanupStart = some 0 := by
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.cleanup_counterexample)

theorem empty_trait_pool_counterexample :
    Admissible emptyPoolData ∧ Compatible emptyPoolData (dyad false true) ∧
    unsampled emptyPoolData (dyad false true) = ∅ ∧
    (¬ ∃ K, TraitProposal emptyPoolData false (dyad false true) K) ∧
    homophily (dyad false true) = some (-1) ∧
    preferential emptyPoolData (dyad false true) = some 0 := by
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.empty_trait_pool_counterexample)

theorem corrected_proposal_preserves (D : Data) (H K : State)
    (hD : Admissible D) (hH : Compatible D H) (hP : Proposal D true H K) :
    Compatible D K := by
  revert D H K hD hH hP
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.corrected_proposal_preserves)

theorem table_counterexample (D : Data) (hD : Admissible D)
    (hn : D.sampled.card = 527) (hM : D.seeds.card = 6)
    (hd : ∑ i ∈ D.sampled, D.degree i = 4487) :
    Compatible D (leafCompletion D false) ∧ totalSpare D = 3445 ∧
    a D + b D + cR D = 521 ∧ HomophilyDefined (leafCompletion D false) ∧
    hValue (leafCompletion D false) = hLower D ∧
    hValue (leafCompletion D false) ≤ -1462/1983 ∧
    hValue (leafCompletion D false) ≤ -178409/241987 ∧
    hValue (leafCompletion D false) < -7027/10000 ∧
    hValue (leafCompletion D false) < -6918/10000 ∧
    hValue (leafCompletion D false) < -7179/10000 := by
  revert D hD hn hM hd
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.table_counterexample)

theorem corrected_table_bound (D : Data) (hD : Admissible D)
    (hn : D.sampled.card = 527) (hM : D.seeds.card = 6)
    (hd : ∑ i ∈ D.sampled, D.degree i = 4487)
    (L : ℝ) (hL : IsGLB (hValues D) L) :
    L ≤ -1462/1983 ∧ L ≤ -178409/241987 ∧
    -7027/10000 - L ≥ 685459/19830000 ∧
    -6918/10000 - L ≥ 450803/9915000 ∧
    -7179/10000 - L ≥ 384043/19830000 := by
  revert D hD hn hM hd L hL
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.corrected_table_bound)

theorem table_degree_converse (D : Data) (Hnom : State) (hD : Admissible D)
    (hn : D.sampled.card = 527) (hM : D.seeds.card = 6)
    (hNom : (∑ i ∈ D.sampled, graphDegree Hnom (s i)) = 4487)
    (L : ℝ) (hL : IsGLB (hValues D) L)
    (hround : ∃ q ∈ ({-7027/10000,-6918/10000,-7179/10000} : Finset ℝ),
      |L-q| ≤ 1/20000) :
    (∑ i ∈ D.sampled, D.degree i) ≠ 4487 ∧
    (∃ i ∈ D.sampled, D.degree i ≠ graphDegree Hnom (s i)) ∧
    ¬ Compatible D Hnom := by
  revert D Hnom hD hn hM hNom L hL hround
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.table_degree_converse)

theorem exact_h_lower (D : Data) (hD : Admissible D)
    (hreg : 0 < totalSpare D ∨
      (0 < 2*a D + cR D ∧ 0 < 2*b D + cR D)) :
    IsLeast (hValues D) (hLower D) ∧
    Compatible D (leafCompletion D false) ∧
    homophily (leafCompletion D false) = some (hLower D) := by
  revert D hD hreg
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.exact_h_lower)

theorem exact_h_region (D : Data) (hD : Admissible D)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true) :
    (∀ H, Compatible D H →
      hDenominator H =
        ((2*(edgeCount H true : ℝ)+mixedCount H)*
          (2*(edgeCount H false : ℝ)+mixedCount H)) /
          (2*((edgeCount H true : ℝ)+edgeCount H false+mixedCount H)) ∧
      0 < hDenominator H ∧
      hValue H = phi (edgeCount H true) (edgeCount H false) (mixedCount H) ∧
      a D ≤ edgeCount H true ∧ edgeCount H true ≤ a D + traitSpare D true ∧
      b D ≤ edgeCount H false ∧ edgeCount H false ≤ b D + traitSpare D false ∧
      cR D ≤ mixedCount H ∧ mixedCount H ≤ cR D + totalSpare D ∧
      hLower D ≤ hValue H ∧ hValue H ≤ hUpper D) ∧
    Compatible D (leafCompletion D false) ∧ Compatible D (leafCompletion D true) ∧
    homophily (leafCompletion D false) = some (hLower D) ∧
    homophily (leafCompletion D true) = some (hUpper D) ∧
    FullHomophilyRegion D (hLower D) (hUpper D) := by
  revert D hD h0 h1
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.exact_h_region)

theorem exact_p_region (D : Data) (hD : Admissible D)
    (hN : D.seeds.card < D.sampled.card) :
    (∀ H, Compatible D H → ∀ j ∈ nonseeds D,
      (laterChildren D j).image s ⊆ susceptible D H (D.parent j) j ∧
      ∃ y q : ℕ, y ≤ spare D (D.parent j) ∧ q ≤ y ∧
        (susceptible D H (D.parent j) j).card = (laterChildren D j).card + y ∧
        (sameSusceptible D H (D.parent j) j).card = childMatches D j + q ∧
        (childMatches D j : ℝ) /
          ((laterChildren D j).card + (spare D (D.parent j) : ℝ)) ≤
          ((childMatches D j : ℝ)+q) / ((laterChildren D j).card+(y : ℝ)) ∧
        ((childMatches D j : ℝ)+q) / ((laterChildren D j).card+(y : ℝ)) ≤
          ((childMatches D j : ℝ)+spare D (D.parent j)) /
          ((laterChildren D j).card+(spare D (D.parent j) : ℝ))) ∧
    Compatible D (leafCompletion D true) ∧ Compatible D (leafCompletion D false) ∧
    preferential D (leafCompletion D true) = some (pLower D) ∧
    preferential D (leafCompletion D false) = some (pUpper D) ∧
    FullPreferentialRegion D (pLower D) (pUpper D) := by
  revert D hD hN
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.exact_p_region)

theorem result1_proof_counterexample :
    Admissible proofStepData ∧ Compatible proofStepData result1BadStart ∧
    1 < 3 ∧ 3 ∈ nonseeds proofStepData ∧ proofStepData.parent 3 ≠ 1 ∧
    recruitmentDegree proofStepData 1 < proofStepData.degree 1 ∧
    recruitmentDegree proofStepData 3 < proofStepData.degree 3 ∧
    {s 1,u 4 0} ∈ result1BadStart.edges ∧ {s 3,u 4 0} ∈ result1BadStart.edges ∧
    {s 1,s 3} ∈ result1BadStart.edges ∧
    ¬ Compatible proofStepData result1BadEnd ∧
    (induced proofStepData result1BadStart).edges =
      (induced proofStepData result1BadEnd).edges := by
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.result1_proof_counterexample)

theorem result2_proof_counterexample :
    Admissible proofStepData ∧ Compatible proofStepData result2BadStart ∧
    recruitmentDegree proofStepData 1 < proofStepData.degree 1 ∧
    recruitmentDegree proofStepData 3 < proofStepData.degree 3 ∧
    proofStepData.trait 1 = false ∧ proofStepData.trait 3 = true ∧
    result2BadStart.trait (u 4 0) = false ∧ result2BadStart.trait (u 5 0) = true ∧
    {s 1,u 4 0} ∈ result2BadStart.edges ∧ {s 3,u 5 0} ∈ result2BadStart.edges ∧
    {s 1,u 5 0} ∈ result2BadStart.edges ∧ {s 3,u 4 0} ∈ result2BadStart.edges ∧
    ¬ Compatible proofStepData result2BadEnd := by
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.result2_proof_counterexample)

theorem result1 (D : Data) (hD : Admissible D) (i j : ℕ)
    (hi : i ∈ D.sampled) (hj : j ∈ D.sampled) (ht : D.time i < D.time j)
    (hr : ¬ (j ∈ nonseeds D ∧ D.parent j = i))
    (hdi : recruitmentDegree D i < D.degree i)
    (hdj : recruitmentDegree D j < D.degree j) :
    ∃ H K : State, Compatible D H ∧ Compatible D K ∧
      {s i,s j} ∉ H.edges ∧ {s i,s j} ∈ K.edges ∧
      (induced D H).edges = recruitmentEdges D ∧
      (induced D K).edges = insert {s i,s j} (recruitmentEdges D) ∧
      InducedCompatible D (induced D H) ∧ InducedCompatible D (induced D K) ∧
      ∃ v ∈ unsampled D H, {s i,v} ∈ H.edges ∧ {s j,v} ∈ H.edges ∧
        K = cleanup D true (addEdge (removeEdge (removeEdge H (s i) v) (s j) v)
          (s i) (s j)) := by
  revert D hD i j hi hj ht hr hdi hdj
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.result1)

theorem result2 (D : Data) (hD : Admissible D) (i j : ℕ)
    (hi : i ∈ D.sampled) (hj : j ∈ D.sampled)
    (hdi : recruitmentDegree D i < D.degree i)
    (hdj : recruitmentDegree D j < D.degree j) (hz : D.trait i ≠ D.trait j) :
    ∃ H K : State, Compatible D H ∧ Compatible D K ∧
      H = leafCompletion D true ∧
      {s i,u i 0} ∈ H.edges ∧ {s j,u j 0} ∈ H.edges ∧
      {s i,u j 0} ∉ H.edges ∧ {s j,u i 0} ∉ H.edges ∧
      K = addEdge (addEdge (removeEdge (removeEdge H (s i) (u i 0))
        (s j) (u j 0)) (s i) (u j 0)) (s j) (u i 0) ∧
      H.vertices = K.vertices ∧ H.edges.card = K.edges.card ∧ H.trait = K.trait ∧
      (∀ v, graphDegree H v = graphDegree K v) ∧
      0 < hDenominator H ∧ hDenominator H = hDenominator K ∧
      hValue H - hValue K = 2 / hDenominator H ∧
      hValue H ≠ hValue K ∧ ¬ PointIdentified (hValues D) := by
  revert D hD i j hi hj hdi hdj hz
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.result2)

theorem result2_swap_formula (D : Data) (hD : Admissible D) (i j : ℕ)
    (hi : i ∈ D.sampled) (hj : j ∈ D.sampled)
    (hdi : recruitmentDegree D i < D.degree i)
    (hdj : recruitmentDegree D j < D.degree j)
    (hzi : D.trait i = false) (hzj : D.trait j = true)
    (H : State) (hv : H.vertices = (leafCompletion D true).vertices)
    (he : H.edges = (leafCompletion D true).edges)
    (htraits : ∀ k ∈ D.sampled, H.trait (s k) = D.trait k)
    (hu1 : H.trait (u i 0) = false) (hu2 : H.trait (u j 0) = true) :
    let K := addEdge (addEdge (removeEdge (removeEdge H (s i) (u i 0))
      (s j) (u j 0)) (s i) (u j 0)) (s j) (u i 0)
    let Q := ∑ v ∈ H.vertices, (graphDegree H v:ℝ)*z H v
    Compatible D H ∧ Compatible D K ∧
    {s i,u i 0} ∈ H.edges ∧ {s j,u j 0} ∈ H.edges ∧
    {s i,u j 0} ∉ H.edges ∧ {s j,u i 0} ∉ H.edges ∧
    H.vertices = K.vertices ∧ H.trait = K.trait ∧ H.edges.card = K.edges.card ∧
    (∀ v, graphDegree H v = graphDegree K v) ∧
    hDenominator H = Q-Q^2/(2*(H.edges.card:ℝ)) ∧
    hDenominator H = Q*(2*(H.edges.card:ℝ)-Q)/(2*(H.edges.card:ℝ)) ∧
    hDenominator H = hDenominator K ∧ 0 < hDenominator H ∧
    hValue H-hValue K =
      (2*(1-(graphDegree H (s j):ℝ)*graphDegree H (u j 0)/(2*(H.edges.card:ℝ))) -
        2*(0-(graphDegree H (s j):ℝ)*graphDegree H (u j 0)/(2*(H.edges.card:ℝ)))) /
        hDenominator H ∧
    hValue H-hValue K = 2/hDenominator H ∧ hValue H ≠ hValue K := by
  revert D hD i j hi hj hdi hdj hzi hzj H hv he htraits hu1 hu2
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.result2_swap_formula)

theorem a2_counterexample :
    Admissible a2Data ∧ Compatible a2Data (a2State true) ∧
    Compatible a2Data (a2State false) ∧
    recruitmentDegree a2Data 1 < a2Data.degree 1 ∧ a2Data.parent 2 = 1 ∧
    (∀ i ∈ a2Data.sampled, {s i,u 4 0} ∈ (a2State true).edges ↔ i = 1) ∧
    susceptible a2Data (a2State true) 1 2 = {s 2,s 3,u 4 0} ∧
    susceptible a2Data (a2State true) 1 3 = {s 3,u 4 0} ∧
    preferential a2Data (a2State true) = some 0 ∧
    preferential a2Data (a2State false) = some (5/12) ∧
    pValue a2Data (a2State true) - pValue a2Data (a2State false) = -5/12 ∧
    pValue a2Data (a2State true) - pValue a2Data (a2State false) ≠
      -1 / ((nonseeds a2Data).card *
        ((susceptible a2Data (a2State true) 1 2).card : ℝ)) ∧
    pValue a2Data (a2State true) - pValue a2Data (a2State false) ≠
      -1 / ((nonseeds a2Data).card *
        ((susceptible a2Data (a2State true) 1 3).card : ℝ)) := by
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.a2_counterexample)

theorem a1_exact_instance :
    let D : Data := ⟨{1,2},{1},fun _ => 1,id,fun _ => 2,fun i => i == 2⟩
    let H : State := ⟨{s 1,s 2,u 3 0,u 4 0},
      {{s 1,s 2},{s 1,u 3 0},{s 2,u 4 0}},fun v => decide (v = s 2) || decide (v = u 4 0)⟩
    let K := addEdge (addEdge (removeEdge (removeEdge H (s 1) (u 3 0))
      (s 2) (u 4 0)) (s 1) (u 4 0)) (s 2) (u 3 0)
    Admissible D ∧ Compatible D H ∧ Compatible D K ∧
    H.edges.card = 3 ∧ degreeTraitSum H = 3 ∧ hDenominator H = 3/2 ∧
    hDenominator K = 3/2 ∧ homophily H = some (1/3) ∧ homophily K = some (-1) ∧
    hValue H-hValue K = 4/3 ∧ hValue H-hValue K = 2/hDenominator H := by
  exact AronowAudit.P012.a1_exact_instance

theorem opposite_leaf_counts (D : Data) (hD : Admissible D) :
    edgeCount (leafCompletion D false) true = a D ∧
    edgeCount (leafCompletion D false) false = b D ∧
    mixedCount (leafCompletion D false) = cR D+totalSpare D := by
  revert D hD
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.opposite_leaf_counts)

theorem leaf_edge_card (D : Data) : (leafEdges D).card = totalSpare D := by
  revert D
  simpa only [data_back, back_data, state_back, back_state, forall_state, exists_state, vertices_eq, edges_eq, trait_eq, sampled_eq, seeds_eq, parent_eq, time_eq, degree_eq, data_trait_eq, s_eq, u_eq, state_inj, nonseeds_eq, sampledVertices_eq, recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq, totalSpare_eq, a_eq, b_eq, cR_eq, hLower_eq, hUpper_eq, pLower_eq, pUpper_eq, leafVertices_eq, leafEdges_eq, traitSpare_eq, sampledTraitDegree_eq, Admissible_eq, Simple_eq, HomophilyDefined_eq, PreferentialDefined_eq, Augmented_eq, Compatible_eq, GraphCompatible_eq, adjacency_eq, z_eq, hNumerator_eq, hDenominator_eq, hValue_eq, homophily_eq, mixedCount_eq, degreeTraitSum_eq, notYetSampled_eq, susceptible_eq, sameSusceptible_eq, pSum_eq, pValue_eq, preferential_eq, unsampled_eq, traitDegree_eq, edgeCount_eq, phi_eq, laterChildren_eq, childMatches_eq, observedMatch_eq, InducedCompatible_eq, replacementPool_eq, recruitmentState_eq, leafCompletion_eq, induced_eq, removeEdge_eq, addEdge_eq, addVertex_eq, flipTrait_eq, cleanup_eq, hValues_eq, pValues_eq, full_h_eq, full_p_eq, point_eq, proposalData_eq, proofStepData_eq, a2Data_eq, domainA_eq, proposalDataB_eq, cleanupData_eq, emptyPoolData_eq, proposalStart_eq, result1BadStart_eq, result1BadEnd_eq, result2BadStart_eq, result2BadEnd_eq, proposalStartB_eq, cleanupStart_eq, proposalBad_eq, a2State_eq, proposalBadB_eq, dyad_eq, forall_data, graph_eq, trait_proposal_eq, proposal_eq] using (@AronowAudit.P012.leaf_edge_card)

end
end SAP.P012a.Bridge
