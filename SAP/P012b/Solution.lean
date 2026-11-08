import SAP.P012b.Defs
import SAP.P012b.Bridge
import AronowAudit.P012.P012_Identification
import AronowAudit.P012.P012_PrintedRefutations
import AronowAudit.P008.Wave1.Gap.WretiredunstatedB1
import SAP.P012b.WH.W1.Proofs.T14
import SAP.P012b.WH.W1.Proofs.T15
import SAP.P012b.WH.W1.Proofs.T17
import SAP.P012b.WH.W1.Proofs.T18
import SAP.P012b.WH.W1.Proofs.T22
import SAP.P012b.WH.W2.Proofs.T23

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

open Finset Filter
open scoped Topology
open SAP.P012b SAP.P012b.Bridge

theorem SAP.P012b.T13 : SAP.P012b.T13Statement := by
  refine ⟨?_, ?_⟩
  · have h := @AronowAudit.P012.result3
    simp only [
    forall_data, forall_state, exists_state, toData_inj,
    toState_inj, data_sampled, data_seeds, data_parent,
    data_time, data_degree, data_trait, state_vertices,
    state_edges, state_trait, nonseeds_eq, sampledVertices_eq,
    recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq,
    sampledTraitDegree_eq, Admissible_eq, Simple_eq, Augmented_eq,
    Compatible_eq, GraphCompatible_eq, InducedCompatible_eq, hNumerator_eq,
    hDenominator_eq, hValue_eq, HomophilyDefined_eq, homophily_eq,
    susceptible_eq, pSum_eq, pValue_eq, PreferentialDefined_eq,
    preferential_eq, traitDegree_eq, unsampled_eq, replacementPool_eq,
    children_eq, degreeTraitSum_eq, PointIdentified_eq, cooling_eq,
    leafCompletion_eq, recruitmentState_eq, induced_eq, flipTrait_eq,
    removeEdge_eq, addEdge_eq, addVertex_eq, cleanup_eq,
    hValues_eq, pValues_eq, FullHomophilyRegion_eq, FullPreferentialRegion_eq,
    domainA_eq, domainB_eq, domainC_eq, domainD_eq,
    figureData_eq, dyad_eq, domainCState_eq, domainDState_eq,
    printed_table_intervals_eq, sampled_name_eq, unsampled_name_eq, cooling_function_eq,
    Proposal_eq ] at h ⊢
    exact h
  · have h := @AronowAudit.P012.private_trait_flip_difference
    simp only [
    forall_data, forall_state, exists_state, toData_inj,
    toState_inj, data_sampled, data_seeds, data_parent,
    data_time, data_degree, data_trait, state_vertices,
    state_edges, state_trait, nonseeds_eq, sampledVertices_eq,
    recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq,
    sampledTraitDegree_eq, Admissible_eq, Simple_eq, Augmented_eq,
    Compatible_eq, GraphCompatible_eq, InducedCompatible_eq, hNumerator_eq,
    hDenominator_eq, hValue_eq, HomophilyDefined_eq, homophily_eq,
    susceptible_eq, pSum_eq, pValue_eq, PreferentialDefined_eq,
    preferential_eq, traitDegree_eq, unsampled_eq, replacementPool_eq,
    children_eq, degreeTraitSum_eq, PointIdentified_eq, cooling_eq,
    leafCompletion_eq, recruitmentState_eq, induced_eq, flipTrait_eq,
    removeEdge_eq, addEdge_eq, addVertex_eq, cleanup_eq,
    hValues_eq, pValues_eq, FullHomophilyRegion_eq, FullPreferentialRegion_eq,
    domainA_eq, domainB_eq, domainC_eq, domainD_eq,
    figureData_eq, dyad_eq, domainCState_eq, domainDState_eq,
    printed_table_intervals_eq, sampled_name_eq, unsampled_name_eq, cooling_function_eq,
    Proposal_eq ] at h ⊢
    exact h

theorem SAP.P012b.T14 : SAP.P012b.T14WholeStatement :=
  SAP.P012b.WH.W1.T14_whole

theorem SAP.P012b.T15 : SAP.P012b.T15WholeStatement :=
  SAP.P012b.WH.W1.T15_whole

theorem SAP.P012b.T16 : SAP.P012b.T16Statement := by
  refine ⟨@AronowAudit.P012.no_positive_nondecreasing_zero_limit,
    @AronowAudit.P012.printed_first_temperature_undefined, ?_, ?_,
    @AronowAudit.P012.cooling_series_diverges⟩
  · sap_transfer (@AronowAudit.P012.cooling_properties)
  · intro ε D t hε ht hD hdepth
    refine ⟨?_, AronowAudit.P012.cooling_term_bound ε D t hε ht hD hdepth⟩
    congr 1
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    ring

theorem SAP.P012b.T17 : SAP.P012b.T17WholeStatement :=
  SAP.P012b.WH.W1.T17_whole

theorem SAP.P012b.T18 : SAP.P012b.T18WholeStatement :=
  SAP.P012b.WH.W1.T18_whole

theorem SAP.P012b.T19 : SAP.P012b.T19Statement := by
  unfold T19Statement
  sap_transfer (AronowAudit.P012.printed_proposal_preserves_refuted)

theorem SAP.P012b.T20 : SAP.P012b.T20Statement := by
  unfold T20Statement
  sap_transfer (@AronowAudit.P012.Wave1.printed_table_intervals_refuted)

theorem SAP.P012b.T22 : SAP.P012b.T22WholeStatement :=
  SAP.P012b.WH.W1.T22_whole

theorem SAP.P012b.T23 : SAP.P012b.T23WholeStatement :=
  SAP.P012b.WH.W2.T23_whole

theorem SAP.P012b.T24 : SAP.P012b.T24Statement := by
  intro ε hε
  have hb (h p : ℝ) (hh : -1 ≤ h) :
      0 < annealingObjective ε h p ∧ annealingObjective ε h p ≤ 1 / ε ∧
        annealingObjective ε (-1) p = 1 / ε := by
    simpa only [annealingObjective_eq] using AronowAudit.P012.objective_bounds ε h p hε hh
  have hmax : annealingObjective ε (-1) 0 = 1 / ε := (hb (-1) 0 le_rfl).2.2
  refine ⟨?_, ⟨?_, ?_⟩, hmax, ?_⟩
  · intro h hh p _hp
    exact ⟨(hb h p hh.1).1, (hb h p hh.1).2.1⟩
  · exact ⟨-1, by norm_num, 0, by norm_num, hmax.symm⟩
  · rintro r ⟨h, hh, p, _hp, rfl⟩
    exact (hb h p hh.1).2.1
  · intro H hS h0 h1
    have hr : HomophilyDefined H ∧ -1 ≤ hValue H ∧ hValue H ≤ 1 := by
      simpa only [HomophilyDefined_eq, hValue_eq] using
        AronowAudit.P012.homophily_global_range (toState H) hS h0 h1
    have ho := hb (hValue H) 0 hr.2.1
    exact ⟨hr.1, by simp only [homophily, if_pos hr.1], hr.2.1, hr.2.2, ho.1, ho.2.1⟩
