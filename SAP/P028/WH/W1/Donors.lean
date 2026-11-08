import SAP.P028.Defs.WholeW1
import SAP.P028.Bridge
import AronowAudit.P028.P028_Results
import AronowAudit.P028.P028_MissingOutcomes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028.WH.W1
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SAP.P028 SAP.P028.Bridge
noncomputable section
open Classical

theorem existingT1 : SAP.P028.T1Statement := by
  have ha : missingAssumptions := by
    have h := AronowAudit.P028.missing_witness_assumptions
    rw [← lower_law, ← upper_law] at h
    exact h
  have hj : missingJointProbability := by
    have h := AronowAudit.P028.missing_witness_joint_probability
    rw [← lower_law, ← upper_law] at h
    exact h
  have hc : missingCells := by
    have h := AronowAudit.P028.missing_witness_observed_cells
    rw [← lower_law, ← upper_law] at h
    exact h
  have hx : missingCounterexample := by
    have h := AronowAudit.P028.missing_outcome_counterexample
    rw [← lower_law, ← upper_law] at h
    exact h
  have hm : missingMoments := by
    have h := AronowAudit.P028.missing_witness_reported_moments
    refine ⟨?_, ?_⟩
    · intro M hM
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
      rcases hM with rfl | rfl
      · have h' := h.1 AronowAudit.P028.lowerLaw (by simp)
        rw [← lower_law] at h'
        exact h'
      · have h' := h.1 AronowAudit.P028.upperLaw (by simp)
        rw [← upper_law] at h'
        exact h'
    · have h' := h.2
      rw [← lower_law, ← upper_law] at h'
      exact h'
  have hf : missingCorollaryComparison := by
    have h := AronowAudit.P028.missing_witness_corollary_comparison
    rw [← lower_law, ← upper_law] at h
    exact h
  refine ⟨ha, hj, ?_, ?_, hc, hx, hm, hf, ?_⟩
  · intro M hM
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl
    · exact lower_mean_domain
    · exact upper_mean_domain
  · intro M _ E z
    exact AronowAudit.P028.finite_assignment_independent (toAuditLaw M) E z
  · intro d h
    apply AronowAudit.P028.missing_outcome_not_identified d
    rcases h with ⟨F, hF⟩
    exact ⟨F, fun M hM => hF (fromAuditLaw M) hM⟩

theorem existingT2 {Ω : Type*} [MeasurableSpace Ω] : SAP.P028.T2Statement Ω := by
  refine ⟨?_, AronowAudit.P028.response_source_table_calculations⟩
  intro M T hb
  let A := toAudit M
  let R := toAuditResponse T
  have hpart : complierProbability M = 1-cellProbability M true false-cellProbability M false true := by
    have h : cellProbability M true false+cellProbability M false true = 1-complierProbability M :=
      (AronowAudit.P028.pure_cell_probabilities A).2.2
    linarith
  refine ⟨(AronowAudit.P028.first_stage_population A).2,
    hpart,
    AronowAudit.P028.response_joint_moment_identity A, ?_, ?_, ?_,
    AronowAudit.P028.response_sensitivity_bounds A R hb⟩
  · intro hq hr hp hm
    exact AronowAudit.P028.response_mixed_identification A R hb hq hr hp hm
  · intro hp hi
    refine ⟨fun z => AronowAudit.P028.independent_response_arm_mean A R z (hp z) (hi z), ?_⟩
    intro hq hr
    have h := AronowAudit.P028.response_independence_sufficient A R hb hq hr hp hi
    exact ⟨h.1, h.2, AronowAudit.P028.response_mixed_identification A R hb hq hr h.2 h.1⟩
  · intro hc
    exact AronowAudit.P028.response_cell_reweighting A R hb hc

theorem existingT6 {Ω : Type*} [MeasurableSpace Ω] : SAP.P028.T6Statement Ω := by
  refine ⟨?_, AronowAudit.P028.full_compliance_endpoints⟩
  intro M hb
  let A := toAudit M
  have h : boundaryRepair M := AronowAudit.P028.boundary_proof_repair A hb
  have residual : ∀ z, 0 ≤ armMean M z-complierProbability M*complierMean M z ∧
      armMean M z-complierProbability M*complierMean M z ≤ 1-complierProbability M := by
    intro z
    have he := h.2.2.2.1 z
    constructor <;> linarith [h.2.2.1.1, h.2.2.1.2]
  refine ⟨h, fun d => AronowAudit.P028.complier_mean_bounds A hb d, residual, ?_, ?_⟩
  · intro z
    have hr := (AronowAudit.P028.contribution_interval (complierProbability M)
      (armMean M z) (complierMean M z) h.1).mp (residual z)
    simpa only [AronowAudit.P028.third_lower_identity _ _ h.1] using hr
  · have ht := AronowAudit.P028.bounds_from_mixture_moments
      (complierProbability M) (armMean M false) (armMean M true)
      (complierMean M false) (complierMean M true) (noncomplierContribution M) h.1
      (h.2.2.2.1 false) (h.2.2.2.1 true)
      (AronowAudit.P028.complier_mean_bounds A hb false)
      (AronowAudit.P028.complier_mean_bounds A hb true) h.2.2.1
    exact ⟨ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2, ht.1⟩


end
end SAP.P028.WH.W1
