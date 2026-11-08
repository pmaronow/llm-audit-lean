import SAP.P015a.WH.W1.LeafTypes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a.WH.W1

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

private theorem circle_properties (c ρ : ℝ) (hρpos : 0 < ρ)
    (hρ : ρ < inverseLogitRadius c) :
    (inverseLogitCircleImage c ρ).Nonempty ∧
    BddAbove (inverseLogitCircleImage c ρ) ∧
    (∃ z ∈ Metric.sphere (c : ℂ) ρ,
      sSup (inverseLogitCircleImage c ρ) = ‖complexInverseLogit z‖) := by
  have hne : (Metric.sphere (c : ℂ) ρ).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hρpos.le
  have hc : ContinuousOn (fun z : ℂ => ‖complexInverseLogit z‖)
      (Metric.sphere (c : ℂ) ρ) := by
    intro z hz
    have hd := AronowAudit.P015.UniformTaylorCompletion.denominator_ne_zero c z
      ((mem_sphere_iff_norm.mp hz).trans_lt hρ)
    exact (AronowAudit.P015.TaylorCompletion.differentiableAt_fc z hd).continuousAt.norm.continuousWithinAt
  exact ⟨hne.image _, (isCompact_sphere (c : ℂ) ρ).bddAbove_image hc,
    (isCompact_sphere (c : ℂ) ρ).exists_sSup_image_eq hne hc⟩

private theorem outside_taylor_witness : outsideTaylorWitness := by
  have hext : outsideTaylorLikelihood = AronowAudit.P015.extremeLikelihood := by
    funext θ
    simp [outsideTaylorLikelihood, outsideTaylorDesign, logLikelihood,
      AronowAudit.P015.extremeLikelihood, bernoulliLogLikelihood,
      AronowAudit.P015.binomialLogLikelihood, inverseLogit, AronowAudit.P015.logistic,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hfit : outsideTaylorDesign.mulVec ![-Real.log 99, 2 * Real.log 99] =
      ![-Real.log 99, Real.log 99] := by
    ext i
    fin_cases i <;> simp [outsideTaylorDesign, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  have hL : Real.pi < Real.log 99 := by
    linarith [AronowAudit.P015.log99_lower_bound, Real.pi_lt_four]
  have hc : logOdds ((1 + 99) / 200) = 0 := by norm_num [logOdds]
  refine ⟨AronowAudit.P015.extreme_grouped_data_arithmetic.1, ?_, ?_,
    ⟨by norm_num, hc⟩, hfit, hL, ?_, ?_⟩
  · simpa only [hext] using AronowAudit.P015.extreme_unique_mle.1
  · simpa only [hext] using AronowAudit.P015.extreme_unique_mle.2
  · intro i
    rw [hfit, hc]
    have hR : inverseLogitRadius 0 = Real.pi := by
      simp [inverseLogitRadius, Real.sqrt_sq Real.pi_pos.le]
    rw [hR]
    have hp : 0 < Real.log 99 := Real.pi_pos.trans hL
    fin_cases i <;> simpa [abs_of_pos hp] using hL
  · intro N
    have h := (AronowAudit.P015.all_degree_taylor_counterexample).2.2.2.2.2.2.2 N
    simpa only [inverseLogit, inverseLogitTaylor, AronowAudit.P015.logistic,
      AronowAudit.P015.logisticTaylor, abs_sub_comm] using And.intro h.1 h.2.1

/-- All new T12 packaging is elementary; the analytic and finite-MLE certificates
are existing proved donors. Thus no unproved mathematical leaf is needed. -/
theorem T12_assembly : T12WholeStatement := by
  refine ⟨?_, ?_, ?_, outside_taylor_witness⟩
  · intro p hp hu
    exact ⟨fun a => ((AronowAudit.P015.corrected_logistic_taylor p hp hu).2.2.2.2.1 a).1,
      AronowAudit.P015.local_logistic_remainder p hp hu⟩
  · intro p _ _
    exact AronowAudit.P015.UniformTaylorCompletion.real_center_radius (logOdds p)
  · intro p r ρ hp hu hr hrρ hρ
    obtain ⟨hne, hbd, hmax⟩ := circle_properties (logOdds p) ρ (hr.trans_lt hrρ) hρ
    have h := AronowAudit.P015.restricted_taylor_convergence p r ρ hp hu hr hrρ hρ
    refine ⟨hne, hbd, hmax, ?_, h.2.2⟩
    intro N
    have he : (inverseLogitErrorImage (logOdds p) r N).Nonempty :=
      ⟨_, ⟨logOdds p, by simpa using hr, rfl⟩⟩
    have hb : ∀ x ∈ inverseLogitErrorImage (logOdds p) r N,
        x ≤ sSup (inverseLogitCircleImage (logOdds p) ρ) * (r / ρ) ^ (N + 1) / (1 - r / ρ) := by
      rintro x ⟨a, ha, rfl⟩
      exact h.2.1 N a ha
    exact ⟨he, ⟨_, hb⟩, csSup_le he hb⟩


end
end SAP.P015a.WH.W1
