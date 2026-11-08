import SAP.P008a.Defs.WholeW1
import SAP.P008a.Bridge
import AronowAudit.P008.P008_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a.WH.W1

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

/-- Short matrix glue for the existing OLS and scalar-HAC certificates. -/
theorem ols_identities : WholeOLSIdentities := by
  intro N z m h₁ h₀
  let X := binaryDesign z
  have ht : nTreated z ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h₁)
  have hc : nControl z ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h₀)
  have hb (i : Fin N) : bit (z i) * bit (z i) = bit (z i) := by
    cases z i <;> norm_num [bit]
  have hg : X.transpose * X =
      !![(N : ℝ), nTreated z; nTreated z, nTreated z] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [X, Matrix.mul_apply, binaryDesign, hb, nTreated]
  have hd : (X.transpose * X).det = nTreated z * nControl z := by
    rw [hg, Matrix.det_fin_two_of]
    simp only [nControl]
    ring
  have hn : (X.transpose * X).det ≠ 0 := by rw [hd]; exact mul_ne_zero ht hc
  have he : X.transpose.mulVec (olsResidual z m) = 0 := by
    change X.transpose.mulVec (m - X.mulVec (((X.transpose * X)⁻¹).mulVec
      (X.transpose.mulVec m))) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hn), Matrix.one_mulVec, sub_self]
  have hw := AronowAudit.P008.binary_regression_weights_residuals z m h₁ h₀
  have hs : wholeOLSScore z m = regressionScore z m := by
    funext i
    exact congrArg₂ (· * ·) (hw.1 i) (hw.2 i)
  have hz : (∑ i, wholeOLSScore z m i) = 0 := by
    rw [hs]
    exact AronowAudit.P008.regression_score_sum_zero z m ht hc
  refine ⟨hd, hn, he, hw.1, hw.2, hs, ?_, hz, ?_⟩
  · rw [hz, he]
    simp
  · intro D c
    rw [hs]
    exact (AronowAudit.P008.matrix_hac_reduction z m D c h₁ h₀).2.2

/-- The retained T7 clauses, discharged by their existing certificates. -/
theorem risk_counting : T7Statement := by
  refine ⟨AronowAudit.P008.risk_circle_calculation,
    AronowAudit.P008.summed_risk_counterexample_bernoulli,
    AronowAudit.P008.risk_sampling_probabilities_bernoulli,
    AronowAudit.P008.binary_companion_counterexample_bernoulli,
    AronowAudit.P008.risk_design_and_companion_estimates, ?_⟩
  intro w hw hs
  have hm := AronowAudit.P008.summed_risk_counterexample_bernoulli.2.1
  have he (j : Fin 4) : finiteAMR (uniformLaw (Assignment 4))
      (fun i z => riskM i j z) = -321 / 40000 := by
    convert hm j using 1
    norm_num [finiteAMR]
    rfl
  simp_rw [he]
  exact (AronowAudit.P008.constant_radius_effect_for_sampling w hw hs (-321 / 40000)).2

/-- The retained T9 clauses already include a genuine spatial circle-integral model. -/
theorem bandwidth_spatial : T9Statement := by
  exact ⟨AronowAudit.P008.bandwidth_spatial_realization,
    AronowAudit.P008.spatial_grid_position_counterexample,
    AronowAudit.P008.grid_position_counterexample.1,
    AronowAudit.P008.toy_archived_sixth_row_incompatible⟩

/-- The retained T10 clauses, including the zero-cutoff equality. -/
theorem corrected_counting : T10Statement := by
  refine ⟨?_, AronowAudit.P008.grid_position_counterexample.2.2.2.2, ?_⟩
  · intro N z m D c h₁ h₀ j k
    have hs : (∑ i, regressionScore z m i) = 0 :=
      AronowAudit.P008.regression_score_sum_zero z m h₁ h₀
    have hi := AronowAudit.P008.corrected_bandwidth_invariant (regressionScore z m) D c j k
    refine ⟨hi.1, hi.2, hs, ?_⟩
    intro hall
    have hz : hac (regressionScore z m) D c = 0 :=
      AronowAudit.P008.regression_all_pairs_zero z m D c h₁ h₀ hall
    exact ⟨by rw [hz, hs]; norm_num, hz⟩
  · intro z m h₁ h₀
    have ht := AronowAudit.P008.toy_cutoff_is_hc0 (regressionScore z m)
    refine ⟨ht.2, ?_, (AronowAudit.P008.toy_archived_sixth_row_incompatible z m h₁ h₀).2.1⟩
    apply ht.2.trans
    symm
    exact AronowAudit.P008.hac_equals_hc0 _ _ 0 le_rfl (fun _ => dist_self _)
      (fun i j hij => lt_trans (by norm_num) (ht.1 i j hij))

/-- Interchange two finite averages, without any analytic assumptions. -/
theorem countMean_expect {Ω I : Type*} [Fintype Ω] [Fintype I]
    (Q : FiniteLaw Ω) (f : I → Ω → ℝ) :
    countMean Finset.univ (fun i => Q.expect (f i)) =
      Q.expect (fun z => countMean Finset.univ (fun i => f i z)) := by
  simp only [countMean, FiniteLaw.expect]
  rw [Finset.sum_comm]
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  rw [Finset.sum_div]

end
end SAP.P008a.WH.W1
