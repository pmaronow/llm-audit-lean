import SAP.P039.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.Bridge
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

/-- A nonzero exported integral cannot be the value used for a non-integrable function. -/
lemma integrable_of_nonzero_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (h : (∫ ω, f ω ∂μ) ≠ 0) : Integrable f μ := by
  by_contra hn
  exact h (integral_undef hn)

/-- Transport the complete concrete Gaussian counterexample, certifying finite second moments. -/
theorem gaussian_witness : GaussianWitnessStatement := by
  intro σ hσ γ
  have h := AronowAudit.P039.residual_gaussian_reference_counterexample σ hσ γ
  dsimp only at h ⊢
  obtain ⟨joint, ratio, law, moment4, moment3, moment2, neq⟩ := h
  refine ⟨joint, ratio, law, moment4, moment3, moment2, neq, ?_, ?_, ?_⟩
  · apply integrable_of_nonzero_integral
    exact ne_of_eq_of_ne moment4 (by norm_num)
  · apply integrable_of_nonzero_integral
    exact ne_of_eq_of_ne moment3 (by norm_num)
  · apply integrable_of_nonzero_integral
    exact ne_of_eq_of_ne moment2 (by norm_num)

/-- Assemble all deterministic witness fits and the actual Gaussian distributional refutation. -/
theorem T3_correspondence : T3Statement := by
  have hb := AronowAudit.P039.witness_baseline
  have hp := AronowAudit.P039.witness_residual_projection
  exact ⟨⟨hb.1, hb.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2,
      hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩,
    AronowAudit.P039.residual_orthogonal_witness_fit,
    AronowAudit.P039.full_orthogonal_witness_fit,
    AronowAudit.P039.residual_correlated_witness_fit,
    AronowAudit.P039.full_correlated_witness_fit,
    AronowAudit.P039.correlated_regressor_residual_ratio,
    AronowAudit.P039.regression_five_percent_counterexample,
    AronowAudit.P039.residual_test_five_percent_disagreement,
    AronowAudit.P039.regression_procedure_counterexample,
    gaussian_witness⟩

/-- Retain the unconditional covariance conclusions and discard the law-transfer premise. -/
theorem residual_covariance : ResidualCovarianceStatement := by
  intro Ω _ μ _ n k Z x γ ε σ hσ hZ h1 hx hn hi hij he hc
  have h := AronowAudit.P039.PaperDomains.corrected_residual_covariance_assessment
    μ Z x γ ε σ hσ hZ h1 hx hn hi hij he hc
  dsimp only at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- The supported linear algebra and finite-moment covariance portion of target T4. -/
theorem T4_correspondence : T4Statement := by
  refine ⟨?_, residual_covariance⟩
  intro n k Z x y hZ h1 hx hn
  exact AronowAudit.P039.corrected_residual_regression Z x y hZ h1 hx hn

end SAP.P039.Bridge
