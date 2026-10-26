import AronowAudit.P001.Wave1.PdaMeanNotIdentified

/-! # P001-T3: negation of the universal printed PDA contract

Definition 4.3.7 (printed p. 167), its well-definedness remark (p. 168), and
footnote 13 (p. 166) assert distributional well-definedness of the derivative
at the covariate mean, assuming a continuous covariate and differentiability
on its positive-density support. Definition 2.2.15 (p. 69) only determines the
CEF on that support. The scalar case already refutes the vector assertion.

The contract below quantifies over probability spaces, laws, covariates,
responses, densities, and both CEF versions. Measurability is the random-variable
convention; integrability of X makes its displayed mean genuine, and integrability
of Y is included in `IsCEF`. No support-at-the-mean premise is supplied by the book.
The counterexample is bounded and jointly absolutely continuous, and its two CEF
versions agree pointwise on the entire positive-density support.
-/

namespace AronowAudit.P001.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableRepairT3 (p : Prop) : Decidable p := Classical.propDecidable p

/-- The printed distributional well-definedness implication, universally
quantified in its scalar case. CEF versions differentiable at every point
with positive covariate density must have a common actual derivative at E[X]. -/
def pda_at_mean_printed_contract : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ (X Y : Ω → ℝ), Measurable X → Measurable Y → Integrable X μ →
    ∀ (fX : ℝ → ℝ), HasPDF (μ.map X) fX →
    ∀ (m m' : ℝ → ℝ),
      IsCEF μ X Y m → IsCEF μ X Y m' →
      (∀ x, 0 < fX x → DifferentiableAt ℝ m x) →
      (∀ x, 0 < fX x → DifferentiableAt ℝ m' x) →
      ∃ a : ℝ, HasDerivAt m a (mean μ X) ∧ HasDerivAt m' a (mean μ X)


/-- Universally asserting the printed implication contradicts the existing
fixed-law counterexample, with all its admissibility conditions discharged. -/
theorem pda_at_mean_printed_contract_refuted : ¬ pda_at_mean_printed_contract := by
  intro hcontract
  obtain ⟨hprob, _hjoint, hpdf, _hsnd, _hprod, hbounds, _hmean, _hgap,
    _hzero, _hC1, _hfamily, hrefute⟩ := pda_at_mean_not_identified
  let instProbabilityRepairT3 : IsProbabilityMeasure gapJointLaw := hprob
  have hXint : Integrable Prod.fst gapJointLaw := by
    apply Integrable.of_bound measurable_fst.aestronglyMeasurable 2
    filter_upwards [hbounds] with xy hxy
    simpa only [Real.norm_eq_abs] using abs_le.mpr hxy.1
  exact hrefute (hcontract (ℝ × ℝ) gapJointLaw hprob Prod.fst Prod.snd
    measurable_fst measurable_snd hXint gapPDF hpdf)

end
end AronowAudit.P001.Wave1
