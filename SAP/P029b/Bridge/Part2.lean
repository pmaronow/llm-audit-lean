import SAP.P029b.Defs
import AronowAudit.P029.P029_Audit
import AronowAudit.P029.Wave1.Gap.GP029B1
import AronowAudit.P029.Wave1.Gap.GP029B2b
import AronowAudit.P029.Wave1.Gap.GP029B3b
import AronowAudit.P029.Wave1.Gap.GLP029B1
import AronowAudit.P029.Wave1.Gap.GLP029B2
import AronowAudit.P029.Wave1.IgnorabilityOrdering
import AronowAudit.P029.Wave1.MarginalSufficiency
import AronowAudit.P029.Wave1.ConditionalSufficiency
import AronowAudit.P029.Wave1.Gap.FidP029
import AronowAudit.P029.Wave1.LateIdentity
import SAP.P029b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.Bridge

universe u v

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

theorem corrected_nested_receipt_model_proof {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hxmeas : Measurable (fun ω => (U ω).x))
    (hd0 : Measurable (fun ω => (U ω).d0)) (hd1 : Measurable (fun ω => (U ω).d1))
    (hz : Measurable Z)
    (hmon : μ {ω | (U ω).defier} = 0)
    (hi : IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1)) μ)
    (hz0 : 0 < mP μ {ω | Z ω = true}) (hz1 : mP μ {ω | Z ω = true} < 1)
    (x : X) (hx : 0 < mP μ {ω | (U ω).x = x})
    (hAC : 0 < mCE μ (fun ω => bit (U ω).d1) {ω | (U ω).x = x}) :
    let a := mCE μ (fun ω => bit (U ω).d1) {ω | (U ω).x = x}
    let b := alwaysAmongAC μ U x
    a*b = mCE μ (fun ω => bit (U ω).d0) {ω | (U ω).x = x} ∧
    a*(1-b) = scoreAt μ U x ∧
    (∀ z, mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | (U ω).x = x ∧ Z ω = z} =
      scoreAt μ U x * bit z + mCE μ (fun ω => bit (U ω).d0) {ω | (U ω).x = x} ∧
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | (U ω).x = x ∧ Z ω = z} =
        nestedReceipt a b z) := by
  exact AronowAudit.P029.Wave1.corrected_nested_receipt_model_proof μ (fun ω => toUnit (U ω)) Z hxmeas hd0 hd1 hz hmon hi hz0 hz1 x hx hAC


theorem constant_effect_population_limits_proof {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool) (hiv : IVAssumptions μ U Z)
    (c m : X → ℝ) (hv : ScoreVersions μ U c m)
    (ε : ℝ) (he : 0 < ε) (hpos : ∀ᵐ ω ∂μ, ε < c (U ω).x ∧ c (U ω).x ≤ 1)
    (τ : ℝ) (hτ : ∀ ω, (U ω).tau = τ) :
    (∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x →
      mCE μ (fun ω => (U ω).tau) {ω | (U ω).x = x} = τ ∧ complierAt μ U x = τ) ∧
    A1Versions μ U m ∧ mWald μ U Z (fun _ => 1) = τ ∧
      mWald μ U Z (fun ω => 1/c (U ω).x) = τ := by
  exact AronowAudit.P029.Wave1.constant_effect_population_limits_proof μ (fun ω => toUnit (U ω)) Z hiv c m hv ε he hpos τ hτ


theorem late_identity_paper_scope {Ω : Type u} {X : Type v}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z) :
    mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = true} -
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = false} =
        mP μ {ω | (U ω).complier} ∧
    mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = true} -
      mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = false} =
        (∫ ω, if (U ω).complier then (U ω).tau else 0 ∂μ) ∧
    (∫ ω, if (U ω).complier then (U ω).tau else 0 ∂μ) =
      mP μ {ω | (U ω).complier} * mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} ∧
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} = mWald μ U Z (fun _ => 1) := by
  exact AronowAudit.P029.Wave1.late_identity_paper_scope μ (fun ω => toUnit (U ω)) Z hiv


theorem appendix_population_identities_proof {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool) (hiv : IVAssumptions μ U Z)
    (c m : X → ℝ) (hv : ScoreVersions μ U c m)
    (ε : ℝ) (he : 0 < ε) (hpos : ∀ᵐ ω ∂μ, ε < c (U ω).x ∧ c (U ω).x ≤ 1) :
    mP μ {ω | (U ω).complier} * mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} =
      (∫ ω, c (U ω).x * m (U ω).x ∂μ) ∧
    mP μ {ω | (U ω).complier} = (∫ ω, c (U ω).x ∂μ) ∧
    (mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => (U ω).outcome (Z ω)) true -
      mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => (U ω).outcome (Z ω)) false) =
        (∫ ω, m (U ω).x ∂μ)/(∫ ω, 1/c (U ω).x ∂μ) ∧
    (mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => bit ((U ω).receipt (Z ω))) true -
      mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => bit ((U ω).receipt (Z ω))) false) =
        1/(∫ ω, 1/c (U ω).x ∂μ) ∧
    mWald μ U Z (fun ω => 1/c (U ω).x) = (∫ ω, m (U ω).x ∂μ) ∧
    (A1Versions μ U m → mWald μ U Z (fun ω => 1/c (U ω).x) = (∫ ω, (U ω).tau ∂μ)) := by
  exact AronowAudit.P029.Wave1.appendix_population_identities_proof μ (fun ω => toUnit (U ω)) Z hiv c m hv ε he hpos


theorem complier_covariate_distribution_proof {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z) (c m : X → ℝ) (hversions : ScoreVersions μ U c m)
    (hc : 0 < mP μ {ω | (U ω).complier}) :
    complierCovariateLaw μ U =
      (Measure.map (fun ω => (U ω).x) μ).withDensity
        (fun x => ENNReal.ofReal (c x / mP μ {ω | (U ω).complier})) ∧
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} =
      ∫ x, m x ∂complierCovariateLaw μ U := by
  exact AronowAudit.P029.Wave1.complier_covariate_distribution_proof μ (fun ω => toUnit (U ω)) Z hiv c m hversions hc


theorem icsw_consistency_proof {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ)
    (h : ICSWConditions μ U Z c m s) (a : X → ℝ)
    (ha : Measurable a)
    (haVersion : ∀ i, (fun ω => a (U i ω).x) =ᵐ[μ]
      condExp (covariateSigma (U i)) μ (fun ω => (U i ω).tau))
    (hA1 : ∀ x ∈ (Measure.map (fun ω => (U 0 ω).x) μ).support, m x = a x)
    (hA3 : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ (Measure.map (fun ω => (U 0 ω).x) μ).support,
      ε < c x ∧ c x ≤ 1) :
    TendstoInMeasure μ (icswSequence U Z s) atTop (fun _ => ∫ ω, (U 0 ω).tau ∂μ) := by
  exact AronowAudit.P029.Wave1.icsw_consistency_proof μ (fun i ω => toUnit (U i ω)) Z c m s (toConditions μ U Z c m s h) a ha haVersion hA1 hA3


theorem icsw_complier_effect_limit_proof {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ)
    (h : ICSWConditions μ U Z c m s)
    (hA3 : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ (Measure.map (fun ω => (U 0 ω).x) μ).support,
      ε < c x ∧ c x ≤ 1) :
    TendstoInMeasure μ (icswSequence U Z s) atTop (fun _ => ∫ ω, m (U 0 ω).x ∂μ) := by
  exact AronowAudit.P029.Wave1.icsw_complier_effect_limit_proof μ (fun i ω => toUnit (U i ω)) Z c m s (toConditions μ U Z c m s h) hA3


theorem winsorization_corrected_limit_proof {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ)
    (cutoff : ℕ → Ω → ℝ) (h : ICSWConditions μ U Z c m s) (α : ℝ) (hα : 0 < α)
    (hA3 : ∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < mP μ {ω | (U 0 ω).x = x} →
      ε < scoreAt μ (U 0) x ∧ scoreAt μ (U 0) x ≤ 1)
    (hcmeas : ∀ n, Measurable (cutoff n))
    (hquantile : ∀ n, ∀ᵐ ω ∂μ,
      Type7Quantile (fun i : Fin (n+1) => s n i.val ω)
        (((n+1 : ℕ) : ℝ)^(-α)) (cutoff n ω)) :
    TendstoInMeasure μ (fun n ω => winsorizedSequence U Z s cutoff n ω -
      icswSequence U Z s n ω) atTop (fun _ => 0) ∧
    TendstoInMeasure μ (icswSequence U Z s) atTop
      (fun _ => ∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) ∧
    TendstoInMeasure μ (winsorizedSequence U Z s cutoff) atTop
      (fun _ => ∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) ∧
    ((∀ x, 0 < mP μ {ω | (U 0 ω).x = x} → latentAt μ (U 0) x) →
      (∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) = ∫ ω, (U 0 ω).tau ∂μ) := by
  exact AronowAudit.P029.Wave1.winsorization_corrected_limit_proof μ (fun i ω => toUnit (U i ω)) Z c m s cutoff (toConditions μ U Z c m s h) α hα hA3 hcmeas hquantile


theorem printed_ignorability_ordering_refuted :
  ¬ (∀ {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z → ∀ (x : X), 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x →
        typicalAt μ U Z x → latentAt μ U x) := by
  intro h
  apply AronowAudit.P029.Wave1.printed_ignorability_ordering_refuted
  intro Ω X mΩ mX singleton μ prob U Z hiv x hx hc hi
  exact h μ (fun ω => fromUnit (U ω)) Z hiv x hx hc hi


theorem printed_marginal_sufficiency_refuted :
  ¬ (∀ {Ω X : Type} [MeasurableSpace Ω]
      [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x) →
      IndepFun (fun ω => (U ω).tau) (fun ω => decide (U ω).complier) μ →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) ∧
      mWald μ U Z (fun _ => 1) = (∫ ω, (U ω).tau ∂μ) ∧
      mWald μ U Z (fun ω => 1 / scoreAt μ U (U ω).x) = (∫ ω, (U ω).tau ∂μ)) := by
  intro h
  apply AronowAudit.P029.Wave1.printed_marginal_sufficiency_refuted
  intro Ω X mΩ finX mX singleton μ prob U Z hiv hpos hind
  exact h μ (fun ω => fromUnit (U ω)) Z hiv hpos hind


theorem printed_conditional_sufficiency_refuted :
  ¬ (∀ {Ω X : Type} [MeasurableSpace Ω]
      [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x) →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} →
        IndepFun (fun ω => (U ω).tau) (fun ω => ((U ω).d0, (U ω).d1))
          (ENNReal.ofReal ((mP μ {ω | (U ω).x = x})⁻¹) • μ.restrict {ω | (U ω).x = x})) →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) ∧
      mWald μ U Z (fun _ => 1) = (∫ ω, (U ω).tau ∂μ) ∧
      mWald μ U Z (fun ω => 1 / scoreAt μ U (U ω).x) = (∫ ω, (U ω).tau ∂μ)) := by
  intro h
  apply AronowAudit.P029.Wave1.printed_conditional_sufficiency_refuted
  intro Ω X mΩ finX mX singleton μ prob U Z hiv hpos hind
  exact h μ (fun ω => fromUnit (U ω)) Z hiv hpos hind


theorem package_fit_counterexample : ∃ q : ReceiptParameters,
      q.val = packageCells ∧
      IsMinimizer
        (fun t : ReceiptParameters =>
          packageObjective
            (receiptLikelihood t)
            observationWeight) q ∧
      ¬ IsMinimizer
        (fun t : ReceiptParameters =>
          weightedObjective
            (receiptLikelihood t)
            observationWeight) q := by
  exact AronowAudit.P029.Wave1.nested_bernoulli_package_weighted_fit_counterexample

end
end SAP.P029b.Bridge
