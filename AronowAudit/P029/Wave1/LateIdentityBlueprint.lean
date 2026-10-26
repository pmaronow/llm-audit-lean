import AronowAudit.P029.P029_Audit

/-!
# P029-T25: the LATE and ITT identities

Paper: P029 p. 495 (PDF p. 4), equation (3) and its two ITT identities, under the five IV
assumptions on an arbitrary probability space, with integrable potential outcomes and no
defiers almost surely.

The intermediate propositions express the independent-event mean, fixed-response
regularity, equality of arm means and fixed-response means, almost-sure ITT integration,
and complier normalization. Dependencies are explicit hypotheses.
-/

namespace AronowAudit.P029.Wave1.LateIdentity

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

universe u v

noncomputable section

/-- Equation (3) with both ITT identities, on an arbitrary
probability space, under exactly `IVAssumptions`. -/
def Target : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
    IVAssumptions μ U Z →
    mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = true} -
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = false} =
        mP μ {ω | (U ω).complier} ∧
    mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = true} -
      mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = false} =
        (∫ ω, if (U ω).complier then (U ω).tau else 0 ∂μ) ∧
    (∫ ω, if (U ω).complier then (U ω).tau else 0 ∂μ) =
      mP μ {ω | (U ω).complier} * mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} ∧
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} =
      mWald μ U Z (fun _ => 1)


/-- On a probability space, an integrable `v` independent of a measurable Boolean `Z` has the same
mean on every positive-probability arm: `∫_{Z=z} v = P(Z=z) ∫ v`, hence
`mCE μ v {Z = z} = ∫ v`. Use `IndepFun.comp` (indicator of `{z}` is measurable on `Bool`)
and `IndepFun.integral_fun_mul_eq_mul_integral`, `integral_indicator`. -/
def N1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → Bool) (v : Ω → ℝ), Measurable Z → Integrable v μ → IndepFun Z v μ →
      ∀ z : Bool, 0 < mP μ {ω | Z ω = z} → mCE μ v {ω | Z ω = z} = ∫ ω, v ω ∂μ

/-- From `IVAssumptions`: for each fixed arm `z`, the fixed-response receipt `bit (receipt z)` and
outcome `outcome z` are integrable and independent of `Z` (compose the tuple independence
with a measurable map of `(x, d0, d1, y0, y1)`; `|outcome z| ≤ |y0| + |y1|`); the complier
effect `1_C τ` is integrable; the complier and arm events are measurable. -/
def N2 : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
    IVAssumptions μ U Z →
      (∀ z : Bool,
        Integrable (fun ω => bit ((U ω).receipt z)) μ ∧
        Integrable (fun ω => (U ω).outcome z) μ ∧
        IndepFun Z (fun ω => bit ((U ω).receipt z)) μ ∧
        IndepFun Z (fun ω => (U ω).outcome z) μ ∧
        MeasurableSet {ω | Z ω = z}) ∧
      Integrable (fun ω => if (U ω).complier then (U ω).tau else 0) μ ∧
      MeasurableSet {ω | (U ω).complier}

/-- On the arm `{Z = z}` observed
receipt and outcome equal the fixed responses at `z` (`setIntegral_congr_fun`); by `N1` the
arm means are the unconditional fixed-response means. Both arms have positive mass
(`0 < P(Z=1) < 1`), so the arm mean of the constant `1` is `1`. Takes `N1` and `N2`. -/
def N3 : Prop :=
  N1.{u} → N2.{u, v} →
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
    IVAssumptions μ U Z → ∀ z : Bool,
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = z} =
          ∫ ω, bit ((U ω).receipt z) ∂μ ∧
      mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = z} = ∫ ω, (U ω).outcome z ∂μ ∧
      mCE μ (fun _ => (1 : ℝ)) {ω | Z ω = z} = 1

/-- Since `μ {defier} = 0`, the
pointwise identities `unit_itt_identities` hold almost everywhere; integrating them
(`integral_sub`, `integral_congr_ae`) gives `ΔD = P(C)` and `ΔY = E(1_C τ)` for the
fixed-response means. Takes `N2` (integrability). -/
def N4 : Prop :=
  N2.{u, v} →
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
    IVAssumptions μ U Z →
      (∫ ω, bit ((U ω).receipt true) ∂μ) - (∫ ω, bit ((U ω).receipt false) ∂μ) =
          mP μ {ω | (U ω).complier} ∧
      (∫ ω, (U ω).outcome true ∂μ) - (∫ ω, (U ω).outcome false ∂μ) =
          ∫ ω, (if (U ω).complier then (U ω).tau else 0) ∂μ

/-- With positive complier mass,
`E(1_C τ) = P(C) · E(τ | C)` (restricted integral = integral of the indicator; cancel
`P(C) ≠ 0`). Takes `N2` (measurability of `C`). -/
def N5 : Prop :=
  N2.{u, v} →
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
    IVAssumptions μ U Z → 0 < mP μ {ω | (U ω).complier} →
      (∫ ω, (if (U ω).complier then (U ω).tau else 0) ∂μ) =
        mP μ {ω | (U ω).complier} * mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier}

/-- Relevance forces `P(C) > 0`; the unit-weight Wald ratio is `ΔY / ΔD`.
The intermediate identities imply the conclusion. -/
theorem assemble (h1 : N1.{u}) (h2 : N2.{u, v}) (h3 : N3.{u, v}) (h4 : N4.{u, v})
    (h5 : N5.{u, v}) : Target.{u, v} := by
  intro Ω X _ _ μ _ U Z hiv
  have harm := h3 h1 h2 μ U Z hiv
  obtain ⟨hD, hY⟩ := h4 h2 μ U Z hiv
  have ha : mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = true} -
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = false} =
        mP μ {ω | (U ω).complier} := by
    rw [(harm true).1, (harm false).1]
    exact hD
  have hb : mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = true} -
      mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = false} =
        ∫ ω, (if (U ω).complier then (U ω).tau else 0) ∂μ := by
    rw [(harm true).2.1, (harm false).2.1]
    exact hY
  have hpos : 0 < mP μ {ω | (U ω).complier} := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hrel⟩ := hiv
    rw [ha] at hrel
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hrel)
  have hc := h5 h2 μ U Z hiv hpos
  refine ⟨ha, hb, hc, ?_⟩
  have hw : mWald μ U Z (fun _ => 1) =
      (mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = true} -
        mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = false}) /
      (mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = true} -
        mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = false}) := by
    simp only [mWald, mArm, one_mul, (harm true).2.2, (harm false).2.2, div_one]
  rw [hw, ha, hb, hc, mul_div_cancel_left₀ _ (ne_of_gt hpos)]

end

end AronowAudit.P029.Wave1.LateIdentity
