import AronowAudit.P029.P029_Audit

/-!
# Wave1 blueprint: P029-T25, `AronowAudit.P029.finite_late_identity` (bridge to paper scope)

Paper: P029 p. 495 (PDF p. 4), equation (3) and its two ITT identities, under the five IV
assumptions on an arbitrary probability space, with integrable potential outcomes and no
defiers only almost surely. The held `finite_late_identity` is proved but only for finite
unit lists with pointwise no-defiers; the general `late_identity` is an admitted draft and is
NOT a proof input. Resolution: `bridge` — a new general-probability theorem.

`Target` is the full (a)-(c) contract; the fidelity theorem checks by `rfl` that it is
literally the statement of the frozen draft `AronowAudit.P029.late_identity` (whose unfinished
proof is never used: `type_of%` only reads the statement).

Final theorem (writers): `AronowAudit.P029.Wave1.late_identity_paper_scope`
in `AronowAudit/P029/Wave1/LateIdentity.lean`.

Nodes (mapper record 6): N1 independent-event mean; N2 fixed-response regularity; N3 arm
means = fixed-response means; N4 almost-sure ITT integration; N5 complier normalization.
Nodes needing earlier nodes take them as hypotheses.
-/

namespace AronowAudit.P029.Wave1.LateIdentity

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

universe u v

noncomputable section

/-- The frozen final statement: equation (3) with both ITT identities, on an arbitrary
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

/-- Fidelity check: `Target` is literally the statement of the frozen general draft
`late_identity` (same universes). -/
theorem target_eq_late_identity_statement :
    Target.{u, v} = type_of% @AronowAudit.P029.late_identity.{u, v} := rfl

/-- **Node L-N1** (`independent_event_mean`; mapper record 6, paper-proof step 2). On a
probability space, an integrable `v` independent of a measurable Boolean `Z` has the same
mean on every positive-probability arm: `∫_{Z=z} v = P(Z=z) ∫ v`, hence
`mCE μ v {Z = z} = ∫ v`. Use `IndepFun.comp` (indicator of `{z}` is measurable on `Bool`)
and `IndepFun.integral_fun_mul_eq_mul_integral`, `integral_indicator`. -/
def N1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → Bool) (v : Ω → ℝ), Measurable Z → Integrable v μ → IndepFun Z v μ →
      ∀ z : Bool, 0 < mP μ {ω | Z ω = z} → mCE μ v {ω | Z ω = z} = ∫ ω, v ω ∂μ

/-- **Node L-N2** (`fixed_response_measurable_integrable`; mapper record 6, step 1). From
`IVAssumptions`: for each fixed arm `z`, the fixed-response receipt `bit (receipt z)` and
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

/-- **Node L-N3** (`arm_means`; mapper record 6, steps 2-3). On the arm `{Z = z}` observed
receipt and outcome equal the fixed responses at `z` (`setIntegral_congr_fun`); by L-N1 the
arm means are the unconditional fixed-response means. Both arms have positive mass
(`0 < P(Z=1) < 1`), so the arm mean of the constant `1` is `1`. Takes L-N1 and L-N2. -/
def N3 : Prop :=
  N1.{u} → N2.{u, v} →
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
    IVAssumptions μ U Z → ∀ z : Bool,
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = z} =
          ∫ ω, bit ((U ω).receipt z) ∂μ ∧
      mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = z} = ∫ ω, (U ω).outcome z ∂μ ∧
      mCE μ (fun _ => (1 : ℝ)) {ω | Z ω = z} = 1

/-- **Node L-N4** (`ae_no_defier_itt`; mapper record 6, step 4). Since `μ {defier} = 0`, the
pointwise identities `unit_itt_identities` hold almost everywhere; integrating them
(`integral_sub`, `integral_congr_ae`) gives `ΔD = P(C)` and `ΔY = E(1_C τ)` for the
fixed-response means. Takes L-N2 (integrability). -/
def N4 : Prop :=
  N2.{u, v} →
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
    IVAssumptions μ U Z →
      (∫ ω, bit ((U ω).receipt true) ∂μ) - (∫ ω, bit ((U ω).receipt false) ∂μ) =
          mP μ {ω | (U ω).complier} ∧
      (∫ ω, (U ω).outcome true ∂μ) - (∫ ω, (U ω).outcome false ∂μ) =
          ∫ ω, (if (U ω).complier then (U ω).tau else 0) ∂μ

/-- **Node L-N5** (`late_normalization`; mapper record 6, step 5). With positive complier mass,
`E(1_C τ) = P(C) · E(τ | C)` (restricted integral = integral of the indicator; cancel
`P(C) ≠ 0`). Takes L-N2 (measurability of `C`). -/
def N5 : Prop :=
  N2.{u, v} →
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
    IVAssumptions μ U Z → 0 < mP μ {ω | (U ω).complier} →
      (∫ ω, (if (U ω).complier then (U ω).tau else 0) ∂μ) =
        mP μ {ω | (U ω).complier} * mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier}

/-- The nodes suffice (mapper record 6, steps 5-6: relevance forces `P(C) > 0`; the unit-weight
Wald ratio is `ΔY / ΔD`). -/
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
