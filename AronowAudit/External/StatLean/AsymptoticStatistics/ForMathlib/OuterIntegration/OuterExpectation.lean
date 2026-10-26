/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic



/-!
# Outer expectation `E*`

The **outer expectation** `E*[X]` of a (possibly non-measurable) function
`X : Ω → ℝ≥0∞` with respect to a measure `μ` is the infimum of `∫⁻ U ∂μ`
over all *measurable majorants* `U ≥ X`:
`E*[X] = ⨅ {U : Measurable, X ≤ U}, ∫⁻ U ∂μ`.

This is the outer-integral construction used to give meaning to weak
convergence of non-measurable maps (van der Vaart, *Asymptotic Statistics*
§18.1; Hoffmann-Jørgensen; van der Vaart–Wellner, *Weak Convergence and
Empirical Processes*, Ch. 1.2). It is the cornerstone primitive of the
abstract-Donsker / empirical-process framework, where the empirical process
need not be Borel measurable.

## Main definitions

* `MeasureTheory.outerExpectation μ X` — the outer expectation `E*[X]`.
* `MeasureTheory.Measure.outerMeasureStar μ A` — the outer measure
  `P*(A) = E*[1_A]`.

## Main results

* `outerExpectation_eq_lintegral` — for measurable `X`, `E*[X] = ∫⁻ X`.
* `outerExpectation_mono` — monotonicity in `X`.
* `outerExpectation_add_le` — binary subadditivity:
  `E*[X + Y] ≤ E*[X] + E*[Y]`.

Additional results cover scaling by finite constants, constant functions, and
the equality of `outerMeasureStar` with the measure on measurable sets.

## Implementation notes

The infimum is taken over the **subtype** `{U // Measurable U ∧ X ≤ U}`
rather than a bounded `⨅ U ∈ {…}`, keeping a single clean `iInf` so the
`ENNReal` infimum-manipulation lemmas (`ENNReal.iInf_add`, `le_iInf`,
`iInf_le`, …) apply directly. The
majorant subtype is always inhabited by the constant `⊤` function, recorded
as the `Nonempty` instance below.
-/

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Outer expectation `E*[X]` of a (possibly non-measurable) function
`X : Ω → ℝ≥0∞`: the infimum of `∫⁻ U ∂μ` over all measurable majorants
`U ≥ X` (van der Vaart §18.1; Hoffmann-Jørgensen / van der Vaart–Wellner
Ch. 1.2).

The index is the **subtype** `{U // Measurable U ∧ X ≤ U}` (inlined rather
than wrapped in a named type, so the `MeasurableSpace` instance and the
subtype coercion to `Ω → ℝ≥0∞` stay transparent to elaboration). This keeps a
single clean `iInf` so the `ENNReal` infimum-manipulation lemmas apply
directly.

Constitutive (vdV §18.1 p.258): the outer integral is *defined* as this
infimum over measurable majorants; the measurability and majorization
conditions on `U` are part of the definition. -/
noncomputable def outerExpectation (μ : Measure Ω) (X : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ U : {U : Ω → ℝ≥0∞ // Measurable U ∧ X ≤ U}, ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ

/-- The majorant subtype is always inhabited: the constant `⊤` function is a
measurable majorant of any `X`. (Recorded so the `iInf` is over a nonempty
index, which some `ENNReal` infimum lemmas require.) -/
instance (X : Ω → ℝ≥0∞) :
    Nonempty {U : Ω → ℝ≥0∞ // Measurable U ∧ X ≤ U} :=
  ⟨⟨fun _ => ⊤, measurable_const, le_top⟩⟩

/-! ### Fundamental lemmas -/

/-- For a measurable `X`, the outer expectation reduces to
the ordinary lower Lebesgue integral: `E*[X] = ∫⁻ X`. -/
theorem outerExpectation_eq_lintegral {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    (hX : Measurable X) : outerExpectation μ X = ∫⁻ ω, X ω ∂μ := by
  refine le_antisymm ?_ ?_
  · -- `X` is itself a measurable majorant of `X`, so the infimum is `≤ ∫⁻ X`.
    exact iInf_le (fun U : {U : Ω → ℝ≥0∞ // Measurable U ∧ X ≤ U} =>
      ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ) ⟨X, hX, le_rfl⟩
  · -- Every majorant `U ≥ X` has `∫⁻ X ≤ ∫⁻ U`.
    refine le_iInf fun U => ?_
    exact lintegral_mono U.2.2

/-- Outer expectation is monotone in the integrand. -/
theorem outerExpectation_mono {μ : Measure Ω} {X Y : Ω → ℝ≥0∞} (hXY : X ≤ Y) :
    outerExpectation μ X ≤ outerExpectation μ Y := by
  -- Every measurable majorant of `Y` is a measurable majorant of `X`
  -- (by `X ≤ Y ≤ U`). The infimum over the smaller set of majorants of `Y`
  -- is therefore at least the infimum over the larger set of majorants of `X`.
  refine le_iInf fun V => ?_
  exact iInf_le (fun U : {U : Ω → ℝ≥0∞ // Measurable U ∧ X ≤ U} =>
    ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ) ⟨(V : Ω → ℝ≥0∞), V.2.1, le_trans hXY V.2.2⟩

/-- Binary subadditivity of outer expectation:
`E*[X + Y] ≤ E*[X] + E*[Y]`.

Countable subadditivity of `E*` underlies the outer-integration framework, and
the binary case is the crux. The proof pulls the two infima out of the sum on the right via
`ENNReal.iInf_add` / `ENNReal.add_iInf`, then bounds `E*[X+Y]` by the sum
majorant `U + V` and uses additivity of the lower integral
(`lintegral_add_left`, available because the majorants carry measurability). -/
theorem outerExpectation_add_le {μ : Measure Ω} (X Y : Ω → ℝ≥0∞) :
    outerExpectation μ (X + Y) ≤ outerExpectation μ X + outerExpectation μ Y := by
  -- Unfold all three outer expectations, then pull both infima out of the
  -- sum on the right-hand side.
  simp only [outerExpectation]
  rw [ENNReal.iInf_add]
  refine le_iInf fun U => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun V => ?_
  -- `U + V` is a measurable majorant of `X + Y`.
  have hUVmeas : Measurable (fun ω => (U : Ω → ℝ≥0∞) ω + (V : Ω → ℝ≥0∞) ω) :=
    U.2.1.add V.2.1
  have hUVmaj : (X + Y) ≤ fun ω => (U : Ω → ℝ≥0∞) ω + (V : Ω → ℝ≥0∞) ω := by
    intro ω
    exact add_le_add (U.2.2 ω) (V.2.2 ω)
  -- Bound `E*[X+Y]` by the integral of this majorant, then split the integral.
  calc
    (⨅ W : {W : Ω → ℝ≥0∞ // Measurable W ∧ (X + Y) ≤ W},
          ∫⁻ ω, (W : Ω → ℝ≥0∞) ω ∂μ)
        ≤ ∫⁻ ω, ((U : Ω → ℝ≥0∞) ω + (V : Ω → ℝ≥0∞) ω) ∂μ :=
          iInf_le (fun W : {W : Ω → ℝ≥0∞ // Measurable W ∧ (X + Y) ≤ W} =>
            ∫⁻ ω, (W : Ω → ℝ≥0∞) ω ∂μ) ⟨_, hUVmeas, hUVmaj⟩
    _ = (∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ) + ∫⁻ ω, (V : Ω → ℝ≥0∞) ω ∂μ :=
          lintegral_add_left U.2.1 _


/-! ### Scaling, constants, and the induced outer measure -/

/-- Outer expectation commutes with scaling by a finite constant.

The hypothesis `c ≠ ⊤` is used when moving multiplication through the infimum
and when dividing a majorant by nonzero `c`. The zero case is handled separately.
The proof scales measurable majorants in both directions and uses
`lintegral_const_mul` for their integrals.

The excluded value `c = ⊤` gives `⊤` where `X ω > 0` and `0` where
`X ω = 0`. -/
theorem outerExpectation_const_smul {μ : Measure Ω} (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (X : Ω → ℝ≥0∞) :
    outerExpectation μ (c • X) = c • outerExpectation μ X := by
  -- `c • ·` on `ℝ≥0∞`-functions is pointwise multiplication.
  have hsmul : (c • X) = fun ω => c * X ω := by
    funext ω; simp [Pi.smul_apply, smul_eq_mul]
  rw [hsmul, smul_eq_mul]
  -- Unfold both outer expectations, then pull `c` inside the RHS infimum.
  simp only [outerExpectation]
  rw [ENNReal.mul_iInf (fun h => absurd h hc)]
  -- `c * ∫⁻ V = ∫⁻ (c • V)` for each majorant `V` of `X`.
  refine le_antisymm ?_ ?_
  · -- `E*[c·X] ≤ ⨅_V (c * ∫⁻ V)`: each `c • V` is a measurable majorant of `c·X`.
    refine le_iInf fun V => ?_
    rw [← lintegral_const_mul c V.2.1]
    refine iInf_le (fun U : {U : Ω → ℝ≥0∞ // Measurable U ∧ (fun ω => c * X ω) ≤ U} =>
      ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ)
      ⟨fun ω => c * (V : Ω → ℝ≥0∞) ω, measurable_const.mul V.2.1, ?_⟩
    intro ω; dsimp only; gcongr; exact V.2.2 ω
  · -- `⨅_V (c * ∫⁻ V) ≤ E*[c·X]`: for `c ≠ 0`, divide each majorant `U` of `c·X` by `c`.
    rcases eq_or_ne c 0 with hc0 | hc0
    · simp [hc0]
    refine le_iInf fun U => ?_
    -- `c⁻¹ • U` is a measurable majorant of `X`.
    refine le_trans (iInf_le (fun V : {V : Ω → ℝ≥0∞ // Measurable V ∧ X ≤ V} =>
      c * ∫⁻ ω, (V : Ω → ℝ≥0∞) ω ∂μ)
      ⟨fun ω => c⁻¹ * (U : Ω → ℝ≥0∞) ω, measurable_const.mul U.2.1, ?_⟩) ?_
    · intro ω
      -- `X ω ≤ c⁻¹ * U ω` from `c * X ω ≤ U ω`.
      rw [← ENNReal.mul_le_iff_le_inv hc0 hc]
      exact U.2.2 ω
    · -- `c * ∫⁻ (c⁻¹ • U) = ∫⁻ U`.
      erw [← lintegral_const_mul c (measurable_const.mul U.2.1)]
      refine lintegral_mono fun ω => ?_
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hc, one_mul]

/-- Outer expectation of a constant function: `E*[fun _ => c] = c * μ univ`. -/
theorem outerExpectation_const {μ : Measure Ω} (c : ℝ≥0∞) :
    outerExpectation μ (fun _ => c) = c * μ Set.univ := by
  rw [outerExpectation_eq_lintegral measurable_const, lintegral_const]

/-- The **outer measure** induced by `μ`: `P*(A) = E*[1_A]`, the outer
expectation of the indicator of `A`. -/
noncomputable def Measure.outerMeasureStar (μ : Measure Ω) (A : Set Ω) : ℝ≥0∞ :=
  outerExpectation μ (A.indicator 1)

/-- For a measurable set, the outer measure agrees with the measure. -/
theorem outerMeasureStar_eq_measure {μ : Measure Ω} {A : Set Ω}
    (hA : MeasurableSet A) : μ.outerMeasureStar A = μ A := by
  rw [Measure.outerMeasureStar,
    outerExpectation_eq_lintegral (measurable_one.indicator hA),
    lintegral_indicator hA]
  simp


end MeasureTheory
