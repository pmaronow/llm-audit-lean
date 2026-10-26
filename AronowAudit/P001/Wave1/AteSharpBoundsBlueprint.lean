import AronowAudit.P001.P001_Foundations

/-!
# Sharp ATE bounds with the printed endpoints (P001-T114)

Theorem 7.1.7 (p. 241, proof pp. 241-242), width pp. 242-243,
sharpness p. 244. The statement uses a.e. bounds and binary values, both arms
in support, the printed conditional-arm endpoints `L`, `U`, the width `b - a`,
and sharpness at every `c ∈ [L, U]` with the same observable joint law of `(Y, D)`.

Write `l = ateLower Y D a b`, `u = ateUpper Y D a b` for the imputed endpoints.
`N1` identifies their means with the printed endpoints, `N2` gives interval
membership and width, and `N3` gives attainment of every value with the same
observable law.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.AteSharpBounds

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Sharp ATE bounds with the printed conditional-arm endpoints and sharpness
under equality of observable laws. -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : Ω → ℝ), Measurable Y0 → Measurable Y1 → Measurable D → ∀ (a b : ℝ),
    (∀ᵐ ω ∂μ, Y0 ω ∈ Set.Icc a b ∧ Y1 ω ∈ Set.Icc a b) →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    0 < prob μ {ω | D ω = 0} → 0 < prob μ {ω | D ω = 1} →
    let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
    let L := conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} + a * prob μ {ω | D ω = 0} -
      (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} + b * prob μ {ω | D ω = 1})
    let U := conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} + b * prob μ {ω | D ω = 0} -
      (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} + a * prob μ {ω | D ω = 1})
    mean μ (fun ω => Y1 ω - Y0 ω) ∈ Set.Icc L U ∧ U - L = b - a ∧
    ∀ c ∈ Set.Icc L U, ∃ Z0 Z1 : Ω → ℝ,
      Measurable Z0 ∧ Measurable Z1 ∧
      (∀ᵐ ω ∂μ, Z0 ω ∈ Set.Icc a b ∧ Z1 ω ∈ Set.Icc a b) ∧
      μ.map (fun ω => (observedOutcome (Z0 ω) (Z1 ω) (D ω), D ω)) =
        μ.map (fun ω => (Y ω, D ω)) ∧
      mean μ (fun ω => Z1 ω - Z0 ω) = c

/-- For any integrable observed outcome and a.e. binary `D` with both arms of
positive mass, the imputed endpoint means are the printed conditional-arm endpoints.

The identity `E[Y 1_{D=d}] = E[Y|D=d] P_d` permits cancellation because `P_d > 0`.
Integrating the event decompositions gives `E[l] = L` and `E[u] = U`.
Proof outline: `D = 1_{D=1}` and `1 - D = 1_{D=0}` a.e.; use
`integral_congr_ae`, `integral_indicator`, and linearity of the integral.
The product of `conditionalMeanAt` and `prob` cancels by `div_mul_cancel₀`. -/
def N1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y D : Ω → ℝ), Integrable Y μ → Measurable D → (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    0 < prob μ {ω | D ω = 0} → 0 < prob μ {ω | D ω = 1} → ∀ (a b : ℝ),
    mean μ (fun ω => ateLower (Y ω) (D ω) a b) =
        conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} + a * prob μ {ω | D ω = 0} -
          (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} + b * prob μ {ω | D ω = 1}) ∧
    mean μ (fun ω => ateUpper (Y ω) (D ω) a b) =
        conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} + b * prob μ {ω | D ω = 0} -
          (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} + a * prob μ {ω | D ω = 1})

/-- Integrability of the observed outcome, interval membership and width for
the imputed endpoints, under a.e. bounds and a.e. binary `D`.

There is a probability-one set on which `Y0,Y1 ∈ [a,b]` and `D ∈ {0,1}`.
It is nonempty, so `a ≤ b`. Splitting into `D = 0` and `D = 1` shows
`l ≤ Y1 - Y0 ≤ u` almost surely. Also `u - l = b - a` almost surely, so
`U - L = E[b-a] = b-a`. The integral bounds follow from `integral_mono_ae`;
`Integrable.of_bound` supplies integrability and `integral_congr_ae` gives the width. -/
def N2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : Ω → ℝ), Measurable Y0 → Measurable Y1 → Measurable D → ∀ (a b : ℝ),
    (∀ᵐ ω ∂μ, Y0 ω ∈ Set.Icc a b ∧ Y1 ω ∈ Set.Icc a b) →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    Integrable (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) μ ∧
    mean μ (fun ω => Y1 ω - Y0 ω) ∈ Set.Icc
      (mean μ (fun ω => ateLower (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b))
      (mean μ (fun ω => ateUpper (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b)) ∧
    mean μ (fun ω => ateUpper (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b) -
      mean μ (fun ω => ateLower (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b) = b - a

/-- Every value between the imputed endpoint means is the ATE of a bounded
completion with the same observable law.

Fix `c ∈ [L,U]` and set `q = a + c - L`,
`Z0 = Y0(1-D) + (a+b-q)D`, and `Z1 = Y1D + q(1-D)`.
Both completions lie in `[a,b]` almost surely, and their observed outcome agrees
almost surely with `Y`, with `D` unchanged. The measurable observable pairs
therefore have the same pushforward law, and `E[Z1-Z0] = L + (c-L) = c`.
This construction works without division by `b-a`. Equality of laws follows
from `Measure.map_congr`; the mean follows from linearity and `integral_congr_ae`. -/
def N3 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : Ω → ℝ), Measurable Y0 → Measurable Y1 → Measurable D → ∀ (a b : ℝ),
    (∀ᵐ ω ∂μ, Y0 ω ∈ Set.Icc a b ∧ Y1 ω ∈ Set.Icc a b) →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    ∀ c ∈ Set.Icc
      (mean μ (fun ω => ateLower (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b))
      (mean μ (fun ω => ateUpper (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b)),
    ∃ Z0 Z1 : Ω → ℝ,
      Measurable Z0 ∧ Measurable Z1 ∧
      (∀ᵐ ω ∂μ, Z0 ω ∈ Set.Icc a b ∧ Z1 ω ∈ Set.Icc a b) ∧
      μ.map (fun ω => (observedOutcome (Z0 ω) (Z1 ω) (D ω), D ω)) =
        μ.map (fun ω => (observedOutcome (Y0 ω) (Y1 ω) (D ω), D ω)) ∧
      mean μ (fun ω => Z1 ω - Z0 ω) = c

/-- The nodes suffice: `N2` gives integrability, interval and width for the imputed
endpoints, `N1` identifies them with the printed `L`, `U`, and `N3` gives sharpness. -/
theorem assemble (h1 : N1.{u}) (h2 : N2.{u}) (h3 : N3.{u}) : Target.{u} := by
  intro Ω _ μ _ Y0 Y1 D hY0 hY1 hD a b hbound hbin hD0 hD1 Y L U
  obtain ⟨hYi, hmem, hwidth⟩ := h2 μ Y0 Y1 D hY0 hY1 hD a b hbound hbin
  obtain ⟨hl, hu⟩ := h1 μ Y D hYi hD hbin hD0 hD1 a b
  have hl' : mean μ (fun ω => ateLower (Y ω) (D ω) a b) = L := hl
  have hu' : mean μ (fun ω => ateUpper (Y ω) (D ω) a b) = U := hu
  refine ⟨?_, ?_, ?_⟩
  · rw [← hl', ← hu']; exact hmem
  · rw [← hl', ← hu']; exact hwidth
  · intro c hc
    rw [← hl', ← hu'] at hc
    exact h3 μ Y0 Y1 D hY0 hY1 hD a b hbound hbin c hc

end

end AronowAudit.P001.Wave1.AteSharpBounds
