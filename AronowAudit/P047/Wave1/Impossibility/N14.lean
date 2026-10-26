import AronowAudit.P047.Wave1.ImpossibilityBlueprint
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

/-- Every atom of the actual fair product prior has the advertised weight. -/
private theorem typePrior_real_singleton (K : ℕ) (σ : Fin K → Bool) :
    (typePrior K).real {σ} = (1 / 2 : ℝ) ^ K := by
  classical
  have hb (b : Bool) : (fairBool {b}).toReal = (1 / 2 : ℝ) := by
    change fairBool.real {b} = (1 / 2 : ℝ)
    unfold fairBool
    rw [bernoulliMeasure_real_apply _ (measurableSet_singleton b)]
    cases b <;> norm_num
  simp only [measureReal_def, typePrior, Measure.pi_singleton, ENNReal.toReal_prod]
  simp_rw [hb]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The weights sum to one, including for the empty cell index type. -/
private theorem prior_weight_sum (K : ℕ) :
    (∑ _σ : Fin K → Bool, (1 / 2 : ℝ) ^ K) = 1 := by
  classical
  have h := sum_measureReal_singleton (μ := typePrior K)
    (Finset.univ : Finset (Fin K → Bool))
  simp only [typePrior_real_singleton, Finset.coe_univ] at h
  simpa only [probReal_univ] using h

theorem prior_average_const (K : ℕ) (a : ℝ) :
    (∑ _σ : Fin K → Bool, (1 / 2 : ℝ) ^ K * a) = a := by
  rw [← Finset.sum_mul, prior_weight_sum, one_mul]

theorem n14_proof : N14 := by
  classical
  intro family M
  let B : Set (Fin (M + 1) → Bool) :=
    {σ | (1 / 12 : ℝ) ≤ |familyEffect family (M + 1) σ - familyCenter family|}
  have hB : MeasurableSet B := (Set.toFinite B).measurableSet
  have hI : Integrable (B.indicator (1 : (Fin (M + 1) → Bool) → ℝ)) (typePrior (M + 1)) :=
    Integrable.of_finite
  have hsum := integral_fintype hI
  rw [integral_indicator_one hB] at hsum
  have hidentity : (typePrior (M + 1)).real B =
      ∑ σ : Fin (M + 1) → Bool, (1 / 2 : ℝ) ^ (M + 1) *
        (if (1 / 12 : ℝ) ≤ |familyEffect family (M + 1) σ - familyCenter family|
          then 1 else 0) := by
    simpa only [typePrior_real_singleton, smul_eq_mul, Set.indicator_apply,
      Set.mem_setOf_eq, B, Pi.one_apply] using hsum
  rw [← hidentity]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (familyEffect_prior_concentration family (M := M + 1) (by omega))

end

end AronowAudit.P047.Wave1.Impossibility
