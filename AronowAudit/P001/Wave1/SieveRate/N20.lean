import AronowAudit.P001.Wave1.SieveRateBlueprint

/-! # Full uniform risk dominates the fixed-interval risk -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n20_proof : N20 := by
  classical
  intro p
  have hunif : uniformLaw (0 : ℝ) 1 = volume.restrict (Set.Icc (0 : ℝ) 1) := by
    have hdensity :
        (fun x : ℝ => ENNReal.ofReal
          (if x ∈ Set.Icc (0 : ℝ) 1 then (1 - 0)⁻¹ else 0)) =
        (Set.Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) := by
      funext x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [hx]
    rw [uniformLaw, hdensity, withDensity_indicator_one measurableSet_Icc]
  have hint : IntegrableOn (fun z : ℝ => p.eval z ^ 2) (Set.Icc (0 : ℝ) 1) :=
    (p.continuous.pow 2).integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun z : ℝ => p.eval z ^ 2) :=
    Filter.Eventually.of_forall fun z => sq_nonneg (p.eval z)
  have hsub : Set.Icc (0 : ℝ) (1 / 2) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, hz.2.trans (by norm_num)⟩
  have hmono : (∫ z in Set.Icc (0 : ℝ) (1 / 2), p.eval z ^ 2) ≤
      ∫ z in Set.Icc (0 : ℝ) 1, p.eval z ^ 2 :=
    setIntegral_mono_set hint hnonneg (Filter.Eventually.of_forall fun z hz => hsub hz)
  simpa only [regionInt, hunif, sieveM, sub_zero, pow_two] using hmono

end

end AronowAudit.P001.Wave1.SieveRate
