import AronowAudit.P042.Wave1.SixAtomicBlueprint

/-!
The probability law and finite-average integral for the shared six-voter witness.
-/

set_option autoImplicit false

namespace AronowAudit.P042.Wave1.SixAtomic

open AronowAudit.P042 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n1_proof : N1 := by
  classical
  let s : Finset SixΩ := sixAllocations
  have hs : s.card = 90 := six_design.1
  have hmeasure : sixMeasure =
      (90 : ℝ≥0∞)⁻¹ • ∑ a ∈ s, Measure.dirac a := by
    set_option maxRecDepth 10000 in rfl
  have hdirac (a : SixΩ) : (Measure.dirac a) Set.univ = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_univ a)
  have hmass :
      (∑ a ∈ s, (Measure.dirac a : Measure SixΩ)) Set.univ =
        (90 : ℝ≥0∞) := by
    calc
      (∑ a ∈ s, (Measure.dirac a : Measure SixΩ)) Set.univ =
          (s.card : ℝ≥0∞) := by
        simp only [Measure.finsetSum_apply, hdirac, Finset.sum_const, nsmul_eq_mul,
          mul_one]
      _ = 90 := by norm_num [hs]
  constructor
  · refine ⟨?_⟩
    rw [hmeasure, Measure.smul_apply, smul_eq_mul, hmass]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  · intro f
    change (∫ ω, f ω ∂sixMeasure) = (∑ a ∈ s, f a) / 90
    have hf : ∀ a ∈ s, Integrable f (Measure.dirac a) := by
      intro a _
      exact Integrable.of_finite
    calc
      (∫ ω, f ω ∂sixMeasure) =
          ((90 : ℝ≥0∞)⁻¹).toReal •
            (∫ ω, f ω ∂(∑ a ∈ s, Measure.dirac a)) := by
        rw [hmeasure, integral_smul_measure]
      _ = ((90 : ℝ≥0∞)⁻¹).toReal • (∑ a ∈ s, f a) := by
        rw [integral_finsetSum_measure hf]
        simp only [integral_dirac]
      _ = (∑ a ∈ s, f a) / 90 := by
        simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul,
          div_eq_mul_inv]
        ring

end

end AronowAudit.P042.Wave1.SixAtomic
