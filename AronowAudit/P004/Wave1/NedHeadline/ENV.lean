import AronowAudit.P004.Wave1.NedHeadlineBlueprint
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

/-- Extend an eventual power envelope to every radius at least one. -/
theorem env_proof : ENV := by
  intro ψ e C S hψ hanti he _hS htail
  let R : ℝ := max 1 S
  let B : ℝ := ψ 1 * R ^ e
  let A : ℝ := max C B
  have hR1 : 1 ≤ R := le_max_left 1 S
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hψ1 : 0 ≤ ψ 1 := hψ 1 (by norm_num)
  have hB : 0 ≤ B := mul_nonneg hψ1 (Real.rpow_nonneg hR0.le e)
  refine ⟨A, hB.trans (le_max_right C B), ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hnegpow : 0 ≤ t ^ (-e) := Real.rpow_nonneg ht0.le (-e)
  by_cases hSt : S ≤ t
  · calc
      ψ t ≤ C * t ^ (-e) := htail t hSt
      _ ≤ A * t ^ (-e) :=
        mul_le_mul_of_nonneg_right (le_max_left C B) hnegpow
  · have htS : t < S := lt_of_not_ge hSt
    have htR : t ≤ R := htS.le.trans (le_max_right 1 S)
    have hpowers : t ^ e ≤ R ^ e := Real.rpow_le_rpow ht0.le htR he
    have hte : 0 < t ^ e := Real.rpow_pos_of_pos ht0 e
    have hcompact : ψ 1 ≤ B * t ^ (-e) := by
      rw [Real.rpow_neg ht0.le e, ← div_eq_mul_inv]
      apply (le_div_iff₀ hte).2
      exact mul_le_mul_of_nonneg_left hpowers hψ1
    calc
      ψ t ≤ ψ 1 := hanti (by norm_num) ht0.le ht
      _ ≤ B * t ^ (-e) := hcompact
      _ ≤ A * t ^ (-e) :=
        mul_le_mul_of_nonneg_right (le_max_right C B) hnegpow

end
end AronowAudit.P004.Wave1.NedHeadline
