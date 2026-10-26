import AronowAudit.P002.Wave1.E61EigenvalueBlueprint
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

universe u

/-- Condition the Bernoulli bound on the sample count, and use the allocation and
mean-square bounds. The zero sum-of-squares case has an empty deviation event. -/
theorem n5_proof : N5 := by
  intro hCondition hHoeffding N m r C t a hm hmN hr hrm hC hmean ht
  have hmnat : 0 < m := by omega
  have hNnat : 0 < N := lt_trans hmnat hmN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmnat
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  let V : ℝ := ∑ i, a i ^ 2
  have hVnonneg : 0 ≤ V := Finset.sum_nonneg (fun i _ => sq_nonneg (a i))
  by_cases hVzero : V = 0
  · have ha (i : Fin N) : a i = 0 := by
      have hi : a i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (a j))).mp
          hVzero i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hi
    have hmean0 : mean a = 0 := by simp [mean, ha]
    have hgroup0 (T : Finset (Fin N)) : groupMean T a = 0 := by
      simp [groupMean, ha]
    have hfilter : ((Finset.univ.powersetCard m).filter
        (fun T => t ≤ |groupMean T a - mean a|)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      have hh := (Finset.mem_filter.mp hT).2
      rw [hgroup0, hmean0, sub_self, abs_zero] at hh
      exact (not_le.mpr ht) hh
    rw [hfilter]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity
  · have hVpos : 0 < V := lt_of_le_of_ne hVnonneg (Ne.symm hVzero)
    let p : ℝ := (m : ℝ) / N
    have hp : 0 ≤ p := (div_pos hmR hN).le
    have hp1 : p ≤ 1 := (div_le_one hN).2 (by exact_mod_cast hmN.le)
    have hs : 0 ≤ (m : ℝ) * t := (mul_pos hmR ht).le
    have hdev (T : Finset (Fin N)) (hcard : T.card = m) :
        (∑ i ∈ T, a i) - p * (∑ i, a i) =
          (m : ℝ) * (groupMean T a - mean a) := by
      unfold groupMean mean
      rw [hcard]
      dsimp [p]
      field_simp [hN.ne', hmR.ne'] <;> ring
    have hevent (T : Finset (Fin N)) (hcard : T.card = m) :
        (t ≤ |groupMean T a - mean a|) ↔
          ((m : ℝ) * t ≤ |(∑ i ∈ T, a i) - p * ∑ i, a i|) := by
      rw [hdev T hcard, abs_mul, abs_of_pos hmR]
      exact (mul_le_mul_iff_right₀ hmR).symm
    have hfilter : (Finset.univ.powersetCard m).filter
        (fun T => t ≤ |groupMean T a - mean a|) =
        (Finset.univ.powersetCard m).filter
          (fun T => (m : ℝ) * t ≤ |(∑ i ∈ T, a i) - p * ∑ i, a i|) := by
      apply Finset.filter_congr
      intro T hT
      exact hevent T (Finset.mem_powersetCard.mp hT).2
    have hcond := hCondition N m hmnat hmN
      (fun T => (m : ℝ) * t ≤ |(∑ i ∈ T, a i) - p * ∑ i, a i|)
    have hbern := hHoeffding N p a ((m : ℝ) * t) hp hp1 hs hVpos
    have hVle : V ≤ C * (N : ℝ) := (div_le_iff₀ hN).mp hmean
    have hsq : (r * (N : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 := by
      have hmul := mul_nonneg (sub_nonneg.mpr hrm)
        (add_nonneg hmR.le (mul_nonneg hr.le hN.le))
      nlinarith [hmul]
    have hratio : r ^ 2 * (N : ℝ) * V ≤ (m : ℝ) ^ 2 * C := by
      calc
        _ ≤ r ^ 2 * (N : ℝ) * (C * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hVle (by positivity)
        _ = (r * (N : ℝ)) ^ 2 * C := by ring
        _ ≤ (m : ℝ) ^ 2 * C := mul_le_mul_of_nonneg_right hsq hC.le
    have hexponent : -2 * ((m : ℝ) * t) ^ 2 / V ≤
        -2 * r ^ 2 * (N : ℝ) * t ^ 2 / C := by
      apply (div_le_div_iff₀ hVpos hC).2
      have hh := mul_le_mul_of_nonneg_right hratio (sq_nonneg t)
      nlinarith [hh]
    rw [hfilter]
    calc
      _ ≤ ((N : ℝ) + 1) * ∑ T : Finset (Fin N),
          if (m : ℝ) * t ≤ |(∑ i ∈ T, a i) - p * ∑ i, a i| then
            p ^ T.card * (1 - p) ^ (N - T.card) else 0 := hcond
      _ ≤ ((N : ℝ) + 1) * (2 * Real.exp (-2 * ((m : ℝ) * t) ^ 2 / V)) :=
        mul_le_mul_of_nonneg_left hbern (by positivity)
      _ = 2 * ((N : ℝ) + 1) * Real.exp (-2 * ((m : ℝ) * t) ^ 2 / V) := by ring
      _ ≤ 2 * ((N : ℝ) + 1) * Real.exp (-2 * r ^ 2 * N * t ^ 2 / C) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity)

end
end AronowAudit.P002.Wave1.E61Eigenvalue
