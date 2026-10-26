import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint

/-! The exact randomization variance, from the population moments. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem n3_proof : N3 := by
  intro hMom n
  have hq0 : (∑ i, hcQ n i) = 0 := (hMom n).1
  have hq2 : (∑ i, hcQ n i ^ 2) = (hcN n : ℝ) := (hMom n).2
  let a : ℝ := (2 : ℝ) ^ (2 * (n + 1) ^ 2)
  have ha2 : a ^ 2 = (hcN n : ℝ) := by
    calc
      a ^ 2 = (2 : ℝ) ^ ((2 * (n + 1) ^ 2) * 2) := by
        dsimp [a]
        rw [← pow_mul]
      _ = (2 : ℝ) ^ (4 * (n + 1) ^ 2) := by
        congr 1
        ring
      _ = (hcN n : ℝ) := by simp [hcN, hcK]
  have hN16 : (16 : ℝ) ≤ (hcN n : ℝ) := by exact_mod_cast hcN_ge n
  have hN : (hcN n : ℝ) ≠ 0 := by linarith
  have hN1 : (hcN n : ℝ) - 1 ≠ 0 := by linarith

  have hmean1 : groupMean Finset.univ (hypercubePopulation n).y1 = 0 := by
    unfold groupMean
    simp only [Finset.card_univ, Fintype.card_fin]
    change ((∑ i : Fin (hcN n), hcQ n i / a) / (hcN n : ℝ)) = 0
    rw [← Finset.sum_div, hq0]
    simp
  have hmean0 : groupMean Finset.univ (hypercubePopulation n).y0 = 0 := by
    simp [groupMean, hypercubePopulation]
  have hvar1 : popVariance (hypercubePopulation n).y1 = 1 / (hcN n : ℝ) := by
    unfold popVariance
    rw [hmean1]
    simp only [sub_zero, Fintype.card_fin]
    change (∑ i : Fin (hcN n), (hcQ n i / a) ^ 2) / (hcN n : ℝ) = _
    simp_rw [div_pow]
    rw [← Finset.sum_div, hq2, ha2, div_self hN]
  have hvar0 : popVariance (hypercubePopulation n).y0 = 0 := by
    unfold popVariance
    rw [hmean0]
    simp [hypercubePopulation]
  have hcov : popCovariance (hypercubePopulation n).y1
      (hypercubePopulation n).y0 = 0 := by
    unfold popCovariance
    rw [hmean0]
    simp [hypercubePopulation]

  constructor
  · have hsize := population_sizes (hypercubePopulation n)
    have hK : 2 ≤ Fintype.card (Fin (hcN n)) - 2 := by
      simpa only [hypercubePopulation, Fintype.card_fin] using hsize.2.1
    have hMN : 2 ≤ Fintype.card (Fin (hcN n)) := by
      simpa only [hypercubePopulation, Fintype.card_fin] using hsize.2.2.1
    change randomizationVariance 2 (hypercubePopulation n).y1
      (hypercubePopulation n).y0 = _
    rw [randomization_variance_alternative 2 (by norm_num) hK hMN,
      hvar1, hvar0, hcov]
    simp only [Fintype.card_fin, Nat.cast_ofNat, mul_zero, add_zero]
    field_simp [hN, hN1] <;> ring
  · change groupMean Finset.univ (hypercubePopulation n).y1 -
      groupMean Finset.univ (hypercubePopulation n).y0 = 0
    rw [hmean1, hmean0, sub_self]

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
