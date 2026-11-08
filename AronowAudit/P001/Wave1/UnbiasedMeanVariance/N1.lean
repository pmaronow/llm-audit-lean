import AronowAudit.P001.Wave1.UnbiasedMeanVarianceBlueprint

namespace AronowAudit.P001.Wave1.UnbiasedMeanVariance

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableUnbiasedMeanVarianceN1 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n1_proof : N1 := by
  intro Ω X n ω hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : (∑ i ∈ Finset.range n, (X i ω - sampleMean X n ω) ^ 2) =
      (∑ i ∈ Finset.range n, (X i ω) ^ 2) -
        2 * sampleMean X n ω * (∑ i ∈ Finset.range n, X i ω) +
        (n : ℝ) * (sampleMean X n ω) ^ 2 := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hs]
  unfold sampleVariance sampleMean
  field_simp [hn0] <;> ring

end
end AronowAudit.P001.Wave1.UnbiasedMeanVariance
