import AronowAudit.P018.Wave1.WeightedConsistency.M5
import AronowAudit.P018.Wave1.WeightedConsistency.G3

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem normalized_dyad_count_le {N : ℕ} (hN : 2 ≤ N) :
    ((N : ℝ) / (Dreal N)^2) * (N : ℝ)^3 ≤ 16 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ = (N : ℝ) * ((N : ℝ)^3 / (Dreal N)^2) := by ring
    _ ≤ (N : ℝ) * (16 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (dyad_normalization_rate hN) hn.le
    _ = 16 := mul_div_cancel₀ _ hn.ne'

theorem m11_proof : M11.{u} := by
  intro _ g4 U _ k R X Y dir v C H hS hreg
  letI instUnitProbability : IsProbabilityMeasure R.μ := hS.1.1
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hS.1 N
  let β := popBeta R.μ X Y
  obtain ⟨Bq, hBq, hb⟩ := blockScore_uniform_bound R X Y dir v C H hS hreg β
  refine ⟨32 * Bq^2, ?_⟩
  intro N
  by_cases hN : 2 ≤ N
  · let q := fun d : Dyad N => fun ω : Fin N → U => recordWeightedBlockScore R (v N) β ω d
    have hLp (d : Dyad N) (a : Fin k) : MemLp (fun ω => q d ω a) 2 (repeatedLaw R N) :=
      blockScore_memLp R hS.1 hreg (v N) β d a 2
    have hbound (d : Dyad N) (a : Fin k) : ∀ᵐ ω ∂repeatedLaw R N, |q d ω a| ≤ Bq :=
      (hb N d).mono (fun ω hω => (norm_le_pi_norm _ a).trans hω)
    have hcov (d f : Dyad N) (a b : Fin k) :
        |covariance (fun ω => q d ω a) (fun ω => q f ω b) (repeatedLaw R N)| ≤
          if overlap d f then 2 * Bq^2 else 0 := by
      split_ifs with hov
      · exact abs_covariance_le_two_sq _ (hLp d a) (hLp f b) (hbound d a) (hbound f b)
      · have hz := g2_proof R.μ (members d) (members f) (fun ω => q d ω a) (fun ω => q f ω b)
          (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hov))
          (blockScore_measurable R hreg (v N) β d a)
          (blockScore_measurable R hreg (v N) β f b)
          (fun ω ω' h => congrFun (blockScore_support R (v N) β d ω ω' h) a)
          (fun ω ω' h => congrFun (blockScore_support R (v N) β f ω ω' h) b)
          (hLp d a) (hLp f b)
        have hz' : covariance (fun ω => q d ω a) (fun ω => q f ω b) (repeatedLaw R N) = 0 := hz
        rw [hz']
        simp only [abs_zero, le_refl]
    have hv (a b : Fin k) : |varMat (repeatedLaw R N) (fun ω => ∑ d, q d ω) a b| ≤
        2 * Bq^2 * (N : ℝ)^3 := by
      change |covariance (fun ω => (∑ d, q d ω) a) (fun ω => (∑ d, q d ω) b) _| ≤ _
      simp only [Finset.sum_apply]
      rw [covariance_fun_sum_fun_sum (fun d => hLp d a) (fun f => hLp f b)]
      calc
        _ ≤ ∑ d, |∑ f, covariance (fun ω => q d ω a) (fun ω => q f ω b) (repeatedLaw R N)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d, ∑ f, if overlap d f then 2 * Bq^2 else 0 := by
          apply Finset.sum_le_sum
          intro d hd
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum (fun f _ => hcov d f a b))
        _ = 2 * Bq^2 * ∑ d : Dyad N,
            ((univ.filter (fun f : Dyad N => (members d ∩ members f).Nonempty)).card : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          rw [← Finset.sum_filter]
          simp only [sum_const, nsmul_eq_mul]
          have he : ((univ : Finset (Dyad N)).filter (fun f => overlap d f)) =
              (univ : Finset (Dyad N)).filter (fun f => (members d ∩ members f).Nonempty) := by
            apply Finset.filter_congr
            intro f hf
            rfl
          rw [he]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (g4 N).1 (by positivity)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro b
    change |((N : ℝ) / (Dreal N)^2) * varMat (repeatedLaw R N) (fun ω => ∑ d, q d ω) a b| ≤ _
    rw [abs_mul, abs_of_nonneg (show 0 ≤ (N : ℝ) / (Dreal N)^2 by positivity)]
    calc
      _ ≤ ((N : ℝ) / (Dreal N)^2) * (2 * Bq^2 * (N : ℝ)^3) :=
        mul_le_mul_of_nonneg_left (hv a b) (by positivity)
      _ = 2 * Bq^2 * (((N : ℝ) / (Dreal N)^2) * (N : ℝ)^3) := by ring
      _ ≤ 2 * Bq^2 * 16 := mul_le_mul_of_nonneg_left (normalized_dyad_count_le hN) (by positivity)
      _ = _ := by ring
  · have hsmall : N = 0 ∨ N = 1 := by omega
    rcases hsmall with rfl | rfl <;> simp [targetMeat, Dreal, sq_nonneg]

end
end AronowAudit.P018.Wave1.WeightedConsistency
