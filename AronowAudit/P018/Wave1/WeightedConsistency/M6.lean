import AronowAudit.P018.Wave1.WeightedConsistency.M5

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem m6_proof : M6.{u} := by
  intro g3 g4 g5 U _ k R X Y dir v C H hS hreg hcent
  letI instUnitProbability : IsProbabilityMeasure R.μ := hS.1.1
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hS.1 N
  let β := popBeta R.μ X Y
  let F := fun N (ω : Fin N → U) =>
    (Dreal N)⁻¹ • ∑ d : Dyad N, recordWeightedBlockScore R (v N) β ω d
  obtain ⟨Bq, hBq, hb⟩ := blockScore_uniform_bound R X Y dir v C H hS hreg β
  have hentry (N : ℕ) (ω : Fin N → U) (a : Fin k) :
      F N ω a = (Dreal N)⁻¹ * ∑ d, recordWeightedBlockScore R (v N) β ω d a := by
    simp only [F, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  have hLp (N : ℕ) (a : Fin k) : MemLp (fun ω => F N ω a) 2 (repeatedLaw R N) := by
    simp_rw [hentry]
    exact (memLp_finsetSum _ (fun d _ => blockScore_memLp R hS.1 hreg (v N) β d a 2)).const_mul _
  have hvar (a : Fin k) : Tendsto (fun N => variance (fun ω => F N ω a)
      (repeatedLaw R N)) atTop (𝓝 0) := by
    simp_rw [hentry]
    apply dyad_scaled_variance_tendsto g3 g4 R.μ _ Bq
    · intro N d
      exact blockScore_measurable R hreg (v N) β d a
    · intro N d ω ω' h
      exact congrFun (blockScore_support R (v N) β d ω ω' h) a
    · intro N d
      filter_upwards [hb N d] with ω hω
      exact (norm_le_pi_norm (recordWeightedBlockScore R (v N) β ω d) a).trans hω
  have hmean (N : ℕ) : meanVec (repeatedLaw R N) (F N) = 0 := by
    ext a
    change (∫ ω, F N ω a ∂repeatedLaw R N) = 0
    simp_rw [hentry]
    rw [integral_const_mul, integral_finsetSum _ (fun d _ =>
      (blockScore_memLp R hS.1 hreg (v N) β d a 2).integrable one_le_two)]
    have hz (d : Dyad N) :
        (∫ ω, recordWeightedBlockScore R (v N) β ω d a ∂repeatedLaw R N) = 0 :=
      congrFun (hcent N d) a
    simp_rw [hz]
    simp
  have hh := (g5 (repeatedLaw R)).2 F hLp hvar
  change inProbability (repeatedLaw R) F
  simpa only [hmean, sub_zero] using hh

end
end AronowAudit.P018.Wave1.WeightedConsistency
