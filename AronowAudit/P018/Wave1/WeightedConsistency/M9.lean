import AronowAudit.P018.Wave1.WeightedConsistency.M5

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem meat_normalization_rate {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ)^7 / (Dreal N)^4 ≤ 256 / (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (N : ℝ)^7 / ((N : ℝ)^2 / 4)^4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) (Dreal_lower hN) 4
    _ = 256 / (N : ℝ) := by field_simp; ring

def meatProduct {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (v : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (β : Vec k) (a b : Fin k) (P : Dyad N × Dyad N) (ω : Fin N → U) : ℝ :=
  if overlap P.1 P.2 then recordWeightedBlockScore R v β ω P.1 a *
    recordWeightedBlockScore R v β ω P.2 b else 0

theorem m9_proof : M9.{u} := by
  intro g3 g4 g5 U _ k R X Y dir v C H hS hreg
  letI instUnitProbability : IsProbabilityMeasure R.μ := hS.1.1
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hS.1 N
  let β := popBeta R.μ X Y
  obtain ⟨Bq, hBq, hb⟩ := blockScore_uniform_bound R X Y dir v C H hS hreg β
  have hm (N : ℕ) (a b : Fin k) (P : Dyad N × Dyad N) :
      Measurable (meatProduct R (v N) β a b P) := by
    unfold meatProduct
    split_ifs
    · exact (blockScore_measurable R hreg (v N) β P.1 a).mul
        (blockScore_measurable R hreg (v N) β P.2 b)
    · exact measurable_const
  have hs (N : ℕ) (a b : Fin k) (P : Dyad N × Dyad N) (ω ω' : Fin N → U)
      (h : ∀ i ∈ pairSupport P, ω i = ω' i) :
      meatProduct R (v N) β a b P ω = meatProduct R (v N) β a b P ω' := by
    unfold meatProduct
    split_ifs with hP
    · have hd := blockScore_support R (v N) β P.1 ω ω'
        (fun i hi => h i (by simp [pairSupport, hP, hi]))
      have hf := blockScore_support R (v N) β P.2 ω ω'
        (fun i hi => h i (by simp [pairSupport, hP, hi]))
      rw [hd, hf]
    · rfl
  have hbound (N : ℕ) (a b : Fin k) (P : Dyad N × Dyad N) :
      ∀ᵐ ω ∂repeatedLaw R N, |meatProduct R (v N) β a b P ω| ≤ Bq^2 := by
    filter_upwards [hb N P.1, hb N P.2] with ω hd hf
    unfold meatProduct
    split_ifs
    · rw [abs_mul, pow_two]
      exact mul_le_mul ((norm_le_pi_norm _ a).trans hd)
        ((norm_le_pi_norm _ b).trans hf) (abs_nonneg _) hBq
    · simp [sq_nonneg]
  have hentry (N : ℕ) (ω : Fin N → U) (a b : Fin k) :
      scaledMeatAt R v N β ω a b = ((N : ℝ) / (Dreal N)^2) *
        ∑ P : Dyad N × Dyad N, meatProduct R (v N) β a b P ω := by
    simp only [scaledMeatAt, meat, Matrix.sum_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type, meatProduct, overlap, matrix_ite_apply, outer, Matrix.zero_apply, Pi.zero_apply]
    congr 1
  have hprodLp (N : ℕ) (a b : Fin k) (P : Dyad N × Dyad N) :
      MemLp (meatProduct R (v N) β a b P) 2 (repeatedLaw R N) := by
    apply MemLp.of_bound (hm N a b P).aestronglyMeasurable (Bq^2)
    simpa only [Real.norm_eq_abs] using hbound N a b P
  have hLp (N : ℕ) (a b : Fin k) :
      MemLp (fun ω => scaledMeatAt R v N β ω a b) 2 (repeatedLaw R N) := by
    simp_rw [hentry]
    have hsum : MemLp (fun ω => ∑ P : Dyad N × Dyad N, meatProduct R (v N) β a b P ω)
        2 (repeatedLaw R N) := memLp_finsetSum univ (fun P _ => hprodLp N a b P)
    exact hsum.const_mul ((N : ℝ) / (Dreal N)^2)
  have hvar (a b : Fin k) : Tendsto (fun N => variance
      (fun ω => scaledMeatAt R v N β ω a b) (repeatedLaw R N)) atTop (𝓝 0) := by
    have ht : Tendsto (fun N : ℕ => (6144 * (Bq^2)^2) / (N : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
          Tendsto (fun N : ℕ => (6144 * (Bq^2)^2) * (N : ℝ)⁻¹) atTop (𝓝 ((6144 * (Bq^2)^2) * 0)))
    apply squeeze_zero' (Eventually.of_forall fun _ => variance_nonneg _ _) _ ht
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp_rw [hentry]
    rw [variance_const_mul]
    have hv := g3 R.μ pairSupport (meatProduct R (v N) β a b) (Bq^2)
      (hm N a b) (hs N a b) (hbound N a b)
    calc
      _ ≤ ((N : ℝ) / (Dreal N)^2)^2 * (24 * (Bq^2)^2 * (N : ℝ)^5) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hh := hv.trans (mul_le_mul_of_nonneg_left (g4 N).2 (by positivity))
        convert hh using 1 <;> first | rfl | ring
      _ = 24 * (Bq^2)^2 * ((N : ℝ)^7 / (Dreal N)^4) := by ring
      _ ≤ 24 * (Bq^2)^2 * (256 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (meat_normalization_rate hN) (by positivity)
      _ = (6144 * (Bq^2)^2) / (N : ℝ) := by ring
  exact (g5 (repeatedLaw R)).1 (fun N => scaledMeatAt R v N β) hLp hvar

end
end AronowAudit.P018.Wave1.WeightedConsistency
