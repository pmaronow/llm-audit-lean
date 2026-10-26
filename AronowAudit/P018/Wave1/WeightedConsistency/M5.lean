import AronowAudit.P018.Wave1.WeightedConsistency.M8

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

/-- The normalization has quadratic growth on the nonempty-dyad tail. -/
theorem Dreal_lower {N : ℕ} (hN : 2 ≤ N) : (N : ℝ)^2 / 4 ≤ Dreal N := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold Dreal
  nlinarith

theorem dyad_normalization_rate {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ)^3 / (Dreal N)^2 ≤ 16 / (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hD : 0 < Dreal N := lt_of_lt_of_le (by positivity) (Dreal_lower hN)
  calc
    _ ≤ (N : ℝ)^3 / ((N : ℝ)^2 / 4)^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) (Dreal_lower hN) 2
    _ = 16 / (N : ℝ) := by field_simp; ring

theorem dyad_scaled_variance_tendsto (g3 : G3.{u}) (g4 : G4)
    {U : Type u} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (Z : ∀ N, Dyad N → (Fin N → U) → ℝ) (B : ℝ)
    (hm : ∀ N d, Measurable (Z N d))
    (hs : ∀ N d ω ω', (∀ i ∈ members d, ω i = ω' i) → Z N d ω = Z N d ω')
    (hb : ∀ N d, ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => μ), |Z N d ω| ≤ B) :
    Tendsto (fun N => variance (fun ω => (Dreal N)⁻¹ * ∑ d, Z N d ω)
      (Measure.pi (fun _ : Fin N => μ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => (32 * B^2) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
        Tendsto (fun N : ℕ => (32 * B^2) * (N : ℝ)⁻¹) atTop (𝓝 ((32 * B^2) * 0)))
  apply squeeze_zero' (Eventually.of_forall fun _ => variance_nonneg _ _) _ ht
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [variance_const_mul]
  have hv := g3 μ members (Z N) B (hm N) (hs N) (hb N)
  calc
    _ ≤ ((Dreal N)⁻¹)^2 * (2 * B^2 * (N : ℝ)^3) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact hv.trans (mul_le_mul_of_nonneg_left (g4 N).1 (by positivity))
    _ = 2 * B^2 * ((N : ℝ)^3 / (Dreal N)^2) := by ring
    _ ≤ 2 * B^2 * (16 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (dyad_normalization_rate hN) (by positivity)
    _ = (32 * B^2) / (N : ℝ) := by ring

theorem records_le_two {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (dir : ∀ N, (d : Dyad N) → Fin (R.T N d) → Bool)
    (hdir : ∀ N d, Function.Injective (dir N d)) (N : ℕ) (d : Dyad N) : R.T N d ≤ 2 := by
  simpa using Fintype.card_le_of_injective (dir N d) (hdir N d)

theorem abs_dot_le_of_norm_le {k : ℕ} (x β : Vec k) (B : ℝ) (hx : ‖x‖ ≤ B) :
    |dot x β| ≤ (k : ℝ) * B * ‖β‖ := by
  unfold dot
  calc
    _ ≤ ∑ a : Fin k, |x a * β a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin k, B * ‖β‖ := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      exact mul_le_mul ((norm_le_pi_norm x a).trans hx)
        (norm_le_pi_norm β a) (abs_nonneg _) (hx.trans' (norm_nonneg _))
    _ = _ := by simp [mul_assoc]

/-- Uniform score-block bound, with no lower bound on the weights. -/
theorem blockScore_uniform_bound {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (X : U → U → Vec k) (Y : U → U → ℝ)
    (dir : ∀ N, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k)
    (hS : Setting R X Y dir v C H) (hreg : RecordRegular R) (β : Vec k) :
    ∃ Bq : ℝ, 0 ≤ Bq ∧ ∀ N (d : Dyad N),
      ∀ᵐ ω ∂repeatedLaw R N, ‖recordWeightedBlockScore R (v N) β ω d‖ ≤ Bq := by
  obtain ⟨B, hB, hb⟩ := hreg.2
  let L := |C| * (B + (k : ℝ) * B * ‖β‖) * B
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨2 * L, by positivity, ?_⟩
  intro N d
  filter_upwards [ae_all_iff.mpr (fun t => hb N d t)] with ω hω
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  simp only [recordWeightedBlockScore, Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  change |∑ t, v N d t * (repeatedY R ω d t - dot (repeatedX R ω d t) β) *
    repeatedX R ω d t a| ≤ _
  calc
    _ ≤ ∑ t, |v N d t * (repeatedY R ω d t - dot (repeatedX R ω d t) β) *
        repeatedX R ω d t a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin (R.T N d), L := by
      apply Finset.sum_le_sum
      intro t ht
      have hw : |v N d t| ≤ |C| := by
        rw [abs_of_pos (hS.2.2.2.1 N d t).1]
        exact (hS.2.2.2.1 N d t).2.trans (le_abs_self C)
      have he : |repeatedY R ω d t - dot (repeatedX R ω d t) β| ≤
          B + (k : ℝ) * B * ‖β‖ :=
        (abs_sub _ _).trans (add_le_add (hω t).2
          (abs_dot_le_of_norm_le _ _ B (hω t).1))
      have hx : |repeatedX R ω d t a| ≤ B :=
        (norm_le_pi_norm (repeatedX R ω d t) a).trans (hω t).1
      simp only [abs_mul]
      dsimp [L]
      exact mul_le_mul (mul_le_mul hw he (abs_nonneg _) (abs_nonneg _)) hx
        (abs_nonneg _) (by positivity)
    _ = (R.T N d : ℝ) * L := by simp
    _ ≤ 2 * L := mul_le_mul_of_nonneg_right
      (by exact_mod_cast records_le_two R dir hS.2.1 N d) hL

/-- One two-unit contribution to the weighted sample Gram. -/
def gramBlock {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (v : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (d : Dyad N) (a b : Fin k) (ω : Fin N → U) : ℝ :=
  ∑ t, v d t * (repeatedX R ω d t a * repeatedX R ω d t b)

theorem m5_proof : M5.{u} := by
  intro g3 g4 g5 U _ k R X Y dir v C H hS hreg
  letI instUnitProbability : IsProbabilityMeasure R.μ := hS.1.1
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hS.1 N
  obtain ⟨B, hB, hb⟩ := hreg.2
  let BZ := 2 * (|C| * B^2)
  have hm (N : ℕ) (d : Dyad N) (a b : Fin k) :
      Measurable (gramBlock R (v N) d a b) := by
    apply Finset.measurable_fun_sum
    intro t ht
    exact measurable_const.mul ((((measurable_pi_apply a).comp (hreg.1 N d t).1).mul
      ((measurable_pi_apply b).comp (hreg.1 N d t).1)))
  have hs (N : ℕ) (d : Dyad N) (a b : Fin k) (ω ω' : Fin N → U)
      (h : ∀ i ∈ members d, ω i = ω' i) :
      gramBlock R (v N) d a b ω = gramBlock R (v N) d a b ω' := by
    simp only [gramBlock, repeatedX, h _ (firstUnit_mem d), h _ (secondUnit_mem d)]
  have hbound (N : ℕ) (d : Dyad N) (a b : Fin k) :
      ∀ᵐ ω ∂repeatedLaw R N, |gramBlock R (v N) d a b ω| ≤ BZ := by
    filter_upwards [ae_all_iff.mpr (fun t => hb N d t)] with ω hω
    unfold gramBlock
    calc
      _ ≤ ∑ t, |v N d t * (repeatedX R ω d t a * repeatedX R ω d t b)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin (R.T N d), |C| * B^2 := by
        apply Finset.sum_le_sum
        intro t ht
        have hw : |v N d t| ≤ |C| := by
          rw [abs_of_pos (hS.2.2.2.1 N d t).1]
          exact (hS.2.2.2.1 N d t).2.trans (le_abs_self C)
        have ha := (norm_le_pi_norm (repeatedX R ω d t) a).trans (hω t).1
        have hb' := (norm_le_pi_norm (repeatedX R ω d t) b).trans (hω t).1
        simp only [abs_mul, pow_two]
        exact mul_le_mul hw (mul_le_mul ha hb' (abs_nonneg _) hB)
          (by positivity) (abs_nonneg _)
      _ ≤ BZ := by
        simp only [sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast records_le_two R dir hS.2.1 N d) (by positivity)
  have hentry (N : ℕ) (ω : Fin N → U) (a b : Fin k) :
      normGram R v N ω a b = (Dreal N)⁻¹ * ∑ d, gramBlock R (v N) d a b ω := by
    simp [normGram, recordWeightedGram, gramBlock, Matrix.sum_apply, Matrix.smul_apply, outer]
  have hblockLp (N : ℕ) (d : Dyad N) (a b : Fin k) :
      MemLp (gramBlock R (v N) d a b) 2 (repeatedLaw R N) := by
    apply MemLp.of_bound (hm N d a b).aestronglyMeasurable BZ
    simpa only [Real.norm_eq_abs] using hbound N d a b
  have hLp (N : ℕ) (a b : Fin k) : MemLp (fun ω => normGram R v N ω a b) 2 (repeatedLaw R N) := by
    simp_rw [hentry]
    have hsum : MemLp (fun ω => ∑ d : Dyad N, gramBlock R (v N) d a b ω) 2 (repeatedLaw R N) :=
      memLp_finsetSum univ (fun d _ => hblockLp N d a b)
    exact hsum.const_mul ((Dreal N)⁻¹)
  have hvar (a b : Fin k) : Tendsto (fun N => variance
      (fun ω => normGram R v N ω a b) (repeatedLaw R N)) atTop (𝓝 0) := by
    simp_rw [hentry]
    exact dyad_scaled_variance_tendsto g3 g4 R.μ (fun N d => gramBlock R (v N) d a b)
      BZ (fun N d => hm N d a b) (fun N d => hs N d a b) (fun N d => hbound N d a b)
  have hh := (g5 (repeatedLaw R)).1 (normGram R v) hLp hvar
  have hmean (N : ℕ) : meanMat (repeatedLaw R N) (normGram R v N) = recordWeightedH R (v N) := by
    change meanMat (repeatedLaw R N) (fun ω => (Dreal N)⁻¹ • recordWeightedGram R (v N) ω) = _
    rw [meanMat_scale]
    rfl
  change inProbability (repeatedLaw R) (fun N ω => normGram R v N ω - recordWeightedH R (v N))
  simpa only [hmean] using hh

end
end AronowAudit.P018.Wave1.WeightedConsistency
