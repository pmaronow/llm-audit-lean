import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section

namespace SAP.P018a.WH.W1.P.T10_L5

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.P018
open AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

/-- The regularity bound on the records gives a uniform bound on a weighted block score.
The direction injection bounds the number of terms by two, including when a block is empty. -/
theorem blockScore_uniform_bound_empty {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : AronowAudit.P018.RepeatedKernel U k)
    (dir : ∀ N : ℕ, (d : AronowAudit.P018.Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : AronowAudit.P018.Dyad N) → Fin (R.T N d) → ℝ)
    (C : ℝ) (hμ : IsProbabilityMeasure R.μ)
    (hdir : ∀ N d, Function.Injective (dir N d))
    (hv : ∀ N d t, 0 < v N d t ∧ v N d t ≤ C)
    (hreg : RecordRegular R) (β : AronowAudit.P018.Vec k) :
    ∃ Bq : ℝ, 0 ≤ Bq ∧ ∀ N (d : AronowAudit.P018.Dyad N),
      ∀ᵐ ω ∂AronowAudit.P018.repeatedLaw R N,
        ‖AronowAudit.P018.recordWeightedBlockScore R (v N) β ω d‖ ≤ Bq := by
  letI : IsProbabilityMeasure R.μ := hμ
  letI : ∀ N, IsProbabilityMeasure (AronowAudit.P018.repeatedLaw R N) := fun N => by
    unfold AronowAudit.P018.repeatedLaw
    infer_instance
  obtain ⟨B, hB, hb⟩ := hreg.2
  let L := |C| * (B + (k : ℝ) * B * ‖β‖) * B
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨2 * L, by positivity, ?_⟩
  intro N d
  filter_upwards [ae_all_iff.mpr (fun t => hb N d t)] with ω hω
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  simp only [AronowAudit.P018.recordWeightedBlockScore, Finset.sum_apply, score, Pi.smul_apply,
    smul_eq_mul, Real.norm_eq_abs]
  change |∑ t, v N d t * (AronowAudit.P018.repeatedY R ω d t -
    dot (AronowAudit.P018.repeatedX R ω d t) β) *
      AronowAudit.P018.repeatedX R ω d t a| ≤ _
  calc
    _ ≤ ∑ t, |v N d t * (AronowAudit.P018.repeatedY R ω d t -
        dot (AronowAudit.P018.repeatedX R ω d t) β) *
          AronowAudit.P018.repeatedX R ω d t a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin (R.T N d), L := by
      apply Finset.sum_le_sum
      intro t ht
      have hw : |v N d t| ≤ |C| := by
        rw [abs_of_pos (hv N d t).1]
        exact (hv N d t).2.trans (le_abs_self C)
      have he : |AronowAudit.P018.repeatedY R ω d t -
          dot (AronowAudit.P018.repeatedX R ω d t) β| ≤
          B + (k : ℝ) * B * ‖β‖ :=
        (abs_sub _ _).trans (add_le_add (hω t).2
          (abs_dot_le_of_norm_le _ _ B (hω t).1))
      have hx : |AronowAudit.P018.repeatedX R ω d t a| ≤ B :=
        (norm_le_pi_norm (AronowAudit.P018.repeatedX R ω d t) a).trans (hω t).1
      simp only [abs_mul]
      dsimp [L]
      exact mul_le_mul (mul_le_mul hw he (abs_nonneg _) (abs_nonneg _)) hx
        (abs_nonneg _) (by positivity)
    _ = (R.T N d : ℝ) * L := by simp
    _ ≤ 2 * L := mul_le_mul_of_nonneg_right
      (by exact_mod_cast records_le_two R dir hdir N d) hL

end SAP.P018a.WH.W1.P.T10_L5

end

open SAP.P018a.WH.W1
open AronowAudit.P018

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

theorem SAP.P018a.WH.W1.T10_L5_proof : SAP.P018a.WH.W1.T10_L5 := by
  intro U _ k R K dir v C H hS hreg
  let R' := Bridge.toRepeated R
  have hK : IsProbabilityMeasure K.μ := hS.1.1
  have hRK : W1DirectedRecords R K dir := hS.2.1
  letI : IsProbabilityMeasure R'.μ := by
    change IsProbabilityMeasure R.μ
    rw [hRK.1]
    exact hK
  letI : ∀ N, IsProbabilityMeasure (AronowAudit.P018.repeatedLaw R' N) := fun N => by
    unfold AronowAudit.P018.repeatedLaw
    infer_instance
  let β : Vec k := populationBeta K
  have hdir : ∀ N d, Function.Injective (dir N d) := hRK.2.1
  have hv : ∀ N d t, 0 < v N d t ∧ v N d t ≤ C := hS.2.2.1
  obtain ⟨Bq, hBq, hb⟩ :=
    SAP.P018a.WH.W1.P.T10_L5.blockScore_uniform_bound_empty
      R' dir v C (by infer_instance) hdir hv hreg β
  have hm (N : ℕ) (a b : Fin k) (P : AronowAudit.P018.Dyad N × AronowAudit.P018.Dyad N) :
      Measurable (meatProduct R' (v N) β a b P) := by
    unfold meatProduct
    split_ifs
    · exact (blockScore_measurable R' hreg (v N) β P.1 a).mul
        (blockScore_measurable R' hreg (v N) β P.2 b)
    · exact measurable_const
  have hs (N : ℕ) (a b : Fin k)
      (P : AronowAudit.P018.Dyad N × AronowAudit.P018.Dyad N)
      (ω ω' : Fin N → U)
      (h : ∀ i ∈ pairSupport P, ω i = ω' i) :
      meatProduct R' (v N) β a b P ω = meatProduct R' (v N) β a b P ω' := by
    unfold meatProduct
    split_ifs with hP
    · have hd := blockScore_support R' (v N) β P.1 ω ω'
        (fun i hi => h i (by simp [pairSupport, hP, hi]))
      have hf := blockScore_support R' (v N) β P.2 ω ω'
        (fun i hi => h i (by simp [pairSupport, hP, hi]))
      rw [hd, hf]
    · rfl
  have hbound (N : ℕ) (a b : Fin k)
      (P : AronowAudit.P018.Dyad N × AronowAudit.P018.Dyad N) :
      ∀ᵐ ω ∂AronowAudit.P018.repeatedLaw R' N,
        |meatProduct R' (v N) β a b P ω| ≤ Bq^2 := by
    filter_upwards [hb N P.1, hb N P.2] with ω hd hf
    unfold meatProduct
    split_ifs
    · rw [abs_mul, pow_two]
      exact mul_le_mul ((norm_le_pi_norm _ a).trans hd)
        ((norm_le_pi_norm _ b).trans hf) (abs_nonneg _) hBq
    · simp [sq_nonneg]
  have hentry (N : ℕ) (ω : Fin N → U) (a b : Fin k) :
      scaledMeatAt R' v N β ω a b = ((N : ℝ) / (Dreal N)^2) *
        ∑ P : AronowAudit.P018.Dyad N × AronowAudit.P018.Dyad N,
          meatProduct R' (v N) β a b P ω := by
    simp only [AronowAudit.P018.Wave1.WeightedConsistency.scaledMeatAt,
      AronowAudit.P018.meat, Matrix.sum_apply, Matrix.smul_apply, Pi.smul_apply,
      smul_eq_mul, Fintype.sum_prod_type,
      AronowAudit.P018.Wave1.WeightedConsistency.meatProduct,
      AronowAudit.P018.overlap, matrix_ite_apply, AronowAudit.P018.outer,
      Matrix.zero_apply, Pi.zero_apply]
    congr 1
  have hprodLp (N : ℕ) (a b : Fin k)
      (P : AronowAudit.P018.Dyad N × AronowAudit.P018.Dyad N) :
      MemLp (meatProduct R' (v N) β a b P) 2 (AronowAudit.P018.repeatedLaw R' N) := by
    apply MemLp.of_bound (hm N a b P).aestronglyMeasurable (Bq^2)
    simpa only [Real.norm_eq_abs] using hbound N a b P
  have hLp (N : ℕ) (a b : Fin k) :
      MemLp (fun ω => scaledMeatAt R' v N β ω a b) 2
        (AronowAudit.P018.repeatedLaw R' N) := by
    simp_rw [hentry]
    have hsum : MemLp
        (fun ω => ∑ P : AronowAudit.P018.Dyad N × AronowAudit.P018.Dyad N,
          meatProduct R' (v N) β a b P ω) 2 (AronowAudit.P018.repeatedLaw R' N) :=
      memLp_finsetSum univ (fun P _ => hprodLp N a b P)
    exact hsum.const_mul ((N : ℝ) / (Dreal N)^2)
  have hvar (a b : Fin k) : Tendsto (fun N => variance
      (fun ω => scaledMeatAt R' v N β ω a b) (AronowAudit.P018.repeatedLaw R' N))
      atTop (𝓝 0) := by
    have ht : Tendsto (fun N : ℕ => (6144 * (Bq^2)^2) / (N : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
          Tendsto (fun N : ℕ => (6144 * (Bq^2)^2) * (N : ℝ)⁻¹) atTop
            (𝓝 ((6144 * (Bq^2)^2) * 0)))
    apply squeeze_zero' (Eventually.of_forall fun _ => variance_nonneg _ _) _ ht
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp_rw [hentry]
    rw [variance_const_mul]
    have hdep := g3_proof R'.μ pairSupport (meatProduct R' (v N) β a b)
      (Bq^2) (hm N a b) (hs N a b) (hbound N a b)
    calc
      _ ≤ ((N : ℝ) / (Dreal N)^2)^2 * (24 * (Bq^2)^2 * (N : ℝ)^5) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hh := hdep.trans (mul_le_mul_of_nonneg_left (g4_proof N).2 (by positivity))
        convert hh using 1 <;> first | rfl | ring
      _ = 24 * (Bq^2)^2 * ((N : ℝ)^7 / (Dreal N)^4) := by ring
      _ ≤ 24 * (Bq^2)^2 * (256 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (meat_normalization_rate hN) (by positivity)
      _ = (6144 * (Bq^2)^2) / (N : ℝ) := by ring
  have hlln := (g5_proof (AronowAudit.P018.repeatedLaw R')).1
    (fun N => scaledMeatAt R' v N β) hLp hvar
  change AronowAudit.P018.inProbability (AronowAudit.P018.repeatedLaw R') (fun N ω =>
    scaledMeatAt R' v N (populationBeta K) ω -
      AronowAudit.P018.meanMat (AronowAudit.P018.repeatedLaw R' N)
        (scaledMeatAt R' v N (populationBeta K)))
  simpa only [β] using hlln
