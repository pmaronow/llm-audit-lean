import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

universe u
noncomputable section

namespace SAP.P018a.WH.W1.P.T10_L3

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.P018
open AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

theorem blockScore_uniform_bound_empty {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : AronowAudit.P018.RepeatedKernel U k) (dir : ∀ N : ℕ, (d : AronowAudit.P018.Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : AronowAudit.P018.Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ)
    (hdir : ∀ N d, Function.Injective (dir N d))
    (hw : ∀ N d t, 0 < v N d t ∧ v N d t ≤ C)
    (hreg : AronowAudit.P018.Wave1.WeightedConsistency.RecordRegular R) (β : AronowAudit.P018.Vec k) :
    ∃ Bq : ℝ, 0 ≤ Bq ∧ ∀ N (d : AronowAudit.P018.Dyad N),
      ∀ᵐ ω ∂AronowAudit.P018.repeatedLaw R N, ‖AronowAudit.P018.recordWeightedBlockScore R (v N) β ω d‖ ≤ Bq := by
  obtain ⟨B, hB, hb⟩ := hreg.2
  let L := |C| * (B + (k : ℝ) * B * ‖β‖) * B
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨2 * L, by positivity, ?_⟩
  intro N d
  filter_upwards [ae_all_iff.mpr (fun t => hb N d t)] with ω hω
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  simp only [AronowAudit.P018.recordWeightedBlockScore, Finset.sum_apply, AronowAudit.P018.score, Pi.smul_apply,
    smul_eq_mul, Real.norm_eq_abs]
  change |∑ t, v N d t * (AronowAudit.P018.repeatedY R ω d t - AronowAudit.P018.dot (AronowAudit.P018.repeatedX R ω d t) β) *
    AronowAudit.P018.repeatedX R ω d t a| ≤ _
  calc
    _ ≤ ∑ t, |v N d t * (AronowAudit.P018.repeatedY R ω d t - AronowAudit.P018.dot (AronowAudit.P018.repeatedX R ω d t) β) *
        AronowAudit.P018.repeatedX R ω d t a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin (R.T N d), L := by
      apply Finset.sum_le_sum
      intro t ht
      have hweight : |v N d t| ≤ |C| := by
        rw [abs_of_pos (hw N d t).1]
        exact (hw N d t).2.trans (le_abs_self C)
      have he : |AronowAudit.P018.repeatedY R ω d t - AronowAudit.P018.dot (AronowAudit.P018.repeatedX R ω d t) β| ≤
          B + (k : ℝ) * B * ‖β‖ :=
        (abs_sub _ _).trans (add_le_add (hω t).2
          (AronowAudit.P018.Wave1.WeightedConsistency.abs_dot_le_of_norm_le _ _ B (hω t).1))
      have hx : |AronowAudit.P018.repeatedX R ω d t a| ≤ B :=
        (norm_le_pi_norm (AronowAudit.P018.repeatedX R ω d t) a).trans (hω t).1
      simp only [abs_mul]
      dsimp [L]
      exact mul_le_mul (mul_le_mul hweight he (abs_nonneg _) (abs_nonneg _)) hx
        (abs_nonneg _) (by positivity)
    _ = (R.T N d : ℝ) * L := by simp
    _ ≤ 2 * L := mul_le_mul_of_nonneg_right
      (by exact_mod_cast AronowAudit.P018.Wave1.WeightedConsistency.records_le_two R dir hdir N d) hL

theorem popBeta_bridge {U : Type u} [MeasurableSpace U] {k : ℕ}
    (K : SAP.P018a.Kernel U k) :
    AronowAudit.P018.Wave1.WeightedConsistency.popBeta K.μ
      (fun u v => K.X u v) (fun u v => K.Y u v) = SAP.P018a.populationBeta K := by
  unfold AronowAudit.P018.Wave1.WeightedConsistency.popBeta
    AronowAudit.P018.Wave1.WeightedConsistency.popQ
    AronowAudit.P018.Wave1.WeightedConsistency.popR
    SAP.P018a.populationBeta SAP.P018a.populationGram
  have hM : SAP.P018a.meanMat (K.μ.prod K.μ)
        (fun uv => SAP.P018a.outer (K.X uv.1 uv.2) (K.X uv.1 uv.2)) =
      AronowAudit.P018.meanMat (K.μ.prod K.μ)
        (fun uv => AronowAudit.P018.outer (K.X uv.1 uv.2) (K.X uv.1 uv.2)) := by
    ext a b
    rfl
  have hr : SAP.P018a.meanVec (K.μ.prod K.μ)
        (fun uv => SAP.P018a.score (K.X uv.1 uv.2) (K.Y uv.1 uv.2)) =
      AronowAudit.P018.meanVec (K.μ.prod K.μ)
        (fun uv => AronowAudit.P018.score (K.X uv.1 uv.2) (K.Y uv.1 uv.2)) := by
    ext a
    rfl
  rw [hM, hr]

end SAP.P018a.WH.W1.P.T10_L3

/- The leaf permits empty blocks, so its LLNs use the donor variance argument
with the injective direction map supplying T ≤ 2. -/
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.P018
open AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

theorem SAP.P018a.WH.W1.T10_L3_proof : SAP.P018a.WH.W1.T10_L3 := by
  intro U hU k R K dir v C H hSetting hreg hcent
  rcases hSetting with ⟨hOrdered, hDirected, hWeights, hH, hLimit⟩
  rcases hDirected with ⟨hMu, hdir, hCommon⟩
  let R' : AronowAudit.P018.RepeatedKernel U k := Bridge.toRepeated R
  have hprob : IsProbabilityMeasure R'.μ := by
    change IsProbabilityMeasure R.μ
    rw [hMu]
    exact hOrdered.1
  letI : IsProbabilityMeasure R'.μ := hprob
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (AronowAudit.P018.repeatedLaw R' N) :=
    fun N => by
      unfold AronowAudit.P018.repeatedLaw
      infer_instance
  have hdir' : ∀ N d, Function.Injective (dir N d) := hdir
  have hw' : ∀ N d t, 0 < v N d t ∧ v N d t ≤ C := hWeights
  obtain ⟨Bq, hBq, hbScore⟩ := SAP.P018a.WH.W1.P.T10_L3.blockScore_uniform_bound_empty R' dir v C hdir' hw' hreg
    (SAP.P018a.populationBeta K)
  have hgramBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ N d a b,
      ∀ᵐ ω ∂AronowAudit.P018.repeatedLaw R' N,
        |AronowAudit.P018.Wave1.WeightedConsistency.gramBlock R' (v N) d a b ω| ≤ B := by
    obtain ⟨B, hB, hb⟩ := hreg.2
    let BZ := 2 * (|C| * B^2)
    refine ⟨BZ, by positivity, ?_⟩
    intro N d a b
    filter_upwards [ae_all_iff.mpr (fun t => hb N d t)] with ω hω
    unfold AronowAudit.P018.Wave1.WeightedConsistency.gramBlock
    calc
      _ ≤ ∑ t, |v N d t * (AronowAudit.P018.repeatedX R' ω d t a * AronowAudit.P018.repeatedX R' ω d t b)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin (R'.T N d), |C| * B^2 := by
        apply Finset.sum_le_sum
        intro t ht
        have hweight : |v N d t| ≤ |C| := by
          rw [abs_of_pos (hw' N d t).1]
          exact (hw' N d t).2.trans (le_abs_self C)
        have ha := (norm_le_pi_norm (AronowAudit.P018.repeatedX R' ω d t) a).trans (hω t).1
        have hb' := (norm_le_pi_norm (AronowAudit.P018.repeatedX R' ω d t) b).trans (hω t).1
        simp only [abs_mul, pow_two]
        exact mul_le_mul hweight (mul_le_mul ha hb' (abs_nonneg _) hB)
          (by positivity) (abs_nonneg _)
      _ ≤ BZ := by
        simp only [sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast AronowAudit.P018.Wave1.WeightedConsistency.records_le_two R' dir hdir' N d)
          (by positivity)
  -- Gram concentration, coordinatewise by the sparse variance and matrix Chebyshev nodes.
  have hGram : GramLLN R' v := by
    obtain ⟨BZ, hBZ, hbound⟩ := hgramBound
    letI : IsProbabilityMeasure R'.μ := hprob
    letI : ∀ N, IsProbabilityMeasure (AronowAudit.P018.repeatedLaw R' N) := instSamplesProbability
    have hm (N : ℕ) (d : AronowAudit.P018.Dyad N) (a b : Fin k) :
        Measurable (AronowAudit.P018.Wave1.WeightedConsistency.gramBlock R' (v N) d a b) := by
      apply Finset.measurable_fun_sum
      intro t ht
      exact measurable_const.mul ((((measurable_pi_apply a).comp (hreg.1 N d t).1).mul
        ((measurable_pi_apply b).comp (hreg.1 N d t).1)))
    have hs (N : ℕ) (d : AronowAudit.P018.Dyad N) (a b : Fin k) (ω ω' : Fin N → U)
        (h : ∀ i ∈ AronowAudit.P018.members d, ω i = ω' i) :
        AronowAudit.P018.Wave1.WeightedConsistency.gramBlock R' (v N) d a b ω =
          AronowAudit.P018.Wave1.WeightedConsistency.gramBlock R' (v N) d a b ω' := by
      simp only [AronowAudit.P018.Wave1.WeightedConsistency.gramBlock,
        AronowAudit.P018.repeatedX,
        h _ (AronowAudit.P018.Wave1.WeightedConsistency.firstUnit_mem d),
        h _ (AronowAudit.P018.Wave1.WeightedConsistency.secondUnit_mem d)]
    have hentry (N : ℕ) (ω : Fin N → U) (a b : Fin k) :
        AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω a b = (AronowAudit.P018.Dreal N)⁻¹ *
          ∑ d, AronowAudit.P018.Wave1.WeightedConsistency.gramBlock R' (v N) d a b ω := by
      simp [AronowAudit.P018.Wave1.WeightedConsistency.normGram,
        AronowAudit.P018.recordWeightedGram,
        AronowAudit.P018.Wave1.WeightedConsistency.gramBlock,
        Matrix.sum_apply, Matrix.smul_apply, AronowAudit.P018.outer]
    have hblockLp (N : ℕ) (d : AronowAudit.P018.Dyad N) (a b : Fin k) :
        MemLp (AronowAudit.P018.Wave1.WeightedConsistency.gramBlock R' (v N) d a b) 2 (AronowAudit.P018.repeatedLaw R' N) := by
      apply MemLp.of_bound (hm N d a b).aestronglyMeasurable BZ
      simpa only [Real.norm_eq_abs] using hbound N d a b
    have hLp (N : ℕ) (a b : Fin k) :
        MemLp (fun ω => AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω a b) 2 (AronowAudit.P018.repeatedLaw R' N) := by
      simp_rw [hentry]
      have hsum : MemLp (fun ω => ∑ d : Dyad N,
          AronowAudit.P018.Wave1.WeightedConsistency.gramBlock R' (v N) d a b ω) 2 (AronowAudit.P018.repeatedLaw R' N) :=
        memLp_finsetSum univ (fun d _ => hblockLp N d a b)
      exact hsum.const_mul ((AronowAudit.P018.Dreal N)⁻¹)
    have hvar (a b : Fin k) : Tendsto (fun N =>
        variance (fun ω => AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω a b) (AronowAudit.P018.repeatedLaw R' N)) atTop (𝓝 0) := by
      simp_rw [hentry]
      exact AronowAudit.P018.Wave1.WeightedConsistency.dyad_scaled_variance_tendsto AronowAudit.P018.Wave1.WeightedConsistency.g3_proof
        AronowAudit.P018.Wave1.WeightedConsistency.g4_proof R'.μ
        (fun N d => AronowAudit.P018.Wave1.WeightedConsistency.gramBlock R' (v N) d a b) BZ
        (fun N d => hm N d a b) (fun N d => hs N d a b)
        (fun N d => hbound N d a b)
    have hcenter := (AronowAudit.P018.Wave1.WeightedConsistency.g5_proof (AronowAudit.P018.repeatedLaw R')).1
      (AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v) hLp hvar
    have hmean (N : ℕ) : AronowAudit.P018.meanMat (AronowAudit.P018.repeatedLaw R' N)
        (AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N) =
        AronowAudit.P018.recordWeightedH R' (v N) := by
      change AronowAudit.P018.meanMat (AronowAudit.P018.repeatedLaw R' N)
        (fun ω => (AronowAudit.P018.Dreal N)⁻¹ • AronowAudit.P018.recordWeightedGram R' (v N) ω) = _
      rw [AronowAudit.P018.meanMat_scale]
      rfl
    change AronowAudit.P018.inProbability (AronowAudit.P018.repeatedLaw R')
      (fun N ω => AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω - AronowAudit.P018.recordWeightedH R' (v N))
    simpa only [hmean] using hcenter
  -- Score concentration uses the same block variance count and the supplied centering.
  have hScore : ScoreLLN R' v (SAP.P018a.populationBeta K) := by
    let β : AronowAudit.P018.Vec k := AronowAudit.P018.Wave1.WeightedConsistency.popBeta R'.μ
      (fun u₁ u₂ => (Bridge.toKernel K).X u₁ u₂)
      (fun u₁ u₂ => (Bridge.toKernel K).Y u₁ u₂)
    have hBeta : β = SAP.P018a.populationBeta K := by
      change AronowAudit.P018.Wave1.WeightedConsistency.popBeta R.μ
        (fun u₁ u₂ => K.X u₁ u₂) (fun u₁ u₂ => K.Y u₁ u₂) = _
      rw [hMu]
      exact SAP.P018a.WH.W1.P.T10_L3.popBeta_bridge K
    have hcent' : ∀ N (d : AronowAudit.P018.Dyad N),
        AronowAudit.P018.meanVec (AronowAudit.P018.repeatedLaw R' N)
          (fun ω => AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d) = 0 := by
      intro N d
      rw [hBeta]
      change SAP.P018a.meanVec (SAP.P018a.repeatedLaw R N)
        (fun ω => SAP.P018a.recordWeightedBlockScore R (v N)
          (SAP.P018a.populationBeta K) ω d) = 0
      exact hcent N d
    let F := fun N (ω : Fin N → U) =>
      (AronowAudit.P018.Dreal N)⁻¹ • ∑ d : AronowAudit.P018.Dyad N,
        AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d
    obtain ⟨Bq, hBq, hb⟩ := SAP.P018a.WH.W1.P.T10_L3.blockScore_uniform_bound_empty R' dir v C hdir' hw' hreg β
    have hentry (N : ℕ) (ω : Fin N → U) (a : Fin k) :
        F N ω a = (AronowAudit.P018.Dreal N)⁻¹ *
          ∑ d, AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d a := by
      simp [F, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    have hm (N : ℕ) (d : AronowAudit.P018.Dyad N) (a : Fin k) :
        Measurable (fun ω => AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d a) :=
      AronowAudit.P018.Wave1.WeightedConsistency.blockScore_measurable R' hreg (v N) β d a
    have hs (N : ℕ) (d : AronowAudit.P018.Dyad N) (ω ω' : Fin N → U)
        (h : ∀ i ∈ AronowAudit.P018.members d, ω i = ω' i) :
        AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d =
          AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω' d :=
      AronowAudit.P018.Wave1.WeightedConsistency.blockScore_support R' (v N) β d ω ω' h
    have hblockLp (N : ℕ) (d : AronowAudit.P018.Dyad N) (a : Fin k) :
        MemLp (fun ω => AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d a) 2 (AronowAudit.P018.repeatedLaw R' N) := by
      apply MemLp.of_bound (hm N d a).aestronglyMeasurable Bq
      filter_upwards [hb N d] with ω hω
      exact (norm_le_pi_norm (AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d) a).trans hω
    have hLp (N : ℕ) (a : Fin k) : MemLp (fun ω => F N ω a) 2 (AronowAudit.P018.repeatedLaw R' N) := by
      simp_rw [hentry]
      have hsum : MemLp (fun ω => ∑ d : Dyad N,
          AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d a) 2 (AronowAudit.P018.repeatedLaw R' N) :=
        memLp_finsetSum univ (fun d _ => hblockLp N d a)
      exact hsum.const_mul ((AronowAudit.P018.Dreal N)⁻¹)
    have hvar (a : Fin k) : Tendsto (fun N =>
        variance (fun ω => F N ω a) (AronowAudit.P018.repeatedLaw R' N)) atTop (𝓝 0) := by
      simp_rw [hentry]
      exact AronowAudit.P018.Wave1.WeightedConsistency.dyad_scaled_variance_tendsto AronowAudit.P018.Wave1.WeightedConsistency.g3_proof
        AronowAudit.P018.Wave1.WeightedConsistency.g4_proof R'.μ
        (fun N d ω => AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d a) Bq
        (fun N d => hm N d a)
        (fun N d ω ω' h => congrFun (hs N d ω ω' h) a)
        (fun N d => by
          filter_upwards [hb N d] with ω hω
          exact (norm_le_pi_norm (AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d) a).trans hω)
    have hmean (N : ℕ) : AronowAudit.P018.meanVec (AronowAudit.P018.repeatedLaw R' N) (F N) = 0 := by
      ext a
      change (∫ ω, F N ω a ∂AronowAudit.P018.repeatedLaw R' N) = 0
      simp_rw [hentry]
      rw [integral_const_mul, integral_finsetSum _ (fun d _ =>
        (hblockLp N d a).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2))]
      have hz (d : AronowAudit.P018.Dyad N) :
          (∫ ω, AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d a ∂AronowAudit.P018.repeatedLaw R' N) = 0 :=
        congrFun (hcent' N d) a
      simp_rw [hz]
      simp
    have hprobScore := (AronowAudit.P018.Wave1.WeightedConsistency.g5_proof (AronowAudit.P018.repeatedLaw R')).2 F hLp hvar
    have hscoreβ : ScoreLLN R' v β := by
      change AronowAudit.P018.inProbability (AronowAudit.P018.repeatedLaw R') F
      simpa only [hmean, sub_zero] using hprobScore
    exact hBeta ▸ hscoreβ
  constructor
  · change GramLLN R' v
    exact hGram
  · exact hScore

