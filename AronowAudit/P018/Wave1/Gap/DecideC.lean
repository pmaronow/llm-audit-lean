import AronowAudit.P018.Wave1.WeightedConsistency.G1
import AronowAudit.P018.Wave1.WeightedConsistency.G3
import AronowAudit.P018.Wave1.WeightedConsistency.G4
import AronowAudit.P018.Wave1.WeightedConsistency.G5
import AronowAudit.P018.Wave1.WeightedConsistency.G7
import AronowAudit.P018.Wave1.WeightedConsistency.G8
import AronowAudit.P018.Wave1.WeightedConsistency.M9
import AronowAudit.P018.Wave1.WeightedConsistency.M10

/-!
P018-T10: repeated-data sandwich consistency with overlap mean control.
P018-T25: refutation of the printed benchmark covariance correspondence.

The repeated-data proof uses finite-dependence and probability bounds.
All data bounds are transferred to the product sample law almost surely;
individual block scores need not have zero mean.
-/

set_option autoImplicit false

namespace AronowAudit.P018.Wave1

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

open WeightedConsistency

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

private theorem DecideC_card (N : ℕ) (hN : 2 ≤ N) :
    (Fintype.card (Dyad N) : ℝ) = Dreal N := by
  rw [number_of_dyads]
  exact Nat.cast_choose_two ℝ N

private theorem DecideC_L_bounds {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (N : ℕ) (hN : 2 ≤ N) :
    0 < repeatedL R N ∧ Dreal N ≤ repeatedL R N := by
  have hD : 0 < Dreal N := lt_of_lt_of_le (by positivity) (Dreal_lower hN)
  have hl : Dreal N ≤ repeatedL R N := by
    rw [← DecideC_card N hN]
    calc
      _ = ∑ _d : Dyad N, (1 : ℝ) := by simp
      _ ≤ repeatedL R N := Finset.sum_le_sum (fun d _ => by
        exact_mod_cast hR.2.1 N hN d)
  exact ⟨hD.trans_le hl, hl⟩

private theorem DecideC_L_nonneg {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) : 0 ≤ repeatedL R N :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

private theorem DecideC_scalar_variance {U : Type u} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ]
    (c : ℕ → ℝ) (hc : ∀ N, 2 ≤ N → 0 ≤ c N ∧ c N ≤ (Dreal N)⁻¹)
    (Z : ∀ N, Dyad N → (Fin N → U) → ℝ) (B : ℝ)
    (hm : ∀ N d, Measurable (Z N d))
    (hs : ∀ N d ω ω', (∀ i ∈ members d, ω i = ω' i) → Z N d ω = Z N d ω')
    (hb : ∀ N d, ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => μ), |Z N d ω| ≤ B) :
    Tendsto (fun N => variance (fun ω => c N * ∑ d, Z N d ω)
      (Measure.pi (fun _ : Fin N => μ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => (32 * B^2) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
        Tendsto (fun N : ℕ => (32 * B^2) * (N : ℝ)⁻¹) atTop (𝓝 ((32 * B^2) * 0)))
  apply squeeze_zero' (Eventually.of_forall fun _ => variance_nonneg _ _) _ ht
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [variance_const_mul]
  have hv := g3_proof μ members (Z N) B (hm N) (hs N) (hb N)
  calc
    _ ≤ ((Dreal N)⁻¹)^2 * (2 * B^2 * (N : ℝ)^3) := by
      apply mul_le_mul
        (pow_le_pow_left₀ (hc N hN).1 (hc N hN).2 2)
        (hv.trans (mul_le_mul_of_nonneg_left (g4_proof N).1 (by positivity)))
        (variance_nonneg _ _) (by positivity)
    _ = 2 * B^2 * ((N : ℝ)^3 / (Dreal N)^2) := by ring
    _ ≤ 2 * B^2 * (16 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (dyad_normalization_rate hN) (by positivity)
    _ = (32 * B^2) / (N : ℝ) := by ring

private def DecideC_xy {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (ω : Fin N → U) : Vec k :=
  ∑ d : Dyad N, ∑ t, score (repeatedX R ω d t) (repeatedY R ω d t)

private def DecideC_A {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) (ω : Fin N → U) : Mat k :=
  (repeatedL R N)⁻¹ • repeatedGram R ω

private def DecideC_F {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) (ω : Fin N → U) : Vec k :=
  (repeatedL R N)⁻¹ • DecideC_xy R ω

private def DecideC_e {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) : Vec k :=
  meanVec (repeatedLaw R N) (DecideC_F R N)

private theorem DecideC_one_score {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (β : Vec k) (ω : Fin N → U) (d : Dyad N) :
    recordWeightedBlockScore R (fun _ _ => 1) β ω d = repeatedBlockScore R β ω d := by
  simp only [recordWeightedBlockScore, repeatedBlockScore, one_mul]

private theorem DecideC_q_meas {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hreg : RecordRegular R) (β : Vec k) (d : Dyad N) (a : Fin k) :
    Measurable (fun ω => repeatedBlockScore R β ω d a) := by
  simpa only [DecideC_one_score] using blockScore_measurable R hreg (fun _ _ => 1) β d a

private theorem DecideC_q_lp {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (β : Vec k) (d : Dyad N) (a : Fin k) (p : ℝ≥0∞) :
    MemLp (fun ω => repeatedBlockScore R β ω d a) p (repeatedLaw R N) := by
  simpa only [DecideC_one_score] using blockScore_memLp R hR hreg (fun _ _ => 1) β d a p

private theorem DecideC_q_support {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (β : Vec k) (d : Dyad N) (ω ω' : Fin N → U)
    (h : ∀ i ∈ members d, ω i = ω' i) :
    repeatedBlockScore R β ω d = repeatedBlockScore R β ω' d := by
  simpa only [DecideC_one_score] using blockScore_support R (fun _ _ => 1) β d ω ω' h

/-- Bounded record arrays obey the dyad LLN, including heterogeneous record counts. -/
private theorem DecideC_records_moments {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R)
    (T0 : ℕ) (hT : ∀ N d, R.T N d ≤ T0)
    (Z : ∀ N, (d : Dyad N) → Fin (R.T N d) → (Fin N → U) → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hm : ∀ N d t, Measurable (Z N d t))
    (hs : ∀ N d t ω ω', (∀ i ∈ members d, ω i = ω' i) → Z N d t ω = Z N d t ω')
    (hb : ∀ N d t, ∀ᵐ ω ∂repeatedLaw R N, |Z N d t ω| ≤ B) :
    (∀ N, MemLp (fun ω => (repeatedL R N)⁻¹ * ∑ d, ∑ t, Z N d t ω) 2 (repeatedLaw R N)) ∧
    Tendsto (fun N => variance (fun ω => (repeatedL R N)⁻¹ * ∑ d, ∑ t, Z N d t ω)
      (repeatedLaw R N)) atTop (𝓝 0) := by
  letI instUnitProbability : IsProbabilityMeasure R.μ := hR.1
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hR N
  let W := fun N (d : Dyad N) (ω : Fin N → U) => ∑ t, Z N d t ω
  have hmW (N : ℕ) (d : Dyad N) : Measurable (W N d) :=
    Finset.measurable_fun_sum _ (fun t _ => hm N d t)
  have hbW (N : ℕ) (d : Dyad N) :
      ∀ᵐ ω ∂repeatedLaw R N, |W N d ω| ≤ (T0 : ℝ) * B := by
    filter_upwards [ae_all_iff.mpr (fun t => hb N d t)] with ω hω
    calc
      _ ≤ ∑ t, |Z N d t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin (R.T N d), B := Finset.sum_le_sum (fun t _ => hω t)
      _ ≤ (T0 : ℝ) * B := by
        simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT N d) hB
  constructor
  · intro N
    have hp (d : Dyad N) : MemLp (W N d) 2 (repeatedLaw R N) :=
      MemLp.of_bound (hmW N d).aestronglyMeasurable ((T0 : ℝ) * B) (hbW N d)
    have hsum : MemLp (fun ω => ∑ d : Dyad N, W N d ω) 2 (repeatedLaw R N) :=
      memLp_finsetSum univ (fun d _ => hp d)
    exact hsum.const_mul _
  · apply DecideC_scalar_variance R.μ (fun N => (repeatedL R N)⁻¹) _ W
      ((T0 : ℝ) * B) hmW _ hbW
    · intro N hN
      have hl := DecideC_L_bounds R hR N hN
      exact ⟨inv_nonneg.mpr hl.1.le, inv_anti₀
        (lt_of_lt_of_le (by positivity) (Dreal_lower hN)) hl.2⟩
    · intro N d ω ω' h
      exact Finset.sum_congr rfl (fun t _ => hs N d t ω ω' h)

private theorem DecideC_design_lln {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (T0 : ℕ) (hT : ∀ N d, R.T N d ≤ T0) :
    inProbability (repeatedLaw R) (fun N ω => DecideC_A R N ω - repeatedH R N) ∧
    inProbability (repeatedLaw R) (fun N ω => DecideC_F R N ω - DecideC_e R N) := by
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hR N
  obtain ⟨B, hB, hb⟩ := hreg.2
  have hg (a b : Fin k) := DecideC_records_moments R hR T0 hT
    (fun N d t ω => repeatedX R ω d t a * repeatedX R ω d t b) (B^2) (sq_nonneg B)
    (fun N d t => (((measurable_pi_apply a).comp (hreg.1 N d t).1).mul
      ((measurable_pi_apply b).comp (hreg.1 N d t).1)))
    (fun N d t ω ω' h => by
      simp only [repeatedX, h _ (firstUnit_mem d), h _ (secondUnit_mem d)])
    (fun N d t => (hb N d t).mono (fun ω hω => by
      rw [abs_mul, pow_two]
      exact mul_le_mul ((norm_le_pi_norm _ a).trans hω.1)
        ((norm_le_pi_norm _ b).trans hω.1) (abs_nonneg _) hB))
  have hf (a : Fin k) := DecideC_records_moments R hR T0 hT
    (fun N d t ω => repeatedY R ω d t * repeatedX R ω d t a) (B^2) (sq_nonneg B)
    (fun N d t => (hreg.1 N d t).2.mul ((measurable_pi_apply a).comp (hreg.1 N d t).1))
    (fun N d t ω ω' h => by
      simp only [repeatedX, repeatedY, h _ (firstUnit_mem d), h _ (secondUnit_mem d)])
    (fun N d t => (hb N d t).mono (fun ω hω => by
      rw [abs_mul, pow_two]
      exact mul_le_mul hω.2 ((norm_le_pi_norm _ a).trans hω.1) (abs_nonneg _) hB))
  constructor
  · have h := (g5_proof (repeatedLaw R)).1 (DecideC_A R)
      (fun N a b => by simpa only [DecideC_A, repeatedGram, outer, Matrix.smul_apply,
        Pi.smul_apply, smul_eq_mul, Matrix.sum_apply] using (hg a b).1 N)
      (fun a b => by simpa only [DecideC_A, repeatedGram, outer, Matrix.smul_apply,
        Pi.smul_apply, smul_eq_mul, Matrix.sum_apply] using (hg a b).2)
    have he (N : ℕ) : meanMat (repeatedLaw R N) (DecideC_A R N) = repeatedH R N :=
      meanMat_scale _ _ _
    simpa only [he] using h
  · exact (g5_proof (repeatedLaw R)).2 (DecideC_F R)
      (fun N a => by simpa only [DecideC_F, DecideC_xy, score, Pi.smul_apply,
        smul_eq_mul, Finset.sum_apply] using (hf a).1 N)
      (fun a => by simpa only [DecideC_F, DecideC_xy, score, Pi.smul_apply,
        smul_eq_mul, Finset.sum_apply] using (hf a).2)

private theorem DecideC_e_bound {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N, ‖DecideC_e R N‖ ≤ C := by
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hR N
  obtain ⟨B, hB, hb⟩ := hreg.2
  refine ⟨B^2, sq_nonneg _, fun N => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (sq_nonneg B)).mpr
  intro a
  change ‖∫ ω, DecideC_F R N ω a ∂repeatedLaw R N‖ ≤ _
  have hbound : ∀ᵐ ω ∂repeatedLaw R N, ‖DecideC_F R N ω a‖ ≤ B^2 := by
    filter_upwards [ae_all_iff.mpr (fun d => ae_all_iff.mpr (fun t => hb N d t))] with ω hω
    by_cases hL : repeatedL R N = 0
    · simp [DecideC_F, hL, sq_nonneg]
    have hLp : 0 < repeatedL R N := lt_of_le_of_ne (DecideC_L_nonneg R N) (Ne.symm hL)
    change |(repeatedL R N)⁻¹ * (∑ d : Dyad N, ∑ t,
      score (repeatedX R ω d t) (repeatedY R ω d t)) a| ≤ _
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hLp.le)]
    simp only [Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul]
    calc
      _ ≤ (repeatedL R N)⁻¹ * (∑ d : Dyad N, ∑ _t : Fin (R.T N d), B^2) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hLp.le)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
        rw [abs_mul, pow_two]
        exact mul_le_mul (hω d t).2 ((norm_le_pi_norm _ a).trans (hω d t).1)
          (abs_nonneg _) hB
      _ = B^2 := by
        simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin, ← Finset.sum_mul]
        change (repeatedL R N)⁻¹ * (repeatedL R N * B^2) = B^2
        rw [← mul_assoc, inv_mul_cancel₀ hL, one_mul]
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hbound

private theorem DecideC_beta_scale {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) (hL : repeatedL R N ≠ 0) :
    repeatedBeta R N = (repeatedH R N)⁻¹.mulVec (DecideC_e R N) := by
  unfold repeatedH DecideC_e DecideC_F
  rw [meanVec_scale, matrix_inverse_scale_total _ _ (inv_ne_zero hL), inv_inv,
    Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hL, one_smul]
  rfl

private theorem DecideC_ols_scale {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (ω : Fin N → U) (hL : repeatedL R N ≠ 0) :
    repeatedOLS R ω = (DecideC_A R N ω)⁻¹.mulVec (DecideC_F R N ω) := by
  unfold DecideC_A DecideC_F
  rw [matrix_inverse_scale_total _ _ (inv_ne_zero hL), inv_inv,
    Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hL, one_smul]
  rfl

private theorem DecideC_inverse_limits {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (H : Mat k) (hH : H.PosDef)
    (hlim : Tendsto (repeatedH R) atTop (𝓝 H))
    (hGram : inProbability (repeatedLaw R) (fun N ω => DecideC_A R N ω - repeatedH R N)) :
    Tendsto (fun N => (repeatedH R N)⁻¹) atTop (𝓝 H⁻¹) ∧
    inProbability (repeatedLaw R) (fun N ω => (DecideC_A R N ω)⁻¹ - H⁻¹) ∧
    inProbability (repeatedLaw R) (fun N ω => (DecideC_A R N ω)⁻¹ - (repeatedH R N)⁻¹) := by
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hR N
  have hdet : H.det ≠ 0 := ne_of_gt hH.det_pos
  have hA : inProbability (repeatedLaw R) (fun N ω => DecideC_A R N ω - H) := by
    have hd := inProbability_deterministic (repeatedLaw R) (fun N => repeatedH R N - H)
      (by
        convert hlim.sub_const H using 1
        simp only [sub_self]
        rfl)
    simpa only [sub_add_sub_cancel] using inProbability_add (repeatedLaw R) hGram hd
  have h0 := (g7_proof.{u} H hdet).1 _ hlim
  have h1 := (g7_proof.{u} H hdet).2 (repeatedLaw R) (DecideC_A R) hA
  refine ⟨h0, h1, ?_⟩
  have hd := inProbability_deterministic (repeatedLaw R) (fun N => H⁻¹ - (repeatedH R N)⁻¹)
    (by
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => H⁻¹) atTop (𝓝 H⁻¹)).sub h0 using 1
      simp only [sub_self]
      rfl)
  simpa only [sub_add_sub_cancel] using inProbability_add (repeatedLaw R) h1 hd

private theorem DecideC_beta_bound {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (H : Mat k) (hH : H.PosDef) (hlim : Tendsto (repeatedH R) atTop (𝓝 H)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N, ‖repeatedBeta R N‖ ≤ C := by
  have hi := (g7_proof.{u} H (ne_of_gt hH.det_pos)).1 _ hlim
  obtain ⟨c, hc⟩ := (Metric.isBounded_range_of_tendsto _ hi).exists_norm_le
  obtain ⟨Ce, hCe, he⟩ := DecideC_e_bound R hR hreg
  let C := (k : ℝ) * |c| * Ce + ‖repeatedBeta R 0‖ + ‖repeatedBeta R 1‖
  refine ⟨C, by dsimp [C]; positivity, fun N => ?_⟩
  by_cases hN : 2 ≤ N
  · rw [DecideC_beta_scale R N (DecideC_L_bounds R hR N hN).1.ne']
    calc
      _ ≤ (k : ℝ) * ‖(repeatedH R N)⁻¹‖ * ‖DecideC_e R N‖ := norm_mulVec_le _ _
      _ ≤ (k : ℝ) * |c| * Ce := by
        gcongr
        exact (hc _ (Set.mem_range_self N)).trans (le_abs_self c)
        exact he N
      _ ≤ C := by dsimp [C]; linarith [norm_nonneg (repeatedBeta R 0), norm_nonneg (repeatedBeta R 1)]
  · have hs : N = 0 ∨ N = 1 := by omega
    have hp : 0 ≤ (k : ℝ) * |c| * Ce := by positivity
    rcases hs with rfl | rfl <;> dsimp [C] <;>
      linarith [norm_nonneg (repeatedBeta R 0), norm_nonneg (repeatedBeta R 1)]

private theorem DecideC_coef_consistency {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (H : Mat k) (hH : H.PosDef) (hlim : Tendsto (repeatedH R) atTop (𝓝 H))
    (hGram : inProbability (repeatedLaw R) (fun N ω => DecideC_A R N ω - repeatedH R N))
    (hXY : inProbability (repeatedLaw R) (fun N ω => DecideC_F R N ω - DecideC_e R N)) :
    inProbability (repeatedLaw R) (fun N ω => repeatedOLS R ω - repeatedBeta R N) := by
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hR N
  obtain ⟨_, hi, hd⟩ := DecideC_inverse_limits R hR H hH hlim hGram
  obtain ⟨Ce, hCe, he⟩ := DecideC_e_bound R hR hreg
  have h1 := inProbability_product_null (repeatedLaw R)
    (fun (A : Mat k) (s : Vec k) => A.mulVec s) (k : ℝ) (Nat.cast_nonneg _)
    norm_mulVec_le (fun N ω => (DecideC_A R N ω)⁻¹) H⁻¹
    (fun N ω => DecideC_F R N ω - DecideC_e R N) hi hXY
  have h2 : inProbability (repeatedLaw R) (fun N ω =>
      ((DecideC_A R N ω)⁻¹ - (repeatedH R N)⁻¹).mulVec (DecideC_e R N)) := by
    apply inProbability_of_norm_bound (repeatedLaw R) hd ((k : ℝ) * Ce + 1) (by positivity)
    apply Eventually.of_forall
    intro N ω
    calc
      _ ≤ (k : ℝ) * ‖(DecideC_A R N ω)⁻¹ - (repeatedH R N)⁻¹‖ * ‖DecideC_e R N‖ :=
        norm_mulVec_le _ _
      _ ≤ (k : ℝ) * ‖(DecideC_A R N ω)⁻¹ - (repeatedH R N)⁻¹‖ * Ce := by gcongr; exact he N
      _ ≤ _ := by nlinarith [norm_nonneg ((DecideC_A R N ω)⁻¹ - (repeatedH R N)⁻¹)]
  apply inProbability_eventually_eq (repeatedLaw R) _ (inProbability_add (repeatedLaw R) h1 h2)
  filter_upwards [eventually_ge_atTop 2] with N hN ω
  have hL := (DecideC_L_bounds R hR N hN).1.ne'
  rw [DecideC_ols_scale R ω hL, DecideC_beta_scale R N hL,
    Matrix.mulVec_sub, Matrix.sub_mulVec]
  abel

private theorem DecideC_q_bound {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hreg : RecordRegular R)
    (T0 : ℕ) (hT : ∀ N d, R.T N d ≤ T0)
    (β : ℕ → Vec k) (Cβ : ℝ) (hCβ : 0 ≤ Cβ) (hβ : ∀ N, ‖β N‖ ≤ Cβ) :
    ∃ Bq : ℝ, 0 ≤ Bq ∧ ∀ N (d : Dyad N),
      ∀ᵐ ω ∂repeatedLaw R N, ‖repeatedBlockScore R (β N) ω d‖ ≤ Bq := by
  obtain ⟨B, hB, hb⟩ := hreg.2
  refine ⟨(T0 : ℝ) * ((B + (k : ℝ) * B * Cβ) * B), by positivity, ?_⟩
  intro N d
  filter_upwards [ae_all_iff.mpr (fun t => hb N d t)] with ω hω
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  simp only [repeatedBlockScore, Finset.sum_apply, score, Pi.smul_apply,
    smul_eq_mul, Real.norm_eq_abs]
  change |∑ t, (repeatedY R ω d t - dot (repeatedX R ω d t) (β N)) *
    repeatedX R ω d t a| ≤ _
  calc
    _ ≤ ∑ t, |(repeatedY R ω d t - dot (repeatedX R ω d t) (β N)) *
      repeatedX R ω d t a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin (R.T N d), (B + (k : ℝ) * B * Cβ) * B := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul]
      apply mul_le_mul _ ((norm_le_pi_norm _ a).trans (hω t).1) (abs_nonneg _) (by positivity)
      calc
        _ ≤ |repeatedY R ω d t| + |dot (repeatedX R ω d t) (β N)| := abs_sub _ _
        _ ≤ B + (k : ℝ) * B * ‖β N‖ := add_le_add (hω t).2
          (abs_dot_le_of_norm_le _ _ B (hω t).1)
        _ ≤ _ := by gcongr; exact hβ N
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT N d) (by positivity)

private def DecideC_M {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (β : ℕ → Vec k) (N : ℕ) (ω : Fin N → U) : Mat k :=
  ((N : ℝ) / (repeatedL R N)^2) • meat members (repeatedBlockScore R (β N) ω)

private def DecideC_V {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (β : ℕ → Vec k) (N : ℕ) : Mat k :=
  ((N : ℝ) / (repeatedL R N)^2) •
    varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N, repeatedBlockScore R (β N) ω d)

/-- The uncentered overlap meat retains the deterministic product of block means. -/
private theorem DecideC_uncentered_expectation {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R) (β : Vec k) :
    meanMat (repeatedLaw R N) (fun ω => meat members (repeatedBlockScore R β ω)) =
      varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N, repeatedBlockScore R β ω d) +
      meat members (fun d : Dyad N => meanVec (repeatedLaw R N)
        (fun ω => repeatedBlockScore R β ω d)) := by
  classical
  letI instUnitProbability : IsProbabilityMeasure R.μ := hR.1
  letI instSampleProbability : IsProbabilityMeasure (repeatedLaw R N) :=
    repeatedLaw_probability R hR N
  let q := fun d : Dyad N => fun ω : Fin N → U => repeatedBlockScore R β ω d
  have hLp (d : Dyad N) (a : Fin k) : MemLp (fun ω => q d ω a) 2 (repeatedLaw R N) :=
    DecideC_q_lp R hR hreg β d a 2
  have hcov (d f : Dyad N) (hdf : ¬(members d ∩ members f).Nonempty) (a b : Fin k) :
      covariance (fun ω => q d ω a) (fun ω => q f ω b) (repeatedLaw R N) = 0 :=
    g2_proof R.μ (members d) (members f) (fun ω => q d ω a) (fun ω => q f ω b)
      (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hdf))
      (DecideC_q_meas R hreg β d a) (DecideC_q_meas R hreg β f b)
      (fun ω ω' h => congrFun (DecideC_q_support R β d ω ω' h) a)
      (fun ω ω' h => congrFun (DecideC_q_support R β f ω ω' h) b)
      (hLp d a) (hLp f b)
  ext a b
  change (∫ ω, (meat members (fun d => q d ω)) a b ∂repeatedLaw R N) =
    covariance (fun ω => (∑ d, q d ω) a) (fun ω => (∑ d, q d ω) b) (repeatedLaw R N) + _
  simp only [meat, Matrix.sum_apply, matrix_ite_apply, outer, Matrix.zero_apply, Pi.zero_apply,
    Finset.sum_apply, Matrix.add_apply]
  have hi (d f : Dyad N) : Integrable
      (fun ω => if (members d ∩ members f).Nonempty then q d ω a * q f ω b else 0)
        (repeatedLaw R N) := by
    split_ifs
    · exact (hLp d a).integrable_mul (hLp f b)
    · exact integrable_const _
  rw [integral_finsetSum _ (fun d _ => integrable_finsetSum _ (fun f _ => hi d f))]
  simp_rw [integral_finsetSum _ (fun f _ => hi _ f)]
  rw [covariance_fun_sum_fun_sum (fun d => hLp d a) (fun f => hLp f b),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hov : (members d ∩ members f).Nonempty
  · simp only [if_pos hov, meanVec]
    rw [covariance_eq_sub (hLp d a) (hLp f b)]
    dsimp only [q, Pi.mul_apply]
    ring
  · simp only [if_neg hov, integral_zero, hcov d f hov a b, add_zero]

private def DecideC_product {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (β : Vec k) (a b : Fin k)
    (P : Dyad N × Dyad N) (ω : Fin N → U) : ℝ :=
  if overlap P.1 P.2 then repeatedBlockScore R β ω P.1 a * repeatedBlockScore R β ω P.2 b else 0

private theorem DecideC_meat_lln {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (β : ℕ → Vec k) (Bq : ℝ) (hBq : 0 ≤ Bq)
    (hb : ∀ N (d : Dyad N), ∀ᵐ ω ∂repeatedLaw R N, ‖repeatedBlockScore R (β N) ω d‖ ≤ Bq) :
    inProbability (repeatedLaw R) (fun N ω =>
      DecideC_M R β N ω - meanMat (repeatedLaw R N) (DecideC_M R β N)) := by
  letI instUnitProbability : IsProbabilityMeasure R.μ := hR.1
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hR N
  have hm (N : ℕ) (a b : Fin k) (P : Dyad N × Dyad N) :
      Measurable (DecideC_product R (β N) a b P) := by
    unfold DecideC_product
    split_ifs
    · exact (DecideC_q_meas R hreg (β N) P.1 a).mul (DecideC_q_meas R hreg (β N) P.2 b)
    · exact measurable_const
  have hs (N : ℕ) (a b : Fin k) (P : Dyad N × Dyad N) (ω ω' : Fin N → U)
      (h : ∀ i ∈ pairSupport P, ω i = ω' i) :
      DecideC_product R (β N) a b P ω = DecideC_product R (β N) a b P ω' := by
    unfold DecideC_product
    split_ifs with hP
    · have hd := DecideC_q_support R (β N) P.1 ω ω'
        (fun i hi => h i (by simp [pairSupport, hP, hi]))
      have hf := DecideC_q_support R (β N) P.2 ω ω'
        (fun i hi => h i (by simp [pairSupport, hP, hi]))
      rw [hd, hf]
    · rfl
  have hbound (N : ℕ) (a b : Fin k) (P : Dyad N × Dyad N) :
      ∀ᵐ ω ∂repeatedLaw R N, |DecideC_product R (β N) a b P ω| ≤ Bq^2 := by
    filter_upwards [hb N P.1, hb N P.2] with ω hd hf
    unfold DecideC_product
    split_ifs
    · rw [abs_mul, pow_two]
      exact mul_le_mul ((norm_le_pi_norm _ a).trans hd)
        ((norm_le_pi_norm _ b).trans hf) (abs_nonneg _) hBq
    · simp [sq_nonneg]
  have hentry (N : ℕ) (ω : Fin N → U) (a b : Fin k) :
      DecideC_M R β N ω a b = ((N : ℝ) / (repeatedL R N)^2) *
        ∑ P : Dyad N × Dyad N, DecideC_product R (β N) a b P ω := by
    simp only [DecideC_M, meat, Matrix.sum_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type, DecideC_product, overlap, matrix_ite_apply, outer,
      Matrix.zero_apply, Pi.zero_apply]
    congr 1
  have hprodLp (N : ℕ) (a b : Fin k) (P : Dyad N × Dyad N) :
      MemLp (DecideC_product R (β N) a b P) 2 (repeatedLaw R N) :=
    MemLp.of_bound (hm N a b P).aestronglyMeasurable (Bq^2) (hbound N a b P)
  have hLp (N : ℕ) (a b : Fin k) :
      MemLp (fun ω => DecideC_M R β N ω a b) 2 (repeatedLaw R N) := by
    simp_rw [hentry]
    exact (memLp_finsetSum univ (fun P _ => hprodLp N a b P)).const_mul _
  have hvar (a b : Fin k) : Tendsto (fun N => variance
      (fun ω => DecideC_M R β N ω a b) (repeatedLaw R N)) atTop (𝓝 0) := by
    have ht : Tendsto (fun N : ℕ => (6144 * (Bq^2)^2) / (N : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
          Tendsto (fun N : ℕ => (6144 * (Bq^2)^2) * (N : ℝ)⁻¹) atTop (𝓝 ((6144 * (Bq^2)^2) * 0)))
    apply squeeze_zero' (Eventually.of_forall fun _ => variance_nonneg _ _) _ ht
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp_rw [hentry]
    rw [variance_const_mul]
    have hv := g3_proof R.μ pairSupport (DecideC_product R (β N) a b) (Bq^2)
      (hm N a b) (hs N a b) (hbound N a b)
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hD : 0 < Dreal N := lt_of_lt_of_le (by positivity) (Dreal_lower hN)
    have hrate : (N : ℝ)^7 / (repeatedL R N)^4 ≤ 256 / (N : ℝ) := by
      calc
        _ ≤ (N : ℝ)^7 / (Dreal N)^4 := div_le_div_of_nonneg_left (by positivity)
          (by positivity)
          (pow_le_pow_left₀ hD.le
            (DecideC_L_bounds R hR N hN).2 4)
        _ ≤ _ := meat_normalization_rate hN
    calc
      _ ≤ ((N : ℝ) / (repeatedL R N)^2)^2 * (24 * (Bq^2)^2 * (N : ℝ)^5) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hh := hv.trans (mul_le_mul_of_nonneg_left (g4_proof N).2 (by positivity))
        convert hh using 1 <;> first | rfl | ring
      _ = 24 * (Bq^2)^2 * ((N : ℝ)^7 / (repeatedL R N)^4) := by ring
      _ ≤ 24 * (Bq^2)^2 * (256 / (N : ℝ)) := mul_le_mul_of_nonneg_left hrate (by positivity)
      _ = (6144 * (Bq^2)^2) / (N : ℝ) := by ring
  exact (g5_proof (repeatedLaw R)).1 (DecideC_M R β) hLp hvar

private theorem DecideC_scaled_count_le {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hN : 2 ≤ N) :
    ((N : ℝ) / (repeatedL R N)^2) * (N : ℝ)^3 ≤ 16 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hD : 0 < Dreal N := lt_of_lt_of_le (by positivity) (Dreal_lower hN)
  calc
    _ ≤ ((N : ℝ) / (Dreal N)^2) * (N : ℝ)^3 := by
      gcongr
      exact (DecideC_L_bounds R hR N hN).2
    _ ≤ 16 := normalized_dyad_count_le hN

private theorem DecideC_covariance_bound {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (β : ℕ → Vec k) (Bq : ℝ) (hBq : 0 ≤ Bq)
    (hb : ∀ N (d : Dyad N), ∀ᵐ ω ∂repeatedLaw R N, ‖repeatedBlockScore R (β N) ω d‖ ≤ Bq) :
    ∃ c : ℝ, ∀ N, ‖DecideC_V R β N‖ ≤ c := by
  letI instUnitProbability : IsProbabilityMeasure R.μ := hR.1
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hR N
  refine ⟨32 * Bq^2, fun N => ?_⟩
  by_cases hN : 2 ≤ N
  · let q := fun d : Dyad N => fun ω : Fin N → U => repeatedBlockScore R (β N) ω d
    have hLp (d : Dyad N) (a : Fin k) : MemLp (fun ω => q d ω a) 2 (repeatedLaw R N) :=
      DecideC_q_lp R hR hreg (β N) d a 2
    have hbound (d : Dyad N) (a : Fin k) : ∀ᵐ ω ∂repeatedLaw R N, |q d ω a| ≤ Bq :=
      (hb N d).mono (fun ω hω => (norm_le_pi_norm _ a).trans hω)
    have hcov (d f : Dyad N) (a b : Fin k) :
        |covariance (fun ω => q d ω a) (fun ω => q f ω b) (repeatedLaw R N)| ≤
          if overlap d f then 2 * Bq^2 else 0 := by
      split_ifs with hov
      · exact abs_covariance_le_two_sq _ (hLp d a) (hLp f b) (hbound d a) (hbound f b)
      · have hz := g2_proof R.μ (members d) (members f) (fun ω => q d ω a) (fun ω => q f ω b)
          (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hov))
          (DecideC_q_meas R hreg (β N) d a) (DecideC_q_meas R hreg (β N) f b)
          (fun ω ω' h => congrFun (DecideC_q_support R (β N) d ω ω' h) a)
          (fun ω ω' h => congrFun (DecideC_q_support R (β N) f ω ω' h) b)
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
        _ = 2 * Bq^2 * ∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then (1 : ℝ) else 0 := by
          simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_left (total_dyad_overlap_bound N) (by positivity)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro b
    change |((N : ℝ) / (repeatedL R N)^2) * varMat (repeatedLaw R N) (fun ω => ∑ d, q d ω) a b| ≤ _
    rw [abs_mul, abs_of_nonneg (show 0 ≤ (N : ℝ) / (repeatedL R N)^2 by positivity)]
    calc
      _ ≤ ((N : ℝ) / (repeatedL R N)^2) * (2 * Bq^2 * (N : ℝ)^3) :=
        mul_le_mul_of_nonneg_left (hv a b) (by positivity)
      _ = 2 * Bq^2 * (((N : ℝ) / (repeatedL R N)^2) * (N : ℝ)^3) := by ring
      _ ≤ 2 * Bq^2 * 16 := mul_le_mul_of_nonneg_left (DecideC_scaled_count_le R hR hN) (by positivity)
      _ = _ := by ring
  · letI instNoDyads : IsEmpty (Dyad N) := Fintype.card_eq_zero_iff.mp (by
      rw [number_of_dyads]
      exact Nat.choose_eq_zero_of_lt (by omega))
    simp [DecideC_V, repeatedL, sq_nonneg]

private def DecideC_fittedM {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) (ω : Fin N → U) : Mat k :=
  ((N : ℝ) / (repeatedL R N)^2) •
    meat members (repeatedBlockScore R (repeatedOLS R ω) ω)

private theorem DecideC_substitution {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (T0 : ℕ) (hT : ∀ N d, R.T N d ≤ T0)
    (β : ℕ → Vec k) (Bq : ℝ) (hBq : 0 ≤ Bq)
    (hq : ∀ N (d : Dyad N), ∀ᵐ ω ∂repeatedLaw R N, ‖repeatedBlockScore R (β N) ω d‖ ≤ Bq)
    (hcoef : inProbability (repeatedLaw R) (fun N ω => repeatedOLS R ω - β N)) :
    inProbability (repeatedLaw R) (fun N ω => DecideC_fittedM R N ω - DecideC_M R β N ω) := by
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hR N
  let δ := fun N (ω : Fin N → U) => repeatedOLS R ω - β N
  change inProbability (repeatedLaw R) δ at hcoef
  obtain ⟨B, hB, hb⟩ := hreg.2
  let L := (T0 : ℝ) * (k : ℝ) * B^2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let φ : Vec k → ℝ := fun z => 16 * (2 * Bq * (L * ‖z‖) + (L * ‖z‖)^2)
  have hφ : ContinuousAt φ 0 := by unfold φ; fun_prop
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hnull : inProbability (repeatedLaw R) (fun N ω => φ (δ N ω)) := by
    have hh := inProbability_continuousAt (repeatedLaw R) (f := δ) hφ
      (by simpa only [sub_zero] using hcoef)
    simpa only [hφ0, sub_zero] using hh
  apply inProbability_ae_norm_le (repeatedLaw R) _ _ hnull
  filter_upwards [eventually_ge_atTop 2] with N hN
  filter_upwards [ae_all_iff.mpr (fun d => ae_all_iff.mpr (fun t => hb N d t)),
    ae_all_iff.mpr (fun d => hq N d)] with ω hdata hqω
  have hchange (d : Dyad N) :
      ‖repeatedBlockScore R (β N) ω d - repeatedBlockScore R (repeatedOLS R ω) ω d‖ ≤ L * ‖δ N ω‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    have hid : (repeatedBlockScore R (β N) ω d - repeatedBlockScore R (repeatedOLS R ω) ω d) a =
        ∑ t, dot (repeatedX R ω d t) (δ N ω) * repeatedX R ω d t a := by
      simp only [repeatedBlockScore, score, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, Finset.sum_apply, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have hdot : dot (repeatedX R ω d t) (δ N ω) =
          dot (repeatedX R ω d t) (repeatedOLS R ω) - dot (repeatedX R ω d t) (β N) := by
        simp only [δ, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      rw [hdot]
      ring
    simp only [Real.norm_eq_abs]
    rw [hid]
    calc
      _ ≤ ∑ t, |dot (repeatedX R ω d t) (δ N ω) * repeatedX R ω d t a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin (R.T N d), ((k : ℝ) * B * ‖δ N ω‖) * B := by
        apply Finset.sum_le_sum
        intro t ht
        rw [abs_mul]
        exact mul_le_mul (abs_dot_le_of_norm_le _ _ B (hdata d t).1)
          ((norm_le_pi_norm _ a).trans (hdata d t).1) (abs_nonneg _) (by positivity)
      _ ≤ (T0 : ℝ) * (((k : ℝ) * B * ‖δ N ω‖) * B) := by
        simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT N d) (by positivity)
      _ = _ := by dsimp [L]; ring
  have hmeat := meat_difference_norm_bound members
    (repeatedBlockScore R (β N) ω) (repeatedBlockScore R (repeatedOLS R ω) ω)
    Bq (L * ‖δ N ω‖) hBq (by positivity) hqω hchange
  have hP : 0 ≤ 2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2 := by positivity
  change ‖DecideC_fittedM R N ω - DecideC_M R β N ω‖ ≤ |φ (δ N ω)|
  rw [abs_of_nonneg (show 0 ≤ φ (δ N ω) by dsimp [φ]; positivity)]
  unfold DecideC_fittedM DecideC_M
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (N : ℝ) / (repeatedL R N)^2 by positivity)]
  calc
    _ ≤ ((N : ℝ) / (repeatedL R N)^2) *
        ((N : ℝ)^3 * (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hmeat.trans (mul_le_mul_of_nonneg_right (g4_proof N).1 hP)
    _ = (((N : ℝ) / (repeatedL R N)^2) * (N : ℝ)^3) *
        (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2) := by ring
    _ ≤ 16 * (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2) :=
      mul_le_mul_of_nonneg_right (DecideC_scaled_count_le R hR hN) hP
    _ = _ := rfl

private theorem DecideC_variance_rescale {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (ω : Fin N → U) (hL : repeatedL R N ≠ 0) :
    (N : ℝ) • repeatedVariance R ω = sandwich (DecideC_A R N ω)⁻¹ (DecideC_fittedM R N ω) := by
  unfold DecideC_A DecideC_fittedM
  rw [matrix_inverse_scale_total _ _ (inv_ne_zero hL), inv_inv]
  unfold repeatedVariance sandwich
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  field_simp

/-- Repeated-data sandwich consistency with the deterministic overlap mean term controlled. -/
theorem repeated_consistency_with_overlap_mean_control
    {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R)
    (hCommon : ∃ fX : ℕ → U → U → Vec k, ∃ fY : ℕ → U → U → ℝ,
      ∀ N d (t : Fin (R.T N d)) u v,
        R.X N d t u v = fX t.val u v ∧ R.Y N d t u v = fY t.val u v)
    (hT : ∃ T0 : ℕ, ∀ N d, R.T N d ≤ T0)
    (H : Mat k) (hH : H.PosDef)
    (hlim : Tendsto (repeatedH R) atTop (𝓝 H))
    (hMean : Tendsto (fun N : ℕ =>
      ((N : ℝ) / (repeatedL R N)^2) • meat members
        (fun d : Dyad N => meanVec (repeatedLaw R N)
          (fun ω => repeatedBlockScore R (repeatedBeta R N) ω d)))
      atTop (𝓝 0)) :
    inProbability (repeatedLaw R) (fun N ω =>
      (N : ℝ) • repeatedVariance R ω - repeatedTarget R N) := by
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hR N
  obtain ⟨T0, hT0⟩ := hT
  have hreg := m0_proof g1_proof R hR
  obtain ⟨hGram, hXY⟩ := DecideC_design_lln R hR hreg T0 hT0
  have hcoef := DecideC_coef_consistency R hR hreg H hH hlim hGram hXY
  obtain ⟨Cβ, hCβ, hβ⟩ := DecideC_beta_bound R hR hreg H hH hlim
  obtain ⟨Bq, hBq, hq⟩ := DecideC_q_bound R hreg T0 hT0 (repeatedBeta R) Cβ hCβ hβ
  have hlln := DecideC_meat_lln R hR hreg (repeatedBeta R) Bq hBq hq
  have hmeans := inProbability_deterministic (repeatedLaw R) _ hMean
  have hmeat : inProbability (repeatedLaw R) (fun N ω =>
      DecideC_M R (repeatedBeta R) N ω - DecideC_V R (repeatedBeta R) N) := by
    have he (N : ℕ) : meanMat (repeatedLaw R N) (DecideC_M R (repeatedBeta R) N) =
        DecideC_V R (repeatedBeta R) N + ((N : ℝ) / (repeatedL R N)^2) •
          meat members (fun d : Dyad N => meanVec (repeatedLaw R N)
            (fun ω => repeatedBlockScore R (repeatedBeta R N) ω d)) := by
      unfold DecideC_M DecideC_V
      rw [meanMat_scale, DecideC_uncentered_expectation R hR hreg, smul_add]
    have hh := inProbability_add (repeatedLaw R) hlln hmeans
    simp only [he] at hh
    convert hh using 1
    funext N ω
    abel
  have hsub := DecideC_substitution R hR hreg T0 hT0 (repeatedBeta R) Bq hBq hq hcoef
  have hfit : inProbability (repeatedLaw R) (fun N ω =>
      DecideC_fittedM R N ω - DecideC_V R (repeatedBeta R) N) := by
    simpa only [sub_add_sub_cancel] using inProbability_add (repeatedLaw R) hsub hmeat
  obtain ⟨h0, h1, _⟩ := DecideC_inverse_limits R hR H hH hlim hGram
  have hb := DecideC_covariance_bound R hR hreg (repeatedBeta R) Bq hBq hq
  have hs := g8_proof (repeatedLaw R) (fun N ω => (DecideC_A R N ω)⁻¹)
    (DecideC_fittedM R) (fun N => (repeatedH R N)⁻¹)
    (DecideC_V R (repeatedBeta R)) H⁻¹ h1 h0 hb hfit
  apply inProbability_eventually_eq (repeatedLaw R) _ hs
  filter_upwards [eventually_ge_atTop 2] with N hN ω
  rw [DecideC_variance_rescale R ω (DecideC_L_bounds R hR N hN).1.ne']
  unfold repeatedTarget DecideC_V sandwich
  simp only [Matrix.mul_smul, Matrix.smul_mul]

private def DecideC_d01 : Dyad 3 :=
  ⟨{0, 1}, by decide⟩

private def DecideC_d12 : Dyad 3 :=
  ⟨{1, 2}, by decide⟩

private theorem DecideC_endpoints :
    firstUnit DecideC_d01 = 0 ∧ secondUnit DecideC_d01 = 1 ∧
    firstUnit DecideC_d12 = 1 ∧ secondUnit DecideC_d12 = 2 := by
  decide

/-- The shared unit is in opposite endpoint roles in these two dyads. -/
private theorem DecideC_cross_role_entry (t1 t2 σ : ℝ) :
    sharedCov 3 1 1 DecideC_d01 DecideC_d12 = 1 ∧
    twoRoleCov 3 t1 t2 σ DecideC_d01 DecideC_d12 = 0 := by
  classical
  have hne : DecideC_d01 ≠ DecideC_d12 := by decide
  rcases DecideC_endpoints with ⟨h0, h1, h1', h2⟩
  simp [sharedCov, twoRoleCov, Matrix.mul_apply, Matrix.transpose_apply,
    endpointZ1, endpointZ2, h0, h1, h1', h2, hne, Fin.sum_univ_succ]

/-- The covariance family fitted in the benchmark cannot match the shared-effect model. -/
theorem benchmark_correspondence_printed_false :
  ¬ (∀ (N : ℕ) (hN : 3 ≤ N),
    ∃ t1 t2 σ : ℝ, 0 ≤ t1 ∧ 0 ≤ t2 ∧ 0 ≤ σ ∧
      sharedCov N 1 1 = twoRoleCov N t1 t2 σ) := by
  intro h
  obtain ⟨t1, t2, σ, _, _, _, heq⟩ := h 3 (by omega)
  have hentry := congrFun (congrFun heq DecideC_d01) DecideC_d12
  rcases DecideC_cross_role_entry t1 t2 σ with ⟨hs, ht⟩
  rw [hs, ht] at hentry
  norm_num at hentry

end
end AronowAudit.P018.Wave1
