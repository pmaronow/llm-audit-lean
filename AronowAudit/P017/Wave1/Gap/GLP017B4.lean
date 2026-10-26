import AronowAudit.P017.Wave1.Gap.GP017B2
import AronowAudit.P017.Wave1.Gap.GP017B3
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! P017-T5 and P017-T8: exact probability counterexample and finite MSE bounds. -/

namespace AronowAudit.P017.Wave1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

private theorem t5b4_standard_absolute_tail (a : ℝ) (ha : 0 < a) :
    pr (gaussianReal 0 1) {z : ℝ | a < |z|} = 2 * normalCDF (-a) := by
  let γ := gaussianReal 0 1
  letI : NullSingletonClass γ := nullSingletonClass_gaussianReal (by norm_num)
  have hset : {z : ℝ | a < |z|} = Iio (-a) ∪ Ioi a := by
    ext z
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hdis : Disjoint (Iio (-a)) (Ioi a) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    simp only [mem_Iio, mem_Ioi] at hz hz'
    linarith
  have hleft : γ (Iio (-a)) = γ (Iic (-a)) :=
    measure_congr (Iio_ae_eq_Iic' (measure_singleton (-a)))
  have hright : γ (Ioi a) = γ (Iio (-a)) := by
    have hmap : γ.map (fun z : ℝ => -z) = γ := by
      simpa [γ] using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
    calc
      γ (Ioi a) = γ.map (fun z : ℝ => -z) (Iio (-a)) := by
        rw [Measure.map_apply measurable_neg measurableSet_Iio]
        congr 1
        ext z
        simp only [mem_preimage, mem_Iio, mem_Ioi]
        constructor <;> intro h <;> linarith
      _ = γ (Iio (-a)) := by rw [hmap]
  unfold pr normalCDF
  rw [hset, measureReal_def, measure_union hdis measurableSet_Ioi,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hright, hleft]
  change (γ (Iic (-a))).toReal + (γ (Iic (-a))).toReal =
    2 * (γ (Iic (-a))).toReal
  ring

private theorem t5b4_moment_transport {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (X : Ξ → ℝ) (hX : Measurable X) (v : ℝ≥0)
    (hlaw : P.map X = gaussianReal 0 v) (k : ℕ) :
    Integrable (fun ω => X ω ^ k) P ∧
    (∫ ω, X ω ^ k ∂P) = (∫ x : ℝ, x ^ k ∂gaussianReal 0 v) := by
  have hi : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
    have h := (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := v) (k : ℝ≥0)).integrable_norm_pow'
    apply h.mono' (by fun_prop)
    exact ae_of_all _ (fun x => by simp [Real.norm_eq_abs, abs_pow])
  constructor
  · have hi' : Integrable (fun x : ℝ => x ^ k) (P.map X) := hlaw.symm ▸ hi
    exact hi'.comp_measurable hX
  · rw [← hlaw, integral_map hX.aemeasurable (by fun_prop)]

private theorem t5b4_remainder :
    NormalRemainder (iidSamples normalPopulation) shiftedNormalMean normalZ normalEpsilon 0 1 :=
  normal_shift_mse_counterexample_proof.2.2.2.2.2.1

private theorem t5b4_mean_measurable (n : ℕ) : Measurable (normalMean n) := by
  unfold normalMean sampleMean
  fun_prop

private theorem t5b4_mean_abs_measurable (n : ℕ) :
    Measurable (fun s => |normalMean n s|) := by
  simpa only [Real.norm_eq_abs] using (t5b4_mean_measurable n).norm

private theorem t5b4_mean_law (n : ℕ) (hn : 1 ≤ n) :
    (iidSamples normalPopulation).map (normalMean n) =
      gaussianReal 0 ⟨1 / (n : ℝ), by positivity⟩ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < sqrtN n := Real.sqrt_pos.mpr hnR
  have hs2 : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have heq : normalMean n = (fun z : ℝ => z / sqrtN n) ∘ normalZ n := by
    funext s
    dsimp only [Function.comp_def, normalZ]
    field_simp
  rw [heq, ← Measure.map_map (by fun_prop) (t5b4_remainder.1 n hn).1,
    (t5b4_remainder.1 n hn).2, gaussianReal_map_div_const]
  simp only [zero_div]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, hs2]
  rfl

private theorem t5b4_second_moment (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun s => normalMean n s ^ 2) (iidSamples normalPopulation) ∧
    (∫ s, normalMean n s ^ 2 ∂iidSamples normalPopulation) = 1 / (n : ℝ) := by
  have ht := t5b4_moment_transport (iidSamples normalPopulation) (normalMean n)
    (t5b4_mean_measurable n) _ (t5b4_mean_law n hn) 2
  refine ⟨ht.1, ht.2.trans ?_⟩
  have h := variance_of_integral_eq_zero
    (μ := gaussianReal 0 ⟨1 / (n : ℝ), by positivity⟩)
    (X := fun x : ℝ => x) measurable_id.aemeasurable
    (by simpa using (integral_id_gaussianReal (μ := (0 : ℝ))
      (v := ⟨1 / (n : ℝ), by positivity⟩)))
  exact h.symm.trans (variance_id_gaussianReal (μ := (0 : ℝ))
    (v := (⟨1 / (n : ℝ), by positivity⟩ : ℝ≥0)))

private theorem t5b4_tail_bound (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a) :
    pr (iidSamples normalPopulation) {s | a < |normalMean n s|} ≤
      (1 / (n : ℝ)) / a ^ 2 := by
  have h2 := t5b4_second_moment n hn
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := iidSamples normalPopulation) (ae_of_all _ (fun s => sq_nonneg (normalMean n s)))
    h2.1 (a ^ 2)
  have hsub : {s | a < |normalMean n s|} ⊆ {s | a ^ 2 ≤ normalMean n s ^ 2} := by
    intro s hs
    change a ^ 2 ≤ normalMean n s ^ 2
    simpa only [sq_abs] using (sq_le_sq₀ ha.le (abs_nonneg _)).mpr hs.le
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg a)).trans
    (hm.trans_eq h2.2)

private theorem t5b4_central_bound (n : ℕ) (hn : 1 ≤ n) :
    1 - 4 / (n : ℝ) ≤
      pr (iidSamples normalPopulation) {s | |normalMean n s| ≤ 1 / 2} := by
  have h := t5b4_tail_bound n hn (1 / 2) (by norm_num)
  have hm : MeasurableSet {s | |normalMean n s| ≤ 1 / 2} := by
    exact measurableSet_le (t5b4_mean_abs_measurable n) measurable_const
  have heq : {s | 1 / 2 < |normalMean n s|} = {s | |normalMean n s| ≤ 1 / 2}ᶜ := by
    ext s
    simp only [mem_setOf_eq, mem_compl_iff, not_le]
  rw [heq, show pr (iidSamples normalPopulation) {s | |normalMean n s| ≤ 1 / 2}ᶜ =
    1 - pr (iidSamples normalPopulation) {s | |normalMean n s| ≤ 1 / 2} from
      probReal_compl_eq_one_sub hm] at h
  have he : (1 / (n : ℝ)) / (1 / 2) ^ 2 = 4 / (n : ℝ) := by ring
  rw [he] at h
  linarith

private theorem t5b4_central_algebra (n : ℕ) (hn : 2 ≤ n)
    (s : ℕ → ℝ × ℝ) (hs : |normalMean n s| ≤ 1 / 2) :
    shiftedDifference n s = -1 / (n : ℝ) ∧
    shiftedNormalMean n s - clipReal 0 1 (shiftedNormalMean n s) = 0 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hδ : 0 < 1 / (n : ℝ) := by positivity
  have hδle : 1 / (n : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hnR
  have hx := abs_le.mp hs
  have hclip : clipReal 0 1 (shiftedNormalMean n s) = shiftedNormalMean n s := by
    apply (clipReal_eq_self_iff _ _ _ (by norm_num)).mpr
    dsimp only [shiftedNormalMean]
    rw [sub_zero]
    apply abs_le.mpr
    constructor <;> linarith
  constructor
  · rw [shiftedDifference, hclip, shiftedNormalMean]
    ring
  · rw [hclip]
    ring

private theorem t5b4_shift_limit :
    Tendsto (fun n : ℕ => sqrtN n / (n : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / sqrtN n) atTop (𝓝 0) := by
    simpa only [one_div, sqrtN, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < sqrtN n := Real.sqrt_pos.mpr hnR
  have hs2 : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  field_simp
  nlinarith [hs2]

private theorem t5b4_shift_littleOp :
    LittleOp (iidSamples normalPopulation)
      (fun n (_ : ℕ → ℝ × ℝ) => sqrtN n / (n : ℝ)) (fun _ => 1) := by
  intro η hη
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_order.1 t5b4_shift_limit.abs).2 η (by simpa using hη)] with n hn
  have he : {s : ℕ → ℝ × ℝ | |sqrtN n / (n : ℝ)| > η * 1} = ∅ := by
    ext s
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, mul_one]
    exact not_lt.mpr hn.le
  simp only [he, pr, measureReal_empty]

private theorem t5b4_rootN :
    RootNNormal (iidSamples normalPopulation) shiftedNormalMean 0 := by
  let Q := iidSamples normalPopulation
  let X := normalZ
  let Y := fun n s => sqrtN n * (shiftedNormalMean n s - 0)
  have hX : TendstoInDistribution X atTop (fun z : ℝ => z) (fun _ => Q)
      (gaussianReal 0 1) := by
    refine ⟨fun n => (measurable_const.mul (t5b4_mean_measurable n)).aemeasurable,
      measurable_id.aemeasurable, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    apply ProbabilityMeasure.toMeasure_injective
    change (gaussianReal 0 1).map id = Q.map (X n)
    rw [Measure.map_id]
    exact (t5b4_remainder.1 n hn).2.symm
  have hdiff : TendstoInMeasure Q (Y - X) atTop 0 := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => by
      change AEStronglyMeasurable (fun s => sqrtN n * (normalMean n s + 1 / (n : ℝ) - 0) -
        sqrtN n * normalMean n s) Q
      exact ((measurable_const.mul (((t5b4_mean_measurable n).add measurable_const).sub
        measurable_const)).sub (measurable_const.mul (t5b4_mean_measurable n))).aestronglyMeasurable)
    apply ae_of_all
    intro s
    convert t5b4_shift_limit using 1
    funext n
    dsimp only [Y, X, Pi.sub_apply, shiftedNormalMean, normalZ]
    ring
  refine ⟨1, by norm_num, ?_⟩
  exact tendstoInDistribution_of_tendstoInMeasure_sub Y (fun z : ℝ => z) hX hdiff
    (fun n => by
      dsimp only [Y, shiftedNormalMean]
      exact (measurable_const.mul (((t5b4_mean_measurable n).add measurable_const).sub
        measurable_const)).aemeasurable)

private theorem t5b4_tail_identity (n : ℕ) (hn : 1 ≤ n) :
    pr (iidSamples normalPopulation) {s | |normalMean n s| > 1} =
      2 * normalCDF (-sqrtN n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < sqrtN n := Real.sqrt_pos.mpr hnR
  rw [← t5b4_standard_absolute_tail (sqrtN n) hs]
  unfold pr
  rw [← (t5b4_remainder.1 n hn).2,
    map_measureReal_apply (t5b4_remainder.1 n hn).1 (by measurability)]
  congr 1
  ext s
  simp only [mem_preimage, mem_setOf_eq, normalZ, abs_mul, abs_of_pos hs]
  exact (lt_mul_iff_one_lt_right hs).symm

private theorem t5b4_tail_lt_one (n : ℕ) (hn : 1 ≤ n) :
    pr (iidSamples normalPopulation) {s | |normalMean n s| > 1} < 1 := by
  let C : Set (ℕ → ℝ × ℝ) := {s | |normalMean n s| ≤ 1}
  have hmC : MeasurableSet C := measurableSet_le (t5b4_mean_abs_measurable n) measurable_const
  have hv : (⟨1 / (n : ℝ), by positivity⟩ : ℝ≥0) ≠ 0 := by
    apply ne_of_gt
    change 0 < 1 / (n : ℝ)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hC : iidSamples normalPopulation C ≠ 0 := by
    intro hz
    have hγ : gaussianReal 0 ⟨1 / (n : ℝ), by positivity⟩ (Icc (-1) 1) = 0 := by
      rw [← t5b4_mean_law n hn, Measure.map_apply (t5b4_mean_measurable n) measurableSet_Icc]
      convert hz using 2
      ext s
      simp only [mem_preimage, mem_Icc, C, mem_setOf_eq, abs_le, neg_le_neg_iff]
    have hvol := gaussianReal_absolutelyContinuous' (μ := (0 : ℝ)) hv hγ
    norm_num at hvol
  have hp : 0 < pr (iidSamples normalPopulation) C :=
    ENNReal.toReal_pos hC (measure_ne_top _ _)
  have heq : {s | |normalMean n s| > 1} = Cᶜ := by
    ext s
    simp only [C, mem_setOf_eq, mem_compl_iff, not_le]
  rw [heq]
  change (iidSamples normalPopulation).real Cᶜ < 1
  rw [probReal_compl_eq_one_sub hmC]
  change 0 < (iidSamples normalPopulation).real C at hp
  linarith

private theorem t5b4_nonzero_probability (n : ℕ) (hn : 1 ≤ n) :
    pr (iidSamples normalPopulation) {s | shiftedDifference n s ≠ 0} = 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hz (s) : shiftedDifference n s = 0 ↔ normalMean n s = 1 :=
    shifted_clip_zero_iff _ _ (by positivity)
  have hv : (⟨1 / (n : ℝ), by positivity⟩ : ℝ≥0) ≠ 0 := by
    apply ne_of_gt
    change 0 < 1 / (n : ℝ)
    positivity
  letI t5b4_nullSingleton := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) hv
  have hsing : pr (iidSamples normalPopulation) {s | normalMean n s = 1} = 0 := by
    have h := map_measureReal_apply (μ := iidSamples normalPopulation)
      (t5b4_mean_measurable n) (measurableSet_singleton (1 : ℝ))
    rw [t5b4_mean_law n hn] at h
    simpa only [measureReal_def, measure_singleton, ENNReal.toReal_zero, pr, Set.preimage, mem_singleton_iff] using h.symm
  have heq : {s | shiftedDifference n s ≠ 0} = {s | normalMean n s = 1}ᶜ := by
    ext s
    simp only [mem_setOf_eq, mem_compl_iff]
    exact not_congr (hz s)
  rw [heq]
  have hm : MeasurableSet {s | normalMean n s = 1} := measurableSet_eq_fun
    (t5b4_mean_measurable n) measurable_const
  change (iidSamples normalPopulation).real _ = 1
  rw [probReal_compl_eq_one_sub hm, ← show pr (iidSamples normalPopulation)
    {s | normalMean n s = 1} = (iidSamples normalPopulation).real {s | normalMean n s = 1} from rfl,
    hsing]
  ring

private theorem t5b4_difference_limit :
    LittleOp (iidSamples normalPopulation)
      (fun n s => (n : ℝ) * shiftedDifference n s + 1) (fun _ => 1) := by
  intro η hη
  have hlim : Tendsto (fun n : ℕ => 4 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (4 : ℝ)
  apply squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) _ hlim
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hcentral := t5b4_central_bound n (by omega)
  have hm : MeasurableSet {s | |normalMean n s| ≤ 1 / 2} :=
    measurableSet_le (t5b4_mean_abs_measurable n) measurable_const
  have hb : pr (iidSamples normalPopulation)
      {s | |(n : ℝ) * shiftedDifference n s + 1| > η * 1} ≤
      pr (iidSamples normalPopulation) {s | |normalMean n s| ≤ 1 / 2}ᶜ := by
    apply measureReal_mono (h₂ := measure_ne_top (iidSamples normalPopulation) _)
    intro s hs hc
    have hd := (t5b4_central_algebra n hn s hc).1
    have hnR : (n : ℝ) ≠ 0 := by
      have hp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      exact hp.ne' 
    have he : (n : ℝ) * shiftedDifference n s + 1 = 0 := by rw [hd]; field_simp; ring
    change η * 1 < |(n : ℝ) * shiftedDifference n s + 1| at hs
    rw [he, abs_zero, mul_one] at hs
    exact (not_lt_of_ge hη.le) hs
  rw [show pr (iidSamples normalPopulation) {s | |normalMean n s| ≤ 1 / 2}ᶜ =
      1 - pr (iidSamples normalPopulation) {s | |normalMean n s| ≤ 1 / 2} from
        probReal_compl_eq_one_sub hm] at hb
  dsimp only [pr] at hcentral hb ⊢
  linarith

private theorem t5b4_not_littleOp :
    ¬ LittleOp (iidSamples normalPopulation) shiftedDifference (fun n => 1 / (n : ℝ)) := by
  intro h
  have hzero := h (1 / 2) (by norm_num)
  have hfour : Tendsto (fun n : ℕ => 1 - 4 / (n : ℝ)) atTop (𝓝 1) := by
    have hi := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (4 : ℝ)
    simpa only [div_eq_mul_inv, mul_zero, sub_zero, Function.comp_def] using tendsto_const_nhds.sub hi
  have hone : Tendsto (fun n => pr (iidSamples normalPopulation)
      {s | |shiftedDifference n s| > (1 / 2) * (1 / (n : ℝ))}) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hfour tendsto_const_nhds _
      (Eventually.of_forall fun n => measureReal_le_one)
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    apply (t5b4_central_bound n (by omega)).trans
    apply measureReal_mono (h₂ := measure_ne_top (iidSamples normalPopulation) _)
    intro s hs
    have hd := (t5b4_central_algebra n hn s hs).1
    have hδ : 0 < 1 / (n : ℝ) := by
      have hp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      positivity
    change (1 / 2) * (1 / (n : ℝ)) < |shiftedDifference n s|
    rw [hd, neg_div, abs_neg, abs_of_pos hδ]
    linarith
  have he : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
  norm_num at he


theorem normal_shift_probability_counterexample_proof :
    Measurable normalEffect ∧ Integrable normalEffect normalPopulation ∧
    populationMean normalPopulation normalEffect = 0 ∧
    effectSupport normalPopulation normalEffect = {-1, 1} ∧ effectRadius normalPopulation normalEffect = 1 ∧
    RootNNormal (iidSamples normalPopulation) shiftedNormalMean 0 ∧
    NormalRemainder (iidSamples normalPopulation) shiftedNormalMean normalZ normalEpsilon 0 1 ∧
    LittleOp (iidSamples normalPopulation) (fun n (_ : ℕ → ℝ × ℝ) => sqrtN n / (n : ℝ)) (fun _ => 1) ∧
    (∀ n : ℕ, 1 ≤ n →
      (iidSamples normalPopulation).map (normalMean n) = gaussianReal 0 ⟨1 / (n : ℝ), by positivity⟩ ∧
      (∀ s, shiftedDifference n s =
        if normalMean n s < -1 - 1 / (n : ℝ) then normalMean n s + 1
        else if normalMean n s ≤ 1 - 1 / (n : ℝ) then -1 / (n : ℝ) else normalMean n s - 1) ∧
      (∀ s, shiftedDifference n s = 0 ↔ normalMean n s = 1) ∧
      pr (iidSamples normalPopulation) {s | shiftedDifference n s ≠ 0} = 1 ∧
      pr (iidSamples normalPopulation) {s | |normalMean n s| > 1} = 2 * normalCDF (-sqrtN n) ∧
      2 * normalCDF (-sqrtN n) < 1 ∧ 2 * normalCDF (-sqrtN n) ≤ 1 / (n : ℝ)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (∀ s, |normalMean n s| ≤ 1 / 2 → shiftedDifference n s = -1 / (n : ℝ) ∧
        shiftedNormalMean n s - clipReal 0 1 (shiftedNormalMean n s) = 0) ∧
      pr (iidSamples normalPopulation) {s | |normalMean n s| ≤ 1 / 2} ≥ 1 - 4 / (n : ℝ) ∧
      pr (iidSamples normalPopulation) {s | |shiftedDifference n s| / (1 / (n : ℝ)) ≥ 1 / 2} ≥ 1 - 4 / (n : ℝ)) ∧
    LittleOp (iidSamples normalPopulation) (fun n s => (n : ℝ) * shiftedDifference n s + 1) (fun _ => 1) ∧
    ¬ LittleOp (iidSamples normalPopulation) shiftedDifference (fun n => 1 / (n : ℝ)) := by
  have hpop := normal_shift_mse_counterexample_proof
  refine ⟨hpop.1, hpop.2.1, hpop.2.2.1, hpop.2.2.2.1, hpop.2.2.2.2.1,
    t5b4_rootN, t5b4_remainder, t5b4_shift_littleOp, ?_, ?_,
    t5b4_difference_limit, t5b4_not_littleOp⟩
  · intro n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    refine ⟨t5b4_mean_law n hn, ?_, ?_, t5b4_nonzero_probability n hn,
      t5b4_tail_identity n hn, ?_, ?_⟩
    · intro s
      dsimp only [shiftedDifference, shiftedNormalMean]
      simp only [clipReal, min_def, max_def]
      split_ifs <;> (try simp only [neg_div]) <;> linarith
    · intro s
      exact shifted_clip_zero_iff _ _ (by positivity)
    · rw [← t5b4_tail_identity n hn]
      exact t5b4_tail_lt_one n hn
    · rw [← t5b4_tail_identity n hn]
      simpa only [one_pow, div_one] using t5b4_tail_bound n hn 1 (by norm_num)
  · intro n hn
    refine ⟨t5b4_central_algebra n hn, t5b4_central_bound n (by omega), ?_⟩
    apply (t5b4_central_bound n (by omega)).trans
    apply measureReal_mono (h₂ := measure_ne_top (iidSamples normalPopulation) _)
    intro s hs
    have hd := (t5b4_central_algebra n hn s hs).1
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hδ : 0 < 1 / (n : ℝ) := by positivity
    change (1 / 2 : ℝ) ≤ |shiftedDifference n s| / (1 / (n : ℝ))
    rw [hd, neg_div, abs_neg, abs_of_pos hδ, div_self hδ.ne']
    norm_num


/-! Gaussian moment recurrence with the variance parametrization. -/
private theorem t8b4_density_pow_integrable (v : ℝ≥0) (hv : 0 < v) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * gaussianPDFReal 0 v x) := by
  have hvR : 0 < (v : ℝ) := hv
  have hbase := integrable_rpow_mul_exp_neg_mul_sq
    (b := 1 / (2 * (v : ℝ))) (by positivity) (s := (k : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have heq : (fun x : ℝ => x ^ k * gaussianPDFReal 0 v x) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        (x ^ (k : ℝ) * Real.exp (-(1 / (2 * (v : ℝ))) * x ^ 2))) := by
    funext x
    rw [Real.rpow_natCast]
    simp only [gaussianPDFReal, sub_zero]
    have hexp : -(x ^ 2) / (2 * (v : ℝ)) = -(1 / (2 * (v : ℝ))) * x ^ 2 := by ring
    rw [hexp]
    ring
  rw [heq]
  exact hbase.const_mul _

/-- Differentiate the centered Gaussian density, retaining the variance factor. -/
private theorem t8b4_density_deriv (v : ℝ≥0) (hv : 0 < v) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-x / (v : ℝ) * gaussianPDFReal 0 v x) x := by
  have hvR : (v : ℝ) ≠ 0 := ne_of_gt hv
  have hh := (((hasDerivAt_id' x).pow 2).neg.div_const (2 * (v : ℝ))).exp
  have hh' := hh.const_mul (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  convert hh' using 1
  · funext y
    simp only [gaussianPDFReal, sub_zero, Pi.pow_apply, Pi.neg_apply]
  · simp only [gaussianPDFReal, sub_zero, Pi.pow_apply, Pi.neg_apply,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    field_simp [hvR]
    <;> ring

/-- Integration by parts with an integrable product avoids boundary limits. -/
private theorem t8b4_gaussian_moment_recurrence (v : ℝ≥0) (hv : 0 < v) (k : ℕ) :
    (∫ x : ℝ, x ^ (k + 2) ∂gaussianReal 0 v) =
      ((k + 1 : ℕ) : ℝ) * (v : ℝ) * (∫ x : ℝ, x ^ k ∂gaussianReal 0 v) := by
  have hvR : (v : ℝ) ≠ 0 := ne_of_gt hv
  have hleft : Integrable (fun x : ℝ =>
      x ^ (k + 1) * (-x / (v : ℝ) * gaussianPDFReal 0 v x)) := by
    convert (t8b4_density_pow_integrable v hv (k + 2)).const_mul (-(v : ℝ)⁻¹) using 1
    funext x
    simp only [pow_add, pow_one, pow_two]
    ring
  have hright : Integrable (fun x : ℝ =>
      ((k + 1 : ℕ) : ℝ) * x ^ k * gaussianPDFReal 0 v x) := by
    simpa only [mul_assoc] using (t8b4_density_pow_integrable v hv k).const_mul ((k + 1 : ℕ) : ℝ)
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x ^ (k + 1)) (u' := fun x => ((k + 1 : ℕ) : ℝ) * x ^ k)
    (v := gaussianPDFReal 0 v) (v' := fun x => -x / (v : ℝ) * gaussianPDFReal 0 v x)
    (fun x _ => by
      convert (hasDerivAt_id' x).pow (k + 1) using 1 <;> simp)
    (fun x _ => t8b4_density_deriv v hv x) hleft hright
    (t8b4_density_pow_integrable v hv (k + 1))
  have hl : (fun x : ℝ => x ^ (k + 1) * (-x / (v : ℝ) * gaussianPDFReal 0 v x)) =
      (fun x : ℝ => (-(v : ℝ)⁻¹) * (x ^ (k + 2) * gaussianPDFReal 0 v x)) := by
    funext x
    simp only [pow_add, pow_one, pow_two]
    ring
  rw [hl, integral_const_mul] at hparts
  have hr : (fun x : ℝ => ((k + 1 : ℕ) : ℝ) * x ^ k * gaussianPDFReal 0 v x) =
      (fun x : ℝ => ((k + 1 : ℕ) : ℝ) * (x ^ k * gaussianPDFReal 0 v x)) := by
    funext x; ring
  rw [hr, integral_const_mul] at hparts
  rw [integral_gaussianReal_eq_integral_smul hv.ne',
    integral_gaussianReal_eq_integral_smul hv.ne']
  simp only [smul_eq_mul] at *
  simp_rw [mul_comm (gaussianPDFReal 0 v _)]
  have hh := congrArg (fun z : ℝ => -(v : ℝ) * z) hparts
  field_simp [hvR] at hh
  nlinarith [hh]

private theorem t8b4_gaussian_even_moments (v : ℝ≥0) (hv : 0 < v) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) ∧
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 ∧
    (∫ x : ℝ, x ^ 6 ∂gaussianReal 0 v) = 15 * (v : ℝ) ^ 3 := by
  have h2 := t8b4_gaussian_moment_recurrence v hv 0
  have h4 := t8b4_gaussian_moment_recurrence v hv 2
  have h6 := t8b4_gaussian_moment_recurrence v hv 4
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, pow_zero, integral_const,
    probReal_univ, smul_eq_mul, one_mul, mul_one] at h2 h4 h6
  refine ⟨h2, ?_, ?_⟩
  · rw [h2] at h4
    nlinarith [h4]
  · rw [h2] at h4
    rw [h4] at h6
    nlinarith [h6]

private theorem t8b4_gaussian_two_sided_tail (v : ℝ≥0) (c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ, if |x| > c then x ^ 2 else 0 ∂gaussianReal 0 v) =
      2 * (∫ x in Ioi c, x ^ 2 ∂gaussianReal 0 v) := by
  let γ := gaussianReal 0 v
  have hi : Integrable (fun x : ℝ => x ^ 2) γ := by
    have h := (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := v) (2 : ℝ≥0)).integrable_norm_pow'
    simpa only [id_eq, Real.norm_eq_abs, sq_abs] using h
  have hip : Integrable (fun x : ℝ => if c < x then x ^ 2 else 0) γ := by
    convert hi.indicator (measurableSet_Ioi : MeasurableSet (Ioi c)) using 1
    funext x; rfl
  have hin : Integrable (fun x : ℝ => if x < -c then x ^ 2 else 0) γ := by
    convert hi.indicator (measurableSet_Iio : MeasurableSet (Iio (-c : ℝ))) using 1
    funext x; rfl
  have hneg : (∫ x : ℝ, if x < -c then x ^ 2 else 0 ∂γ) =
      (∫ x : ℝ, if c < x then x ^ 2 else 0 ∂γ) := by
    have hmap : γ.map (fun x : ℝ => -x) = γ := by
      simpa only [γ, neg_zero] using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := v))
    calc
      (∫ x : ℝ, if x < -c then x ^ 2 else 0 ∂γ) =
          (∫ x : ℝ, if c < -x then (-x) ^ 2 else 0 ∂γ) := by
            apply integral_congr_ae
            apply ae_of_all
            intro x
            have he : c < -x ↔ x < -c := by constructor <;> intro h <;> linarith
            simp only [he, neg_sq]
      _ = (∫ x : ℝ, if c < x then x ^ 2 else 0 ∂γ.map (fun x : ℝ => -x)) := by
        rw [integral_map (by fun_prop)
          ((Measurable.ite measurableSet_Ioi (measurable_id'.pow_const 2) measurable_const).aestronglyMeasurable)]
      _ = _ := by rw [hmap]
  have hsplit (x : ℝ) : (if |x| > c then x ^ 2 else 0) =
      (if x < -c then x ^ 2 else 0) + (if c < x then x ^ 2 else 0) := by
    by_cases hn : x < -c
    · have hp : ¬ c < x := by linarith
      have ha : c < |x| := by rw [abs_of_neg (by linarith)]; linarith
      simp only [hn, hp, ha, ↓reduceIte, add_zero]
    · by_cases hp : c < x
      · have ha : c < |x| := lt_of_lt_of_le hp (le_abs_self x)
        simp only [hn, hp, ha, ↓reduceIte, zero_add]
      · have ha : ¬ c < |x| := not_lt.mpr (abs_le.mpr (by constructor <;> linarith))
        simp only [hn, hp, ha, ↓reduceIte, zero_add]
  simp_rw [hsplit]
  rw [integral_add hin hip, hneg]
  have hpos : (∫ x : ℝ, if c < x then x ^ 2 else 0 ∂γ) =
      ∫ x in Ioi c, x ^ 2 ∂γ := by
    simpa only [Set.indicator, mem_Ioi] using
      (integral_indicator (μ := γ) (f := fun x : ℝ => x ^ 2) measurableSet_Ioi)
  rw [hpos]
  ring

private theorem t8b4_scaled_density (n : ℕ) (hn : 1 ≤ n) (v : ℝ≥0) (hv : 0 < v) (x : ℝ) :
    gaussianPDFReal 0 (v / (n : ℝ≥0)) x =
      (sqrtN n / (Real.sqrt (v : ℝ) * Real.sqrt (2 * Real.pi))) *
        Real.exp (-(x ^ 2 * (n : ℝ)) / (2 * Real.sqrt (v : ℝ) ^ 2)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hvR : 0 < (v : ℝ) := hv
  have hs : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hvR.le
  have hden : Real.sqrt (2 * Real.pi * ((v / (n : ℝ≥0) : ℝ≥0) : ℝ)) =
      (Real.sqrt (v : ℝ) * Real.sqrt (2 * Real.pi)) / sqrtN n := by
    simp only [NNReal.coe_div, NNReal.coe_natCast]
    rw [show 2 * Real.pi * ((v : ℝ) / (n : ℝ)) =
      (v : ℝ) * (2 * Real.pi) / (n : ℝ) by ring,
      Real.sqrt_div (by positivity), Real.sqrt_mul hvR.le]
    rfl
  unfold gaussianPDFReal
  rw [hden, inv_div, hs]
  simp only [sub_zero, NNReal.coe_div, NNReal.coe_natCast]
  congr 2
  field_simp

private theorem t8b4_tail_density {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (X : Ξ → ℝ) (hX : Measurable X)
    (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 < c) (v : ℝ≥0) (hv : 0 < v)
    (hlaw : P.map X = gaussianReal 0 (v / (n : ℝ≥0))) :
    (∫ ω, if |X ω| > c then X ω ^ 2 else 0 ∂P) =
      normalTail n c (Real.sqrt (v : ℝ)) := by
  let γ := gaussianReal 0 (v / (n : ℝ≥0))
  have hpull : (∫ ω, if |X ω| > c then X ω ^ 2 else 0 ∂P) =
      ∫ x : ℝ, if |x| > c then x ^ 2 else 0 ∂γ := by
    change _ = ∫ x : ℝ, if |x| > c then x ^ 2 else 0 ∂gaussianReal 0 (v / (n : ℝ≥0))
    rw [← hlaw, integral_map hX.aemeasurable
      ((Measurable.ite (measurableSet_lt measurable_const (by
        simpa only [Real.norm_eq_abs] using (measurable_id' : Measurable (fun x : ℝ => x)).norm))
        (measurable_id'.pow_const 2) measurable_const).aestronglyMeasurable)]
  rw [hpull, t8b4_gaussian_two_sided_tail _ c hc]
  have hvn : (v / (n : ℝ≥0)) ≠ 0 := by
    have hnR : 0 < (n : ℝ≥0) := by exact_mod_cast (show 0 < n by omega)
    exact (div_pos hv hnR).ne'
  have hrestrict : (∫ x in Ioi c, x ^ 2 ∂γ) =
      ∫ x in Ioi c, x ^ 2 * gaussianPDFReal 0 (v / (n : ℝ≥0)) x := by
    rw [← integral_indicator measurableSet_Ioi,
      integral_gaussianReal_eq_integral_smul hvn]
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    by_cases hx : x ∈ Ioi c
    · simp only [Set.indicator_of_mem hx, smul_eq_mul, mul_comm]
    · simp only [Set.indicator_of_notMem hx, smul_zero]
  rw [hrestrict]
  unfold normalTail
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [t8b4_scaled_density n hn v hv x]
  ring

private theorem t8b4_residual_positive_part (μ c x : ℝ) (hc : 0 < c) :
    residual μ c x ^ 2 = max (|x - μ| - c) 0 ^ 2 := by
  by_cases hl : x < μ - c
  · have hx : x - μ ≤ 0 := by linarith
    have hp : 0 ≤ |x - μ| - c := by rw [abs_of_nonpos hx]; linarith
    rw [abs_of_nonpos hx] at hp
    simp only [residual, clipReal, max_eq_left hl.le,
      min_eq_right (by linarith : μ - c ≤ μ + c), abs_of_nonpos hx, max_eq_left hp]
    ring
  · by_cases hu : x ≤ μ + c
    · have ha : |x - μ| ≤ c := abs_le.mpr (by constructor <;> linarith)
      have he := (clipReal_eq_self_iff μ c x hc.le).mpr ha
      simp only [residual, he, sub_self, max_eq_right (by linarith : |x - μ| - c ≤ 0)]
    · have hx : 0 ≤ x - μ := by linarith
      have hp : 0 ≤ |x - μ| - c := by rw [abs_of_nonneg hx]; linarith
      rw [abs_of_nonneg hx] at hp
      simp only [residual, clipReal, max_eq_right (by linarith : μ - c ≤ x),
        min_eq_left (by linarith : μ + c ≤ x), abs_of_nonneg hx, max_eq_left hp]
      ring

private theorem t8b4_centered_law {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (Z : Ξ → ℝ) (hZ : Measurable Z) (v : ℝ≥0)
    (hlaw : P.map Z = gaussianReal 0 v) (n : ℕ) (hn : 1 ≤ n) :
    P.map (fun ω => Z ω / sqrtN n) = gaussianReal 0 (v / (n : ℝ≥0)) := by
  have heq : (fun ω => Z ω / sqrtN n) = (fun z : ℝ => z / sqrtN n) ∘ Z := rfl
  rw [heq, ← Measure.map_map (by fun_prop) hZ, hlaw, gaussianReal_map_div_const]
  simp only [zero_div]
  congr 2
  apply NNReal.eq
  simp only [NNReal.coe_mk, NNReal.coe_natCast]
  exact Real.sq_sqrt (Nat.cast_nonneg n)


theorem corrected_proposition4_finite_proof {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ)
    (μ c : ℝ) (v : ℝ≥0) (hc : 0 < c) (hv : 0 < v)
    (hhm : ∀ n, Measurable (hat n)) (hr : NormalRemainder P hat Z ε μ v)
    (n : ℕ) (hn : 1 ≤ n) :
    let tilde := fun ω => μ + Z n ω / sqrtN n
    (∀ x y, |clipReal μ c x - clipReal μ c y| ≤ |x - y| ∧
      |residual μ c x - residual μ c y| ≤ |x - y|) ∧
    (∀ᵐ ω ∂P, |residual μ c (hat n ω)| ≤ |residual μ c (tilde ω)| + |ε n ω| / sqrtN n) ∧
    ((∫ ω, residual μ c (hat n ω) ^ 2 ∂P) ≤
      2 * (∫ ω, residual μ c (tilde ω) ^ 2 ∂P) + 2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) ∧
    (∀ x, residual μ c x ^ 2 = max (|x - μ| - c) 0 ^ 2 ∧
      residual μ c x ^ 2 ≤ (if |x - μ| > c then (x - μ) ^ 2 else 0) ∧
      (if |x - μ| > c then (x - μ) ^ 2 else 0) ≤ (x - μ) ^ 4 / c ^ 2) ∧
    ((∫ ω, (tilde ω - μ) ^ 4 ∂P) = 3 * (v : ℝ) ^ 2 / (n : ℝ) ^ 2) ∧
    ((∫ ω, residual μ c (hat n ω) ^ 2 ∂P) ≤
      6 * (v : ℝ) ^ 2 / (c ^ 2 * (n : ℝ) ^ 2) + 2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) ∧
    (∀ᵐ ω ∂P, |tilde ω - clipReal μ c (hat n ω)| ≤
      |residual μ c (tilde ω)| + |ε n ω| / sqrtN n) ∧
    ((∫ ω, (tilde ω - clipReal μ c (hat n ω)) ^ 2 ∂P) ≤
      6 * (v : ℝ) ^ 2 / (c ^ 2 * (n : ℝ) ^ 2) + 2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) ∧
    ((∫ ω, residual μ c (tilde ω) ^ 2 ∂P) ≤
      (∫ ω, if |tilde ω - μ| > c then (tilde ω - μ) ^ 2 else 0 ∂P)) ∧
    ((∫ ω, if |tilde ω - μ| > c then (tilde ω - μ) ^ 2 else 0 ∂P) = normalTail n c (Real.sqrt v)) := by
  dsimp only
  let T : Ξ → ℝ := fun ω => μ + Z n ω / sqrtN n
  have hZ := hr.1 n hn
  have he := hr.2.1 n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < sqrtN n := Real.sqrt_pos.mpr hnR
  have hs2 : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hTm : Measurable T := measurable_const.add (hZ.1.div_const _)
  have hXm : Measurable (fun ω => T ω - μ) := hTm.sub measurable_const
  have hXlaw : P.map (fun ω => T ω - μ) = gaussianReal 0 (v / (n : ℝ≥0)) := by
    simpa only [T, add_sub_cancel_left] using t8b4_centered_law P (Z n) hZ.1 v hZ.2 n hn
  have hvn : 0 < v / (n : ℝ≥0) := by
    apply div_pos hv
    exact_mod_cast (show 0 < n by omega)
  have h2 := t5b4_moment_transport P (fun ω => T ω - μ) hXm _ hXlaw 2
  have h4 := t5b4_moment_transport P (fun ω => T ω - μ) hXm _ hXlaw 4
  have h4val : (∫ ω, (T ω - μ) ^ 4 ∂P) = 3 * (v : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    rw [h4.2, (t8b4_gaussian_even_moments _ hvn).2.1]
    simp only [NNReal.coe_div, NNReal.coe_natCast]
    ring
  have hrep : ∀ᵐ ω ∂P, hat n ω = T ω + ε n ω / sqrtN n := by
    filter_upwards [hr.2.2 n hn] with ω hω
    have hdiv : hat n ω - μ = (Z n ω + ε n ω) / sqrtN n := by
      apply (eq_div_iff hs.ne').mpr
      simpa only [mul_comm] using hω
    dsimp only [T]
    rw [add_div] at hdiv
    linarith only [hdiv]
  have hRmeas : Measurable (fun ω => residual μ c (T ω) ^ 2) := by
    unfold residual clipReal
    fun_prop
  have hRint : Integrable (fun ω => residual μ c (T ω) ^ 2) P := by
    apply (h4.1.div_const (c ^ 2)).mono_nonneg hRmeas.aestronglyMeasurable
      (ae_of_all _ (fun ω => sq_nonneg _))
    exact ae_of_all _ (fun ω => (residual_tail_fourth_bound μ c (T ω) hc).1.trans
      (residual_tail_fourth_bound μ c (T ω) hc).2)
  have habsm : Measurable (fun ω => |T ω - μ|) := by
    simpa only [Real.norm_eq_abs] using hXm.norm
  have hTailm : Measurable (fun ω => if |T ω - μ| > c then (T ω - μ) ^ 2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_const habsm) (hXm.pow_const 2) measurable_const
  have hTaili : Integrable (fun ω => if |T ω - μ| > c then (T ω - μ) ^ 2 else 0) P := by
    apply h2.1.mono_nonneg hTailm.aestronglyMeasurable
    · exact ae_of_all _ (fun ω => by split_ifs <;> positivity)
    · exact ae_of_all _ (fun ω => by split_ifs; exact le_rfl; exact sq_nonneg _)
  let D : Ξ → ℝ := fun ω => 2 * residual μ c (T ω) ^ 2 + 2 * (ε n ω ^ 2 / (n : ℝ))
  have hDi : Integrable D P := (hRint.const_mul 2).add ((he.2.div_const _).const_mul 2)
  have hpoint : ∀ᵐ ω ∂P, residual μ c (hat n ω) ^ 2 ≤ D ω := by
    filter_upwards [hrep] with ω hω
    have hp := (perturbation_square_bounds μ c (T ω) (ε n ω / sqrtN n) hc.le).1
    rw [← hω, div_pow, hs2] at hp
    exact hp
  have hAi : Integrable (fun ω => residual μ c (hat n ω) ^ 2) P := by
    apply hDi.mono_nonneg (by
      have hm := hhm n
      unfold residual clipReal
      fun_prop) (ae_of_all _ (fun ω => sq_nonneg _)) hpoint
  have hA : (∫ ω, residual μ c (hat n ω) ^ 2 ∂P) ≤
      2 * (∫ ω, residual μ c (T ω) ^ 2 ∂P) +
        2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ) := by
    calc
      _ ≤ ∫ ω, D ω ∂P := integral_mono_ae hAi hDi hpoint
      _ = _ := by
        dsimp only [D]
        rw [integral_add (hRint.const_mul 2) ((he.2.div_const _).const_mul 2)]
        simp only [integral_const_mul, integral_div]
        ring
  have hfinal := t8limits_finite_bounds P hat Z ε μ c v hc hhm hr n hn
  rw [(t8b4_gaussian_even_moments v hv).2.1] at hfinal
  have hfinalA : (∫ ω, residual μ c (hat n ω) ^ 2 ∂P) ≤
      6 * (v : ℝ) ^ 2 / (c ^ 2 * (n : ℝ) ^ 2) +
        2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ) := by
    convert hfinal.1 using 1 <;> ring
  have hfinalB : (∫ ω, (T ω - clipReal μ c (hat n ω)) ^ 2 ∂P) ≤
      6 * (v : ℝ) ^ 2 / (c ^ 2 * (n : ℝ) ^ 2) +
        2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ) := by
    convert hfinal.2 using 1 <;> ring
  refine ⟨fun x y => clip_and_residual_lipschitz μ c x y hc.le, ?_, hA, ?_,
    h4val, hfinalA, ?_, hfinalB, ?_, ?_⟩
  · filter_upwards [hrep] with ω hω
    have hlip := (clip_and_residual_lipschitz μ c (hat n ω) (T ω) hc.le).2
    have hdist : |hat n ω - T ω| = |ε n ω| / sqrtN n := by
      rw [hω, add_sub_cancel_left, abs_div, abs_of_pos hs]
    calc
      |residual μ c (hat n ω)| =
          |(residual μ c (hat n ω) - residual μ c (T ω)) + residual μ c (T ω)| := by
            congr 1
            ring
      _ ≤ |residual μ c (hat n ω) - residual μ c (T ω)| + |residual μ c (T ω)| :=
        abs_add_le _ _
      _ ≤ |residual μ c (T ω)| + |ε n ω| / sqrtN n := by rw [hdist] at hlip; linarith
  · intro x
    exact ⟨t8b4_residual_positive_part μ c x hc, residual_tail_fourth_bound μ c x hc⟩
  · filter_upwards [hrep] with ω hω
    have hlip := (clip_and_residual_lipschitz μ c (T ω) (hat n ω) hc.le).1
    have hdist : |T ω - hat n ω| = |ε n ω| / sqrtN n := by
      rw [abs_sub_comm, hω, add_sub_cancel_left, abs_div, abs_of_pos hs]
    calc
      |T ω - clipReal μ c (hat n ω)| =
          |residual μ c (T ω) + (clipReal μ c (T ω) - clipReal μ c (hat n ω))| := by
            unfold residual
            congr 1
            ring
      _ ≤ |residual μ c (T ω)| + |clipReal μ c (T ω) - clipReal μ c (hat n ω)| :=
        abs_add_le _ _
      _ ≤ |residual μ c (T ω)| + |ε n ω| / sqrtN n := by rw [hdist] at hlip; linarith
  · exact integral_mono hRint hTaili (fun ω => (residual_tail_fourth_bound μ c (T ω) hc).1)
  · exact t8b4_tail_density P (fun ω => T ω - μ) hXm n hn c hc v hv hXlaw


end
end AronowAudit.P017.Wave1
