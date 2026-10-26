import AronowAudit.Literature.CondP001g14

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

namespace AronowAudit.P001.Wave1

local instance instDecidableCondP001g14 (p : Prop) : Decidable p := Classical.propDecidable p

open AronowAudit.Literature

/-- The bounded transform used in the mean bootstrap theorem. -/
def CondP001g14_sign (x : ℝ) : ℝ := if x ≤ 0 then 1 else 0

@[fun_prop] lemma CondP001g14_sign_measurable : Measurable CondP001g14_sign := by
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

lemma CondP001g14_uniform (a b : ℝ) :
    uniformLaw a b = ENNReal.ofReal ((b-a)⁻¹) • volume.restrict (Set.Icc a b) := by
  unfold uniformLaw
  have he : (fun x : ℝ => ENNReal.ofReal (if x ∈ Set.Icc a b then (b-a)⁻¹ else 0)) =
      (Set.Icc a b).indicator (fun _ => ENNReal.ofReal ((b-a)⁻¹)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b <;> simp [hx]
  rw [he, withDensity_indicator measurableSet_Icc]
  rw [withDensity_const]

lemma CondP001g14_heavy_half : heavyBootstrapLaw (Set.Iic 0) = (1/2 : ℝ≥0∞) := by
  have hp : Measurable (fun u : ℝ => (2 : ℝ) ^ (1/u^2)) := by fun_prop
  have hpos (u : ℝ) : 0 < (2 : ℝ) ^ (1/u^2) := Real.rpow_pos_of_pos (by norm_num) _
  have he1 : (fun u : ℝ => (2 : ℝ) ^ (1/u^2)) ⁻¹' Set.Iic 0 = ∅ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    exact not_le.mpr (hpos u)
  have he2 : (fun u : ℝ => -((2 : ℝ) ^ (1/u^2))) ⁻¹' Set.Iic 0 = Set.univ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
    linarith [hpos u]
  have hi : Set.Iic (0 : ℝ) ∩ Set.Icc (-1 : ℝ) 1 = Set.Icc (-1 : ℝ) 0 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · intro h; exact ⟨h.2.1, h.1⟩
    · intro h; exact ⟨h.2, h.1, by linarith [h.2]⟩
  rw [heavyBootstrapLaw, Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply hp measurableSet_Iic, Measure.map_apply (show Measurable (fun u : ℝ => -((2 : ℝ)^(1/u^2))) from by fun_prop) measurableSet_Iic,
    he1, he2]
  rw [CondP001g14_uniform (-1) 1, CondP001g14_uniform 0 1,
    Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, hi]
  norm_num [Measure.smul_apply, Real.volume_Icc, ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

lemma CondP001g14_sign_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    (hlaw : μ.map Z = heavyBootstrapLaw) :
    MemLp (fun ω => CondP001g14_sign (Z ω)) 2 μ ∧
    (∫ ω, CondP001g14_sign (Z ω) ∂μ) = 1/2 ∧
    variance (fun ω => CondP001g14_sign (Z ω)) μ = 1/4 := by
  have hm := CondP001g14_sign_measurable.comp hZ
  have h2 : MemLp (fun ω => CondP001g14_sign (Z ω)) 2 μ :=
    MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ (by
      intro ω
      simp only [CondP001g14_sign]
      split_ifs <;> norm_num))
  have hs : MeasurableSet {ω | Z ω ≤ 0} := measurableSet_le hZ measurable_const
  have hp : μ {ω | Z ω ≤ 0} = (1/2 : ℝ≥0∞) := by
    rw [← CondP001g14_heavy_half, ← hlaw, Measure.map_apply hZ measurableSet_Iic]
    rfl
  have hmean : (∫ ω, CondP001g14_sign (Z ω) ∂μ) = 1/2 := by
    have he : (fun ω => CondP001g14_sign (Z ω)) =
        {ω | Z ω ≤ 0}.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      simp [CondP001g14_sign, Set.indicator]
    rw [he, integral_indicator_const (1 : ℝ) hs]
    simp only [smul_eq_mul, mul_one]
    change (μ {ω | Z ω ≤ 0}).toReal = _
    rw [hp]
    norm_num
  refine ⟨h2, hmean, ?_⟩
  rw [variance_eq_sub h2]
  have he : (fun ω => CondP001g14_sign (Z ω)^2) =
      (fun ω => CondP001g14_sign (Z ω)) := by
    funext ω
    simp only [CondP001g14_sign]
    split_ifs <;> norm_num
  change (∫ ω, CondP001g14_sign (Z ω)^2 ∂μ) -
    (∫ ω, CondP001g14_sign (Z ω) ∂μ)^2 = _
  rw [he, hmean]
  norm_num

lemma CondP001g14_mean_sign {n : ℕ} (x : Fin n → ℝ) :
    FiniteMean (fun i => CondP001g14_sign (x i)) =
      ((Finset.univ.filter (fun i => x i ≤ 0)).card : ℝ) / (n : ℝ) := by
  unfold FiniteMean
  congr 1
  simp [CondP001g14_sign]

lemma CondP001g14_sd_sign {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    FiniteSD (fun i => CondP001g14_sign (x i)) =
      Real.sqrt (FiniteMean (fun i => CondP001g14_sign (x i)) *
        (1 - FiniteMean (fun i => CondP001g14_sign (x i)))) := by
  unfold FiniteSD
  congr 1
  let p := FiniteMean (fun i => CondP001g14_sign (x i))
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : (∑ i, CondP001g14_sign (x i)) = (n : ℝ) * p := by
    dsimp [p, FiniteMean]
    field_simp
  have he (i : Fin n) : (CondP001g14_sign (x i) - p)^2 =
      (1-2*p)*CondP001g14_sign (x i) + p^2 := by
    simp only [CondP001g14_sign]
    split_ifs <;> ring
  change (∑ i, (CondP001g14_sign (x i) - p)^2) / (n : ℝ) = p*(1-p)
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  <;> ring

lemma CondP001g14_sd_bad {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : FiniteMean (fun i => CondP001g14_sign (x i)) ∉ Set.Icc (1/4 : ℝ) (3/4)) :
    (1/32 : ℝ) < |FiniteSD (fun i => CondP001g14_sign (x i)) - 1/2| := by
  rw [CondP001g14_sd_sign hn]
  let p := FiniteMean (fun i => CondP001g14_sign (x i))
  have hprod : p * (1-p) ≤ 3/16 := by
    have hh : p < 1/4 ∨ 3/4 < p := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hx
    rcases hh with hh | hh <;> nlinarith [sq_nonneg (p-1/4), sq_nonneg (p-3/4)]
  have hroot : Real.sqrt (p*(1-p)) ≤ 7/16 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  have habs := le_abs_self (Real.sqrt (p*(1-p)) - 1/2)
  have hneg := neg_le_abs (Real.sqrt (p*(1-p)) - 1/2)
  change (1/32 : ℝ) < |Real.sqrt (p*(1-p))-1/2|
  linarith

lemma CondP001g14_regular_eq {n : ℕ} (x : Fin n → ℝ)
    (hx : FiniteMean (fun i => CondP001g14_sign (x i)) ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    regularHeavyStatistic x = FiniteMean (fun i => CondP001g14_sign (x i)) - 1/2 := by
  unfold regularHeavyStatistic
  rw [← CondP001g14_mean_sign]
  exact if_pos hx

/-- The two finite conditional averages supplied by the published result. -/
def CondP001g14_reference {n : ℕ} (x : Fin n → ℝ) (f : ℝ → ℝ) : ℝ :=
  ResamplingMean (fun i => CondP001g14_sign (x i))
    (fun y : Fin n → ℝ => f (Real.sqrt n *
      (FiniteMean y - FiniteMean (fun i => CondP001g14_sign (x i)))))

def CondP001g14_tail {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ResamplingMean (fun i => CondP001g14_sign (x i))
    (fun y : Fin n → ℝ => if (1/32 : ℝ) < |FiniteSD y - 1/2| then 1 else 0)

lemma CondP001g14_comparison {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (f : ℝ → ℝ) (C : ℝ) (hC : ∀ z, |f z| ≤ C) :
    |bootstrapTestMean regularHeavyStatistic x f - CondP001g14_reference x f| ≤
      2*C*(if FiniteMean (fun i => CondP001g14_sign (x i)) ∈
        Set.Icc (1/4 : ℝ) (3/4) then CondP001g14_tail x else 1) := by
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  have hfd (z w : ℝ) : |f z - f w| ≤ 2*C :=
    (abs_sub _ _).trans (by linarith [hC z, hC w])
  have hden : 0 < (n : ℝ)^n := pow_pos (by exact_mod_cast hn) _
  let p := FiniteMean (fun i => CondP001g14_sign (x i))
  let v := fun a : Fin n → Fin n => f (Real.sqrt n *
    (regularHeavyStatistic (fun i => x (a i)) - regularHeavyStatistic x))
  let w := fun a : Fin n → Fin n => f (Real.sqrt n *
    (FiniteMean (fun i => CondP001g14_sign (x (a i))) - p))
  let t := fun a : Fin n → Fin n =>
    if (1/32 : ℝ) < |FiniteSD (fun i => CondP001g14_sign (x (a i))) - 1/2|
    then (1 : ℝ) else 0
  have hbasic : |bootstrapTestMean regularHeavyStatistic x f - CondP001g14_reference x f| ≤
      (∑ a, |v a - w a|) / (n : ℝ)^n := by
    change |(∑ a, v a) / (n : ℝ)^n - (∑ a, w a) / (n : ℝ)^n| ≤ _
    rw [← sub_div, abs_div, abs_of_pos hden, ← Finset.sum_sub_distrib]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hden.le
  by_cases hx : p ∈ Set.Icc (1/4 : ℝ) (3/4)
  · have hpoint (a : Fin n → Fin n) : |v a - w a| ≤ 2*C*t a := by
      by_cases hy : FiniteMean (fun i => CondP001g14_sign (x (a i))) ∈
          Set.Icc (1/4 : ℝ) (3/4)
      · have hvw : v a = w a := by
          dsimp [v, w]
          rw [CondP001g14_regular_eq x hx, CondP001g14_regular_eq _ hy]
          congr 2
          dsimp [p]
          ring
        rw [hvw, sub_self, abs_zero]
        dsimp [t]
        split_ifs <;> positivity
      · have hb := CondP001g14_sd_bad hn (fun i => x (a i)) hy
        simp only [t, if_pos hb, mul_one]
        exact hfd _ _
    change _ ≤ 2*C*(if p ∈ Set.Icc (1/4 : ℝ) (3/4) then _ else _)
    rw [if_pos hx]
    calc
      _ ≤ (∑ a, 2*C*t a) / (n : ℝ)^n :=
        hbasic.trans (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => hpoint a)) hden.le)
      _ = 2*C*CondP001g14_tail x := by
        rw [← Finset.mul_sum]
        change (2*C*(∑ a, t a)) / (n : ℝ)^n = 2*C*((∑ a, t a) / (n : ℝ)^n)
        ring
  · change _ ≤ 2*C*(if p ∈ Set.Icc (1/4 : ℝ) (3/4) then _ else _)
    rw [if_neg hx, mul_one]
    calc
      _ ≤ (∑ _a : Fin n → Fin n, 2*C) / (n : ℝ)^n :=
        hbasic.trans (div_le_div_of_nonneg_right
          (Finset.sum_le_sum (fun a _ => hfd _ _)) hden.le)
      _ = 2*C := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
        field_simp

/-- A measurable envelope suffices even for an arbitrary statistic on the bad branch. -/
lemma CondP001g14_CP_envelope {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z U : ℕ → Ω → ℝ) (c : ℝ)
    (hm : ∀ n, Measurable (U n))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => U n ω) atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop, ∀ ω, |Z n ω - c| ≤ |U n ω|) : CP μ Z c := by
  have ht := tendstoInMeasure_of_tendsto_ae (fun n => (hm n).aestronglyMeasurable) hlim
  intro ε hε
  have hu := (tendstoInMeasure_iff_measureReal_dist.mp ht) ε hε
  apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) _ hu
  filter_upwards [hbound] with n hn
  apply measureReal_mono _ (measure_ne_top μ _)
  intro ω hω
  simp only [Real.dist_eq, sub_zero, Set.mem_setOf_eq] at hω ⊢
  exact hω.trans (hn ω)

@[fun_prop] lemma CondP001g14_finiteMean_measurable (n : ℕ) :
    Measurable (@FiniteMean n) := by
  unfold FiniteMean
  fun_prop

@[fun_prop] lemma CondP001g14_finiteSD_measurable (n : ℕ) :
    Measurable (@FiniteSD n) := by
  unfold FiniteSD
  fun_prop

lemma CondP001g14_reference_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (n : ℕ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    Measurable (fun ω => CondP001g14_reference (firstSample X n ω) f) := by
  unfold CondP001g14_reference ResamplingMean firstSample
  fun_prop

lemma CondP001g14_tail_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (fun ω => CondP001g14_tail (firstSample X n ω)) := by
  unfold CondP001g14_tail ResamplingMean firstSample
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro a ha
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_lt measurable_const
  fun_prop

theorem regular_heavy_functional_bootstrap_weak_limit_conditional :
    AronowAudit.P001.regular_heavy_functional_bootstrap_weak_limit_conditional_statement := by
  intro hbootstrap Ω mΩ μ instμ X hiid hlaw
  let B : ℕ → Ω → ℝ := fun i ω => CondP001g14_sign (X i ω)
  have hB : IID μ B := by
    refine ⟨fun i => CondP001g14_sign_measurable.comp (hiid.1 i),
      hiid.2.1.comp (fun _ => CondP001g14_sign) (fun _ => CondP001g14_sign_measurable),
      fun i => (hiid.2.2 i).comp CondP001g14_sign_measurable⟩
  obtain ⟨hB2, hBmean, hBvar⟩ := CondP001g14_sign_moments μ (X 0) (hiid.1 0) hlaw
  change MemLp (B 0) 2 μ at hB2
  change (∫ ω, B 0 ω ∂μ) = 1/2 at hBmean
  change variance (B 0) μ = 1/4 at hBvar
  have hvarpos : 0 < variance (B 0) μ := by rw [hBvar]; norm_num
  have hboot := hbootstrap Ω mΩ μ instμ B hB.1 hB.2.1 hB.2.2 hB2 hvarpos
  have hSLLN := strong_law_ae_real B (hB2.integrable one_le_two)
    (fun i j hij => hB.2.1.indepFun hij) hB.2.2
  have hmeans : ∀ᵐ ω ∂μ, Tendsto (fun n =>
      FiniteMean (fun i : Fin n => B i ω)) atTop (nhds (1/2 : ℝ)) := by
    filter_upwards [hSLLN] with ω hω
    have he (n : ℕ) : FiniteMean (fun i : Fin n => B i ω) =
        (∑ i ∈ Finset.range n, B i ω) / (n : ℝ) := by
      unfold FiniteMean
      rw [Fin.sum_univ_eq_sum_range (fun i => B i ω) n]
    simpa only [he, hBmean] using hω
  have hsqrt : Real.sqrt (variance (B 0) μ) = 1/2 := by
    rw [hBvar]
    norm_num
  have hgauss : gaussianReal 0 (variance (B 0) μ).toNNReal = gaussianReal 0 (1/4) := by
    rw [hBvar]
    congr 1
    apply NNReal.eq
    norm_num
  intro f hf hfbd
  obtain ⟨C, hC⟩ := hfbd
  let L : ℝ := mean (gaussianReal 0 (1/4)) f
  let R : ℕ → Ω → ℝ := fun n ω => CondP001g14_reference (firstSample X n ω) f
  let S : ℕ → Ω → ℝ := fun n ω => CondP001g14_tail (firstSample X n ω)
  let U : ℕ → Ω → ℝ := fun n ω => |R n ω - L| + 2*C*
    (if FiniteMean (fun i : Fin n => B i ω) ∈ Set.Icc (1/4 : ℝ) (3/4)
      then S n ω else 1)
  have hR : ∀ n, Measurable (R n) := fun n => CondP001g14_reference_measurable X hiid.1 n f hf
  have hS : ∀ n, Measurable (S n) := fun n => CondP001g14_tail_measurable X hiid.1 n
  have hU : ∀ n, Measurable (U n) := by
    intro n
    have habs : Measurable (fun ω => |R n ω - L|) := by fun_prop
    apply Measurable.add habs
    apply Measurable.const_mul
    apply Measurable.ite _ (hS n) measurable_const
    exact measurableSet_Icc.preimage (CondP001g14_finiteMean_measurable n |>.comp
      (measurable_pi_iff.mpr (fun i : Fin n => hB.1 i)))
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => U n ω) atTop (nhds 0) := by
    filter_upwards [hboot, hmeans] with ω hb hm
    have hr : Tendsto (fun n => R n ω) atTop (nhds L) := by
      have h := (hb.1 f hf ⟨C, hC⟩).comp tendsto_atTop_diagonal
      simpa only [R, CondP001g14_reference, B, firstSample, hgauss, L, mean, Function.comp_def] using h
    have hs : Tendsto (fun n => S n ω) atTop (nhds 0) := by
      have h := (hb.2 (1/32) (by norm_num)).comp tendsto_atTop_diagonal
      simpa only [S, CondP001g14_tail, B, firstSample, hsqrt, Function.comp_def] using h
    have hgood : ∀ᶠ n in atTop,
        FiniteMean (fun i : Fin n => B i ω) ∈ Set.Icc (1/4 : ℝ) (3/4) :=
      hm.eventually (Icc_mem_nhds (by norm_num) (by norm_num))
    have hu := (hr.sub_const L).abs.add (hs.const_mul (2*C))
    simp only [sub_self, abs_zero, mul_zero, add_zero] at hu
    apply hu.congr'
    filter_upwards [hgood] with n hn
    simp only [U, if_pos hn]
  have hbound : ∀ᶠ n in atTop, ∀ ω,
      |bootstrapTestMean regularHeavyStatistic (firstSample X n ω) f - L| ≤ |U n ω| := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    intro ω
    have hb := CondP001g14_comparison hn (firstSample X n ω) f C hC
    have ht := abs_sub_le (bootstrapTestMean regularHeavyStatistic (firstSample X n ω) f)
      (R n ω) L
    have hh : |bootstrapTestMean regularHeavyStatistic (firstSample X n ω) f - L| ≤ U n ω := by
      dsimp [U]
      dsimp [R, S, B, firstSample] at *
      linarith
    exact hh.trans (le_abs_self _)
  have hcp := CondP001g14_CP_envelope μ
    (fun n ω => bootstrapTestMean regularHeavyStatistic (firstSample X n ω) f) U L hU hlim hbound
  intro ε hε
  have hodd : Tendsto (fun k : ℕ => 2*k+1) atTop atTop :=
    tendsto_atTop_mono (fun k : ℕ => (show k ≤ 2*k+1 by omega)) tendsto_id
  exact (hcp ε hε).comp hodd

end AronowAudit.P001.Wave1
