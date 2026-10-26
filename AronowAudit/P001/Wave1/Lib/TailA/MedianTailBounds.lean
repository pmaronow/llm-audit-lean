import AronowAudit.P001.Wave1.Lib.TailA.MedianWeak
import AronowAudit.P001.Wave1.Lib.TailA.EmpiricalCDFBound
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Deterministic median inversion and conditional empirical-CDF tail bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace AronowAudit.P001.Wave1.TailA
open AronowAudit.P001.TailA AronowAudit.Literature
local instance instDecidableMedianTailBounds (p : Prop) : Decidable p := Classical.propDecidable p

/-- Either side of the upper median separates the empirical CDF from one half. -/
theorem medianTail_rank_separation {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    (t < sampleMedian x → FiniteCDF x t ≤ 1/2) ∧
    (sampleMedian x ≤ t → 1/2 < FiniteCDF x t) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he : FiniteCDF x t =
      ((Finset.univ.filter (fun i => x i ≤ t)).card : ℝ) / n := by
    simp only [FiniteCDF, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [he]
  constructor
  · intro ht
    have hh : (Finset.univ.filter (fun i => x i ≤ t)).card ≤ n/2 := by
      have hh := (upper_median_count hn x t).not.mp (not_le.mpr ht)
      omega
    apply (div_le_iff₀ hnR).2
    have ha : 2 * (n/2) ≤ n := by omega
    have hc : ((Finset.univ.filter (fun i => x i ≤ t)).card : ℝ) ≤ (n/2 : ℕ) :=
      Nat.cast_le.mpr hh
    have hd : 2 * (n/2 : ℕ) ≤ (n : ℝ) := by exact_mod_cast ha
    linarith
  · intro ht
    have hh := (upper_median_count hn x t).mp ht
    apply (lt_div_iff₀ hnR).2
    have ha : n < 2 * (n/2+1) := by omega
    have hc : (n/2+1 : ℕ) ≤ ((Finset.univ.filter (fun i => x i ≤ t)).card : ℝ) :=
      Nat.cast_le.mpr hh
    have hd : (n : ℝ) < 2 * (n/2+1 : ℕ) := by exact_mod_cast ha
    linarith

/-- A half-distance threshold avoids any continuity or no-tie requirement on the sample. -/
theorem medianTail_inverse {n : ℕ} (hn : 0 < n) (P : Measure ℝ)
    [IsProbabilityMeasure P] (x : Fin n → ℝ) (m c r : ℝ)
    (hc : 0 < c) (hr : 0 < r)
    (hg : ∀ u ∈ Set.Icc 0 r,
      c*u ≤ (P (Set.Iic (m+u))).toReal - 1/2 ∧
      c*u ≤ 1/2 - (P (Set.Iic (m-u))).toReal) :
    (c/2) * min |sampleMedian x-m| r ≤ CDFDeviation P x := by
  have hD : ∀ t, |FiniteCDF x t - (P (Set.Iic t)).toReal| ≤ CDFDeviation P x := by
    intro t
    exact le_csSup ⟨1, by
      rintro _ ⟨s, rfl⟩
      exact taila09_pointwise_deviation_le hn P x s⟩ (Set.mem_range_self t)
  let d := min |sampleMedian x-m| r
  have hd : 0 ≤ d := le_min (abs_nonneg _) hr.le
  have hdr : d/2 ∈ Set.Icc 0 r := ⟨by positivity, by dsimp [d]; linarith [min_le_right |sampleMedian x-m| r]⟩
  by_cases hm : sampleMedian x = m
  · simp [hm, hr.le, (taila09_cdfDeviation_bounds hn P x).1]
  by_cases hside : m < sampleMedian x
  · have hab : |sampleMedian x-m| = sampleMedian x-m := abs_of_pos (sub_pos.mpr hside)
    have ht : m+d/2 < sampleMedian x := by
      have hdm : d ≤ sampleMedian x-m := by dsimp [d]; rw [hab]; exact min_le_left _ _
      linarith
    have hs := (medianTail_rank_separation hn x (m+d/2)).1 ht
    have hg' := (hg (d/2) hdr).1
    have ha := (le_abs_self ((P (Set.Iic (m+d/2))).toReal-FiniteCDF x (m+d/2))).trans
      (by simpa only [abs_sub_comm] using hD (m+d/2))
    change (c/2)*d ≤ _
    nlinarith
  · have hside' : sampleMedian x < m := lt_of_le_of_ne (le_of_not_gt hside) hm
    have hab : |sampleMedian x-m| = m-sampleMedian x := by rw [abs_of_neg (sub_neg.mpr hside')]; ring
    have ht : sampleMedian x ≤ m-d/2 := by
      have hdm : d ≤ m-sampleMedian x := by dsimp [d]; rw [hab]; exact min_le_left _ _
      linarith
    have hs := (medianTail_rank_separation hn x (m-d/2)).2 ht
    have hg' := (hg (d/2) hdr).2
    have ha := (le_abs_self (FiniteCDF x (m-d/2)-(P (Set.Iic (m-d/2))).toReal)).trans (hD (m-d/2))
    change (c/2)*d ≤ _
    nlinarith

/-- The empirical probability law has the finite empirical CDF, including tied observations. -/
theorem medianTail_empirical_cdf {n : ℕ} [NeZero n] (x : Fin n → ℝ) (t : ℝ) :
    ((StatLean.ComputationalStatistics.empiricalMeasure x) (Set.Iic t)).toReal =
      FiniteCDF x t := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  calc
    _ = (empiricalThresholdProbability x t : ℝ) := by
      simp only [empiricalThresholdProbability, dif_pos hn, Measure.real]
    _ = _ := empirical_threshold_probability_eq x t
    _ = FiniteCDF x t := by
      simp only [FiniteCDF, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Conditional DKW for the actual resampling maps. -/
theorem medianTail_resampling_dkw {n : ℕ} [NeZero n] (hn : 0 < n)
    (x : Fin n → ℝ) {d : ℝ} (hd : 0 ≤ d) :
    (UniformResampling n) {a | d ≤ Real.sqrt n * CDFDeviation
      (StatLean.ComputationalStatistics.empiricalMeasure x) (resample x a)} ≤
        ENNReal.ofReal (4 * Real.exp (-(d^2)/16)) := by
  let P := StatLean.ComputationalStatistics.empiricalMeasure x
  let Q := Measure.pi (fun _ : Fin n => P)
  have hm : ∀ i : Fin n, Measurable (fun y : Fin n → ℝ => y i) :=
    fun i => measurable_pi_apply i
  have hi : iIndepFun (fun i : Fin n => fun y : Fin n → ℝ => y i) Q :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have hl : ∀ i : Fin n, Q.map (fun y : Fin n → ℝ => y i) = P :=
    fun i => (measurePreserving_eval (fun _ : Fin n => P) i).map_eq
  have hb := StatLean.HypothesisTesting.dkw_uniform (P := Q) hn P _ hm hi hl hd
  simp only [← taila09_cdfDeviation_eq_ksDist] at hb
  have hset : MeasurableSet {y : Fin n → ℝ | d ≤ Real.sqrt n * CDFDeviation P y} :=
    measurableSet_le measurable_const
      ((cdf_deviation_measurable hn P _ hm).const_mul _)
  change Q {y | d ≤ Real.sqrt n * CDFDeviation P y} ≤ _ at hb
  dsimp only [Q, P] at hb hset
  rw [empirical_value_law_eq_index_map x, Measure.map_apply Measurable.of_discrete hset] at hb
  exact hb

/-- The nonsharp Gaussian envelope gives a universal fourth moment, via layer cake. -/
theorem medianTail_fourth_of_tail {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (D : E → ℝ)
    (hD : Measurable D) (hD0 : ∀ a, 0 ≤ D a)
    (hI : Integrable (fun a => (D a)^4) μ)
    (hT : ∀ d : ℝ, 0 ≤ d → μ {a | d ≤ D a} ≤
      ENNReal.ofReal (4 * Real.exp (-(d^2)/16))) :
    (∫ a, (D a)^4 ∂μ) ≤ 8192 := by
  have hW : ∀ t : ℝ, 0 < t → μ {a | t ≤ (D a)^2} ≤
      ENNReal.ofReal (4 * Real.exp (-t/16)) := by
    intro t ht
    have he : {a | t ≤ (D a)^2} = {a | Real.sqrt t ≤ D a} := by
      ext a
      simp only [Set.mem_setOf_eq, Real.sqrt_le_iff, hD0 a, true_and]
    rw [he]
    simpa only [Real.sq_sqrt ht.le] using hT (Real.sqrt t) (Real.sqrt_nonneg _)
  have hL := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (f := fun a => (D a)^2) (ae_of_all _ fun a => sq_nonneg _)
    (hD.pow_const 2).aemeasurable (p := 2) (by norm_num)
  norm_num [Real.rpow_two] at hL
  have hInt : IntegrableOn (fun t : ℝ => 128 * Real.exp (-(1/32 : ℝ)*t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(1/32 : ℝ) < 0) 0).const_mul 128
  have hcalc : ∫ t : ℝ in Set.Ioi 0, 128 * Real.exp (-(1/32 : ℝ)*t) = 4096 := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1/32 : ℝ) < 0) 0]
    norm_num
  have hBound : (∫⁻ a, ENNReal.ofReal ((D a)^4) ∂μ) ≤ ENNReal.ofReal 8192 := by
    rw [show (fun a => ENNReal.ofReal ((D a)^4)) =
      (fun a => ENNReal.ofReal (((D a)^2)^2)) by funext a; congr 1; ring, hL]
    calc
      _ ≤ 2 * ∫⁻ t : ℝ in Set.Ioi 0,
          ENNReal.ofReal (128 * Real.exp (-(1/32 : ℝ)*t)) := by
        apply mul_le_mul_right
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := ht
        calc
          μ {a | t ≤ D a^2} * ENNReal.ofReal t
              ≤ ENNReal.ofReal (4 * Real.exp (-t/16)) * ENNReal.ofReal t := by
                exact mul_le_mul_left (hW t ht0) _
          _ = ENNReal.ofReal (4 * Real.exp (-t/16) * t) :=
            (ENNReal.ofReal_mul (by positivity)).symm
          _ ≤ ENNReal.ofReal (128 * Real.exp (-(1/32 : ℝ)*t)) := by
            apply ENNReal.ofReal_le_ofReal
            have hm := Real.mul_exp_neg_le_exp_neg_one (t/32)
            have he : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
            have hex : Real.exp (-t/16) = Real.exp (-(t/32))*Real.exp (-(t/32)) := by
              rw [← Real.exp_add]
              congr 1
              ring
            have hp := mul_le_mul_of_nonneg_right (hm.trans he) (Real.exp_pos (-(t/32))).le
            rw [hex]
            convert (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 128)) using 1 <;> ring
      _ = ENNReal.ofReal 8192 := by
        rw [← ofReal_integral_eq_lintegral_ofReal hInt
          (ae_restrict_of_ae (ae_of_all _ fun t => by positivity)), hcalc]
        norm_num
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun a => by positivity) hI.aestronglyMeasurable]
  exact (ENNReal.toReal_mono (by simp) hBound).trans_eq (by norm_num)

/-- A resampled empirical CDF differs from the population by at most the two deviations. -/
theorem medianTail_deviation_triangle {n : ℕ} [NeZero n] (hn : 0 < n)
    (P : Measure ℝ) [IsProbabilityMeasure P] (x y : Fin n → ℝ) :
    CDFDeviation P y ≤ CDFDeviation P x +
      CDFDeviation (StatLean.ComputationalStatistics.empiricalMeasure x) y := by
  have hd (Q : Measure ℝ) [IsProbabilityMeasure Q] (z : Fin n → ℝ) (t : ℝ) :
      |FiniteCDF z t-(Q (Set.Iic t)).toReal| ≤ CDFDeviation Q z :=
    le_csSup ⟨1, by rintro _ ⟨s, rfl⟩; exact taila09_pointwise_deviation_le hn Q z s⟩
      (Set.mem_range_self t)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨t, rfl⟩
  have h1 := hd P x t
  have h2 := hd (StatLean.ComputationalStatistics.empiricalMeasure x) y t
  rw [medianTail_empirical_cdf] at h2
  have ht := abs_add_le (FiniteCDF y t-FiniteCDF x t)
    (FiniteCDF x t-(P (Set.Iic t)).toReal)
  have he : FiniteCDF y t-FiniteCDF x t+
      (FiniteCDF x t-(P (Set.Iic t)).toReal) = FiniteCDF y t-(P (Set.Iic t)).toReal := by ring
  rw [he] at ht
  linarith

/-- The conditional fourth moment of the root-size resampling CDF deviation. -/
theorem medianTail_resampling_fourth {n : ℕ} [NeZero n] (hn : 0 < n)
    (x : Fin n → ℝ) :
    (∫ a, (Real.sqrt n * CDFDeviation
      (StatLean.ComputationalStatistics.empiricalMeasure x) (resample x a))^4
      ∂UniformResampling n) ≤ 8192 :=
  medianTail_fourth_of_tail (UniformResampling n) _ Measurable.of_discrete
    (fun a => mul_nonneg (Real.sqrt_nonneg _)
      (taila09_cdfDeviation_bounds hn _ _).1) Integrable.of_finite
    (fun _ hd => medianTail_resampling_dkw hn x hd)

end AronowAudit.P001.Wave1.TailA
