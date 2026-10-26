import AronowAudit.P033.P033_Audit
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
P033-T9: the native-SE normal-power correction.

The Gaussian probability and the strict power comparison are proved independently.
The P053 quantile results are transported across definitionally equal normal CDFs.
-/

namespace AronowAudit.P033.Wave1

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section

lemma native_power_correction_cdf_neg (x : ℝ) :
    normalCDF (-x) = 1 - normalCDF x := by
  simpa only [normalCDF, cdf_eq_real] using
    AronowAudit.P053.NormalCompletion.normal_cdf_neg x

lemma native_power_correction_critical_eq :
    normalCritical = AronowAudit.P053.normalCritical (1/20) := by
  unfold normalCritical normalQuantile AronowAudit.P053.normalCritical
  norm_num [normalCDF, AronowAudit.P053.standardNormalCDF, measureReal_def]

lemma native_power_correction_critical_pos : 0 < normalCritical := by
  rw [native_power_correction_critical_eq]
  exact AronowAudit.P053.NormalCompletion.normalCritical_pos (1/20)
    (by norm_num) (by norm_num)

lemma native_power_correction_critical_cdf : normalCDF normalCritical = 39/40 := by
  change AronowAudit.P053.standardNormalCDF normalCritical = 39/40
  rw [native_power_correction_critical_eq]
  have h := AronowAudit.P053.NormalCompletion.normalCritical_cdf (1/20)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

lemma native_power_correction_power_zero : normalPower 0 = 1/20 := by
  have h := native_power_correction_cdf_neg normalCritical
  rw [native_power_correction_critical_cdf] at h
  simp only [normalPower, zero_sub, neg_zero]
  linarith

lemma native_power_correction_density_continuous : Continuous normalDensity := by
  unfold normalDensity gaussianPDFReal
  fun_prop

lemma native_power_correction_density_even (x : ℝ) :
    normalDensity (-x) = normalDensity x := by
  simp [normalDensity, gaussianPDFReal]

lemma native_power_correction_cdf_integral (x : ℝ) :
    normalCDF x = ∫ t in Iic x, normalDensity t := by
  unfold normalCDF normalDensity
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal) ≠ 0)]
  exact ENNReal.toReal_ofReal
    (integral_nonneg (fun t => gaussianPDFReal_nonneg 0 1 t))

/-- FTC-1, after expressing the lower-tail integral as a constant plus an interval integral. -/
lemma native_power_correction_cdf_deriv (x : ℝ) :
    HasDerivAt normalCDF (normalDensity x) x := by
  have hi : Integrable normalDensity volume := integrable_gaussianPDFReal 0 1
  have hrep : normalCDF = fun y : ℝ =>
      normalCDF 0 + ∫ t in (0:ℝ)..y, normalDensity t := by
    funext y
    have hsub := intervalIntegral.integral_Iic_sub_Iic
      (hi.integrableOn : IntegrableOn normalDensity (Iic (0:ℝ)) volume)
      (hi.integrableOn : IntegrableOn normalDensity (Iic y) volume)
    rw [← native_power_correction_cdf_integral y,
      ← native_power_correction_cdf_integral 0] at hsub
    linarith
  have hbase : HasDerivAt (fun y : ℝ => ∫ t in (0:ℝ)..y, normalDensity t)
      (normalDensity x) x :=
    intervalIntegral.integral_hasDerivAt_right hi.intervalIntegrable
      hi.aestronglyMeasurable.stronglyMeasurableAtFilter
      native_power_correction_density_continuous.continuousAt
  exact (hbase.const_add (normalCDF 0)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => congrFun hrep y))

lemma native_power_correction_power_deriv (a : ℝ) :
    HasDerivAt normalPower
      (normalDensity (a-normalCritical)-normalDensity (a+normalCritical)) a := by
  have hleft := (native_power_correction_cdf_deriv (a-normalCritical)).comp (x := a)
    ((hasDerivAt_id' a).sub_const normalCritical)
  have hright := (native_power_correction_cdf_deriv (-a-normalCritical)).comp (x := a)
    ((hasDerivAt_id' a).neg.sub_const normalCritical)
  have heven : normalDensity (-a-normalCritical) = normalDensity (a+normalCritical) := by
    rw [show -a-normalCritical = -(a+normalCritical) by ring,
      native_power_correction_density_even]
  have hsum : HasDerivAt normalPower
      (normalDensity (a-normalCritical) + -normalDensity (-a-normalCritical)) a := by
    have h := hleft.add hright
    simp only [Function.comp_def, mul_one, mul_neg_one] at h
    exact h
  rw [heven] at hsum
  simpa only [sub_eq_add_neg] using hsum

lemma native_power_correction_deriv_pos (a : ℝ) (ha : 0 < a) :
    0 < normalDensity (a-normalCritical)-normalDensity (a+normalCritical) := by
  have hz := native_power_correction_critical_pos
  apply sub_pos.mpr
  unfold normalDensity gaussianPDFReal
  norm_num only [NNReal.coe_one, sub_zero, mul_one]
  apply mul_lt_mul_of_pos_left
  · apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos ha hz]
  · positivity

lemma native_power_correction_strictMono : StrictMonoOn normalPower (Ici 0) := by
  have hc : Continuous normalPower := continuous_iff_continuousAt.mpr
    (fun a => (native_power_correction_power_deriv a).continuousAt)
  apply strictMonoOn_of_deriv_pos (convex_Ici (0:ℝ)) hc.continuousOn
  intro a ha
  have ha0 : 0 < a := by simpa only [interior_Ici, mem_Ioi] using ha
  rw [(native_power_correction_power_deriv a).deriv]
  exact native_power_correction_deriv_pos a ha0

lemma native_power_correction_power_even (a : ℝ) : normalPower (-a) = normalPower a := by
  simp only [normalPower, neg_neg]
  ring

lemma native_power_correction_power_abs (a : ℝ) : normalPower |a| = normalPower a := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha]
  · rw [abs_of_nonpos ha, native_power_correction_power_even]

/-- Translate the actual Gaussian measure, retaining its variance-one parameter. -/
lemma native_power_correction_shifted_cdf (m x : ℝ) :
    (gaussianReal m 1).real (Iic x) = normalCDF (x-m) := by
  have hm : (gaussianReal 0 1).map (fun t : ℝ => t+m) = gaussianReal m 1 := by
    simpa only [zero_add] using
      (gaussianReal_map_add_const (μ := (0:ℝ)) (v := (1:NNReal)) m)
  have hpre : (fun t : ℝ => t+m) ⁻¹' Iic x = Iic (x-m) := by
    ext t
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro h <;> linarith
  change (gaussianReal m 1).real (Iic x) = (gaussianReal 0 1).real (Iic (x-m))
  rw [← hm, map_measureReal_apply (by fun_prop : Measurable (fun t : ℝ => t + m))
    measurableSet_Iic, hpre]

lemma native_power_correction_gaussian_rejection (m : ℝ) :
    (gaussianReal m 1).real {x : ℝ | normalCritical < |x|} = normalPower m := by
  letI : NullSingletonClass (gaussianReal m 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1:NNReal) ≠ 0)
  have hz : 0 < normalCritical := native_power_correction_critical_pos
  have hset : {x : ℝ | normalCritical < |x|} =
      Iio (-normalCritical) ∪ Ioi normalCritical := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi]
    constructor
    · intro h
      by_cases hx : 0 ≤ x
      · right
        simpa only [abs_of_nonneg hx] using h
      · left
        rw [abs_of_neg (lt_of_not_ge hx)] at h
        linarith
    · rintro (h | h)
      · have hx : x < 0 := by linarith
        rw [abs_of_neg hx]
        linarith
      · have hx : 0 ≤ x := le_of_lt (lt_trans hz h)
        simpa only [abs_of_nonneg hx] using h
  have hd : Disjoint (Iio (-normalCritical)) (Ioi normalCritical) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : x < -normalCritical := hx
    have hy' : normalCritical < x := hy
    linarith
  have hlo : (gaussianReal m 1).real (Iio (-normalCritical)) =
      normalCDF (-normalCritical-m) := by
    calc
      _ = (gaussianReal m 1).real (Iic (-normalCritical)) :=
        measureReal_congr (Iio_ae_eq_Iic' (measure_singleton (-normalCritical)))
      _ = _ := native_power_correction_shifted_cdf m (-normalCritical)
  have hhi : (gaussianReal m 1).real (Ioi normalCritical) =
      1-normalCDF (normalCritical-m) := by
    have h := measureReal_add_measureReal_compl (μ := gaussianReal m 1)
      (s := Iic normalCritical) measurableSet_Iic
    simp only [compl_Iic, probReal_univ] at h
    rw [native_power_correction_shifted_cdf] at h
    linarith
  have hsym : normalCDF (normalCritical-m) = 1-normalCDF (m-normalCritical) := by
    rw [show normalCritical-m = -(m-normalCritical) by ring,
      native_power_correction_cdf_neg]
  rw [hset, measureReal_union hd measurableSet_Ioi, hlo, hhi, hsym]
  unfold normalPower
  rw [show -normalCritical-m = -m-normalCritical by ring]
  ring

lemma native_power_correction_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → ℝ) (τ s : ℝ)
    (hs : 0 < s) (hT : HasLaw T (gaussianReal (τ/s) 1) μ) :
    μ.real {ω | normalCritical < |T ω|} = normalPower (|τ|/s) := by
  have hmeas : MeasurableSet {x : ℝ | normalCritical < |x|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  calc
    _ = (gaussianReal (τ/s) 1).real {x : ℝ | normalCritical < |x|} :=
      hT.measureReal_eq hmeas
    _ = normalPower (τ/s) := native_power_correction_gaussian_rejection (τ/s)
    _ = normalPower |τ/s| := (native_power_correction_power_abs (τ/s)).symm
    _ = normalPower (|τ|/s) := by rw [abs_div, abs_of_pos hs]

lemma native_power_correction_smaller_SE (τ s ρ : ℝ)
    (hτ : τ ≠ 0) (hs : 0 < s) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    normalPower (|τ|/s) < normalPower (|τ|/(s*Real.sqrt ρ)) := by
  have hroot : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hroot1 : Real.sqrt ρ < 1 := by
    have hsq := Real.sq_sqrt hρ.le
    nlinarith
  have hden : 0 < s*Real.sqrt ρ := mul_pos hs hroot
  have hdenlt : s*Real.sqrt ρ < s := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hroot1 hs
  have ha : 0 < |τ| := abs_pos.mpr hτ
  have hab : |τ|/s < |τ|/(s*Real.sqrt ρ) :=
    div_lt_div_of_pos_left ha hden hdenlt
  exact native_power_correction_strictMono (div_nonneg ha.le hs.le)
    (div_nonneg ha.le hden.le) hab

theorem native_power_correction_proof :
    (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (T : Ω → ℝ) (τ s : ℝ), 0 < s → HasLaw T (gaussianReal (τ/s) 1) μ →
      μ.real {ω | normalCritical < |T ω|} = normalPower (|τ|/s)) ∧
    normalPower 0 = 1/20 ∧
    (∀ a : ℝ, 0 < a → HasDerivAt normalPower
      (normalDensity (a-normalCritical)-normalDensity (a+normalCritical)) a ∧
      0 < normalDensity (a-normalCritical)-normalDensity (a+normalCritical)) ∧
    StrictMonoOn normalPower (Ici 0) ∧
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 1/20 < normalPower a → normalPower a < 1 →
      normalPower a = normalPower b → a = b) ∧
    (∀ (α : Type*) [DecidableEq α] (L R : Finset α), L.Nonempty → R.Nonempty →
      L.card+R.card = (L ∪ R).card+(L ∩ R).card ∧
      1/2 ≤ clusterCountRatio L R ∧ clusterCountRatio L R ≤ 1 ∧
      (clusterCountRatio L R < 1 ↔ L ∩ R ≠ ∅)) ∧
    (∀ τ s ρ : ℝ, τ ≠ 0 → 0 < s → 0 < ρ → ρ < 1 →
      normalPower (|τ|/s) < normalPower (|τ|/(s*Real.sqrt ρ))) ∧
    ((57/(23+46):ℝ) = 19/23 ∧ (185/(98+101):ℝ) = 185/199 ∧
      (278/(202+226):ℝ) = 139/214 ∧ (204/(133+130):ℝ) = 204/263) ∧
    ((31/48:ℝ)-1/36 = 89/144 ∧ (113/144:ℝ)-1/36 = 109/144 ∧
      (31/48:ℝ)-1/36 = 89/144 ∧ (61/104:ℝ)-1/26 = 57/104 ∧
      (81/104:ℝ)-1/26 = 77/104 ∧ (61/104:ℝ)-1/26 = 57/104) := by
  refine ⟨?_, native_power_correction_power_zero, ?_, native_power_correction_strictMono,
    ?_, ?_, native_power_correction_smaller_SE, native_power_arithmetic.2.1, ?_⟩
  · intro Ω _ μ _ T τ s hs hT
    exact native_power_correction_hasLaw μ T τ s hs hT
  · intro a ha
    exact ⟨native_power_correction_power_deriv a, native_power_correction_deriv_pos a ha⟩
  · intro a b ha hb _ _ hab
    exact native_power_correction_strictMono.injOn ha hb hab
  · intro α _ L R hL hR
    exact cluster_count_ratio L R hL hR
  · have h := native_power_arithmetic.2.2.2
    exact ⟨h.1, h.2.1, h.1, h.2.2.1, h.2.2.2, h.2.2.1⟩

end
end AronowAudit.P033.Wave1
