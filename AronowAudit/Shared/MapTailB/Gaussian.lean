import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.ChiSquared
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi

/-! Gaussian small-ball bounds and the exact two-dimensional unit-disk mass. -/

set_option autoImplicit false

namespace AronowAudit.Shared.MapTailB

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem TailB_gaussian_small_ball (v : ℝ≥0) (hv : 0 < v)
    (r : ℝ) (hr : 0 ≤ r) :
    ((gaussianReal 0 v) (Set.Icc (-r) r)).toReal ≤
      2 * r / Real.sqrt (2 * Real.pi * (v : ℝ)) := by
  rw [gaussianReal_apply_eq_integral 0 (ne_of_gt hv),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
      (fun x _ => gaussianPDFReal_nonneg 0 v x))]
  calc
    (∫ x in Set.Icc (-r) r, gaussianPDFReal 0 v x) ≤
        ∫ _ in Set.Icc (-r) r, (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
      apply setIntegral_mono_on (integrable_gaussianPDFReal 0 v).integrableOn
        (integrableOn_const (by simp)) measurableSet_Icc
      intro x _
      unfold gaussianPDFReal
      have he : Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
        apply Real.exp_le_one_iff.2
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _))
          (by positivity)
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left he (by positivity :
          0 ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹)
    _ = 2 * r / Real.sqrt (2 * Real.pi * (v : ℝ)) := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith)]
      simp only [smul_eq_mul, div_eq_mul_inv]
      ring

theorem TailB_gaussian_disk :
    let G := (gaussianReal 0 1).prod (gaussianReal 0 1)
    (G {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < 1}).toReal = 1 - Real.exp (-1/2) ∧
    G {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 = 1} = 0 := by
  let P : Measure (Fin 2 → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let G := (gaussianReal 0 1).prod (gaussianReal 0 1)
  let q : ℝ × ℝ → ℝ := fun z => z.1 ^ 2 + z.2 ^ 2
  have hq : Measurable q := by fun_prop
  have hsum : P.map (fun z => ∑ i : Fin 2, z i ^ 2) =
      StatLean.MultipleTesting.chiSquared 2 := by
    apply StatLean.MultipleTesting.map_sum_sq_eq_chiSquared (by norm_num) P
      (fun i z => z i) (fun i => measurable_pi_apply i)
    · intro i
      exact (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) i).map_eq
    · exact iIndepFun_pi (fun _ : Fin 2 => aemeasurable_id)
  have hlaw : G.map q = expMeasure (1 / 2) := by
    have hsplit := (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
    change P.map MeasurableEquiv.finTwoArrow = G at hsplit
    rw [← hsplit, Measure.map_map hq MeasurableEquiv.finTwoArrow.measurable]
    have hfun : q ∘ (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → ℝ × ℝ) =
        (fun z => ∑ i : Fin 2, z i ^ 2) := by
      funext z
      simp [q, Fin.sum_univ_two, MeasurableEquiv.finTwoArrow]
    rw [hfun, hsum]
    norm_num [StatLean.MultipleTesting.chiSquared, expMeasure]
  haveI : IsProbabilityMeasure (expMeasure ((1 : ℝ) / 2)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  haveI : NullSingletonClass (expMeasure ((1 : ℝ) / 2)) := by
    unfold expMeasure gammaMeasure
    infer_instance
  change (G {z | q z < 1}).toReal = _ ∧ G {z | q z = 1} = 0
  constructor
  · have hmass : G {z | q z < 1} = (expMeasure (1 / 2)) (Set.Iic 1) := by
      rw [← measure_congr (Iio_ae_eq_Iic (μ := expMeasure ((1 : ℝ) / 2)))]
      rw [← hlaw, Measure.map_apply hq measurableSet_Iio]
      rfl
    rw [hmass]
    have hc := cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1 / 2) 1
    rw [cdf_eq_real] at hc
    simpa only [measureReal_def, if_pos zero_le_one, mul_one, neg_div] using hc
  · have hmass : G {z | q z = 1} = (expMeasure (1 / 2)) {1} := by
      rw [← hlaw, Measure.map_apply hq (measurableSet_singleton 1)]
      rfl
    rw [hmass, measure_singleton]

end AronowAudit.Shared.MapTailB
