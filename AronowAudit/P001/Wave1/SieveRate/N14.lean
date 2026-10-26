import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
On the two intervals
`[-2 sqrt(v), -sqrt(v)]` and `[sqrt(v), 2 sqrt(v)]`, the Gaussian density is at
least `1 / (24 sqrt(v))`.  Their total length is `2 sqrt(v)`.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n14_proof : N14 := by
  classical
  intro v hv
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hvne : v ≠ 0 := ne_of_gt hv
  let r : ℝ := Real.sqrt (v : ℝ)
  have hr : 0 < r := Real.sqrt_pos.2 hvR
  have hrne : r ≠ 0 := ne_of_gt hr
  have hr2 : r ^ 2 = (v : ℝ) := Real.sq_sqrt hvR.le
  let J : Set ℝ := Set.Icc (-2 * r) (-r) ∪ Set.Icc r (2 * r)
  have hdisj : Disjoint (Set.Icc (-2 * r) (-r)) (Set.Icc r (2 * r)) := by
    apply Set.disjoint_left.2
    intro z hzL hzR
    linarith [hzL.2, hzR.1]
  have hJmeas : MeasurableSet J := measurableSet_Icc.union measurableSet_Icc
  have hJfinite : volume J ≠ ∞ := by
    exact ((measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.2 ⟨measure_Icc_lt_top, measure_Icc_lt_top⟩)).ne
  have hvolume : volume.real J = 2 * r := by
    change volume.real (Set.Icc (-2 * r) (-r) ∪ Set.Icc r (2 * r)) = 2 * r
    rw [measureReal_union hdisj measurableSet_Icc measure_Icc_lt_top.ne
        measure_Icc_lt_top.ne,
      Real.volume_real_Icc_of_le (by linarith),
      Real.volume_real_Icc_of_le (by linarith)]
    ring
  have he1 : Real.exp 1 ≤ (11 / 4 : ℝ) := by
    exact le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
  have he2 : Real.exp 2 ≤ (8 : ℝ) := by
    calc
      Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      _ ≤ (11 / 4 : ℝ) * (11 / 4 : ℝ) := by
        exact mul_le_mul he1 he1 (Real.exp_pos 1).le (by norm_num)
      _ ≤ 8 := by norm_num
  have he_neg2 : (1 / 8 : ℝ) ≤ Real.exp (-2) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos 2) he2
  have hnormpos : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) :=
    Real.sqrt_pos.2 (by positivity)
  have hnormle : Real.sqrt (2 * Real.pi * (v : ℝ)) ≤ 3 * r := by
    have hpi : 2 * Real.pi ≤ (9 : ℝ) := by linarith [Real.pi_lt_four]
    have hm := mul_le_mul_of_nonneg_right hpi hvR.le
    apply Real.sqrt_le_iff.2
    constructor
    · positivity
    · nlinarith [hr2]
  have hnorm : 1 / (3 * r) ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hnormpos hnormle
  have hdensity : ∀ z ∈ J, 1 / (24 * r) ≤ gaussianPDFReal 0 v z := by
    intro z hz
    have habs : |z| ≤ 2 * r := by
      apply abs_le.2
      rcases hz with hz | hz <;> constructor <;> linarith [hz.1, hz.2]
    have hsq_abs : |z| ^ 2 ≤ (2 * r) ^ 2 := by gcongr
    have hsq : z ^ 2 ≤ 4 * (v : ℝ) := by
      nlinarith [sq_abs z, hr2]
    have harg : (-2 : ℝ) ≤ -z ^ 2 / (2 * (v : ℝ)) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (v : ℝ))).2
      linarith
    have hexp : (1 / 8 : ℝ) ≤ Real.exp (-z ^ 2 / (2 * (v : ℝ))) :=
      he_neg2.trans (Real.exp_le_exp.2 harg)
    rw [gaussianPDFReal, sub_zero]
    calc
      1 / (24 * r) = (1 / (3 * r)) * (1 / 8) := by
        field_simp [hrne]
        <;> ring
      _ ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          Real.exp (-z ^ 2 / (2 * (v : ℝ))) :=
        mul_le_mul hnorm hexp (by norm_num) (by positivity)
  have htail : J ⊆ {z : ℝ | (v : ℝ) / 2 < z ^ 2} := by
    intro z hz
    have hsq : (v : ℝ) ≤ z ^ 2 := by
      rcases hz with hz | hz
      · have hle : r ≤ -z := by linarith [hz.2]
        have hpow : r ^ 2 ≤ (-z) ^ 2 := by gcongr
        nlinarith [hr2]
      · have hle : r ≤ z := hz.1
        have hpow : r ^ 2 ≤ z ^ 2 := by gcongr
        nlinarith [hr2]
    change (v : ℝ) / 2 < z ^ 2
    linarith
  have hJint : IntegrableOn (gaussianPDFReal 0 v) J :=
    (integrable_gaussianPDFReal 0 v).integrableOn
  have hlower : volume.real J * (1 / (24 * r)) ≤
      ∫ z in J, gaussianPDFReal 0 v z := by
    simpa only [smul_eq_mul] using
      (setIntegral_ge_of_const_le (μ := volume) (s := J)
        hJmeas hJfinite hdensity hJint)
  have hmass : ((gaussianReal 0 v) J).toReal = ∫ z in J, gaussianPDFReal 0 v z := by
    rw [gaussianReal_apply 0 hvne J]
    symm
    simpa only [toReal_gaussianPDF] using
      (integral_toReal (μ := volume.restrict J)
        (measurable_gaussianPDF 0 v).aemeasurable
        (Filter.Eventually.of_forall (fun z => gaussianPDF_lt_top (μ := 0) (v := v) (x := z))))
  have hconst : volume.real J * (1 / (24 * r)) = (1 / 12 : ℝ) := by
    rw [hvolume]
    field_simp [hrne]
    <;> ring
  calc
    (1 : ℝ) / 12 = volume.real J * (1 / (24 * r)) := hconst.symm
    _ ≤ ∫ z in J, gaussianPDFReal 0 v z := hlower
    _ = ((gaussianReal 0 v) J).toReal := hmass.symm
    _ ≤ ((gaussianReal 0 v) {z : ℝ | (v : ℝ) / 2 < z ^ 2}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono htail)

end

end AronowAudit.P001.Wave1.SieveRate
