import AronowAudit.P053.P053_Audit
import Mathlib.Probability.CDF

/-!
Gaussian quantile facts for the P053 Wald limit.
The first three analytic lemmas are adapted from
StatLean.HypothesisTesting.Randomization.SignChange (Apache-2.0).
See NOTICE at the repository root.
-/
namespace AronowAudit.P053.NormalCompletion
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section

local instance : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1:NNReal) ≠ 0)

 theorem cdf_continuousAt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (t : ℝ) : ContinuousAt (cdf μ) t := by
  have hmono : Monotone (cdf μ) := monotone_cdf μ
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hright : Function.rightLim (cdf μ) t = cdf μ t :=
    (hmono.continuousWithinAt_Ioi_iff_rightLim_eq).1
      (((cdf μ).right_continuous t).mono Set.Ioi_subset_Ici_self)
  have hle : Function.leftLim (cdf μ) t ≤ cdf μ t := hmono.leftLim_le le_rfl
  have hge : cdf μ t ≤ Function.leftLim (cdf μ) t := by
    have h0 := (cdf μ).measure_singleton t
    rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at h0
    exact h0
  rw [le_antisymm hle hge, hright]

 theorem strictMono_normal_cdf : StrictMono (cdf (gaussianReal 0 1)) := by
  intro y z hyz
  rw [cdf_eq_real, cdf_eq_real]
  have hpos : 0 < gaussianReal 0 1 (Set.Ioc y z) := by
    rw [pos_iff_ne_zero]; intro h0
    have hvol := (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:NNReal) ≠ 0)) h0
    rw [Real.volume_Ioc] at hvol
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne' hvol
  have hdisj : gaussianReal 0 1 (Set.Iic z)
      = gaussianReal 0 1 (Set.Iic y) + gaussianReal 0 1 (Set.Ioc y z) := by
    rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hyz.le]
  rw [measureReal_def, measureReal_def, hdisj,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hp2 : 0 < (gaussianReal 0 1 (Set.Ioc y z)).toReal :=
    ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  linarith

 theorem exists_cdf_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : ∃ q, cdf μ q = p := by
  have hcont : Continuous (cdf μ) :=
    continuous_iff_continuousAt.mpr (fun x => cdf_continuousAt μ x)
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hp0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hp1)).exists
  have hab : min a b ≤ max a b := min_le_max
  have hca' : cdf μ (min a b) < p := lt_of_le_of_lt (monotone_cdf (μ := μ) (min_le_left a b)) ha
  have hcb' : p < cdf μ (max a b) := lt_of_lt_of_le hb (monotone_cdf (μ := μ) (le_max_right a b))
  obtain ⟨q, _, hq⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨hca'.le, hcb'.le⟩
  exact ⟨q, hq⟩

 theorem standardNormalCDF_eq_cdf (t : ℝ) :
    standardNormalCDF t = cdf (gaussianReal 0 1) t := by
  rw [cdf_eq_real]
  rfl

 theorem normal_cdf_neg (t : ℝ) :
    cdf (gaussianReal 0 1) (-t) = 1-cdf (gaussianReal 0 1) t := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := (0:ℝ)) (v := (1:NNReal)))
  have hreflect : gaussianReal 0 1 (Iic (-t)) = gaussianReal 0 1 (Ici t) := by
    conv_lhs => rw [← hmap, Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext x
    simp
  have hatom : gaussianReal 0 1 (Ioi t) = gaussianReal 0 1 (Ici t) :=
    measure_congr (Ioi_ae_eq_Ici' (measure_singleton t))
  have hc := measureReal_add_measureReal_compl (μ := gaussianReal 0 1)
    (s := Iic t) measurableSet_Iic
  simp only [compl_Iic, measureReal_def, measure_univ, ENNReal.toReal_one, hatom] at hc
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def, hreflect]
  linarith

 theorem normal_cdf_zero : cdf (gaussianReal 0 1) 0 = 1/2 := by
  have hh := normal_cdf_neg 0
  norm_num only [neg_zero] at hh
  linarith

 theorem normalCritical_cdf (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    standardNormalCDF (normalCritical α) = 1-α/2 := by
  obtain ⟨q,hq⟩ := exists_cdf_eq (gaussianReal 0 1)
    (p := 1-α/2) (by linarith) (by linarith)
  have hset : {t : ℝ | 1-α/2 ≤ standardNormalCDF t} = Ici q := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Ici, standardNormalCDF_eq_cdf, ← hq]
    exact strictMono_normal_cdf.le_iff_le
  have hcrit : normalCritical α = q := by rw [normalCritical,hset]; exact csInf_Ici
  rw [hcrit,standardNormalCDF_eq_cdf,hq]

 theorem normalCritical_pos (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < normalCritical α := by
  apply strictMono_normal_cdf.lt_iff_lt.mp
  rw [normal_cdf_zero, ← standardNormalCDF_eq_cdf, normalCritical_cdf α hα hα1]
  linarith

 theorem normalCritical_interval_mass (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    (gaussianReal 0 1 (Icc (-normalCritical α) (normalCritical α))).toReal = 1-α := by
  have hcont : ContinuousWithinAt (cdf (gaussianReal 0 1))
      (Iic (-normalCritical α)) (-normalCritical α) :=
    (cdf_continuousAt (gaussianReal 0 1) (-normalCritical α)).continuousWithinAt
  have hnonneg : 0 ≤ cdf (gaussianReal 0 1) (normalCritical α)-
      cdf (gaussianReal 0 1) (-normalCritical α) :=
    sub_nonneg.mpr ((monotone_cdf (μ := gaussianReal 0 1))
      (by linarith [normalCritical_pos α hα hα1]))
  have hmass : gaussianReal 0 1 (Icc (-normalCritical α) (normalCritical α)) =
      ENNReal.ofReal (cdf (gaussianReal 0 1) (normalCritical α)-
        cdf (gaussianReal 0 1) (-normalCritical α)) := by
    calc
      _ = (cdf (gaussianReal 0 1)).measure (Icc (-normalCritical α) (normalCritical α)) := by
        rw [measure_cdf]
      _ = _ := by rw [StieltjesFunction.measure_Icc,hcont.leftLim_eq]
  rw [hmass, ENNReal.toReal_ofReal hnonneg, normal_cdf_neg,
    ← standardNormalCDF_eq_cdf, normalCritical_cdf α hα hα1]
  ring

end
end AronowAudit.P053.NormalCompletion
