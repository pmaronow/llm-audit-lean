import SAP.P001d.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace SAP.P001d.WH.W2.P.T61_L2

private theorem uniformLaw_eq (a b : ℝ) :
    SAP.P001d.uniformLaw a b = AronowAudit.P001.uniformLaw a b := rfl

private theorem cdf_heavy_at_neg_one : cdf heavyBootstrapLaw id (-1) = 1/4 := by
  rw [SAP.P001d.Bridge.heavyBootstrapLaw_eq]
  change (AronowAudit.P001.heavyBootstrapLaw (Set.Iic (-1))).toReal = 1/4
  have hu : AronowAudit.P001.uniformLaw (-1) 1 (Set.Iic (-1 : ℝ)) = 0 := by
    rw [AronowAudit.P001.Wave1.regular_uniform_symmetric_eq,
      Measure.smul_apply, Measure.restrict_apply measurableSet_Iic]
    have he : Set.Iic (-1 : ℝ) ∩ Set.Icc (-1 : ℝ) 1 = ({-1} : Set ℝ) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hy, hleft, _⟩
        have : y = -1 := le_antisymm hy hleft
        exact this
      · intro hy
        subst y
        constructor <;> norm_num
    rw [he]
    simp [smul_eq_mul]
  have hpositive : (fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Iic (-1 : ℝ) = ∅ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    exact not_le_of_gt (by
      have h := AronowAudit.P001.Wave1.TailA.heavyMedian_transform_lower u
      linarith)
  have hnegative : (fun u : ℝ => -((2 : ℝ)^(1/u^2))) ⁻¹' Set.Iic (-1 : ℝ) = Set.univ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
    have h := AronowAudit.P001.Wave1.TailA.heavyMedian_transform_lower u
    linarith
  change (AronowAudit.P001.heavyBootstrapLaw (Set.Iic (-1))).toReal = 1/4
  rw [AronowAudit.P001.heavyBootstrapLaw, Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply AronowAudit.P001.Wave1.regular_heavy_transform_measurable
      measurableSet_Iic,
    Measure.map_apply
      (show Measurable (fun u : ℝ => -((2 : ℝ)^(1/u^2))) from
        AronowAudit.P001.Wave1.regular_heavy_transform_measurable.neg)
      measurableSet_Iic,
    hpositive, hnegative, measure_empty, AronowAudit.P001.Wave1.regular_uniform_zero_one_mass, hu]
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

private theorem cdf_heavy_at_one : cdf heavyBootstrapLaw id 1 = 3/4 := by
  rw [SAP.P001d.Bridge.heavyBootstrapLaw_eq]
  change (AronowAudit.P001.heavyBootstrapLaw (Set.Iic 1)).toReal = 3/4
  have hu : AronowAudit.P001.uniformLaw (-1) 1 (Set.Iic (1 : ℝ)) = 1 := by
    rw [AronowAudit.P001.Wave1.regular_uniform_symmetric_eq,
      Measure.smul_apply, Measure.restrict_apply measurableSet_Iic]
    have he : Set.Iic (1 : ℝ) ∩ Set.Icc (-1 : ℝ) 1 = Set.Icc (-1 : ℝ) 1 := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨_, hleft, hright⟩
        exact ⟨hleft, hright⟩
      · rintro ⟨hleft, hright⟩
        exact ⟨hright, hleft, hright⟩
    rw [he]
    norm_num [Real.volume_Icc, ENNReal.inv_mul_cancel]
  have hpositive : (fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Iic (1 : ℝ) = ({0} : Set ℝ) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hu
      have hsquare : 0 < u^2 := sq_pos_of_ne_zero hu
      have hexp : 0 < 1/u^2 := one_div_pos.mpr hsquare
      have hpow : 1 < (2 : ℝ)^(1/u^2) := Real.one_lt_rpow (by norm_num) hexp
      linarith
    · intro hu
      subst u
      norm_num
  have hnegative : (fun u : ℝ => -((2 : ℝ)^(1/u^2))) ⁻¹' Set.Iic (1 : ℝ) = Set.univ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
    have h := AronowAudit.P001.Wave1.TailA.heavyMedian_transform_lower u
    linarith
  have hzero : AronowAudit.P001.uniformLaw 0 1 ({0} : Set ℝ) = 0 := by
    rw [AronowAudit.P001.uniformLaw_zero_one_eq_restrict,
      Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    simp
  change (AronowAudit.P001.heavyBootstrapLaw (Set.Iic 1)).toReal = 3/4
  rw [AronowAudit.P001.heavyBootstrapLaw, Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply AronowAudit.P001.Wave1.regular_heavy_transform_measurable
      measurableSet_Iic,
    Measure.map_apply
      (show Measurable (fun u : ℝ => -((2 : ℝ)^(1/u^2))) from
        AronowAudit.P001.Wave1.regular_heavy_transform_measurable.neg)
      measurableSet_Iic,
    hpositive, hnegative, hzero, AronowAudit.P001.Wave1.regular_uniform_zero_one_mass, hu]
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

end SAP.P001d.WH.W2.P.T61_L2

theorem SAP.P001d.WH.W2.T61_L2_proof : SAP.P001d.WH.W2.T61_L2 := by
  exact ⟨SAP.P001d.WH.W2.P.T61_L2.cdf_heavy_at_neg_one,
    SAP.P001d.WH.W2.P.T61_L2.cdf_heavy_at_one⟩
