import SAP.P001d.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace SAP.P001d.WH.W2.P.T61_L1

open AronowAudit.P001

lemma positive_tail_preimage (x : ℝ) (hx : 2 ≤ x) :
    Set.Icc (0 : ℝ) 1 ∩ (fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Ici x =
      Set.Ioc 0 (1 / Real.sqrt (Real.log x / Real.log 2)) := by
  let q : ℝ := Real.log x / Real.log 2
  let b : ℝ := 1 / Real.sqrt q
  have hxgt1 : 1 < x := by linarith
  have hxpos : 0 < x := lt_trans (by norm_num) hxgt1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos hxgt1
  have hlogle : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hqpos : 0 < q := by dsimp [q]; exact div_pos hlogx hlog2
  have hqge : 1 ≤ q := by
    dsimp [q]
    exact (le_div_iff₀ hlog2).2 (by simpa using hlogle)
  have hrootpos : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
  have hbpos : 0 < b := by dsimp [b]; exact one_div_pos.mpr hrootpos
  have hb_le_one : b ≤ 1 := by
    dsimp [b]
    apply (div_le_iff₀ hrootpos).2
    simpa using (Real.sqrt_le_sqrt hqge)
  have hxpow : (2 : ℝ)^q = x := by
    dsimp [q, Real.logb]
    exact Real.rpow_logb (by norm_num) (by norm_num) hxpos
  have hiff (u : ℝ) (hu : 0 < u) :
      x ≤ (2 : ℝ)^(1/u^2) ↔ u ≤ b := by
    rw [← hxpow, Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
    have hu2 : 0 < u^2 := sq_pos_of_pos hu
    constructor
    · intro h
      have hmul : q * u^2 ≤ 1 := (le_div_iff₀ hu2).mp h
      have hsquare : (u * Real.sqrt q)^2 ≤ 1 := by
        rw [mul_pow, Real.sq_sqrt hqpos.le]
        nlinarith
      have hprod : u * Real.sqrt q ≤ 1 := by
        have hnonneg : 0 ≤ u * Real.sqrt q := mul_nonneg hu.le (Real.sqrt_nonneg q)
        nlinarith
      exact (le_div_iff₀ hrootpos).2 (by simpa using hprod)
    · intro h
      have hprod : u * Real.sqrt q ≤ 1 := (le_div_iff₀ hrootpos).mp h
      have hmul : q * u^2 ≤ 1 := by
        calc
          q * u^2 = (u * Real.sqrt q)^2 := by
            rw [mul_pow, Real.sq_sqrt hqpos.le]
            ring
          _ ≤ 1 := by
            have hnonneg : 0 ≤ u * Real.sqrt q :=
              mul_nonneg hu.le (Real.sqrt_nonneg q)
            nlinarith
      exact (le_div_iff₀ hu2).2 hmul
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage, Set.mem_Ici,
    Set.mem_Ioc]
  constructor
  · rintro ⟨⟨hu0, hu1⟩, htail⟩
    by_cases huz : u = 0
    · subst u
      norm_num at htail
      linarith
    · have hu : 0 < u := lt_of_le_of_ne hu0 (Ne.symm huz)
      exact ⟨hu, (hiff u hu).mp htail⟩
  · rintro ⟨hu, hub⟩
    exact ⟨⟨hu.le, hub.trans hb_le_one⟩, (hiff u hu).mpr hub⟩

lemma positive_tail_mass (x : ℝ) (hx : 2 ≤ x) :
    ((uniformLaw 0 1).map (fun u : ℝ => (2 : ℝ)^(1/u^2))) (Set.Ici x) =
      ENNReal.ofReal (1 / Real.sqrt (Real.log x / Real.log 2)) := by
  have hmeas : Measurable (fun u : ℝ => (2 : ℝ)^(1/u^2)) :=
    AronowAudit.P001.Wave1.regular_heavy_transform_measurable
  have hset : MeasurableSet ((fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Ici x) :=
    measurableSet_Ici.preimage hmeas
  rw [Measure.map_apply hmeas measurableSet_Ici]
  calc
    (uniformLaw 0 1) ((fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Ici x) =
        (volume.restrict (Set.Icc (0 : ℝ) 1)) ((fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Ici x) :=
      congrArg (fun μ : Measure ℝ => μ ((fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Ici x))
        AronowAudit.P001.uniformLaw_zero_one_eq_restrict
    _ = volume ((fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Ici x ∩ Set.Icc (0 : ℝ) 1) :=
      Measure.restrict_apply hset
    _ = volume (Set.Icc (0 : ℝ) 1 ∩ (fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Ici x) := by
      congr 1
      exact Set.inter_comm _ _
    _ = volume (Set.Ioc 0 (1 / Real.sqrt (Real.log x / Real.log 2))) := by
      rw [positive_tail_preimage x hx]
    _ = ENNReal.ofReal (1 / Real.sqrt (Real.log x / Real.log 2)) := by
      rw [Real.volume_Ioc]
      simp

end SAP.P001d.WH.W2.P.T61_L1

theorem SAP.P001d.WH.W2.T61_L1_proof : SAP.P001d.WH.W2.T61_L1 := by
  intro x hx
  have hcentral : uniformLaw (-1) 1 (Set.Ici x) = 0 := by
    have he : Set.Ici x ∩ Set.Icc (-1 : ℝ) 1 = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc, Set.mem_empty_iff_false]
      constructor
      · rintro ⟨hy, hlow, hhigh⟩
        linarith
      · simp
    calc
      uniformLaw (-1) 1 (Set.Ici x) =
          ((1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (-1 : ℝ) 1)) (Set.Ici x) :=
        congrArg (fun μ : Measure ℝ => μ (Set.Ici x))
          AronowAudit.P001.Wave1.regular_uniform_symmetric_eq
      _ = 0 := by
        rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ici, he, measure_empty]
        simp
  have hnegative : (fun u : ℝ => -((2 : ℝ)^(1/u^2))) ⁻¹' Set.Ici x = ∅ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
    intro hu
    have hpos : 0 < (2 : ℝ)^(1/u^2) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    linarith
  have hnegmap :
      ((uniformLaw 0 1).map (fun u : ℝ => -((2 : ℝ)^(1/u^2)))) (Set.Ici x) = 0 := by
    have hm : Measurable (fun u : ℝ => -((2 : ℝ)^(1/u^2))) :=
      AronowAudit.P001.Wave1.regular_heavy_transform_measurable.neg
    rw [Measure.map_apply hm measurableSet_Ici, hnegative, measure_empty]
  have hposmap :
      ((uniformLaw 0 1).map (fun u : ℝ => (2 : ℝ)^(1/u^2))) (Set.Ici x) =
        ENNReal.ofReal (1 / Real.sqrt (Real.log x / Real.log 2)) :=
    SAP.P001d.WH.W2.P.T61_L1.positive_tail_mass x hx
  change (heavyBootstrapLaw (Set.Ici x)).toReal = _
  rw [heavyBootstrapLaw, Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
    hcentral, hposmap, hnegmap]
  simp only [smul_eq_mul, mul_zero, add_zero]
  simp [ENNReal.toReal_mul]
  <;> ring
