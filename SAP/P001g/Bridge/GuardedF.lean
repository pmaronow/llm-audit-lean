import SAP.P001g.Defs
import AronowAudit.P001.Wave1.Gap.PlaceboFTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g.Bridge

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem placeboX_eq : SAP.P001g.placeboX = AronowAudit.P001.placeboX := rfl
theorem placeboZ_eq : SAP.P001g.placeboZ = AronowAudit.P001.placeboZ := rfl
theorem placeboD_eq : SAP.P001g.placeboD = AronowAudit.P001.placeboD := rfl
theorem placeboW_eq : SAP.P001g.placeboW = AronowAudit.P001.placeboW := rfl
theorem placeboRegressor_eq : SAP.P001g.placeboRegressor = AronowAudit.P001.placeboRegressor := rfl
theorem placeboGram_eq : @SAP.P001g.placeboFTest_gram =
    @AronowAudit.P001.Wave1.placeboFTest_gram := rfl
theorem placeboCross_eq : @SAP.P001g.placeboFTest_cross =
    @AronowAudit.P001.Wave1.placeboFTest_cross := rfl
theorem placeboCoef_eq : @SAP.P001g.placeboFTest_coef =
    @AronowAudit.P001.Wave1.placeboFTest_coef := rfl
theorem placeboRisk_eq : @SAP.P001g.placeboFTest_risk =
    @AronowAudit.P001.Wave1.placeboFTest_risk := rfl
theorem placeboRestricted_eq : SAP.P001g.placeboFTest_restricted =
    AronowAudit.P001.Wave1.placeboFTest_restricted := rfl

theorem placeboFrequency_eq {Ω : Type*} (Z : ℕ → Ω → Fin 12) (n : ℕ) (ω : Ω) :
    placeboFrequency (firstSample Z n ω) =
      AronowAudit.P001.Wave1.placeboFTest_frequency Z n ω := by
  ext j
  exact congrArg (fun x : ℝ => x / (n : ℝ))
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => if Z i ω = j then (1 : ℝ) else 0) n)

/-- The validity guard ensures ordinary invertible OLS matrices and positive
RSS and degrees of freedom, by the source's exact sample identities. -/
theorem placeboGood_ols_valid {Ω : Type*} (Z : ℕ → Ω → Fin 12) (n : ℕ) (ω : Ω)
    (hg : placeboGood (firstSample Z n ω)) :
    let R : Matrix (Fin n) (Fin 2) ℝ := fun i => placeboFTest_restricted (Z i.val ω)
    let F : Matrix (Fin n) (Fin 3) ℝ := fun i => placeboRegressor (Z i.val ω)
    let D : Fin n → ℝ := fun i => placeboD (Z i.val ω)
    IsUnit (R.transpose * R).det ∧ IsUnit (F.transpose * F).det ∧
      0 < olsRSS F D (olsCoef F D) ∧ 0 < (n : ℝ) - 3 := by
  obtain ⟨hn, hr, hf, hp⟩ := hg
  rw [placeboFrequency_eq] at hr hf hp
  have hnR : (3 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  dsimp only
  refine ⟨?_, ?_, ?_, by linarith⟩
  · have he := AronowAudit.P001.Wave1.placeboFTest_sample_gram Z
      AronowAudit.P001.Wave1.placeboFTest_restricted n hn0 ω
    apply (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => IsUnit M.det) he).mpr
    rw [Matrix.det_smul]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hn0) hr)
  · have he := AronowAudit.P001.Wave1.placeboFTest_sample_gram Z
      AronowAudit.P001.placeboRegressor n hn0 ω
    apply (congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => IsUnit M.det) he).mpr
    rw [Matrix.det_smul]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hn0) hf)
  · have he := AronowAudit.P001.Wave1.placeboFTest_sample_rss Z
      AronowAudit.P001.placeboRegressor n hn0 ω (isUnit_iff_ne_zero.mpr hf)
    exact (congrArg (fun x : ℝ => 0 < x) he).mpr (mul_pos (by linarith) hp)

/-- This is continuity transport of the source's empirical frequency limit
through its existing Gram and residual-risk maps. -/
theorem placebo_eventually_good {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
    (hiid : AronowAudit.P001.IID μ Z)
    (hlaw : μ.map (Z 0) = AronowAudit.P001.finiteLawMeasure AronowAudit.P001.placeboLaw) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, placeboGood (firstSample Z n ω) := by
  have hR : (AronowAudit.P001.Wave1.placeboFTest_gram
      AronowAudit.P001.Wave1.placeboFTest_restricted AronowAudit.P001.placeboLaw.weight).det ≠ 0 := by
    rw [AronowAudit.P001.Wave1.placeboFTest_determinants.1]
    norm_num
  have hF : (AronowAudit.P001.Wave1.placeboFTest_gram
      AronowAudit.P001.placeboRegressor AronowAudit.P001.placeboLaw.weight).det ≠ 0 := by
    rw [AronowAudit.P001.Wave1.placeboFTest_determinants.2]
    norm_num
  filter_upwards [AronowAudit.P001.Wave1.placeboFTest_frequency_limit μ Z hiid hlaw] with ω hω
  have hRd := ((AronowAudit.P001.Wave1.placeboFTest_gram_continuous
    AronowAudit.P001.Wave1.placeboFTest_restricted).matrix_det.tendsto
      AronowAudit.P001.placeboLaw.weight).comp hω
  have hFd := ((AronowAudit.P001.Wave1.placeboFTest_gram_continuous
    AronowAudit.P001.placeboRegressor).matrix_det.tendsto
      AronowAudit.P001.placeboLaw.weight).comp hω
  have hrf := (AronowAudit.P001.Wave1.placeboFTest_risk_continuousAt
    AronowAudit.P001.placeboRegressor _ hF).tendsto.comp hω
  rw [AronowAudit.P001.Wave1.placeboFTest_population_risks.2] at hrf
  filter_upwards [eventually_gt_atTop (3 : ℕ),
    hRd.eventually (eventually_ne_nhds hR), hFd.eventually (eventually_ne_nhds hF),
    hrf.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 59 / 272))] with n hn hr hf hp
  unfold placeboGood
  rw [placeboFrequency_eq]
  exact ⟨hn, hr, hf, hp⟩

/-- A finite-table adapter applies the source's general rejection theorem to
the rejection margin, taking value negative one off the valid-data event. -/
theorem placebo_guarded_rejection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
    (hiid : AronowAudit.P001.IID μ Z)
    (hlaw : μ.map (Z 0) = AronowAudit.P001.finiteLawMeasure AronowAudit.P001.placeboLaw)
    (critical : ℕ → ℝ) (C : ℝ) (hc : ∀ᶠ n in atTop, critical n ≤ C) :
    Tendsto (fun n => prob μ {ω | placeboGood (firstSample Z n ω) ∧
      critical n < placeboF (firstSample Z n ω)}) atTop (nhds 1) := by
  let margin (n : ℕ) (s : Fin n → Fin 12) : ℝ :=
    if placeboGood s then placeboF s - critical n else -1
  let T (n : ℕ) (ω : Ω) : ℝ := margin n (firstSample Z n ω)
  have hT (n : ℕ) : Measurable (T n) :=
    (measurable_of_finite (margin n)).comp
      (measurable_pi_lambda (fun i : Fin n => hiid.1 i.val))
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => T n ω) atTop atTop := by
    filter_upwards [placebo_eventually_good μ Z hiid hlaw,
      AronowAudit.P001.Wave1.placeboFTest_sampleF_limit μ Z hiid hlaw] with ω hg hf
    have hdiv := AronowAudit.P001.Wave1.placeboFTest_divergence
      (by norm_num : (0 : ℝ) < 64 / 531) hf
    have hsub : Tendsto (fun n => AronowAudit.P001.placeboSampleF Z n ω - C)
        atTop atTop := by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-C) hdiv
    apply tendsto_atTop_mono' atTop _ hsub
    filter_upwards [hg, hc] with n hn hnC
    change AronowAudit.P001.placeboSampleF Z n ω - C ≤
      (if placeboGood (firstSample Z n ω) then
        placeboF (firstSample Z n ω) - critical n else -1)
    rw [if_pos hn]
    change placeboF (firstSample Z n ω) - C ≤
      placeboF (firstSample Z n ω) - critical n
    linarith
  have h := AronowAudit.P001.Wave1.placeboFTest_reject_of_divergence μ T hT hlim
    (fun _ => 0) 0 (Eventually.of_forall fun _ => le_rfl)
  have he (n : ℕ) : {ω | (0 : ℝ) < T n ω} =
      {ω | placeboGood (firstSample Z n ω) ∧ critical n < placeboF (firstSample Z n ω)} := by
    ext ω
    simp only [T, margin, Set.mem_setOf_eq]
    split_ifs with hg <;> simp [hg, sub_pos]
  change Tendsto (fun n => AronowAudit.P001.prob μ
    {ω | placeboGood (firstSample Z n ω) ∧ critical n < placeboF (firstSample Z n ω)})
    atTop (nhds 1)
  simpa only [he] using h

theorem t124 : SAP.P001g.T124Statement := by
  let μ := AronowAudit.P001.Wave1.placeboFTest_sampleSpace
  let Z : ℕ → (ℕ → Fin 12) → Fin 12 := fun i ω => ω i
  let critical : ℕ → ℝ := fun n => if hn : 3 < n then
    (AronowAudit.P001.Wave1.placeboFTest_reference_quantile (n - 3) (by omega)).choose else 0
  have hiid : AronowAudit.P001.IID μ Z := AronowAudit.P001.Wave1.placeboFTest_sampleSpace_iid
  have hlaw : μ.map (Z 0) = AronowAudit.P001.finiteLawMeasure AronowAudit.P001.placeboLaw :=
    AronowAudit.P001.Wave1.placeboFTest_sampleSpace_law
  have hX : Measurable (fun ω : ℕ → Fin 12 => fun _ : Fin 1 => placeboX (ω 0)) :=
    (measurable_of_finite (fun j => fun _ : Fin 1 => placeboX j)).comp (hiid.1 0)
  have hcritical : ∀ n : ℕ, 3 < n →
      prob (fReference 1 (n - 3)) (Set.Iic (critical n)) = 1 / 2 := by
    intro n hn
    change AronowAudit.P001.prob (AronowAudit.P001.fReference 1 (n - 3))
      (Set.Iic (critical n)) = 1 / 2
    simpa only [critical, dif_pos hn] using
      (AronowAudit.P001.Wave1.placeboFTest_reference_quantile (n - 3) (by omega)).choose_spec
  refine ⟨μ, critical, inferInstance,
    AronowAudit.P001.Wave1.placeboFTest_vector_iid μ Z hiid,
    ⟨hX, AronowAudit.P001.Wave1.placeboFTest_CI_lift μ (Z 0) (hiid.1 0) hlaw⟩,
    ?_, placebo_eventually_good μ Z hiid hlaw, hcritical, ?_⟩
  · intro i ω
    generalize ω i = j
    fin_cases j <;> norm_num [placeboD]
  · have hcritical' : ∀ n : ℕ, 3 < n →
        AronowAudit.P001.prob (AronowAudit.P001.fReference 1 (n - 3))
          (Set.Iic (critical n)) = 1 - (1 / 2 : ℝ) := by
      intro n hn
      change prob (fReference 1 (n - 3)) (Set.Iic (critical n)) = 1 - (1 / 2 : ℝ)
      simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using hcritical n hn
    obtain ⟨C, hc⟩ := AronowAudit.P001.Wave1.placeboFTest_critical_bounded
      (1 / 2) (by norm_num) critical hcritical'
    exact placebo_guarded_rejection μ Z hiid hlaw critical C hc

end
end SAP.P001g.Bridge
