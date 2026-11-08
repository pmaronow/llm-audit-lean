import SAP.P006a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace SAP.P006a.WH.W2.P.T8_L2
noncomputable section

lemma bit_measurable {Ω : Type} [MeasurableSpace Ω] (T : Ω → Bool)
    (hT : Measurable T) : Measurable (fun ω => bit (T ω)) :=
  (measurable_of_finite bit).comp hT

lemma bit_integrable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (T : Ω → Bool) (hT : Measurable T) :
    Integrable (fun ω => bit (T ω)) μ := by
  have hnorm : ∀ᵐ ω ∂μ, ‖bit (T ω)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    cases T ω <;> norm_num [bit]
  exact (integrable_const (1 : ℝ)).mono'
    (bit_measurable T hT).aestronglyMeasurable hnorm

lemma integrable_of_measurable_bounded {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfb : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1) : Integrable f μ := by
  have hnorm : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hfb ω).1]
    exact (hfb ω).2
  exact (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable hnorm

lemma setIntegral_restrict_eq_bit {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} (T : Ω → Bool) (hT : Measurable T)
    (s : Set Ω) (hs : MeasurableSet s) (f : Ω → ℝ) :
    (∫ ω in s, f ω ∂ μ.restrict {ω | T ω = true}) =
      ∫ ω in s, bit (T ω) * f ω ∂ μ := by
  let A : Set Ω := {ω | T ω = true}
  have hA : MeasurableSet A := hT (MeasurableSet.singleton true)
  calc
    (∫ ω in s, f ω ∂ μ.restrict A) = ∫ ω in s ∩ A, f ω ∂ μ := by
      rw [Measure.restrict_restrict hs]
    _ = ∫ ω in s, A.indicator f ω ∂ μ := (setIntegral_indicator hA).symm
    _ = ∫ ω in s, bit (T ω) * f ω ∂ μ := by
      apply setIntegral_congr_fun hs
      intro ω _
      cases T ω <;> simp [A, bit, Set.indicator]

lemma residual_setIntegral_eq {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} (T : Ω → Bool) (hT : Measurable T)
    (s : Set Ω) (hs : MeasurableSet s) (H a : Ω → ℝ)
    (hbitH : Integrable (fun ω => bit (T ω) * H ω) μ)
    (hbita : Integrable (fun ω => bit (T ω) * a ω) μ) :
    (∫ ω in s, bit (T ω) * (H ω - a ω) ∂ μ) =
      (∫ ω in s, H ω ∂ μ.restrict {ω | T ω = true}) -
        (∫ ω in s, a ω ∂ μ.restrict {ω | T ω = true}) := by
  have hsplit : (fun ω => bit (T ω) * (H ω - a ω)) =
      fun ω => bit (T ω) * H ω - bit (T ω) * a ω := by
    funext ω
    ring
  calc
    _ = ∫ ω in s, bit (T ω) * H ω - bit (T ω) * a ω ∂ μ := by rw [hsplit]
    _ = (∫ ω in s, bit (T ω) * H ω ∂ μ) -
        (∫ ω in s, bit (T ω) * a ω ∂ μ) :=
      integral_sub hbitH.integrableOn hbita.integrableOn
    _ = _ := by
      rw [← setIntegral_restrict_eq_bit T hT s hs H,
        ← setIntegral_restrict_eq_bit T hT s hs a]

lemma treatedMeasure_setIntegral {Ω : Type} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (m : MeasurableSpace Ω)
    (hm : m ≤ mΩ) (T : Ω → Bool) (p : Ω → ℝ)
    (hT : Measurable[m] T) (hp : Measurable[m] p)
    (hpb : ∀ ω, 0 ≤ p ω ∧ p ω ≤ 1)
    (hcoin : μ[(fun ω => bit (T ω)) | m] =ᵐ[μ] p)
    (s : Set Ω) (hs : MeasurableSet[m] s) :
    (μ.restrict {ω | T ω = true}).real s = ∫ ω in s, p ω ∂ μ := by
  letI : MeasurableSpace Ω := mΩ
  let A : Set Ω := {ω | T ω = true}
  have hTΩ : Measurable T := hT.mono hm le_rfl
  have hA : MeasurableSet A := hTΩ (MeasurableSet.singleton true)
  have hsΩ : MeasurableSet s := hm s hs
  have hbit : Integrable (fun ω => bit (T ω)) μ := bit_integrable (μ := μ) T hTΩ
  have hpμ : Measurable p := hp.mono hm le_rfl
  have hpint : Integrable p μ := integrable_of_measurable_bounded p hpμ hpb
  have hindicator : (s ∩ A).indicator (fun _ : Ω => (1 : ℝ)) =
      s.indicator (fun ω => bit (T ω)) := by
    funext ω
    by_cases hsω : ω ∈ s <;> cases T ω <;> simp [A, Set.indicator, hsω, bit]
  calc
    (μ.restrict A).real s = μ.real (s ∩ A) := by
      simp [Measure.real_def, Measure.restrict_apply hsΩ]
    _ = ∫ ω, (s ∩ A).indicator (fun _ : Ω => (1 : ℝ)) ω ∂ μ :=
      (integral_indicator_one (μ := μ) (hsΩ.inter hA)).symm
    _ = ∫ ω in s, bit (T ω) ∂ μ := by
      calc
        _ = ∫ ω, s.indicator (fun ω => bit (T ω)) ω ∂ μ := by rw [hindicator]
        _ = _ := integral_indicator hsΩ
    _ = ∫ ω in s, μ[(fun η => bit (T η)) | m] ω ∂ μ :=
      (setIntegral_condExp hm hbit hs).symm
    _ = ∫ ω in s, p ω ∂ μ := by
      apply integral_congr_ae
      exact ae_restrict_of_ae hcoin

lemma treatedNull_iff {Ω : Type} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (m : MeasurableSpace Ω)
    (hm : m ≤ mΩ) (T : Ω → Bool) (p : Ω → ℝ)
    (hT : Measurable[m] T) (hp : Measurable[m] p)
    (hpb : ∀ ω, 0 ≤ p ω ∧ p ω ≤ 1)
    (hcoin : μ[(fun ω => bit (T ω)) | m] =ᵐ[μ] p)
    (s : Set Ω) (hs : MeasurableSet[m] s) :
    (μ.restrict {ω | T ω = true}) s = 0 ↔
      ∀ᵐ ω ∂μ, ω ∈ s → p ω = 0 := by
  letI : MeasurableSpace Ω := mΩ
  let ν : Measure Ω := μ.restrict {ω | T ω = true}
  have hmeasure := treatedMeasure_setIntegral (mΩ := mΩ) (μ := μ)
    m hm T p hT hp hpb hcoin s hs
  have hpμ : Measurable p := hp.mono hm le_rfl
  have hsΩ : MeasurableSet s := hm s hs
  have hpint : Integrable p μ := integrable_of_measurable_bounded p hpμ hpb
  have hpintS : Integrable p (μ.restrict s) := hpint.mono_measure Measure.restrict_le_self
  have hpnonneg : 0 ≤ᵐ[μ.restrict s] p := Eventually.of_forall (fun ω => (hpb ω).1)
  have hzeroIntegral : (∫ ω in s, p ω ∂ μ) = 0 ↔
      ∀ᵐ ω ∂μ, ω ∈ s → p ω = 0 := by
    rw [integral_eq_zero_iff_of_nonneg_ae hpnonneg hpintS]
    rw [Filter.EventuallyEq, ae_restrict_iff' hsΩ]
    simp only [Pi.zero_apply]
  constructor
  · intro hνs
    have hreal : ν.real s = 0 := by simp [Measure.real_def, ν, hνs]
    exact hzeroIntegral.mp (hmeasure.symm ▸ hreal)
  · intro hμs
    have hreal : ν.real s = 0 := hmeasure.trans (hzeroIntegral.mpr hμs)
    have htoReal : (ν s).toReal = 0 := by simpa only [Measure.real_def] using hreal
    rcases (ENNReal.toReal_eq_zero_iff (ν s)).mp htoReal with hzero | htop
    · exact hzero
    · exact (measure_ne_top ν s htop).elim

lemma nullOnSet_iff_pos {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    (p : Ω → ℝ) (hpb : ∀ ω, 0 ≤ p ω) (s : Set Ω) :
    (∀ᵐ ω ∂μ, ω ∈ s → p ω = 0) ↔
      ∀ᵐ ω ∂μ, 0 < p ω → ω ∉ s := by
  constructor
  · intro h
    filter_upwards [h] with ω hω
    intro hpω hsω
    exact (ne_of_gt hpω) (hω hsω)
  · intro h
    filter_upwards [h] with ω hω
    intro hsω
    rcases eq_or_lt_of_le (hpb ω) with hp0 | hp0
    · exact hp0.symm
    · exact False.elim (hω hp0 hsω)

end
end SAP.P006a.WH.W2.P.T8_L2

open SAP.P006a.WH.W2.P.T8_L2

theorem SAP.P006a.WH.W2.T8_L2_proof : SAP.P006a.WH.W2.T8_L2 := by
  classical
  unfold SAP.P006a.WH.W2.T8_L2 SAP.P006a.SelectedEquivalenceW2
  intro Ω mΩ μ hμ m hm T H a p hT hH ha hai hp hpb hcoin hR
  letI : MeasurableSpace Ω := mΩ
  let A : Set Ω := {ω | T ω = true}
  let ν : Measure Ω := μ.restrict A
  have hTΩ : Measurable T := hT.mono hm le_rfl
  have hA : MeasurableSet A := hTΩ (MeasurableSet.singleton true)
  haveI : IsFiniteMeasure ν := by
    dsimp [ν, A]
    infer_instance
  have hsel : ∀ᵐ ω ∂ν, T ω = true := by
    change ∀ᵐ ω ∂μ.restrict A, T ω = true
    rw [ae_restrict_iff' hA]
    exact Eventually.of_forall (fun ω hω => hω)
  have hRν : Integrable (fun ω => bit (T ω) * (H ω - a ω)) ν :=
    hR.mono_measure (by dsimp [ν, A]; exact Measure.restrict_le_self)
  have haν : Integrable a ν := hai.mono_measure (by dsimp [ν, A]; exact Measure.restrict_le_self)
  have hsum : Integrable (fun ω => bit (T ω) * (H ω - a ω) + a ω) ν := hRν.add haν
  have hsumH : (fun ω => bit (T ω) * (H ω - a ω) + a ω) =ᵐ[ν] H := by
    filter_upwards [hsel] with ω hω
    simp [bit, hω]
  have hHν : Integrable H ν := hsum.congr hsumH
  have hbit : Integrable (fun ω => bit (T ω)) μ := bit_integrable T hTΩ
  have hbitSM : StronglyMeasurable (fun ω => bit (T ω)) :=
    (bit_measurable T hTΩ).stronglyMeasurable
  have hbitBound : ∀ᵐ ω ∂μ, ‖bit (T ω)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    cases T ω <;> norm_num [bit]
  have hbitA : Integrable (fun ω => bit (T ω) * a ω) μ :=
    hai.bdd_mul hbitSM.aestronglyMeasurable hbitBound
  have hbitH : Integrable (fun ω => bit (T ω) * H ω) μ := by
    have hadd : Integrable
        (fun ω => bit (T ω) * (H ω - a ω) + bit (T ω) * a ω) μ := hR.add hbitA
    have heq : (fun ω => bit (T ω) * (H ω - a ω) + bit (T ω) * a ω) =
        fun ω => bit (T ω) * H ω := by
      funext ω
      ring
    exact hadd.congr (Eventually.of_forall (fun ω => congrFun heq ω))
  have hsetResidualZero
      (hz : μ[(fun ω => bit (T ω) * (H ω - a ω)) | m] =ᵐ[μ] (fun _ => 0))
      (s : Set Ω) (hs : MeasurableSet[m] s) :
      (∫ ω in s, bit (T ω) * (H ω - a ω) ∂ μ) = 0 := by
    calc
      _ = ∫ ω in s, μ[(fun η => bit (T η) * (H η - a η)) | m] ω ∂ μ :=
        (setIntegral_condExp hm hR hs).symm
      _ = ∫ ω in s, (0 : Ω → ℝ) ω ∂ μ := by
        apply integral_congr_ae
        exact ae_restrict_of_ae hz
      _ = 0 := by simp
  have hsetSelectedEq
      (hz : μ[(fun ω => bit (T ω) * (H ω - a ω)) | m] =ᵐ[μ] (fun _ => 0))
      (s : Set Ω) (hs : MeasurableSet[m] s) :
      (∫ ω in s, H ω ∂ ν) = ∫ ω in s, a ω ∂ ν := by
    have hsΩ : MeasurableSet s := hm s hs
    have hres := residual_setIntegral_eq T hTΩ s hsΩ H a hbitH hbitA
    have hzero := hsetResidualZero hz s hs
    linarith
  have hfirst :
      (μ[(fun ω => bit (T ω) * (H ω - a ω)) | m] =ᵐ[μ] (fun _ => 0)) ↔
        (ν[H | m] =ᵐ[ν] a) := by
    constructor
    · intro hz
      apply EventuallyEq.symm
      apply ae_eq_condExp_of_forall_setIntegral_eq hm hHν
      · intro s hs _
        exact haν.integrableOn
      · intro s hs _
        exact (hsetSelectedEq hz s hs).symm
      · exact ha.stronglyMeasurable.aestronglyMeasurable
    · intro hmean
      have hsetEq (s : Set Ω) (hs : MeasurableSet[m] s) :
          (∫ ω in s, H ω ∂ ν) = ∫ ω in s, a ω ∂ ν := by
        calc
          _ = ∫ ω in s, ν[H | m] ω ∂ ν := (setIntegral_condExp hm hHν hs).symm
          _ = ∫ ω in s, a ω ∂ ν := by
            apply integral_congr_ae
            exact ae_restrict_of_ae hmean
      apply (ae_eq_condExp_of_forall_setIntegral_eq hm hR
        (fun s _ _ => (integrable_const (0 : ℝ)).integrableOn)
        (fun s hs _ => ?_)
        stronglyMeasurable_const.aestronglyMeasurable).symm
      rw [setIntegral_const]
      have hsΩ : MeasurableSet s := hm s hs
      have hres := residual_setIntegral_eq T hTΩ s hsΩ H a hbitH hbitA
      rw [hres, hsetEq s hs]
      simp [ν, A]
  have hqsm : StronglyMeasurable[m] (ν[H | m]) := stronglyMeasurable_condExp
  have hq : Measurable[m] (ν[H | m]) := hqsm.measurable
  let F : Set Ω := {ω | ν[H | m] ω ≠ a ω}
  have hF : MeasurableSet[m] F := by
    dsimp [F]
    measurability
  have hfailure : (ν[H | m] =ᵐ[ν] a) ↔ ν F = 0 := by
    rw [Filter.EventuallyEq, ae_iff]
  have hnullpos : (∀ᵐ ω ∂μ, ω ∈ F → p ω = 0) ↔
      ∀ᵐ ω ∂μ, 0 < p ω → ω ∉ F := nullOnSet_iff_pos p (fun ω => (hpb ω).1) F
  have hfinal : (ν[H | m] =ᵐ[ν] a) ↔
      ∀ᵐ ω ∂μ, 0 < p ω → ν[H | m] ω = a ω := by
    calc
      (ν[H | m] =ᵐ[ν] a) ↔ ν F = 0 := hfailure
      _ ↔ ∀ᵐ ω ∂μ, ω ∈ F → p ω = 0 :=
        treatedNull_iff m hm T p hT hp hpb hcoin F hF
      _ ↔ ∀ᵐ ω ∂μ, 0 < p ω → ω ∉ F := hnullpos
      _ ↔ ∀ᵐ ω ∂μ, 0 < p ω → ν[H | m] ω = a ω := by
        simp [F]
  exact ⟨hHν, hfirst, hfinal⟩
