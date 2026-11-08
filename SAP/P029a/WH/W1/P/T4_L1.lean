import SAP.P029a.WH.W1.Leaves
import AronowAudit.P029.Wave1.LateIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029a.WH.W1.P.T4_L1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology

universe u v

noncomputable section

theorem complierProbability_pos {Ω : Type u} {X : Type v}
    [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialResponse X)
    (hprofile : ∀ x, 0 < eventProbability μ {ω | (U ω).x = x})
    (hscore : ∀ x, 0 < complianceProbability μ U x) :
    0 < eventProbability μ {ω | (U ω).isComplier} := by
  let ω : Ω := Classical.choice (MeasureTheory.nonempty_of_isProbabilityMeasure μ)
  let x : X := (U ω).x
  have hx := hprofile x
  have hs := hscore x
  have hnum : 0 < eventProbability μ {ω | (U ω).isComplier ∧ (U ω).x = x} := by
    unfold complianceProbability at hs
    exact (div_pos_iff_of_pos_right hx).mp hs
  have hmono : eventProbability μ {ω | (U ω).isComplier ∧ (U ω).x = x} ≤
      eventProbability μ {ω | (U ω).isComplier} := by
    apply MeasureTheory.measureReal_mono (h₂ := by finiteness)
    intro ω' hω'
    exact hω'.1
  exact lt_of_lt_of_le hnum hmono

theorem randomized_receipt_difference {Ω : Type u} {X : Type v}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialResponse X) (Z : Ω → Bool)
    (hcore : WholeIVCore μ U Z)
    (hno : μ {ω | (U ω).isDefier} = 0) :
    eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω)))
        {ω | Z ω = true} -
      eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω)))
        {ω | Z ω = false} =
      eventProbability μ {ω | (U ω).isComplier} := by
  let R : Bool → (X × Bool × Bool × ℝ × ℝ) → ℝ :=
    fun z t => indicatorValue (if z then t.2.2.1 else t.2.1)
  have hbit : Measurable indicatorValue := Measurable.of_discrete
  have hd0 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.1) :=
    measurable_fst.comp measurable_snd
  have hd1 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hR (z : Bool) : Measurable (R z) := by
    cases z with
    | false => change Measurable (fun t : X × Bool × Bool × ℝ × ℝ => indicatorValue t.2.1)
               exact hbit.comp hd0
    | true => change Measurable (fun t : X × Bool × Bool × ℝ × ℝ => indicatorValue t.2.2.1)
              exact hbit.comp hd1
  have hobs_meas (z : Bool) : Measurable (fun ω => indicatorValue ((U ω).receivedTreatment z)) := by
    cases z with
    | false => change Measurable (fun ω => indicatorValue ((U ω).d0)); exact hbit.comp hcore.d0_measurable
    | true => change Measurable (fun ω => indicatorValue ((U ω).d1)); exact hbit.comp hcore.d1_measurable
  have hobs_int (z : Bool) : Integrable (fun ω => indicatorValue ((U ω).receivedTreatment z)) μ := by
    apply (integrable_const (μ := μ) (1 : ℝ)).mono' (hobs_meas z).aestronglyMeasurable
    filter_upwards with ω
    cases (U ω).receivedTreatment z <;> simp [indicatorValue, Real.norm_eq_abs]
  have hind (z : Bool) :
      IndepFun Z (fun ω => indicatorValue ((U ω).receivedTreatment z)) μ := by
    simpa only [Function.comp_def, R, PotentialResponse.receivedTreatment, id_eq] using
      hcore.randomized.comp (measurable_id : Measurable (id : Bool → Bool)) (hR z)
  have htrue : 0 < eventProbability μ {ω | Z ω = true} := hcore.assignment_pos
  have hfalse_mass : eventProbability μ {ω | Z ω = false} =
      1 - eventProbability μ {ω | Z ω = true} := by
    have hcompl : {ω | Z ω = false} = {ω | Z ω = true}ᶜ := by
      ext ω
      cases Z ω <;> simp
    rw [hcompl]
    change μ.real ({ω | Z ω = true}ᶜ) = 1 - μ.real {ω | Z ω = true}
    exact probReal_compl_eq_one_sub
      ((measurableSet_singleton true).preimage hcore.assignment_measurable)
  have hfalse : 0 < eventProbability μ {ω | Z ω = false} := by
    rw [hfalse_mass]
    linarith [hcore.assignment_lt_one]
  have hmean (z : Bool) (hz : 0 < eventProbability μ {ω | Z ω = z}) :
      eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω)))
          {ω | Z ω = z} =
        ∫ ω, indicatorValue ((U ω).receivedTreatment z) ∂μ := by
    have hset : MeasurableSet {ω | Z ω = z} :=
      (measurableSet_singleton z).preimage hcore.assignment_measurable
    have hobs :
        (∫ ω in {ω | Z ω = z}, indicatorValue ((U ω).receivedTreatment (Z ω)) ∂μ) =
          ∫ ω in {ω | Z ω = z}, indicatorValue ((U ω).receivedTreatment z) ∂μ := by
      apply setIntegral_congr_fun hset
      intro ω hω
      change Z ω = z at hω
      simp only [hω]
    have hn1 := AronowAudit.P029.Wave1.LateIdentity.n1_proof
      μ Z (fun ω => indicatorValue ((U ω).receivedTreatment z))
      hcore.assignment_measurable (hobs_int z) (hind z) z hz
    calc
      eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω)))
          {ω | Z ω = z} =
        AronowAudit.P029.mCE μ
          (fun ω => indicatorValue ((U ω).receivedTreatment z)) {ω | Z ω = z} := by
            simp only [eventMean, eventProbability, AronowAudit.P029.mCE,
              AronowAudit.P029.mP, hobs]
      _ = ∫ ω, indicatorValue ((U ω).receivedTreatment z) ∂μ := hn1
  have hmeans :
      eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω)))
          {ω | Z ω = true} -
        eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω)))
          {ω | Z ω = false} =
        (∫ ω, indicatorValue ((U ω).receivedTreatment true) ∂μ) -
          ∫ ω, indicatorValue ((U ω).receivedTreatment false) ∂μ := by
    rw [hmean true htrue, hmean false hfalse]
  have hint0 : Integrable (fun ω => indicatorValue ((U ω).d0)) μ := by
    simpa [PotentialResponse.receivedTreatment] using hobs_int false
  have hint1 : Integrable (fun ω => indicatorValue ((U ω).d1)) μ := by
    simpa [PotentialResponse.receivedTreatment] using hobs_int true
  have hind0 :
      (∀ᵐ ω ∂μ, indicatorValue ((U ω).receivedTreatment true) -
        indicatorValue ((U ω).receivedTreatment false) =
          if (U ω).isComplier then 1 else 0) := by
    have hdef : ∀ᵐ ω ∂μ, ¬ (U ω).isDefier := by
      exact measure_eq_zero_iff_ae_notMem.mp hno
    filter_upwards [hdef] with ω hω
    cases h0 : (U ω).d0 <;> cases h1 : (U ω).d1 <;>
      simp [PotentialResponse.receivedTreatment, PotentialResponse.isDefier,
        PotentialResponse.isComplier, indicatorValue, h0, h1] at hω ⊢
  have hCmeas : MeasurableSet {ω | (U ω).isComplier} := by
    change MeasurableSet ({ω | (U ω).d0 = false} ∩ {ω | (U ω).d1 = true})
    exact ((measurableSet_singleton false).preimage hcore.d0_measurable).inter
      ((measurableSet_singleton true).preimage hcore.d1_measurable)
  have hCint :
      (∫ ω, (if (U ω).isComplier then (1 : ℝ) else 0) ∂μ) =
        eventProbability μ {ω | (U ω).isComplier} := by
    simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, eventProbability,
      measureReal_def] using (integral_indicator_one (μ := μ) hCmeas)
  calc
    _ = (∫ ω, indicatorValue ((U ω).receivedTreatment true) ∂μ) -
          ∫ ω, indicatorValue ((U ω).receivedTreatment false) ∂μ := hmeans
    _ = ∫ ω, indicatorValue ((U ω).receivedTreatment true) -
          indicatorValue ((U ω).receivedTreatment false) ∂μ := by
      exact (integral_sub (hobs_int true) (hobs_int false)).symm
    _ = ∫ ω, (if (U ω).isComplier then (1 : ℝ) else 0) ∂μ :=
      integral_congr_ae hind0
    _ = eventProbability μ {ω | (U ω).isComplier} := hCint

end

end SAP.P029a.WH.W1.P.T4_L1

theorem SAP.P029a.WH.W1.T4_L1_proof : SAP.P029a.WH.W1.T4_L1 := by
  intro Ω X _ _ _ _ μ _ U Z hm
  let hcore : SAP.P029a.WholeIVCore μ U Z := hm.toWholeIVCore
  have hrel_pos : 0 < eventProbability μ {ω | (U ω).isComplier} :=
    SAP.P029a.WH.W1.P.T4_L1.complierProbability_pos μ U hm.profile_mass hm.score_pos
  have hrel :
      eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω)))
          {ω | Z ω = true} -
        eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω)))
          {ω | Z ω = false} ≠ 0 := by
    rw [SAP.P029a.WH.W1.P.T4_L1.randomized_receipt_difference μ U Z hcore hm.no_defiers]
    exact ne_of_gt hrel_pos
  exact ⟨hm.covariate_measurable, hm.d0_measurable, hm.d1_measurable,
    hm.y0_measurable, hm.y1_measurable, hm.assignment_measurable,
    hm.y0_integrable, hm.y1_integrable, hm.randomized, hm.assignment_pos,
    hm.assignment_lt_one, hm.no_defiers, hrel⟩
