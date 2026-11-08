import SAP.P029a.WH.W1.Leaves
import AronowAudit.P029.Wave1.LateIdentity.N1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029a.WH.W1.P.T2_L1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

universe u v

noncomputable section

end
end SAP.P029a.WH.W1.P.T2_L1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

theorem SAP.P029a.WH.W1.T2_L1_proof : SAP.P029a.WH.W1.T2_L1 := by
  intro Ω X _ _ _ μ hμ U Z hcore hside x hx hc
  let r0 : Ω → ℝ := fun ω => SAP.P029a.indicatorValue (U ω).d0
  let r1 : Ω → ℝ := fun ω => SAP.P029a.indicatorValue (U ω).d1
  have hZ : Measurable Z := hcore.assignment_measurable
  have hbit : Measurable SAP.P029a.indicatorValue := Measurable.of_discrete
  have hr0m : Measurable r0 := by
    exact hbit.comp hcore.d0_measurable
  have hr1m : Measurable r1 := by
    exact hbit.comp hcore.d1_measurable
  have hr0i : Integrable r0 μ := by
    apply (integrable_const (μ := μ) (1 : ℝ)).mono' hr0m.aestronglyMeasurable
    filter_upwards with ω
    dsimp [r0, SAP.P029a.indicatorValue]
    split <;> norm_num
  have hr1i : Integrable r1 μ := by
    apply (integrable_const (μ := μ) (1 : ℝ)).mono' hr1m.aestronglyMeasurable
    filter_upwards with ω
    dsimp [r1, SAP.P029a.indicatorValue]
    split <;> norm_num
  have hproj0 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ =>
      SAP.P029a.indicatorValue t.2.1) := by
    exact hbit.comp measurable_snd.fst
  have hproj1 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ =>
      SAP.P029a.indicatorValue t.2.2.1) := by
    exact hbit.comp (measurable_snd.snd.fst)
  have hind0 : IndepFun Z r0 μ := by
    simpa [r0, Function.comp_def] using
      hcore.randomized.comp (measurable_id : Measurable (id : Bool → Bool)) hproj0
  have hind1 : IndepFun Z r1 μ := by
    simpa [r1, Function.comp_def] using
      hcore.randomized.comp (measurable_id : Measurable (id : Bool → Bool)) hproj1
  have hfalse : 0 < eventProbability μ {ω | Z ω = false} := by
    have hset : {ω | Z ω = false} = ({ω | Z ω = true})ᶜ := by
      ext ω
      cases Z ω <;> simp
    have hsum : eventProbability μ {ω | Z ω = true} +
        eventProbability μ {ω | Z ω = false} = 1 := by
      calc
        eventProbability μ {ω | Z ω = true} + eventProbability μ {ω | Z ω = false} =
            μ.real {ω | Z ω = true} + μ.real ({ω | Z ω = true}ᶜ) := by
              rw [← hset]
              rfl
        _ = 1 := probReal_add_probReal_compl (μ := μ)
          ((measurableSet_singleton true).preimage hZ)
    linarith [hcore.assignment_lt_one]
  have hmean0 : eventMean μ r0 {ω | Z ω = true} = ∫ ω, r0 ω ∂μ := by
    simpa [eventMean, eventProbability, r0, AronowAudit.P029.mCE,
      AronowAudit.P029.mP, Measure.real] using
      (AronowAudit.P029.Wave1.LateIdentity.n1_proof μ Z r0 hZ hr0i hind0 true hcore.assignment_pos)
  have hmean1 : eventMean μ r1 {ω | Z ω = true} = ∫ ω, r1 ω ∂μ := by
    simpa [eventMean, eventProbability, r1, AronowAudit.P029.mCE,
      AronowAudit.P029.mP, Measure.real] using
      (AronowAudit.P029.Wave1.LateIdentity.n1_proof μ Z r1 hZ hr1i hind1 true hcore.assignment_pos)
  have hmean0f : eventMean μ r0 {ω | Z ω = false} = ∫ ω, r0 ω ∂μ := by
    simpa [eventMean, eventProbability, r0, AronowAudit.P029.mCE,
      AronowAudit.P029.mP, Measure.real] using
      (AronowAudit.P029.Wave1.LateIdentity.n1_proof μ Z r0 hZ hr0i hind0 false hfalse)
  have hmean1f : eventMean μ r1 {ω | Z ω = false} = ∫ ω, r1 ω ∂μ := by
    simpa [eventMean, eventProbability, r1, AronowAudit.P029.mCE,
      AronowAudit.P029.mP, Measure.real] using
      (AronowAudit.P029.Wave1.LateIdentity.n1_proof μ Z r1 hZ hr1i hind1 false hfalse)
  have hobstrue0 : eventMean μ
      (fun ω => SAP.P029a.indicatorValue ((U ω).receivedTreatment (Z ω)))
      {ω | Z ω = true} = eventMean μ r1 {ω | Z ω = true} := by
    change (∫ ω in {ω | Z ω = true},
        SAP.P029a.indicatorValue ((U ω).receivedTreatment (Z ω)) ∂μ) /
        eventProbability μ {ω | Z ω = true} =
      (∫ ω in {ω | Z ω = true}, r1 ω ∂μ) /
        eventProbability μ {ω | Z ω = true}
    apply congrArg (fun a : ℝ => a / eventProbability μ {ω | Z ω = true})
    exact setIntegral_congr_fun ((measurableSet_singleton true).preimage hZ)
      (fun ω hω => by
        change Z ω = true at hω
        simp [r1, PotentialResponse.receivedTreatment, hω])
  have hobstrue1 : eventMean μ
      (fun ω => SAP.P029a.indicatorValue ((U ω).receivedTreatment (Z ω)))
      {ω | Z ω = false} = eventMean μ r0 {ω | Z ω = false} := by
    change (∫ ω in {ω | Z ω = false},
        SAP.P029a.indicatorValue ((U ω).receivedTreatment (Z ω)) ∂μ) /
        eventProbability μ {ω | Z ω = false} =
      (∫ ω in {ω | Z ω = false}, r0 ω ∂μ) /
        eventProbability μ {ω | Z ω = false}
    apply congrArg (fun a : ℝ => a / eventProbability μ {ω | Z ω = false})
    exact setIntegral_congr_fun ((measurableSet_singleton false).preimage hZ)
      (fun ω hω => by
        change Z ω = false at hω
        simp [r0, PotentialResponse.receivedTreatment, hω])
  have hC : MeasurableSet {ω | (U ω).isComplier} := by
    change MeasurableSet ({ω | (U ω).d0 = false} ∩ {ω | (U ω).d1 = true})
    exact ((measurableSet_singleton false).preimage hcore.d0_measurable).inter
      ((measurableSet_singleton true).preimage hcore.d1_measurable)
  have hdiff_ae : (fun ω => r1 ω - r0 ω) =ᵐ[μ]
      (fun ω => if (U ω).isComplier then 1 else 0) := by
    filter_upwards [hside] with ω hω
    dsimp [r0, r1]
    cases hd : (U ω).d1 <;>
      simp [SAP.P029a.indicatorValue, PotentialResponse.isComplier, hω, hd]
  have hintdiff : (∫ ω, r1 ω ∂μ) - (∫ ω, r0 ω ∂μ) =
      eventProbability μ {ω | (U ω).isComplier} := by
    rw [← integral_sub hr1i hr0i]
    calc
      (∫ ω, (r1 ω - r0 ω) ∂μ) =
          ∫ ω, (if (U ω).isComplier then 1 else 0) ∂μ := integral_congr_ae hdiff_ae
      _ = μ.real {ω | (U ω).isComplier} := by
          have heq : (fun ω => if (U ω).isComplier then (1 : ℝ) else 0) =
              {ω | (U ω).isComplier}.indicator (fun _ => (1 : ℝ)) := by
            funext ω
            by_cases hω : (U ω).isComplier <;> simp [hω, Set.indicator]
          rw [heq]
          exact integral_indicator_one (μ := μ) hC
      _ = eventProbability μ {ω | (U ω).isComplier} := rfl
  have hprofileC : 0 < eventProbability μ
      {ω | (U ω).isComplier ∧ (U ω).x = x} := by
    have hratio : 0 < eventProbability μ
        {ω | (U ω).isComplier ∧ (U ω).x = x} /
          eventProbability μ {ω | (U ω).x = x} := by
      simpa [complianceProbability] using hc
    exact (div_pos_iff_of_pos_right hx).mp hratio
  have hCpos : 0 < eventProbability μ {ω | (U ω).isComplier} := by
    have hmono : eventProbability μ
        {ω | (U ω).isComplier ∧ (U ω).x = x} ≤
          eventProbability μ {ω | (U ω).isComplier} := by
      exact measureReal_mono (by
        intro ω hω
        exact hω.1)
    exact lt_of_lt_of_le hprofileC hmono
  have hstage :
      eventMean μ (fun ω => SAP.P029a.indicatorValue ((U ω).receivedTreatment (Z ω)))
          {ω | Z ω = true} -
        eventMean μ (fun ω => SAP.P029a.indicatorValue ((U ω).receivedTreatment (Z ω)))
          {ω | Z ω = false} = eventProbability μ {ω | (U ω).isComplier} := by
    rw [hobstrue0, hobstrue1, hmean1, hmean0f, hintdiff]
  intro hzero
  rw [hstage] at hzero
  exact (ne_of_gt hCpos) hzero

