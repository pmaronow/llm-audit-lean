import SAP.P006a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

universe u v

namespace SAP.P006a.WH.W1.P.T2_L1

noncomputable section

lemma unit_mark_numerator {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : AronowAudit.P006.Experiment Ω C n)
    (hS : AronowAudit.P006.Standing E)
    {π : C → ℝ} (hp : AronowAudit.P006.Admissible π) (m : C → ℝ) (hm : Measurable m)
    (hi : Integrable m E.PX) (i : Fin n) :
    (∫ ω, AronowAudit.P006.bit (E.T π i ω) * m (E.X i ω) ∂E.law π) = E.A m π := by
  have hLaw : IsProbabilityMeasure (E.law π) := hS.law_probability π hp
  obtain ⟨hX, hY0, hY1, hT⟩ := hS.measurable_units π hp i
  have hG : E.covariateSigma i ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hmark : Integrable (fun ω => m (E.X i ω)) (E.law π) :=
    (hS.covariate_law π hp i).comp hm |>.integrable_iff.mpr hi
  have hb : Measurable (fun ω => AronowAudit.P006.bit (E.T π i ω)) :=
    (measurable_of_finite AronowAudit.P006.bit).comp hT
  have hbi : Integrable (fun ω => AronowAudit.P006.bit (E.T π i ω)) (E.law π) :=
    (integrable_const (1 : ℝ)).mono' hb.aestronglyMeasurable
      (ae_of_all _ fun ω => AronowAudit.P006.Wave1.T7_bit_norm _)
  have hbm : Integrable
      (fun ω => AronowAudit.P006.bit (E.T π i ω) * m (E.X i ω)) (E.law π) :=
    AronowAudit.P006.Wave1.T7_bit_mul hT hmark
  have hmG : StronglyMeasurable[E.covariateSigma i] (fun ω => m (E.X i ω)) :=
    (hm.comp (comap_measurable (E.X i))).stronglyMeasurable
  have hcond : (E.law π)[(fun ω => AronowAudit.P006.bit (E.T π i ω) * m (E.X i ω)) |
      E.covariateSigma i] =ᵐ[E.law π] (fun ω => π (E.X i ω) * m (E.X i ω)) := by
    exact (condExp_mul_of_stronglyMeasurable_right hmG hbm hbi).trans (by
      filter_upwards [hS.bernoulli π hp i] with ω hω
      exact congrArg (· * m (E.X i ω)) hω)
  rw [AronowAudit.P006.Wave1.T2_total_moment (E.law π) hG hcond]
  simpa only [AronowAudit.P006.Experiment.A, Function.comp_apply, Pi.mul_apply, mul_comm] using
    ((hS.covariate_law π hp i).comp (hm.mul hp.1)).integral_eq

lemma unit_treatment_mass {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : AronowAudit.P006.Experiment Ω C n)
    (hS : AronowAudit.P006.Standing E)
    {π : C → ℝ} (hp : AronowAudit.P006.Admissible π) (i : Fin n) :
    ((E.law π) {ω | E.T π i ω = true}).toReal = E.q π := by
  have hLaw : IsProbabilityMeasure (E.law π) := hS.law_probability π hp
  obtain ⟨hX, hY0, hY1, hT⟩ := hS.measurable_units π hp i
  have hs : MeasurableSet {ω | E.T π i ω = true} :=
    (measurableSet_singleton true).preimage hT
  have hstats := AronowAudit.P006.Wave1.T2_treatment_stats E hS hp
  have hconst : (∫ ω, {ω | E.T π i ω = true}.indicator (fun _ => (1 : ℝ)) ω
      ∂E.law π) = ((E.law π) {ω | E.T π i ω = true}).toReal := by
    simpa only [measureReal_def, smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := E.law π) (1 : ℝ) hs)
  have hbit : (fun ω => {ω | E.T π i ω = true}.indicator (fun _ => (1 : ℝ)) ω) =
      (fun ω => AronowAudit.P006.bit (E.T π i ω)) := by
    funext ω
    by_cases ht : E.T π i ω = true <;>
      simp [ht, AronowAudit.P006.bit]
  rw [← hconst, hbit]
  exact hstats.2.2 i

end

end SAP.P006a.WH.W1.P.T2_L1

theorem SAP.P006a.WH.W1.T2_L1_proof : SAP.P006a.WH.W1.T2_L1 := by
  intro Ω C _ _ n E hD π hp m hm hi i hq
  let hS := SAP.P006a.WH.W1.oracle_standing E hD
  let E' := SAP.P006a.Bridge.experiment (SAP.P006a.oracleBaseline E)
  let hS' := SAP.P006a.Bridge.standing hS
  have hnum := SAP.P006a.WH.W1.P.T2_L1.unit_mark_numerator E' hS' hp m hm hi i
  have hmass := SAP.P006a.WH.W1.P.T2_L1.unit_treatment_mass E' hS' hp i
  have hnum' : (∫ ω, AronowAudit.P006.bit (E.T π i ω) * m (E.X i ω) ∂E.law π) =
      E.A m π := by
    simpa [E', SAP.P006a.Bridge.experiment, SAP.P006a.oracleBaseline,
      SAP.P006a.Experiment.A, AronowAudit.P006.Experiment.A] using hnum
  have hmass' : ((E.law π) {ω | E.T π i ω = true}).toReal = E.q π := by
    simpa [E', SAP.P006a.Bridge.experiment, SAP.P006a.oracleBaseline,
      SAP.P006a.Experiment.q, AronowAudit.P006.Experiment.q] using hmass
  have hset : MeasurableSet {ω | E.T π i ω = true} :=
    (measurableSet_singleton true).preimage (hS.measurable_units π hp i).2.2.2
  have hindicator : (fun ω => {ω | E.T π i ω = true}.indicator (fun ω => m (E.X i ω)) ω) =
      (fun ω => AronowAudit.P006.bit (E.T π i ω) * m (E.X i ω)) := by
    funext ω
    by_cases ht : E.T π i ω = true <;>
      simp [ht, AronowAudit.P006.bit]
  unfold eventMean
  rw [← integral_indicator hset, hindicator, hnum', hmass']
