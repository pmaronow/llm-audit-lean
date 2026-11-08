import SAP.P006b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b.WH.W1.P.T29_L1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem expectedATO_formula {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : SAP.P006b.Experiment Ω C n)
    (hS : SAP.P006b.OutcomeStanding E) (π : C → ℝ) (hπ : SAP.P006b.Admissible π) :
    E.expectedATO π = SAP.P006b.emptyFactor n (∫ x, π x ∂E.PX) *
      (∫ x, π x * E.μ1 x ∂E.PX) := by
  let Eo := SAP.P006b.outcomeExperiment E
  have hSo : SAP.P006b.Standing Eo := hS
  let P := SAP.P006b.Bridge.toProject Eo
  have hP : AronowAudit.P006.Standing P :=
    SAP.P006b.Bridge.standing_toProject hSo
  have hLaw : IsProbabilityMeasure (P.law π) := hP.law_probability π hπ
  have hT (i : Fin n) : Measurable (P.T π i) :=
    (hP.measurable_units π hπ i).2.2.2
  have hZ (i : Fin n) : Measurable (P.Y1 i) :=
    (hP.measurable_units π hπ i).2.2.1
  have hZi (i : Fin n) : Integrable (P.Y1 i) (P.law π) :=
    (hP.integrable_units π hπ i).2.1
  have hI : iIndepFun (fun i ω => (P.Y1 i ω, P.T π i ω)) (P.law π) :=
    (hP.iid_independent π hπ).comp (fun _ z => (z.2.2.1, z.2.2.2))
      (fun _ => measurable_snd.snd.fst.prodMk measurable_snd.snd.snd)
  have hstats := AronowAudit.P006.Wave1.T2_treatment_stats P hP hπ
  have hmarks := AronowAudit.P006.Wave1.T2_unit_mark_moments P hP hπ
  have hmarked := AronowAudit.P006.Wave1.T2_marked_average
    (P.law π) P.hn P.Y1 (P.T π)
    hZ hZi hT hI (P.q π) (P.A P.μ1 π)
    hstats.1 hstats.2.2 (fun i => (hmarks i).1)
  have hobs (ω : Ω) :
      AronowAudit.P006.wATO (fun i => P.T π i ω) (P.observed π ω) =
        AronowAudit.P006.wATO (fun i => P.T π i ω) (fun i => P.Y1 i ω) := by
    calc
      _ = ∑ i, AronowAudit.P006.Wave1.T2_coefficient
          (fun j => P.T π j ω) i * (P.Y1 i ω - 0) :=
        by simpa only [sub_zero] using
          (AronowAudit.P006.Wave1.T2_observed_coefficients P π ω (fun _ => 0))
      _ = ∑ i, AronowAudit.P006.Wave1.T2_coefficient
          (fun j => P.T π j ω) i * P.Y1 i ω := by simp
      _ = _ := (AronowAudit.P006.Wave1.T2_average_coefficients
        (fun i => P.T π i ω) (fun i => P.Y1 i ω)).symm
  have hExpected : P.expectedATO π =
      ∫ ω, AronowAudit.P006.wATO (fun i => P.T π i ω) (fun i => P.Y1 i ω) ∂P.law π := by
    unfold AronowAudit.P006.Experiment.expectedATO
    exact integral_congr_ae (ae_of_all _ hobs)
  have hExpE : E.expectedATO π = Eo.expectedATO π := by rfl
  calc
    E.expectedATO π = Eo.expectedATO π := hExpE
    _ = P.expectedATO π := congrFun (SAP.P006b.Bridge.expectedATO_eq Eo) π
    _ = _ := by
      simpa [P, Eo, SAP.P006b.Bridge.toProject, SAP.P006b.outcomeExperiment,
        AronowAudit.P006.Experiment.q, AronowAudit.P006.Experiment.A,
        AronowAudit.P006.emptyFactor, SAP.P006b.emptyFactor, mul_comm] using
        hExpected.trans hmarked.2.2

end

end SAP.P006b.WH.W1.P.T29_L1

theorem SAP.P006b.WH.W1.T29_L1_proof : SAP.P006b.WH.W1.T29_L1 := by
  intro Ω C mΩ mC n E hS π hπ
  exact SAP.P006b.WH.W1.P.T29_L1.expectedATO_formula E hS π hπ
