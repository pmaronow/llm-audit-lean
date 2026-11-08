import SAP.P028.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028.WH.W1.P.T2_L4

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SAP.P028 SAP.P028.Bridge SAP.P028.WH.W1
noncomputable section
open Classical

private abbrev Obs := Bool × Bool × Bool × ℝ

private theorem local_observed_d_measurable {Ω : Type*} [MeasurableSpace Ω]
    (M : CausalModel Ω) : Measurable (observedD M) := by
  change Measurable (AronowAudit.P028.observedD (SAP.P028.Bridge.toAudit M))
  exact AronowAudit.P028.observed_d_measurable (SAP.P028.Bridge.toAudit M)

private theorem local_observed_y_measurable {Ω : Type*} [MeasurableSpace Ω]
    (M : CausalModel Ω) : Measurable (observedY M) := by
  change Measurable (AronowAudit.P028.observedY (SAP.P028.Bridge.toAudit M))
  exact AronowAudit.P028.observed_y_measurable (SAP.P028.Bridge.toAudit M)

private theorem local_arm_measurable {Ω : Type*} [MeasurableSpace Ω]
    (M : CausalModel Ω) (z : Bool) : MeasurableSet (armEvent M z) := by
  change MeasurableSet (AronowAudit.P028.armEvent (SAP.P028.Bridge.toAudit M) z)
  exact AronowAudit.P028.arm_measurable (SAP.P028.Bridge.toAudit M) z

private theorem observation_measurable {Ω : Type*} [MeasurableSpace Ω]
    (M : CausalModel Ω) (T : Response Ω) : Measurable (wholeObservation M T) := by
  unfold wholeObservation
  exact M.measurableZ.prodMk ((local_observed_d_measurable M).prodMk
    ((T.measurableR).prodMk
      (((Measurable.of_discrete : Measurable realBit).comp T.measurableR).mul
        (local_observed_y_measurable M))))

private theorem arm_mass_eq_law {Ω : Type*} [MeasurableSpace Ω]
    (M : CausalModel Ω) (T : Response Ω) (z : Bool) :
    M.μ.real (armEvent M z) = (wholeObservedLaw M T).real {o : Obs | o.1 = z} := by
  simp only [measureReal_def, wholeObservedLaw]
  have hs : MeasurableSet {o : Obs | o.1 = z} :=
    measurable_fst (measurableSet_singleton z)
  rw [Measure.map_apply (observation_measurable M T) hs]
  congr 1

private theorem cell_mass_eq_law {Ω : Type*} [MeasurableSpace Ω]
    (M : CausalModel Ω) (T : Response Ω) (d z : Bool) :
    M.μ.real (cellEvent M d z) =
      (wholeObservedLaw M T).real {o : Obs | o.2.1 = d ∧ o.1 = z} := by
  simp only [measureReal_def, wholeObservedLaw]
  have hs : MeasurableSet {o : Obs | o.2.1 = d ∧ o.1 = z} :=
    (measurable_snd.fst (measurableSet_singleton d)).inter
      (measurable_fst (measurableSet_singleton z))
  rw [Measure.map_apply (observation_measurable M T) hs]
  congr 1

private theorem missing_mass_eq_law {Ω : Type*} [MeasurableSpace Ω]
    (M : CausalModel Ω) (T : Response Ω) (d z : Bool) :
    M.μ.real {ω | T.R ω = false ∧ observedD M ω = d ∧ M.Z ω = z} =
      (wholeObservedLaw M T).real
        {o : Obs | o.2.2.1 = false ∧ o.2.1 = d ∧ o.1 = z} := by
  simp only [measureReal_def, wholeObservedLaw]
  have hs : MeasurableSet {o : Obs | o.2.2.1 = false ∧ o.2.1 = d ∧ o.1 = z} :=
    (measurable_snd.snd.fst (measurableSet_singleton false)).inter
      ((measurable_snd.fst (measurableSet_singleton d)).inter
        (measurable_fst (measurableSet_singleton z)))
  rw [Measure.map_apply (observation_measurable M T) hs]
  congr 1

private def recordedIntegrand (d z : Bool) : Obs → ℝ := fun o =>
  if o.1 = z then if o.2.1 = d then o.2.2.2 else 0 else 0

private theorem recordedIntegrand_measurable (d z : Bool) :
    Measurable (recordedIntegrand d z) := by
  unfold recordedIntegrand
  exact Measurable.ite (measurable_fst (measurableSet_singleton z))
    (Measurable.ite (measurable_snd.fst (measurableSet_singleton d))
      measurable_snd.snd.snd measurable_const) measurable_const

private theorem recorded_integral_eq_law {Ω : Type*} [MeasurableSpace Ω]
    (M : CausalModel Ω) (T : Response Ω) (d z : Bool) :
    (∫ ω in armEvent M z, realBit (T.R ω) *
      (if observedD M ω = d then observedY M ω else 0) ∂M.μ) =
    ∫ o, recordedIntegrand d z o ∂wholeObservedLaw M T := by
  calc
    (∫ ω in armEvent M z, realBit (T.R ω) *
        (if observedD M ω = d then observedY M ω else 0) ∂M.μ) =
      ∫ ω, recordedIntegrand d z (wholeObservation M T ω) ∂M.μ := by
        rw [← integral_indicator (local_arm_measurable M z)]
        apply integral_congr_ae
        filter_upwards [] with ω
        by_cases hz : M.Z ω = z <;> by_cases hd : observedD M ω = d <;>
          cases hr : T.R ω <;>
          simp [Set.indicator, recordedIntegrand, wholeObservation, realBit,
            armEvent, hz, hd, hr]
    _ = ∫ o, recordedIntegrand d z o ∂wholeObservedLaw M T := by
      symm
      exact integral_map_of_stronglyMeasurable (observation_measurable M T)
        (recordedIntegrand_measurable d z).stronglyMeasurable

private theorem arm_mass_eq_of_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (M : CausalModel Ω) (T : Response Ω) (M' : CausalModel Ω') (T' : Response Ω')
    (he : wholeObservedLaw M T = wholeObservedLaw M' T') (z : Bool) :
    M.μ.real (armEvent M z) = M'.μ.real (armEvent M' z) := by
  calc
    M.μ.real (armEvent M z) = (wholeObservedLaw M T).real {o : Obs | o.1 = z} :=
      arm_mass_eq_law M T z
    _ = (wholeObservedLaw M' T').real {o : Obs | o.1 = z} := by rw [he]
    _ = M'.μ.real (armEvent M' z) := (arm_mass_eq_law M' T' z).symm

private theorem cell_mass_eq_of_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (M : CausalModel Ω) (T : Response Ω) (M' : CausalModel Ω') (T' : Response Ω')
    (he : wholeObservedLaw M T = wholeObservedLaw M' T') (d z : Bool) :
    M.μ.real (cellEvent M d z) = M'.μ.real (cellEvent M' d z) := by
  calc
    M.μ.real (cellEvent M d z) =
        (wholeObservedLaw M T).real {o : Obs | o.2.1 = d ∧ o.1 = z} :=
      cell_mass_eq_law M T d z
    _ = (wholeObservedLaw M' T').real {o : Obs | o.2.1 = d ∧ o.1 = z} := by rw [he]
    _ = M'.μ.real (cellEvent M' d z) := (cell_mass_eq_law M' T' d z).symm

private theorem missing_mass_eq_of_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (M : CausalModel Ω) (T : Response Ω) (M' : CausalModel Ω') (T' : Response Ω')
    (he : wholeObservedLaw M T = wholeObservedLaw M' T') (d z : Bool) :
    M.μ.real {ω | T.R ω = false ∧ observedD M ω = d ∧ M.Z ω = z} =
      M'.μ.real {ω | T'.R ω = false ∧ observedD M' ω = d ∧ M'.Z ω = z} := by
  calc
    M.μ.real {ω | T.R ω = false ∧ observedD M ω = d ∧ M.Z ω = z} =
        (wholeObservedLaw M T).real
          {o : Obs | o.2.2.1 = false ∧ o.2.1 = d ∧ o.1 = z} :=
      missing_mass_eq_law M T d z
    _ = (wholeObservedLaw M' T').real
          {o : Obs | o.2.2.1 = false ∧ o.2.1 = d ∧ o.1 = z} := by rw [he]
    _ = M'.μ.real {ω | T'.R ω = false ∧ observedD M' ω = d ∧ M'.Z ω = z} :=
      (missing_mass_eq_law M' T' d z).symm

private theorem recorded_integrals_eq_of_law {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (M : CausalModel Ω) (T : Response Ω) (M' : CausalModel Ω')
    (T' : Response Ω') (he : wholeObservedLaw M T = wholeObservedLaw M' T')
    (d z : Bool) :
    (∫ ω in armEvent M z, realBit (T.R ω) *
      (if observedD M ω = d then observedY M ω else 0) ∂M.μ) =
    (∫ ω in armEvent M' z, realBit (T'.R ω) *
      (if observedD M' ω = d then observedY M' ω else 0) ∂M'.μ) := by
  calc
    (∫ ω in armEvent M z, realBit (T.R ω) *
        (if observedD M ω = d then observedY M ω else 0) ∂M.μ) =
      ∫ o, recordedIntegrand d z o ∂wholeObservedLaw M T :=
        recorded_integral_eq_law M T d z
    _ = ∫ o, recordedIntegrand d z o ∂wholeObservedLaw M' T' := by
      rw [he]
    _ = (∫ ω in armEvent M' z, realBit (T'.R ω) *
        (if observedD M' ω = d then observedY M' ω else 0) ∂M'.μ) :=
      (recorded_integral_eq_law M' T' d z).symm

end
end SAP.P028.WH.W1.P.T2_L4

open SAP.P028.WH.W1.P.T2_L4

theorem SAP.P028.WH.W1.T2_L4_proof : SAP.P028.WH.W1.T2_L4 := by
  intro Ω Ω' _ _ M T M' T' hb hb' he
  have hArm (z : Bool) : M.μ.real (armEvent M z) = M'.μ.real (armEvent M' z) :=
    arm_mass_eq_of_law M T M' T' he z
  have hCell (d z : Bool) : M.μ.real (cellEvent M d z) = M'.μ.real (cellEvent M' d z) :=
    cell_mass_eq_of_law M T M' T' he d z
  have hcpCell (d z : Bool) : cellProbability M d z = cellProbability M' d z := by
    unfold cellProbability
    rw [hCell d z, hArm z]
  have hp : complierProbability M = complierProbability M' := by
    have hM := (AronowAudit.P028.pure_cell_probabilities (SAP.P028.Bridge.toAudit M)).2.2
    have hM' := (AronowAudit.P028.pure_cell_probabilities (SAP.P028.Bridge.toAudit M')).2.2
    change cellProbability M true false + cellProbability M false true =
      1 - complierProbability M at hM
    change cellProbability M' true false + cellProbability M' false true =
      1 - complierProbability M' at hM'
    rw [hcpCell true false, hcpCell false true] at hM
    linarith
  refine ⟨hp, ?_⟩
  intro d z
  constructor
  · have hnum := recorded_integrals_eq_of_law M T M' T' he d z
    have hden := hArm z
    unfold recordedOutcomeMoment eventMean
    rw [hnum, hden]
  · have hnum := missing_mass_eq_of_law M T M' T' he d z
    have hden := hArm z
    unfold missingOutcomeProbability
    rw [hnum, hden]
