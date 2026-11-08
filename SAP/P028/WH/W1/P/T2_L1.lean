import SAP.P028.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028.WH.W1.P.T2_L1
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SAP.P028 SAP.P028.Bridge
noncomputable section
open Classical

def strataMeasure : Measure (Fin 3) :=
  (1/3 : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 1 + Measure.dirac 2)

instance strataMeasure_probability : IsProbabilityMeasure strataMeasure := by
  constructor
  norm_num [strataMeasure, Measure.smul_apply, Measure.add_apply]
  calc
    (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 3 * 3⁻¹ := by ring
    _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

def fairCoin : Measure Bool :=
  bernoulliMeasure true false halfProbability

instance fairCoin_probability : IsProbabilityMeasure fairCoin := by
  constructor
  change bernoulliMeasure true false halfProbability Set.univ = 1
  rw [bernoulliMeasure_apply halfProbability MeasurableSet.univ]
  simp

def counterMeasure : Measure (Fin 3 × (Bool × Bool)) :=
  strataMeasure.prod (fairCoin.prod fairCoin)

instance counterMeasure_probability : IsProbabilityMeasure counterMeasure where
  measure_univ := by
    change (strataMeasure.prod (fairCoin.prod fairCoin)) Set.univ = 1
    rw [← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod, measure_univ, measure_univ]
    norm_num

def coinAverage (f : Bool → ℝ) : ℝ := (f false + f true) / 2

def pairAverage (f : Bool × Bool → ℝ) : ℝ :=
  (f (false, false) + f (false, true) + f (true, false) + f (true, true)) / 4

def strataAverage (f : Fin 3 → ℝ) : ℝ := (f 0 + f 1 + f 2) / 3

def counterAverage (f : Fin 3 × (Bool × Bool) → ℝ) : ℝ :=
  (f (0, (false, false)) + f (0, (false, true)) + f (0, (true, false)) + f (0, (true, true)) +
   f (1, (false, false)) + f (1, (false, true)) + f (1, (true, false)) + f (1, (true, true)) +
   f (2, (false, false)) + f (2, (false, true)) + f (2, (true, false)) + f (2, (true, true))) / 12

theorem strataIntegral (f : Fin 3 → ℝ) :
    (∫ s, f s ∂strataMeasure) = strataAverage f := by
  unfold strataAverage strataMeasure
  rw [integral_smul_measure, integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_add_measure Integrable.of_finite Integrable.of_finite]
  simp [integral_dirac, smul_eq_mul]
  ring

theorem coinIntegral (f : Bool → ℝ) :
    (∫ b, f b ∂fairCoin) = coinAverage f := by
  unfold fairCoin coinAverage
  rw [integral_bernoulliMeasure]
  norm_num [halfProbability]
  ring

theorem pairIntegral (f : Bool × Bool → ℝ) :
    (∫ b, f b ∂(fairCoin.prod fairCoin)) = pairAverage f := by
  unfold pairAverage
  rw [integral_prod _ Integrable.of_finite]
  simp_rw [coinIntegral]
  simp only [coinAverage]
  ring

theorem counterIntegral (f : Fin 3 × (Bool × Bool) → ℝ) :
    (∫ ω, f ω ∂counterMeasure) = counterAverage f := by
  unfold counterAverage
  change (∫ ω, f ω ∂(strataMeasure.prod (fairCoin.prod fairCoin))) = _
  rw [integral_prod _ Integrable.of_finite]
  simp_rw [pairIntegral]
  rw [strataIntegral]
  norm_num [strataAverage, pairAverage]
  ring

theorem counterProb (E : Set (Fin 3 × (Bool × Bool))) (hE : MeasurableSet E) :
    counterMeasure.real E = counterAverage (fun ω => if ω ∈ E then 1 else 0) := by
  rw [← integral_indicator_one hE, counterIntegral]
  rfl

theorem counterSetIntegral (E : Set (Fin 3 × (Bool × Bool))) (hE : MeasurableSet E)
    (f : Fin 3 × (Bool × Bool) → ℝ) :
    (∫ ω in E, f ω ∂counterMeasure) = counterAverage (fun ω => if ω ∈ E then f ω else 0) := by
  rw [← integral_indicator hE, counterIntegral]
  rfl

theorem counterEventMean (E : Set (Fin 3 × (Bool × Bool))) (hE : MeasurableSet E)
    (f : Fin 3 × (Bool × Bool) → ℝ) :
    eventMean counterMeasure f E =
      counterAverage (fun ω => if ω ∈ E then f ω else 0) /
        counterAverage (fun ω => if ω ∈ E then 1 else 0) := by
  unfold eventMean
  rw [counterSetIntegral E hE, counterProb E hE]

def counterModel : CausalModel (Fin 3 × (Bool × Bool)) where
  μ := counterMeasure
  probability := inferInstance
  S := Prod.fst
  Y := fun d _ => realBit d
  Z := fun ω => ω.2.1
  measurableS := measurable_fst
  measurableY := fun _ => measurable_const
  integrableY := fun _ => Integrable.of_finite
  measurableZ := measurable_fst.comp measurable_snd
  randomAssignment := indepFun_prod
    (X := fun s : Fin 3 => (s, realBit false, realBit true))
    (Y := fun b : Bool × Bool => b.1)
    Measurable.of_discrete measurable_fst
  armPositive := by
    intro z
    rw [counterProb _ MeasurableSet.of_discrete]
    cases z <;> norm_num [counterAverage]
  nonzeroFirstStage := by
    intro h
    have hi := counterIntegral (fun ω =>
      realBit (treatment ω.1 true) - realBit (treatment ω.1 false))
    rw [hi] at h
    norm_num [counterAverage, realBit, treatment] at h

def counterResponse : Response (Fin 3 × (Bool × Bool)) where
  R := fun ω => treatment ω.1 ω.2.1 || ω.2.2
  measurableR := Measurable.of_discrete

theorem counterCellProbability (d z : Bool) :
    cellProbability counterModel d z =
      (counterAverage (fun ω => if ω ∈ cellEvent counterModel d z then 1 else 0)) /
        (counterAverage (fun ω => if ω ∈ armEvent counterModel z then 1 else 0)) := by
  change counterMeasure.real (cellEvent counterModel d z) /
      counterMeasure.real (armEvent counterModel z) = _
  rw [counterProb _ MeasurableSet.of_discrete, counterProb _ MeasurableSet.of_discrete]

theorem counterCellAndArmMeans (d z : Bool) :
    cellMean counterModel d z = realBit d ∧ armMean counterModel z =
      (if z then (2/3 : ℝ) else 1/3) := by
  constructor
  · unfold cellMean
    simp only [counterModel]
    rw [counterEventMean _ MeasurableSet.of_discrete]
    cases d <;> cases z <;>
      norm_num [counterAverage, cellEvent, observedD, armEvent, counterModel, treatment,
        observedY, realBit]
  · unfold armMean
    simp only [counterModel]
    rw [counterEventMean _ MeasurableSet.of_discrete]
    cases z <;> norm_num [counterAverage, armEvent, counterModel, observedY,
      observedD, treatment, realBit]

theorem counterResponseCellMean (d z : Bool) :
    responseCellMean counterModel counterResponse d z = realBit d := by
  unfold responseCellMean
  simp only [counterModel]
  rw [counterEventMean _ MeasurableSet.of_discrete]
  cases d <;> cases z <;>
    norm_num [counterAverage, cellEvent, responseEvent, counterResponse, counterModel,
      observedY, observedD, treatment, realBit]

theorem counterResponseArmMean (z : Bool) :
    responseArmMean counterModel counterResponse z = if z then 4/5 else 1/2 := by
  unfold responseArmMean
  simp only [counterModel]
  rw [counterEventMean _ MeasurableSet.of_discrete]
  cases z <;> norm_num [counterAverage, armEvent, responseEvent, counterResponse,
    counterModel, observedY, observedD, treatment, realBit]

theorem counterComplierProbability : complierProbability counterModel = 1/3 := by
  unfold complierProbability complierEvent
  simp only [counterModel]
  rw [counterProb _ MeasurableSet.of_discrete]
  norm_num [counterAverage, counterModel]

theorem counterComplierMean (d : Bool) : complierMean counterModel d = realBit d := by
  unfold complierMean
  simp only [counterModel]
  rw [counterEventMean _ MeasurableSet.of_discrete]
  cases d <;> norm_num [counterAverage, complierEvent, counterModel, realBit]

theorem counterResponsePositivity : mixedResponsePositive counterModel counterResponse := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    simp only [counterModel]
    change 0 < counterMeasure.real
      ({ω : Fin 3 × (Bool × Bool) | ω.2.1 = z} ∩
        {ω | counterResponse.R ω = true})
    rw [counterProb _ MeasurableSet.of_discrete]
    cases z <;> norm_num [counterAverage, counterResponse, counterModel, treatment]
  · change 0 < counterMeasure.real
      (cellEvent counterModel true false ∩ responseEvent counterResponse)
    rw [counterProb _ MeasurableSet.of_discrete]
    norm_num [counterAverage, cellEvent, responseEvent, counterResponse, counterModel,
      observedD, treatment]
  · change 0 < counterMeasure.real
      (cellEvent counterModel false true ∩ responseEvent counterResponse)
    rw [counterProb _ MeasurableSet.of_discrete]
    norm_num [counterAverage, cellEvent, responseEvent, counterResponse, counterModel,
      observedD, treatment]

theorem counterCellIgnorable : wholeCellIgnorable counterModel counterResponse := by
  intro d z _
  refine ⟨?_, (counterResponseCellMean d z).trans (counterCellAndArmMeans d z).1.symm⟩
  simp only [counterModel]
  change 0 < counterMeasure.real
    (cellEvent counterModel d z ∩ responseEvent counterResponse)
  rw [counterProb _ MeasurableSet.of_discrete]
  cases d <;> cases z <;> norm_num [counterAverage, cellEvent, responseEvent,
    counterResponse, counterModel, observedD, treatment]

theorem counterMixedMeansDiffer : ∀ z, responseArmMean counterModel counterResponse z ≠
    armMean counterModel z := by
  intro z
  rw [counterResponseArmMean z, (counterCellAndArmMeans true z).2]
  cases z <;> norm_num

theorem counterNotMixedIdentification : ¬ mixedIdentification counterModel counterResponse := by
  intro h
  have hfalse := h.1
  rw [counterComplierMean false, counterResponseArmMean false,
    counterCellProbability true false, counterCellProbability false true,
    counterResponseCellMean true false, counterResponseCellMean false true,
    counterComplierProbability] at hfalse
  norm_num [counterAverage, cellEvent, armEvent, counterModel, observedD, treatment, realBit] at hfalse

end
end SAP.P028.WH.W1.P.T2_L1

theorem SAP.P028.WH.W1.T2_L1_proof : SAP.P028.WH.W1.T2_L1 := by
  unfold SAP.P028.WH.W1.T2_L1 SAP.P028.wholeCellCounterexample
  refine ⟨SAP.P028.WH.W1.P.T2_L1.counterModel,
    SAP.P028.WH.W1.P.T2_L1.counterResponse, ?_⟩
  refine ⟨?_, SAP.P028.WH.W1.P.T2_L1.counterCellIgnorable,
    SAP.P028.WH.W1.P.T2_L1.counterResponsePositivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    SAP.P028.WH.W1.P.T2_L1.counterMixedMeansDiffer,
    SAP.P028.WH.W1.P.T2_L1.counterNotMixedIdentification⟩
  · intro d ω
    cases d <;> norm_num [SAP.P028.WH.W1.P.T2_L1.counterModel, realBit]
  · rw [SAP.P028.WH.W1.P.T2_L1.counterCellProbability true false]
    norm_num [SAP.P028.WH.W1.P.T2_L1.counterAverage, SAP.P028.cellEvent,
      SAP.P028.armEvent, SAP.P028.WH.W1.P.T2_L1.counterModel,
      SAP.P028.observedD, SAP.P028.treatment]
  · rw [SAP.P028.WH.W1.P.T2_L1.counterCellProbability false true]
    norm_num [SAP.P028.WH.W1.P.T2_L1.counterAverage, SAP.P028.cellEvent,
      SAP.P028.armEvent, SAP.P028.WH.W1.P.T2_L1.counterModel,
      SAP.P028.observedD, SAP.P028.treatment]
  · exact SAP.P028.WH.W1.P.T2_L1.counterComplierProbability
  · exact (SAP.P028.WH.W1.P.T2_L1.counterCellAndArmMeans false false).2
  · exact (SAP.P028.WH.W1.P.T2_L1.counterCellAndArmMeans false true).2
  · exact SAP.P028.WH.W1.P.T2_L1.counterResponseArmMean false
  · exact SAP.P028.WH.W1.P.T2_L1.counterResponseArmMean true
  · exact SAP.P028.WH.W1.P.T2_L1.counterComplierMean false
  · exact SAP.P028.WH.W1.P.T2_L1.counterComplierMean true
