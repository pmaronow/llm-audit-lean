import SAP.P007.Defs
import AronowAudit.P007.P007_StateFailure
import AronowAudit.P007.P007_Probability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P007.Bridge
open AronowAudit.P007

/-- The finite-law adapters preserve weights and reuse the supplied normalization
proofs. Every probability and expectation depends only on those weights. -/
def toAudit {α : Type*} [Fintype α] (L : Law α) : FiniteLaw α where
  weight := L.weight
  nonneg := L.nonneg
  total := L.total

def fromAudit {α : Type*} [Fintype α] (L : FiniteLaw α) : Law α where
  weight := L.weight
  nonneg := L.nonneg
  total := L.total

theorem to_from {α : Type*} [Fintype α] (L : FiniteLaw α) :
    toAudit (fromAudit L) = L := rfl

theorem from_to {α : Type*} [Fintype α] (L : Law α) :
    fromAudit (toAudit L) = L := rfl

theorem probability_eq {α : Type*} [Fintype α] (L : Law α) (P : α → Prop) :
    probability L P = eventProbability (toAudit L) P := rfl

theorem expectation_eq {α : Type*} [Fintype α] (L : Law α) (f : α → ℝ) :
    expectation L f = finiteExpectation (toAudit L) f := rfl

theorem rowIndependent_eq {n h : ℕ} (L : Law (Array n h)) :
    rowIndependent L = RowsIndependent (toAudit L) := rfl

theorem prefixObserved_eq : @prefixObserved = @observedPrefix := rfl
theorem survival_eq {n h : ℕ} (L : Law (Array n h)) (i : Fin n) (j : ℕ) :
    survival L i j = prefixSurvival (toAudit L) i j := rfl
theorem allDeleted_eq {n h : ℕ} (L : Law (Array n h)) :
    allDeleted L = pAll (toAudit L) := rfl
theorem observationBound_eq {n h : ℕ} (L : Law (Array n h)) (q : ℝ) :
    observationBound L q = ConditionalObservationBound (toAudit L) q := rfl
theorem conditionalObserved_eq {n h : ℕ} (L : Law (Array n h)) (i : Fin n) (j : ℕ) :
    conditionalObserved L i j = repairedConditional (toAudit L) i j := rfl
theorem superlog_eq : superlog = Superlogarithmic := rfl
theorem sameRowLaw_eq {n h : ℕ} (L : Law (Array n h)) :
    sameRowLaw L = RowsIdenticallyDistributed (toAudit L) := rfl
theorem deletedIndicator_eq : @deletedIndicator = @removedRowIndicator := rfl
theorem deletedFraction_eq : @deletedFraction = @removedFraction := rfl
theorem lowerBound_eq : lowerBound = bestCaseBound := rfl
theorem fractionBound_eq : fractionBound = deletedFractionBound := rfl
theorem realThreshold_eq : realThreshold = thresholdReal := rfl
theorem realLowerBound_eq : realLowerBound = realBestCaseBound := rfl

theorem sampleSets_eq : sampleSets = columnSamples := rfl
theorem retainedShare_eq : @retainedShare = @retainedProportion := rfl
theorem meanRetained_eq : @meanRetained = @expectedRetained := rfl
theorem meanLoss_eq : @meanLoss = @expectedLoss := rfl
theorem missingAverage_eq : @missingAverage = @columnMissingAverage := rfl
theorem missingCount_eq : @missingCount = @missingCells := rfl
theorem observedColumns_eq : @observedColumns = @observedSets := rfl

theorem independentCells_weights {n h : ℕ} (a : Fin n → Fin h → ℝ)
    (ha0 : ∀ i j, 0 ≤ a i j) (ha1 : ∀ i j, a i j ≤ 1) :
    (independentCells a ha0 ha1).weight = cellWeights a := rfl
theorem equal_weights (n h : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (equalProbabilityLaw n h q hq0 hq1).weight = equalWeights n h q := rfl
theorem unequal_weights (n h : ℕ) :
    (unequalProbabilityLaw n h).weight = unequalWeights n h := rfl
theorem nullFirst_weights : nullFirstLaw.weight = nullFirstWeights := by
  classical
  funext x
  simp [nullFirstLaw, independentProduct, pointMass, nullFirstWeights]
theorem fullyMissing_weights : fullyMissingLaw.weight = fullyMissingWeights := by
  classical
  funext x
  simp [fullyMissingLaw, independentProduct, pointMass, fullyMissingWeights]
theorem laterNull_weights : laterNullLaw.weight = laterNullWeights := by
  classical
  funext x
  simp [laterNullLaw, independentProduct, mixtureLaw, pointMass, laterNullWeights]
theorem figure5_weights : figure5Witness.weight = figure5Weights := rfl
theorem nonidentical_weights : nonidenticalRowsWitness.weight = nonidenticalWeights := rfl

/-- Package the existing equality model as SAP data; no new normalization proof. -/
theorem equalModel_of_audit (n h : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (P : Law (Array n h) → Prop)
    (hp : P (fromAudit (equalProbabilityLaw n h q hq0 hq1.le))) : equalModel n h q P := by
  have he := bestCase_attained n h q hq0 hq1
  exact ⟨fromAudit (equalProbabilityLaw n h q hq0 hq1.le), rfl, he.1, he.2.1, hp⟩

theorem unequalModel_of_audit (n h : ℕ) (P : Law (Array n h) → Prop)
    (hp : P (fromAudit (unequalProbabilityLaw n h))) : unequalModel n h P := by
  have hs := unequalProbability_assumptions n h
  exact ⟨fromAudit (unequalProbabilityLaw n h), rfl, hs.1, hs.2, hp⟩

end SAP.P007.Bridge
