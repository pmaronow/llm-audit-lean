import SAP.P030.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P030
open scoped BigOperators
noncomputable section

/-- The same genuine ten-unit conditional design used by T2, T5, and T14. -/
def TableDesign : Prop :=
  tenΩ.card = 10 ∧ tableΩ.card = 6 ∧
  conditionalAssignments tenΩ tenS (tenAssignment 6) = tableΩ ∧
  uniformProbability tenΩ (fun z => ∀ i, tenS i = true → z i = tenAssignment 6 i) = 3/5 ∧
  (∀ j : Fin 10, (Finset.univ.filter (fun i => tenAssignment j i = true)).card = 1) ∧
  (∀ j : Fin 10, uniformProbability tenΩ (fun z => z = tenAssignment j) = 1/10) ∧
  (∀ r : Fin 6, uniformProbability tableΩ (fun z => z = tenAssignment (tableTreatment r)) = 1/6) ∧
  (∀ r : Fin 6, uniformProbability tableΩ (fun z => z = tenAssignment (tableTreatment r)) =
    uniformProbability tenΩ (fun z => z = tenAssignment (tableTreatment r)) /
      uniformProbability tenΩ (fun z => ∀ i, tenS i = true → z i = tenAssignment 6 i))

/-- The exact, defined six-row Spearman reference law and its display accuracy. -/
def TableNumerics : Prop :=
  tableY = ![1,3,2,1] ∧
  tableDistances =
    ![![1,6,7,8], ![2,5,6,7], ![3,4,5,6], ![4,3,4,5], ![5,2,3,4], ![6,1,2,3]] ∧
  tableRho = tableValues ∧
  (∀ r : Fin 6, (Finset.univ.filter
    (fun j => tenS j = false ∧ tenAssignment (tableTreatment r) j = true)).Nonempty) ∧
  (∀ r, 0 < rankSquares (tableDistances r)) ∧ rankSquares tableY = 9/2 ∧
  (-3 / Real.sqrt 10 < (-5/6 : ℝ) ∧ (-5/6 : ℝ) < -1 / Real.sqrt 90 ∧
    -1 / Real.sqrt 90 < 0) ∧
  (∀ r, tableRho r < 0) ∧
  |(-1 / Real.sqrt 90) + 0.105| < 0.0005 ∧
  |(-5/6 : ℝ) + 0.833| < 0.0005 ∧
  |(-3 / Real.sqrt 10) + 0.949| < 0.0005

def WeakMonotoneExample : Prop :=
  (∀ i j : Fin 3, (![1,2,3] : Fin 3 → ℝ) i ≤ (![1,2,3] : Fin 3 → ℝ) j →
    (![0,0,1] : Fin 3 → ℝ) i ≤ (![0,0,1] : Fin 3 → ℝ) j) ∧
  rankSquares (![1,2,3] : Fin 3 → ℝ) = 2 ∧
  rankSquares (![0,0,1] : Fin 3 → ℝ) = 3/2 ∧
  spearman (![1,2,3] : Fin 3 → ℝ) ![0,0,1] = Real.sqrt 3 / 2 ∧
  Real.sqrt 3 / 2 ≠ 1 ∧ Real.sqrt 3 / 2 ≠ -1

/-- The corrected fixed-outcome null holds, although two actual statistics differ. -/
def OutcomeNullNonconstant : Prop :=
  NoEffects tenΩ tenYnull ∧ NoInterference tenΩ tenYnull ∧
  conditionalAssignments tenΩ tenS (tenAssignment 6) = tableΩ ∧
  FixedOutcomeNull tableΩ tenS tenYnull ∧
  tenAssignment (tableTreatment 0) ∈ tableΩ ∧
  tenAssignment (tableTreatment 3) ∈ tableΩ ∧
  TableNumerics ∧
  statistic tenS tenYnull tenG (tenAssignment (tableTreatment 0)) ≠
    statistic tenS tenYnull tenG (tenAssignment (tableTreatment 3))

def T1Statement : Prop :=
  (∀ i, ∀ z z' : Assignment 5, fiveY i z = fiveY i z') ∧
  NoEffects fiveΩ fiveY ∧ NoInterference fiveΩ fiveY ∧
  fiveΩ.card = 2 ∧ conditionalAssignments fiveΩ fiveS (fiveAssignment 0) = fiveΩ ∧
  (∀ a : Fin 2, uniformProbability fiveΩ (fun z => z = fiveAssignment a) = 1/2) ∧
  (∀ z ∈ fiveΩ, ∀ i, fiveS i = true → z i = false) ∧
  (∀ a : Fin 2, (Finset.univ.filter (fun i => fiveAssignment a i = true)).card = 1) ∧
  fiveOutcomes = ![0,1,2] ∧
  fiveDistances 0 = ![1,5,9] ∧ fiveDistances 1 = ![2,6,10] ∧
  averageRank fiveOutcomes = ![1,2,3] ∧ centeredRanks fiveOutcomes = ![-1,0,1] ∧
  (∀ a : Fin 2, averageRank (fiveDistances a) = ![1,2,3] ∧
    centeredRanks (fiveDistances a) = ![-1,0,1] ∧ rankCross (fiveDistances a) fiveOutcomes = 2) ∧
  (∀ a : Fin 2, rankSquares (fiveDistances a) = 2 ∧ rankSquares fiveOutcomes = 2 ∧
    fiveStatistic a = 1) ∧
  (∀ a : Fin 2, 0 < rankSquares (fiveDistances a) ∧ 0 < rankSquares fiveOutcomes ∧
    (Finset.univ.filter (fun j => fiveS j = false ∧ fiveAssignment a j = true)).Nonempty) ∧
  (∀ a : Fin 2,
    uniformProbability Finset.univ (fun b => fiveStatistic b ≤ fiveStatistic a) = 1 ∧
    uniformProbability Finset.univ (fun b => fiveStatistic a ≤ fiveStatistic b) = 1) ∧
  (∀ α : ℝ, 0 < α → α < 1 →
    uniformProbability (Finset.univ : Finset (Fin 2))
      (fun a => printedReject α
        (uniformProbability Finset.univ (fun b => fiveStatistic b ≤ fiveStatistic a))) = 1 ∧
    uniformProbability (Finset.univ : Finset (Fin 2))
      (fun a => correctedReject α
        (uniformProbability Finset.univ (fun b => fiveStatistic b ≤ fiveStatistic a))
        (uniformProbability Finset.univ (fun b => fiveStatistic a ≤ fiveStatistic b))) = 0 ∧
    α < 1) ∧
  ((1/20 : ℝ)/2 = 1/40 ∧ 1-(1/20 : ℝ)/2 = 39/40 ∧ (39/40 : ℝ) < 1) ∧
  printedReject (1/20) 1

def T2Statement : Prop :=
  (∀ i, ∀ z z' : Assignment 10, tenYnull i z = tenYnull i z') ∧
  NoEffects tenΩ tenYnull ∧ NoInterference tenΩ tenYnull ∧ TableDesign ∧ TableNumerics ∧
  (∀ r : Fin 6,
    statistic tenS tenYnull tenG (tenAssignment (tableTreatment r)) = tableRho r) ∧
  (∀ r s : Fin 6, referenceStatistic tenS tenYnull tenG (tenAssignment (tableTreatment r))
    (tenAssignment (tableTreatment s)) = tableRho s) ∧
  (∀ r : Fin 6, uniformProbability Finset.univ (fun s => tableRho s ≤ tableRho r) =
    (![1,1,1,1/2,1/3,1/3] : Fin 6 → ℝ) r) ∧
  (∀ r : Fin 6, uniformProbability Finset.univ (fun s => tableRho r ≤ tableRho s) =
    (![1/2,1/2,1/2,2/3,1,1] : Fin 6 → ℝ) r) ∧
  (∀ α : ℝ, 0 < α → α ≤ 2/3 →
    uniformProbability tableΩ (fun z => printedReject α
      (uniformProbability tableΩ (fun w => referenceStatistic tenS tenYnull tenG z w ≤
        statistic tenS tenYnull tenG z))) = 1/2 ∧
    uniformProbability tableΩ (fun z => correctedReject α
      (uniformProbability tableΩ (fun w => referenceStatistic tenS tenYnull tenG z w ≤
        statistic tenS tenYnull tenG z))
      (uniformProbability tableΩ (fun w => statistic tenS tenYnull tenG z ≤
        referenceStatistic tenS tenYnull tenG z w))) = 0) ∧
  ((1/20 : ℝ) < 1/2)

def T3Statement : Prop :=
  (∀ {A : Type*} (μ : FiniteLaw A) (f : A → ℝ),
    (∀ x : ℝ, upperTail μ f x = 1 - lowerTail μ f x + probability μ (fun z => f z = x) ∧
      1 - lowerTail μ f x ≤ upperTail μ f x) ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      probability μ (fun z => lowerTail μ f (f z) ≤ u) ≤ u ∧
      probability μ (fun z => upperTail μ f (f z) ≤ u) ≤ u) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      probability μ (fun z => correctedReject α (lowerTail μ f (f z)) (upperTail μ f (f z))) ≤
        probability μ (fun z => lowerTail μ f (f z) ≤ α/2) +
        probability μ (fun z => upperTail μ f (f z) ≤ α/2) ∧
      probability μ (fun z => lowerTail μ f (f z) ≤ α/2) +
        probability μ (fun z => upperTail μ f (f z) ≤ α/2) ≤ α ∧
      probability μ (fun z => correctedReject α (lowerTail μ f (f z)) (upperTail μ f (f z))) ≤ α ∧
      (∀ x : ℝ, upperTail μ f x < α/2 → 1-α/2 < lowerTail μ f x) ∧
      (∀ x : ℝ, correctedReject α (lowerTail μ f x) (upperTail μ f x) →
        printedReject α (lowerTail μ f x)) ∧
      (∀ pL pU : ℝ, twoTailP pL pU ≤ α ↔ pL ≤ α/2 ∨ pU ≤ α/2) ∧
      probability μ (fun z => twoTailP (lowerTail μ f (f z)) (upperTail μ f (f z)) ≤ α) ≤ α)) ∧
  T1Statement

def T4Statement : Prop := ¬ PrintedTwoTailedExactness

def T5Statement : Prop :=
  (∀ i, ∀ z z' : Assignment 10, tenYnull i z = tenYnull i z') ∧
  TableDesign ∧ TableNumerics ∧ OutcomeNullNonconstant ∧
  (∀ r : Fin 6, statistic tenS tenYnull tenG (tenAssignment (tableTreatment r)) = tableRho r) ∧
  uniformProbability Finset.univ (fun s => tableRho s ≤ tableRho 5) = 1/3 ∧
  (∀ {A : Type*} (Ω : Finset A), Ω.Nonempty → ∀ t : A → ℝ,
    (∀ z ∈ Ω, ∀ z' ∈ Ω, t z = t z') →
    ∀ z ∈ Ω, uniformProbability Ω (fun w => t w ≤ t z) = 1)

end
end SAP.P030
