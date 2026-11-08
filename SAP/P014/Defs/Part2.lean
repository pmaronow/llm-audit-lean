import SAP.P014.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014
open scoped BigOperators
noncomputable section

def eventProbability {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (P : Ω → Prop) : ℝ := (μ {ω | P ω}).toReal

def CorrectedLocalConditions {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) (X : Ω → Fin N → ℝ) (b : ℝ)
    (S : Finset (Fin N)) (v : S → ℝ) : Prop :=
  (∀ i, Measurable (fun ω => X ω i)) ∧
  (∀ i, eventProbability μ (fun ω => insideWindow b (X ω i)) =
    if i ∈ S then 1 else 0) ∧
  (∀ σ : Equiv.Perm S, eventProbability μ (fun ω => ∀ i : S, X ω i = v (σ i)) =
    1 / (S.card.factorial : ℝ))

def FiniteLocalConditions {Ω : Type*} {N : ℕ} (L : FiniteDistribution Ω)
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ) : Prop :=
  (∀ ω ∈ L.atoms, windowSubjects b (X ω) = S) ∧
  (∀ σ : Equiv.Perm S, probability L (fun ω => ∀ i : S, X ω i = v (σ i)) =
    1 / (S.card.factorial : ℝ))

def permutationAssignment {N : ℕ} (S : Finset (Fin N)) (v : S → ℝ)
    (c : TreatmentVector N) (σ : Equiv.Perm S) : TreatmentVector N := fun i =>
  if h : i ∈ S then decide (0 ≤ v (σ ⟨i, h⟩)) else c i

def uniformSix : FiniteDistribution (Fin 6) := ⟨Finset.univ, fun _ => 1/6⟩
def localThree : Finset (Fin 4) := {0, 1, 2}

def scores1 : Fin 6 → Fin 4 → ℝ :=
  ![![-2,-1,1,3], ![-2,1,-1,-3], ![-1,-2,1,-3],
    ![-1,1,-2,-3], ![1,-2,-1,-3], ![1,-1,-2,-3]]

def allocations : Fin 6 → TreatmentVector 4 :=
  ![![false,false,true,true], ![false,true,false,false], ![false,false,true,false],
    ![false,true,false,false], ![true,false,false,false], ![true,false,false,false]]

def outcomes1 : PotentialOutcomes 4 := fun i z => if i = 3 then 0 else binaryValue (z 3)
def outcomes9 : PotentialOutcomes 4 := fun i z => if i = 0 then binaryValue (z 3) else 0

def scores5 : Fin 6 → Fin 4 → ℝ :=
  ![![1,-1,-2,3], ![-1,1,-2,3], ![-1,-2,1,3],
    ![-1,-2,1,4], ![-1,-2,1,5], ![-1,-2,1,6]]

def outcomes5 : PotentialOutcomes 4 := fun i z => if i = 0 then binaryValue (z 0) else 0

def scores9 : Fin 6 → Fin 4 → ℝ :=
  ![![-1,-(1/2),1/2,2], ![-1,1/2,-(1/2),-2], ![-(1/2),-1,1/2,-2],
    ![-(1/2),1/2,-1,-2], ![1/2,-1,-(1/2),-2], ![1/2,-(1/2),-1,-2]]

def assignmentDistribution : FiniteDistribution (TreatmentVector 4) :=
  pushforward uniformSix allocations

def assignmentDistribution5 : FiniteDistribution (TreatmentVector 4) :=
  pushforward uniformSix (fun ω => thresholdAssignment (scores5 ω))

def extendedDistribution : FiniteDistribution (Fin 6 × Bool) :=
  ⟨Finset.univ, fun ω => if ω.2 then 1/9 else 1/18⟩

def extendedScores (ω : Fin 6 × Bool) : Fin 4 → ℝ := fun i =>
  if i = 3 then (if ω.2 then 3 else -3) else scores1 ω.1 i

/-- The first three coordinates, indexed from zero throughout this package. -/
def localCoordinates (X : Fin 6 → Fin 4 → ℝ) (ω : Fin 6) : Fin 3 → ℝ :=
  fun i => X ω (Fin.castSucc i)

def AssignmentMasses : Prop :=
  assignmentDistribution.atoms =
    {![false,false,true,true], ![false,true,false,false],
      ![false,false,true,false], ![true,false,false,false]} ∧
  assignmentDistribution.weight ![false,false,true,true] = 1/6 ∧
  assignmentDistribution.weight ![false,true,false,false] = 1/3 ∧
  assignmentDistribution.weight ![false,false,true,false] = 1/6 ∧
  assignmentDistribution.weight ![true,false,false,false] = 1/3

def CommonWitnessCounts : Prop :=
  (∀ z ∈ assignmentDistribution.atoms, armSize localThree z true = 1) ∧
  (∀ i ∈ localThree, armProbability assignmentDistribution i true = 1/3)

end
end SAP.P014
