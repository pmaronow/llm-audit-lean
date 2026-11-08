import SAP.P014.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014
open scoped BigOperators
noncomputable section

def T1Statement : Prop :=
  IsDistribution uniformSix ∧ IsDistribution assignmentDistribution ∧
  PrintedLocalConditions uniformSix scores1 2 localThree ∧
  localThree.card = 3 ∧ (pushforward uniformSix scores1).atoms.card = 6 ∧
  (fun ω => thresholdAssignment (scores1 ω)) = allocations ∧
  (∀ σ : Equiv.Perm (Fin 3), probability uniformSix (fun ω => ∀ i : Fin 3,
    scores1 ω (Fin.castSucc i) = (![-2,-1,1] : Fin 3 → ℝ) (σ i)) = 1/6) ∧
  AssignmentMasses ∧ CommonWitnessCounts ∧ PositiveArms assignmentDistribution localThree ∧
  supportAverage assignmentDistribution outcomes1 0 true = 0 ∧
  supportAverage assignmentDistribution outcomes1 0 false = 1/3 ∧
  supportAverage assignmentDistribution outcomes1 1 true = 0 ∧
  supportAverage assignmentDistribution outcomes1 1 false = 1/3 ∧
  supportAverage assignmentDistribution outcomes1 2 true = 1/2 ∧
  supportAverage assignmentDistribution outcomes1 2 false = 0 ∧
  conditionalAverage assignmentDistribution outcomes1 0 true = 0 ∧
  conditionalAverage assignmentDistribution outcomes1 0 false = 1/4 ∧
  conditionalAverage assignmentDistribution outcomes1 1 true = 0 ∧
  conditionalAverage assignmentDistribution outcomes1 1 false = 1/4 ∧
  conditionalAverage assignmentDistribution outcomes1 2 true = 1/2 ∧
  conditionalAverage assignmentDistribution outcomes1 2 false = 0 ∧
  (∀ ω : Fin 6, differenceOfMeans localThree outcomes1 (allocations ω) = 0) ∧
  expectation assignmentDistribution (differenceOfMeans localThree outcomes1) = 0 ∧
  windowContrast localThree (supportAverage assignmentDistribution outcomes1) = -1/18 ∧
  windowContrast localThree (conditionalAverage assignmentDistribution outcomes1) = 0 ∧
  expectation assignmentDistribution (differenceOfMeans localThree outcomes1) -
    windowContrast localThree (supportAverage assignmentDistribution outcomes1) = 1/18 ∧
  expectation assignmentDistribution (differenceOfMeans localThree outcomes1) ≠
    windowContrast localThree (supportAverage assignmentDistribution outcomes1)

/-- This is the explicit, positive-arm counterexample form of the refutation. -/
def T4Statement : Prop :=
  IsDistribution uniformSix ∧ IsDistribution assignmentDistribution ∧
  PrintedLocalConditions uniformSix scores1 2 localThree ∧
  (fun ω => thresholdAssignment (scores1 ω)) = allocations ∧
  (∀ σ : Equiv.Perm (Fin 3), probability uniformSix (fun ω => ∀ i : Fin 3,
    scores1 ω (Fin.castSucc i) = (![-2,-1,1] : Fin 3 → ℝ) (σ i)) = 1/6) ∧
  CommonWitnessCounts ∧ PositiveArms assignmentDistribution localThree ∧
  expectation assignmentDistribution (differenceOfMeans localThree outcomes1) = 0 ∧
  windowContrast localThree (supportAverage assignmentDistribution outcomes1) = -1/18 ∧
  expectation assignmentDistribution (differenceOfMeans localThree outcomes1) ≠
    windowContrast localThree (supportAverage assignmentDistribution outcomes1)

def T5Statement : Prop :=
  IsDistribution uniformSix ∧ IsDistribution assignmentDistribution5 ∧
  PrintedLocalConditions uniformSix scores5 2 localThree ∧
  (pushforward uniformSix scores5).atoms.card = 6 ∧
  probability uniformSix (fun ω => localCoordinates scores5 ω = ![1,-1,-2]) = 1/6 ∧
  probability uniformSix (fun ω => localCoordinates scores5 ω = ![-1,1,-2]) = 1/6 ∧
  probability uniformSix (fun ω => localCoordinates scores5 ω = ![-1,-2,1]) = 2/3 ∧
  probability uniformSix (fun ω => localCoordinates scores5 ω = ![-2,-1,1]) = 0 ∧
  probability uniformSix (fun ω => localCoordinates scores5 ω = ![-2,1,-1]) = 0 ∧
  probability uniformSix (fun ω => localCoordinates scores5 ω = ![1,-2,-1]) = 0 ∧
  probability uniformSix (fun ω => localCoordinates scores5 ω = ![-1,-2,1]) ≠ 1/6 ∧
  probability uniformSix (fun ω => thresholdAssignment (scores5 ω) 0 = true) = 1/6 ∧
  probability uniformSix (fun ω => thresholdAssignment (scores5 ω) 1 = true) = 1/6 ∧
  probability uniformSix (fun ω => thresholdAssignment (scores5 ω) 2 = true) = 2/3 ∧
  PositiveArms assignmentDistribution5 localThree ∧
  assignmentDistribution5.atoms =
    {![true,false,false,true], ![false,true,false,true], ![false,false,true,true]} ∧
  assignmentDistribution5.weight ![true,false,false,true] = 1/6 ∧
  assignmentDistribution5.weight ![false,true,false,true] = 1/6 ∧
  assignmentDistribution5.weight ![false,false,true,true] = 2/3 ∧
  (∀ z ∈ assignmentDistribution5.atoms, armSize localThree z true = 1 ∧
    differenceOfMeans localThree outcomes5 z = binaryValue (z 0)) ∧
  (∀ i ∈ localThree, ∀ a, supportAverage assignmentDistribution5 outcomes5 i a =
    (if i = 0 then binaryValue a else 0) ∧
    conditionalAverage assignmentDistribution5 outcomes5 i a =
    (if i = 0 then binaryValue a else 0)) ∧
  Noninterfering localThree outcomes5 ∧
  expectation assignmentDistribution5 (differenceOfMeans localThree outcomes5) = 1/6 ∧
  windowContrast localThree (supportAverage assignmentDistribution5 outcomes5) = 1/3 ∧
  expectation assignmentDistribution5 (differenceOfMeans localThree outcomes5) ≠
    windowContrast localThree (supportAverage assignmentDistribution5 outcomes5)

def T9Statement : Prop :=
  IsDistribution uniformSix ∧ IsDistribution assignmentDistribution ∧
  PrintedLocalConditions uniformSix scores9 1 localThree ∧
  (pushforward uniformSix scores9).atoms.card = 6 ∧
  (fun ω => thresholdAssignment (scores9 ω)) = allocations ∧
  (∀ σ : Equiv.Perm (Fin 3), probability uniformSix (fun ω => ∀ i : Fin 3,
    scores9 ω (Fin.castSucc i) = (![-1,-(1/2),1/2] : Fin 3 → ℝ) (σ i)) = 1/6) ∧
  AssignmentMasses ∧ CommonWitnessCounts ∧ PositiveArms assignmentDistribution localThree ∧
  supportAverage assignmentDistribution outcomes9 0 false = 1/3 ∧
  conditionalAverage assignmentDistribution outcomes9 0 false = 1/4 ∧
  (∀ i ∈ localThree, ∀ a, otherSubjectsAverage assignmentDistribution outcomes9 i a =
    conditionalAverage assignmentDistribution outcomes9 i a) ∧
  supportAverage assignmentDistribution outcomes9 0 true = 0 ∧
  conditionalAverage assignmentDistribution outcomes9 0 true = 0 ∧
  (∀ i ∈ localThree, i ≠ 0 → ∀ a,
    supportAverage assignmentDistribution outcomes9 i a = 0 ∧
    conditionalAverage assignmentDistribution outcomes9 i a = 0) ∧
  windowContrast localThree (supportAverage assignmentDistribution outcomes9) = -1/9 ∧
  windowContrast localThree (conditionalAverage assignmentDistribution outcomes9) = -1/12 ∧
  (∑ i ∈ localThree, directEffect assignmentDistribution outcomes9 i) / localThree.card = 1/12 ∧
  windowContrast localThree (supportAverage assignmentDistribution outcomes9) ≠
    (∑ i ∈ localThree, directEffect assignmentDistribution outcomes9 i) / localThree.card ∧
  windowContrast localThree (supportAverage assignmentDistribution outcomes9) ≠
    -(∑ i ∈ localThree, directEffect assignmentDistribution outcomes9 i) / localThree.card ∧
  (∀ z ∈ assignmentDistribution.atoms, differenceOfMeans localThree outcomes9 z =
    if z = ![false,false,true,true] then -1/2 else 0) ∧
  expectation assignmentDistribution (differenceOfMeans localThree outcomes9) = -1/12 ∧
  expectation assignmentDistribution (differenceOfMeans localThree outcomes9) -
    windowContrast localThree (supportAverage assignmentDistribution outcomes9) = 1/36

end
end SAP.P014
