import SAP.P028.Defs.Part8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

def fullComplianceFacts : Prop :=
  twoAtomProb (fun _ => True) = 1 ∧
    twoAtomProb (fun z => z = false) = 1/2 ∧ twoAtomProb (fun z => z = true) = 1/2 ∧
    bit fullPotential.d0 ≤ bit fullPotential.d1 ∧
    (0 ≤ bit fullPotential.y0 ∧ bit fullPotential.y0 ≤ 1) ∧
    (0 ≤ bit fullPotential.y1 ∧ bit fullPotential.y1 ≤ 1) ∧
    (∑ _ : Bool, (1/2:ℚ)*(bit fullPotential.d1-bit fullPotential.d0)) = 1 ∧
    twoAtomProb (fun _ => fc fullPotential) = 1 ∧
    twoAtomMean (fun z => bit (fy fullPotential z)) (fun z => z = false) = 0 ∧
    twoAtomMean (fun z => bit (fy fullPotential z)) (fun z => z = true) = 1 ∧
    twoAtomMean (fun _ => bit fullPotential.y0) (fun _ => fc fullPotential) = 0 ∧
    twoAtomMean (fun _ => bit fullPotential.y1) (fun _ => fc fullPotential) = 1 ∧
    twoAtomProb (fun _ => fullPotential.d1 = fullPotential.d0) = 0 ∧
    (1-(twoAtomProb (fun _ => fc fullPotential))) = 0 ∧
    ((1:ℚ)-(twoAtomProb (fun _ => fc fullPotential))*1) = 0 ∧
    twoAtomProb (fun z => fd fullPotential z = true ∧ z = false) = 0 ∧
    twoAtomProb (fun z => fd fullPotential z = false ∧ z = true) = 0 ∧
    (∀ n : ℝ, 1*0+(1-1)*n = 0 ∧ 1*1+(1-1)*n = 1) ∧
    (∀ a n : ℝ, 0*a+0*n = 0)

def T7Statement : Prop :=
  fullComplianceFacts ∧
  (∀ (E : BinaryAtom → Prop) (z : Bool),
    twoAtomProb (fun b => E fullPotential ∧ b = z) =
      twoAtomProb (fun _ => E fullPotential) * twoAtomProb (fun b => b = z)) ∧
  (∀ z, fd fullPotential z = z ∧ fy fullPotential z = z) ∧
  (let q := twoAtomProb (fun z => fd fullPotential z = true ∧ z = false) /
      twoAtomProb (fun z => z = false)
   let r := twoAtomProb (fun z => fd fullPotential z = false ∧ z = true) /
      twoAtomProb (fun z => z = true)
   q = 0 ∧ r = 0 ∧ q+r = 0 ∧ ∀ a n : ℚ, q*a+r*n = 0) ∧
  lowerControl 1 0 1 = 0 ∧ upperControl 1 0 1 = 0 ∧
  lowerTreated 1 0 1 = 1 ∧ upperTreated 1 0 1 = 1

def T8Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  (∀ M : CausalModel Ω, boundedOutcomes M →
    0 < complierProbability M ∧ potentialMeanBounds M) ∧
  (∀ p e0 e1 : ℝ, (0 < p ∧ p ≤ 1) → (0 ≤ e0 ∧ e0 ≤ 1) →
    (0 ≤ e1 ∧ e1 ≤ 1) → |e1-e0| ≤ p →
    lowerControl p e0 e1 ≤ upperControl p e0 e1 ∧
    lowerTreated p e0 e1 ≤ upperTreated p e0 e1 ∧
    (∀ x1 : ℝ, (lowerTreated p e0 e1 ≤ x1 ∧ x1 ≤ upperTreated p e0 e1) →
      ∃ M : CausalModel (Bool × Bool), boundedOutcomes M ∧
        complierProbability M = p ∧ armMean M false = e0 ∧ armMean M true = e1 ∧
        complierMean M true = x1 ∧ complierMean M false = x1-effect p e0 e1) ∧
    (∀ x0 : ℝ, (lowerControl p e0 e1 ≤ x0 ∧ x0 ≤ upperControl p e0 e1) →
      ∃ M : CausalModel (Bool × Bool), boundedOutcomes M ∧
        complierProbability M = p ∧ armMean M false = e0 ∧ armMean M true = e1 ∧
        complierMean M false = x0 ∧ complierMean M true = x0+effect p e0 e1))

def corollaryFormulas {Ω : Type*} [MeasurableSpace Ω] (M : CausalModel Ω) : Prop :=
  cellProbability M true false = M.μ.real (alwaysEvent M) ∧
  cellProbability M false true = M.μ.real (neverEvent M) ∧
  complierProbability M = 1-cellProbability M true false-cellProbability M false true ∧
  cellMean M true false = eventMean M.μ (M.Y true) (alwaysEvent M) ∧
  cellMean M false true = eventMean M.μ (M.Y false) (neverEvent M) ∧
  noncomplierMean M =
    (cellProbability M true false*cellMean M true false +
     cellProbability M false true*cellMean M false true) /
    (cellProbability M true false+cellProbability M false true) ∧
  complierMean M false =
    (armMean M false-cellProbability M true false*cellMean M true false-
     cellProbability M false true*cellMean M false true)/complierProbability M ∧
  complierMean M true = complierMean M false +
    (armMean M true-armMean M false)/complierProbability M ∧
  complierMean M true =
    (armMean M true-cellProbability M true false*cellMean M true false-
     cellProbability M false true*cellMean M false true)/complierProbability M

def T9Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ M : CausalModel Ω, (∀ d z, 0 < M.μ.real (cellEvent M d z)) →
    0 < complierProbability M ∧
    0 < M.μ.real (alwaysEvent M) ∧ 0 < M.μ.real (neverEvent M) ∧
    0 < M.μ.real (noncomplierEvent M) ∧
    0 < cellProbability M true false+cellProbability M false true ∧
    (∀ z, armMean M z = ∑ d : Bool, cellProbability M d z*cellMean M d z) ∧
    corollaryFormulas M

def lateFormulas {Ω : Type*} [MeasurableSpace Ω] (M : CausalModel Ω) : Prop :=
  eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M true) -
    eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M false) = complierProbability M ∧
  0 < complierProbability M ∧
  armMean M true-armMean M false = complierProbability M*cace M ∧
  cace M = (armMean M true-armMean M false)/complierProbability M ∧
  cace M = (armMean M true-armMean M false) /
    (eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M true) -
     eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M false))

def nonidentificationOfLevels : Prop :=
  ∃ M₀ M₁ : CausalModel (Bool × Bool), boundedOutcomes M₀ ∧ boundedOutcomes M₁ ∧
    complierProbability M₀ = 1/2 ∧ complierProbability M₁ = 1/2 ∧
    armMean M₀ false = 3/4 ∧ armMean M₀ true = 3/4 ∧
    armMean M₁ false = 3/4 ∧ armMean M₁ true = 3/4 ∧
    cace M₀ = 0 ∧ cace M₁ = 0 ∧
    complierMean M₀ false = 1/2 ∧ complierMean M₀ true = 1/2 ∧
    complierMean M₁ false = 1 ∧ complierMean M₁ true = 1

def T10Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  (∀ M : CausalModel Ω, lateFormulas M) ∧ nonidentificationOfLevels

end
end SAP.P028
