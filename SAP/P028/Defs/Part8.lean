import SAP.P028.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

variable {Ω : Type*} [MeasurableSpace Ω]

def boundaryRepair (M : CausalModel Ω) : Prop :=
  0 < complierProbability M ∧ complierProbability M ≤ 1 ∧
  (0 ≤ noncomplierContribution M ∧ noncomplierContribution M ≤ 1-complierProbability M) ∧
  (∀ z, armMean M z = complierProbability M*complierMean M z + noncomplierContribution M) ∧
  noncomplierContribution M = jointOutcomeMoment M true false + jointOutcomeMoment M false true ∧
  (complierProbability M < 1 →
    M.μ.real (noncomplierEvent M) = 1-complierProbability M ∧
    0 < M.μ.real (noncomplierEvent M) ∧
    noncomplierContribution M = (1-complierProbability M)*noncomplierMean M ∧
    0 ≤ noncomplierMean M ∧ noncomplierMean M ≤ 1) ∧
  (complierProbability M = 1 → noncomplierContribution M = 0 ∧
    complierMean M false = armMean M false ∧ complierMean M true = armMean M true) ∧
  (∀ z, complierMean M z = (armMean M z-noncomplierContribution M)/complierProbability M)

def potentialMeanBounds (M : CausalModel Ω) : Prop :=
  lowerControl (complierProbability M) (armMean M false) (armMean M true) ≤ complierMean M false ∧
  complierMean M false ≤ upperControl (complierProbability M) (armMean M false) (armMean M true) ∧
  lowerTreated (complierProbability M) (armMean M false) (armMean M true) ≤ complierMean M true ∧
  complierMean M true ≤ upperTreated (complierProbability M) (armMean M false) (armMean M true) ∧
  complierMean M true = complierMean M false + effect (complierProbability M) (armMean M false) (armMean M true)

def singletonEndpoints : Prop :=
  ∀ e0 e1 : ℝ, (0 ≤ e0 ∧ e0 ≤ 1) → (0 ≤ e1 ∧ e1 ≤ 1) →
    lowerControl 1 e0 e1 = e0 ∧ upperControl 1 e0 e1 = e0 ∧
    lowerTreated 1 e0 e1 = e1 ∧ upperTreated 1 e0 e1 = e1

def T6Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  (∀ M : CausalModel Ω, boundedOutcomes M → boundaryRepair M ∧
    (∀ d, 0 ≤ complierMean M d ∧ complierMean M d ≤ 1) ∧
    (∀ z, 0 ≤ armMean M z-complierProbability M*complierMean M z ∧
      armMean M z-complierProbability M*complierMean M z ≤ 1-complierProbability M) ∧
    (∀ z, 1-(1-armMean M z)/complierProbability M ≤ complierMean M z ∧
      complierMean M z ≤ armMean M z/complierProbability M) ∧
    potentialMeanBounds M) ∧ singletonEndpoints

end
end SAP.P028
