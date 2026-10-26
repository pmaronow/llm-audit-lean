import AronowAudit.P061.P061_Foundations

/-! False printed claims represented as closed propositions.
Their falsity follows from the general-support counterexample. -/
namespace AronowAudit.P061.PrintedClaims
open scoped BigOperators
noncomputable section

/-- Universally quantified printed assertion, refuted in P061_Refutations. -/
def printed_well_defined_claim : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ) (_hN : 0 < N)
    (hp : IndividualPositivity D g d) (hp' : IndividualPositivity D g d'),
    TargetedMoment D g y d ∧ TargetedMoment D g y d' ∧
    (∀ i, epo D g y i d = conditionalMean D g y i d ∧
      epo D g y i d' = conditionalMean D g y i d') ∧
    aeed D g y d d' = (N : ℝ)⁻¹ * ∑ i, eed D g y i d d' 
/-- Universally quantified printed assertion, refuted in P061_Refutations. -/
def printed_general_ht_unbiased : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ) (_hN : 0 < N)
    (hp : IndividualPositivity D g d) (hp' : IndividualPositivity D g d'),
    Integrable D (ht D g y d) ∧ Integrable D (htContrast D g y d d') ∧
    expectation D (ht D g y d) = aepo D g y d ∧
    expectation D (htContrast D g y d d') = aeed D g y d d' 
end
end AronowAudit.P061.PrintedClaims
