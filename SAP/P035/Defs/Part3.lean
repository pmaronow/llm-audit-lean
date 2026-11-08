import SAP.P035.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P035

/-- The complete specified finite witness, including its design, calibration,
individual and mean effects, and the failure of campaign identification. -/
def T1Statement : Prop :=
  (∀ y, latentSize y = Nat.lcm (reducedDenominator y false) (reducedDenominator y true)) ∧
  (∀ y, 0 < latentSize y ∧ threshold y false ≤ threshold y true ∧
    threshold y true ≤ latentSize y) ∧
  (∀ y z, (threshold y z : ℚ) = (latentSize y : ℚ) * releasedFrequency y z) ∧
  (∀ y z r, conditionalMass y z r =
    (∑ s ∈ latentPopulation y, conditionalMass y z s) *
    (conditionalMass y false r + conditionalMass y true r)) ∧
  ((∀ y z r, 0 ≤ jointMass y z r) ∧
    (∑ y ∈ years, ((∑ r ∈ latentPopulation y, jointMass y false r) +
      (∑ r ∈ latentPopulation y, jointMass y true r))) = 1) ∧
  (∀ y z r, C y z true r = D y z true r) ∧
  (∀ y z, successCount D y z = threshold y z ∧
    successCount C y z = threshold y z ∧
    (successCount D y z : ℚ) / (latentSize y : ℚ) = releasedFrequency y z) ∧
  (Calibrated D ∧ Calibrated C) ∧
  (∀ y, outcomeMean D y true true - outcomeMean D y false true = exactEffect y ∧
    0 < outcomeMean D y true true - outcomeMean D y false true) ∧
  (∀ y z r, campaignDifference D y z r = 0) ∧
  (∀ y r, campaignDifference C y false r = 0) ∧
  (∀ y, campaignMean C y true = exactEffect y ∧
    exactEffect y = ((threshold y true - threshold y false : ℕ) : ℚ) /
      (latentSize y : ℚ) ∧ 0 < campaignMean C y true) ∧
  overallCampaignEffect D = 0 ∧
  (overallCampaignEffect C =
    (96 / 1223 : ℚ) * (326 / 6555) + (157 / 1223) * (699 / 41605) +
      (192 / 1223) * (449 / 7104) ∧
    overallCampaignEffect C = (83755728 / 5240292055 : ℚ) ∧
    0 < overallCampaignEffect C) ∧
  (∀ w, observedLawWith D w = observedLawWith C w) ∧
  (∀ w, observedRealLawWith D w = observedRealLawWith C w) ∧
  (¬ CampaignIdentified) ∧
  (¬ ∃ f : (Year → Bool → Bool → ℚ) → ℚ,
    ∀ Y : PotentialOutcome, Calibrated Y → f (observedLaw Y) = overallCampaignEffect Y)

/-- Both mathematical campaign clauses of the corrected interpretation:
nonidentification and compatibility with full campaign enablement of each
year's porch contrast. All models share the fixed independent finite design. -/
def T2Statement : Prop :=
  (∃ U V : PotentialOutcome,
    Calibrated U ∧ Calibrated V ∧ observedLaw U = observedLaw V ∧
    (∀ y z r, campaignDifference U y z r = 0) ∧
    (∀ y, 0 < campaignMean V y true ∧
      campaignMean V y true = releasedFrequency y true - releasedFrequency y false ∧
      campaignMean V y true = exactEffect y) ∧
    (∀ y r, V y true false r = V y false false r)) ∧
  ¬ CampaignIdentified

end SAP.P035
