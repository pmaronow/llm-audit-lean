import SAP.P035.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P035

/-! The fixed design has uniform latent types independent of porch assignment
within year. Sums are always over the finite latent support. The year and arm
mixture uses raw enrollment shares, not the paper's pooled weighting. -/

def yearMass (y : Year) : ℚ :=
  ((enrolled y false + enrolled y true : ℕ) : ℚ) / 1223

def assignmentMass (y : Year) (z : PorchAssignment) : ℚ :=
  (enrolled y z : ℚ) / ((enrolled y false + enrolled y true : ℕ) : ℚ)

def latentMass (y : Year) : ℚ := 1 / (latentSize y : ℚ)

def conditionalMass (y : Year) (z : PorchAssignment) (_r : ℕ) : ℚ :=
  assignmentMass y z / (latentSize y : ℚ)

def jointMass (y : Year) (z : PorchAssignment) (r : ℕ) : ℚ :=
  yearMass y * conditionalMass y z r

/-- Finite pushforward masses for year, assignment and observed choice.
Weights can be any rational values, including any rational probability mass. -/
def observedLawWith (Y : PotentialOutcome) (w : Year → Bool → ℕ → ℚ)
    (y : Year) (z : PorchAssignment) (b : Choice) : ℚ :=
  ∑ r ∈ latentPopulation y, w y z r * if Y y z true r = b then 1 else 0

/-- The same pushforward with arbitrary real weights, covering every finite
probability distribution and every assignment mechanism on this support. -/
def observedRealLawWith (Y : PotentialOutcome) (w : Year → Bool → ℕ → ℝ)
    (y : Year) (z : PorchAssignment) (b : Choice) : ℝ :=
  ∑ r ∈ latentPopulation y, w y z r * if Y y z true r = b then 1 else 0

/-- Observed masses for the fixed independent design, at campaign present. -/
def observedLaw (Y : PotentialOutcome) : Year → Bool → Bool → ℚ :=
  observedLawWith Y jointMass

def Calibrated (Y : PotentialOutcome) : Prop :=
  ∀ y z, outcomeMean Y y z true = releasedFrequency y z

def overallCampaignEffect (Y : PotentialOutcome) : ℚ :=
  ∑ y ∈ years, yearMass y *
    (assignmentMass y false * campaignMean Y y false +
     assignmentMass y true * campaignMean Y y true)

/-- Identification among binary local models calibrated to the six supplied
frequencies and sharing the fixed independent design. -/
def CampaignIdentified : Prop :=
  ∀ U V : PotentialOutcome, Calibrated U → Calibrated V →
    observedLaw U = observedLaw V → ∀ y, campaignMean U y true = campaignMean V y true

end SAP.P035
