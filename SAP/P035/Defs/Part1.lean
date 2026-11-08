import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P035

/-! Exact inputs and the validator's hypothetical binary potential outcomes.
These definitions describe a nonidentification witness, not a fitted causal
model or a conclusion about the actual effect of the initiative. -/

/-- The three trial years. -/
inductive Year where
  | y2012 | y2014 | y2015
  deriving DecidableEq, Repr

def years : Finset Year := {Year.y2012, Year.y2014, Year.y2015}

/-- Assignment to the implemented Obama porch package (`true`) or the pooled
comparison package (`false`). -/
abbrev PorchAssignment := Bool

/-- Presence (`true`) or absence (`false`) of the initiative, a policy
counterfactual rather than a measured exposure. -/
abbrev Campaign := Bool

/-- Raisins (`true`) or candy (`false`). -/
abbrev Choice := Bool

def fruitValue (b : Choice) : ℚ := if b then 1 else 0

/-- Local binary potential outcomes. Other children's assignments are not
arguments, granting no interference. Observed choice evaluates this function
at the assigned porch and campaign present, granting consistency. All models
below use the same finite independent design defined in Part2. -/
abbrev PotentialOutcome := Year → PorchAssignment → Campaign → ℕ → Choice

/-- Enrolled arm sizes, including the one missing 2012 Obama outcome. -/
def enrolled (y : Year) (z : PorchAssignment) : ℕ :=
  match y, z with
  | .y2012, false => 69 | .y2012, true => 96
  | .y2014, false => 265 | .y2014, true => 157
  | .y2015, false => 444 | .y2015, true => 192

def completeCases (y : Year) (z : PorchAssignment) : ℕ :=
  match y, z with
  | .y2012, false => 69 | .y2012, true => 95
  | .y2014, false => 265 | .y2014, true => 157
  | .y2015, false => 444 | .y2015, true => 192

def fruitCounts (y : Year) (z : PorchAssignment) : ℕ :=
  match y, z with
  | .y2012, false => 14 | .y2012, true => 24
  | .y2014, false => 58 | .y2014, true => 37
  | .y2015, false => 113 | .y2015, true => 61

/-- Supplied complete-case frequencies; not unknown population probabilities. -/
def releasedFrequency (y : Year) (z : PorchAssignment) : ℚ :=
  (fruitCounts y z : ℚ) / (completeCases y z : ℚ)

def reducedDenominator (y : Year) (z : PorchAssignment) : ℕ :=
  completeCases y z / Nat.gcd (fruitCounts y z) (completeCases y z)

/-- Size of the hypothetical uniform latent population, not enrollment. -/
def latentSize : Year → ℕ
  | .y2012 => 6555 | .y2014 => 41605 | .y2015 => 7104

def threshold (y : Year) (z : PorchAssignment) : ℕ :=
  match y, z with
  | .y2012, false => 1330 | .y2012, true => 1656
  | .y2014, false => 9106 | .y2014, true => 9805
  | .y2015, false => 1808 | .y2015, true => 2257

def bit (b : Bool) : ℕ := if b then 1 else 0

/-- Direct-display world: the campaign does not enter the outcome formula. -/
def D : PotentialOutcome := fun y z _ r =>
  decide (r ≤ threshold y false + bit z * (threshold y true - threshold y false))

/-- Campaign-enabled world. The theorem includes threshold ordering, so
natural subtraction agrees with the intended threshold difference. -/
def C : PotentialOutcome := fun y z a r =>
  decide (r ≤ threshold y false + bit a * bit z *
    (threshold y true - threshold y false))

def latentPopulation (y : Year) : Finset ℕ := Finset.Icc 1 (latentSize y)

def uniformMean (y : Year) (f : ℕ → ℚ) : ℚ :=
  (∑ r ∈ latentPopulation y, f r) / (latentSize y : ℚ)

def outcomeMean (Y : PotentialOutcome) (y : Year) (z : PorchAssignment)
    (a : Campaign) : ℚ := uniformMean y (fun r => fruitValue (Y y z a r))

def successCount (Y : PotentialOutcome) (y : Year) (z : PorchAssignment) : ℕ :=
  ((latentPopulation y).filter (fun r => Y y z true r = true)).card

def campaignDifference (Y : PotentialOutcome) (y : Year)
    (z : PorchAssignment) (r : ℕ) : ℚ :=
  fruitValue (Y y z true r) - fruitValue (Y y z false r)

def campaignMean (Y : PotentialOutcome) (y : Year) (z : PorchAssignment) : ℚ :=
  uniformMean y (campaignDifference Y y z)

def exactEffect : Year → ℚ
  | .y2012 => 326 / 6555 | .y2014 => 699 / 41605 | .y2015 => 449 / 7104

end SAP.P035
