import Mathlib

/-!
Exact finite witness for P035-T1 and the mathematical clauses of the correction P035-T2.
These constructions are not potential-outcome definitions or
theorems printed in the paper. All expectations and laws below are rational
finite sums.
-/

namespace AronowAudit.P035

open Finset

/-- "2012 (n = 165) ... 2014 (n = 422) ... 2015 (n = 636)":
the three trial years, Methods, printed pp. 2--3/6. -/
inductive Year where
  | y2012 | y2014 | y2015
  deriving DecidableEq, Repr

/-- The three trial years, enumerated without any other years (Methods, pp. 2--3/6). -/
def years : Finset Year := {Year.y2012, Year.y2014, Year.y2015}

/-- "One side of the porch--denoted Obama ... The other side--denoted Comparison":
Methods, p. 3/6. `true` means the implemented Obama porch package; `false` means
the pooled Comparison package. This does not isolate a photograph component. -/
abbrev PorchAssignment := Bool

/-- `A=1` denotes presence of the Let's Move initiative and `A=0` its absence;
`true` is presence. This is a policy counterfactual, not a measured exposure
or a definition supplied by the paper. -/
abbrev Campaign := Bool

/-- "fruit (a box of raisins) or candy": Methods, p. 3/6. `true` is raisins;
`false` is candy, so every modeled potential outcome is binary. -/
abbrev Choice := Bool

/-- The numerical coding “1 means choosing raisins, 0 means candy” for the
choice described in Methods, p. 3/6. -/
def fruitValue (b : Choice) : ℚ := if b then 1 else 0

/-- A single child's binary potential choices `Y_y(z,a;r)`.
The latent child is `r`; there is no argument for other children's assignments (no interference). Observed choice is evaluation at the assigned
`z` and `a=true` (consistency). These assumptions are granted in the witness,
not claimed to have been verified for the actual queue assignment. -/
abbrev PotentialOutcome := Year → PorchAssignment → Campaign → ℕ → Choice

/-- Raw arm sizes, “Raw comparison N” and “Raw Obama N”.
The 2012 Obama size includes the one missing outcome (Methods, p. 3/6). -/
def enrolled (y : Year) (z : PorchAssignment) : ℕ :=
  match y, z with
  | .y2012, false => 69 | .y2012, true => 96
  | .y2014, false => 265 | .y2014, true => 157
  | .y2015, false => 444 | .y2015, true => 192

/-- "Complete comparison N" and "Complete Obama N".
The 2012 Obama denominator is 95 after excluding the missing choice. -/
def completeCases (y : Year) (z : PorchAssignment) : ℕ :=
  match y, z with
  | .y2012, false => 69 | .y2012, true => 95
  | .y2014, false => 265 | .y2014, true => 157
  | .y2015, false => 444 | .y2015, true => 192

/-- “Comparison fruit k” and “Obama fruit k”: the released fruit counts.
No comparison sub-arm allocation is used. -/
def fruitCounts (y : Year) (z : PorchAssignment) : ℕ :=
  match y, z with
  | .y2012, false => 14 | .y2012, true => 24
  | .y2014, false => 58 | .y2014, true => 37
  | .y2015, false => 113 | .y2015, true => 61

/-- “p0” and “p1”: the six released complete-case fruit frequencies.
They calibrate a hypothetical population; equating these frequencies with
actual unknown population probabilities is not assumed. -/
def releasedFrequency (y : Year) (z : PorchAssignment) : ℚ :=
  (fruitCounts y z : ℚ) / (completeCases y z : ℚ)

/-- The reduced denominator of `p_yz`, used in "L is the least common multiple
of the reduced denominators". -/
def reducedDenominator (y : Year) (z : PorchAssignment) : ℕ :=
  completeCases y z / Nat.gcd (fruitCounts y z) (completeCases y z)

/-- “R uniform on {1,...,L}”, with L=6555,41605,7104.
These are latent population sizes, not enrollment sizes. -/
def latentSize : Year → ℕ
  | .y2012 => 6555 | .y2014 => 41605 | .y2015 => 7104

/-- “t0=L p0” and “t1=L p1”: integer thresholds. -/
def threshold (y : Year) (z : PorchAssignment) : ℕ :=
  match y, z with
  | .y2012, false => 1330 | .y2012, true => 1656
  | .y2014, false => 9106 | .y2014, true => 9805
  | .y2015, false => 1808 | .y2015, true => 2257

/-- Binary numeric coding of `z` and `a` in the indicator formulas; its range is {0,1}. -/
def bit (b : Bool) : ℕ := if b then 1 else 0

/-- "D_y(z,a;r)=1{r <= t_y0 + z(t_y1-t_y0)}": the direct-display
world. It ignores campaign presence. -/
def D : PotentialOutcome := fun y z _ r =>
  decide (r ≤ threshold y false + bit z * (threshold y true - threshold y false))

/-- "C_y(z,a;r)=1{r <= t_y0 + az(t_y1-t_y0)}": the campaign-enabled
world. Natural subtraction equals the integer
difference here because all three `t_y1` exceed `t_y0`. -/
def C : PotentialOutcome := fun y z a r =>
  decide (r ≤ threshold y false + bit a * bit z *
    (threshold y true - threshold y false))

/-- The latent support "{1,...,L}"; children with
indices outside this finite set have no probability mass in the witness. -/
def latentPopulation (y : Year) : Finset ℕ := Icc 1 (latentSize y)

/-- Uniform latent expectation “R uniform on {1,...,L}”, represented by
a rational finite sum divided by L. -/
def uniformMean (y : Year) (f : ℕ → ℚ) : ℚ :=
  (∑ r ∈ latentPopulation y, f r) / (latentSize y : ℚ)

/-- The mean binary choice at fixed `(y,z,a)`. -/
def outcomeMean (Y : PotentialOutcome) (y : Year) (z : PorchAssignment)
    (a : Campaign) : ℚ := uniformMean y (fun r => fruitValue (Y y z a r))

/-- "Exactly t0 [or t1] of the L values ... yield outcome 1": the count
of raisins under the observed setting `A=1`. -/
def successCount (Y : PotentialOutcome) (y : Year) (z : PorchAssignment) : ℕ :=
  ((latentPopulation y).filter (fun r => Y y z true r = true)).card

/-- "Y(z,1;r)-Y(z,0;r)": the individual policy-counterfactual campaign
effect in numeric choice units. -/
def campaignDifference (Y : PotentialOutcome) (y : Year)
    (z : PorchAssignment) (r : ℕ) : ℚ :=
  fruitValue (Y y z true r) - fruitValue (Y y z false r)

/-- “E[Y(1,1;R)-Y(1,0;R)]”, and its analogue at comparison assignment,
as a uniform finite mean. -/
def campaignMean (Y : PotentialOutcome) (y : Year) (z : PorchAssignment) : ℚ :=
  uniformMean y (campaignDifference Y y z)

/-- The exact year-specific campaign effects in C: "326/6555, 699/41605,
449/7104". -/
def exactEffect : Year → ℚ
  | .y2012 => 326 / 6555 | .y2014 => 699 / 41605 | .y2015 => 449 / 7104

/-- “Year probabilities N_y/1223”: the illustrative population mixture;
this is not the paper's reported IPW estimand. -/
def yearMass (y : Year) : ℚ :=
  ((enrolled y false + enrolled y true : ℕ) : ℚ) / 1223

/-- Assignment probabilities equal to raw Obama N_y/N_y and their comparison
complements. Assignment is independent of R. -/
def assignmentMass (y : Year) (z : PorchAssignment) : ℚ :=
  (enrolled y z : ℚ) / ((enrolled y false + enrolled y true : ℕ) : ℚ)

/-- Uniform mass of each supported latent child.
All sums using this mass are restricted to `latentPopulation y`. -/
def latentMass (y : Year) : ℚ := 1 / (latentSize y : ℚ)

/-- The conditional joint mass of `(Z,R)` given year, under the independent
randomization in the witness. -/
def conditionalMass (y : Year) (z : PorchAssignment) (_r : ℕ) : ℚ :=
  assignmentMass y z / (latentSize y : ℚ)

/-- Joint mass of `(year,Z,R)` on the finite supports.
It uses the enrolled year and arm shares. -/
def jointMass (y : Year) (z : PorchAssignment) (r : ℕ) : ℚ :=
  yearMass y * conditionalMass y z r

/-- "The same law ... for any assignment mechanism": the pushforward law
of `(year,Z,observed choice)` under `A=1`.
`w` may be any weights on the finite support; equality for all such weights
includes every probability law and permits assignment to depend on R. -/
def observedLawWith (Y : PotentialOutcome) (w : Year → Bool → ℕ → ℚ)
    (y : Year) (z : PorchAssignment) (b : Choice) : ℚ :=
  ∑ r ∈ latentPopulation y, w y z r * if Y y z true r = b then 1 else 0

/-- The observed law under the explicit independent randomization witness.
Consistency is evaluation of `Y` at `(z,A=1)`. -/
def observedLaw (Y : PotentialOutcome) : Year → Bool → Bool → ℚ :=
  observedLawWith Y jointMass

/-- “Matches each of the six ... outcome frequencies exactly”: calibration
stated as conditional uniform means. -/
def Calibrated (Y : PotentialOutcome) : Prop :=
  ∀ y z, outcomeMean Y y z true = releasedFrequency y z

/-- “The overall campaign effect ... with year probabilities N_y/1223 and
assignment probabilities equal to raw Obama N_y/N_y”.
This average is an illustration, not the reported IPW effect. -/
def overallCampaignEffect (Y : PotentialOutcome) : ℚ :=
  ∑ y ∈ years, yearMass y *
    (assignmentMass y false * campaignMean Y y false +
     assignmentMass y true * campaignMean Y y true)

/-- Identification means that observationally identical allowed models
agree on the target causal quantity. All models here have binary, local
potential outcomes, with the same independent design and consistency.
Restricting to `Calibrated` models requires the observed six frequencies
in the target. -/
def CampaignIdentified : Prop :=
  ∀ U V : PotentialOutcome, Calibrated U → Calibrated V →
    observedLaw U = observedLaw V → ∀ y, campaignMean U y true = campaignMean V y true

/-- The latent sizes are the least common multiples of the reduced frequency
denominators, as specified in P035-T1. -/
theorem latent_sizes_are_lcm (y : Year) :
    latentSize y = Nat.lcm (reducedDenominator y false) (reducedDenominator y true) := by
  cases y <;> decide

/-- All three threshold pairs are ordered and within the nonempty latent
support; P035-T1. -/
theorem threshold_bounds (y : Year) :
    0 < latentSize y ∧ threshold y false ≤ threshold y true ∧
    threshold y true ≤ latentSize y := by
  cases y <;> norm_num [latentSize, threshold]

/-- Each integer threshold is exactly L times its released frequency;
P035-T1. -/
theorem threshold_calibration (y : Year) (z : Bool) :
    (threshold y z : ℚ) = (latentSize y : ℚ) * releasedFrequency y z := by
  cases y <;> cases z <;>
    norm_num [threshold, latentSize, releasedFrequency, fruitCounts, completeCases]

/-- A count of the initial segment is its threshold, avoiding enumeration
of latent children; finite counting lemma for P035-T1. -/
theorem initial_segment_card (L t : ℕ) (h : t ≤ L) :
    ((Icc 1 L).filter (fun r => r ≤ t)).card = t := by
  have heq : (Icc 1 L).filter (fun r => r ≤ t) = Icc 1 t := by
    ext r
    simp only [mem_filter, mem_Icc]
    omega
  rw [heq, Nat.card_Icc]
  omega

/-- The direct model's binary formula reduces to its arm-specific threshold;
P035-T1. -/
theorem D_threshold (y : Year) (z a : Bool) (r : ℕ) :
    D y z a r = decide (r ≤ threshold y z) := by
  cases y <;> cases z <;> simp [D, threshold, bit] <;> rfl

/-- Both models agree for every child and every assignment in the observed
setting A=1; P035-T1(i). -/
theorem observed_choices_equal (y : Year) (z : Bool) (r : ℕ) :
    C y z true r = D y z true r := by
  simp [C, D, bit]

/-- With the initiative absent, the campaign-enabled model always has the
comparison threshold; P035-T1(iv). -/
theorem C_absent (y : Year) (z : Bool) (r : ℕ) :
    C y z false r = D y false true r := by
  simp [C, D, bit]

/-- Exactly t_yz children choose raisins in D at A=1;
P035-T1(ii). -/
theorem D_success_count (y : Year) (z : Bool) :
    successCount D y z = threshold y z := by
  unfold successCount
  simp_rw [D_threshold, decide_eq_true_eq]
  apply initial_segment_card
  cases z
  · exact le_trans (threshold_bounds y).2.1 (threshold_bounds y).2.2
  · exact (threshold_bounds y).2.2

/-- The same exact count holds in C by pointwise observation equality;
P035-T1(i--ii). -/
theorem C_success_count (y : Year) (z : Bool) :
    successCount C y z = threshold y z := by
  simpa only [successCount, observed_choices_equal] using D_success_count y z

/-- For a binary choice the uniform mean is its success count divided by L;
finite lemma for P035-T1(ii). -/
theorem observed_mean_eq_count (Y : PotentialOutcome) (y : Year) (z : Bool) :
    outcomeMean Y y z true = (successCount Y y z : ℚ) / (latentSize y : ℚ) := by
  have hv (b : Bool) : fruitValue b = if b = true then (1 : ℚ) else 0 := by
    cases b <;> simp [fruitValue]
  unfold outcomeMean uniformMean successCount
  simp_rw [hv]
  rw [Finset.sum_boole]

/-- Counts/L reproduce all six released frequencies in both worlds;
P035-T1(ii). -/
theorem six_frequencies_calibrated : Calibrated D ∧ Calibrated C := by
  constructor <;> intro y z
  · rw [observed_mean_eq_count, D_success_count]
    cases y <;> cases z <;>
      norm_num [threshold, latentSize, releasedFrequency, fruitCounts, completeCases]
  · rw [observed_mean_eq_count, C_success_count]
    cases y <;> cases z <;>
      norm_num [threshold, latentSize, releasedFrequency, fruitCounts, completeCases]

/-- No child's choice in D changes when the campaign is removed, under either
porch assignment; P035-T1(iii). -/
theorem D_individual_campaign_zero (y : Year) (z : Bool) (r : ℕ) :
    campaignDifference D y z r = 0 := by
  simp [campaignDifference, D]

/-- At comparison assignment C also has zero campaign effect for every child;
P035-T1(iv). -/
theorem C_comparison_campaign_zero (y : Year) (r : ℕ) :
    campaignDifference C y false r = 0 := by
  simp [campaignDifference, C, bit]

/-- Finite expectation is linear for the campaign contrast;
P035-T1(iv). -/
theorem campaign_mean_sub (Y : PotentialOutcome) (y : Year) (z : Bool) :
    campaignMean Y y z = outcomeMean Y y z true - outcomeMean Y y z false := by
  simp [campaignMean, campaignDifference, outcomeMean, uniformMean,
    Finset.sum_sub_distrib, sub_div]

/-- D has zero mean campaign effect in every year and arm;
P035-T1(iii--iv). -/
theorem D_mean_campaign_zero (y : Year) (z : Bool) : campaignMean D y z = 0 := by
  simp [campaignMean, D_individual_campaign_zero, uniformMean]

/-- C has zero mean campaign effect in the comparison arm;
P035-T1(iv). -/
theorem C_comparison_mean_zero (y : Year) : campaignMean C y false = 0 := by
  simp [campaignMean, C_comparison_campaign_zero, uniformMean]

/-- The mean under absent campaign in C is the observed comparison mean,
regardless of assignment; finite lemma for P035-T1(iv). -/
theorem C_absent_mean (y : Year) (z : Bool) :
    outcomeMean C y z false = releasedFrequency y false := by
  simpa only [outcomeMean, C_absent] using six_frequencies_calibrated.1 y false

/-- The exact positive differences of the released arm frequencies;
P035-T1(iv). -/
theorem frequency_contrast (y : Year) :
    releasedFrequency y true - releasedFrequency y false = exactEffect y ∧
    exactEffect y = ((threshold y true - threshold y false : ℕ) : ℚ) /
      (latentSize y : ℚ) ∧ 0 < exactEffect y := by
  cases y <;> norm_num [releasedFrequency, fruitCounts, completeCases,
    exactEffect, threshold, latentSize]

/-- In C the mean campaign effect at the Obama condition equals the entire
positive porch contrast, with the three specified exact values;
P035-T1(iv) and P035-T2(b). -/
theorem C_obama_campaign_effect (y : Year) :
    campaignMean C y true = exactEffect y ∧
    campaignMean C y true = releasedFrequency y true - releasedFrequency y false ∧
    0 < campaignMean C y true := by
  have hm : campaignMean C y true = releasedFrequency y true - releasedFrequency y false := by
    rw [campaign_mean_sub, six_frequencies_calibrated.2, C_absent_mean]
  rw [hm, (frequency_contrast y).1]
  exact ⟨rfl, rfl, (frequency_contrast y).2.2⟩

/-- D has a strictly positive causal contrast between the implemented porch
conditions in every year despite its zero campaign effect; P035-T1(v).
These are potential-outcome population means in the witness, not a claim that the sample estimates equal the actual effects. -/
theorem D_porch_contrast_positive (y : Year) :
    outcomeMean D y true true - outcomeMean D y false true = exactEffect y ∧
    0 < outcomeMean D y true true - outcomeMean D y false true := by
  rw [six_frequencies_calibrated.1, six_frequencies_calibrated.1,
    (frequency_contrast y).1]
  exact ⟨rfl, (frequency_contrast y).2.2⟩

/-- The raw shares form positive year and arm distributions;
P035-T1's randomized finite witness. -/
theorem design_masses_valid :
    (∀ y z, 0 < assignmentMass y z) ∧
    (∀ y, assignmentMass y false + assignmentMass y true = 1) ∧
    (∀ y, 0 < yearMass y) ∧ (∑ y ∈ years, yearMass y) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y z; cases y <;> cases z <;> norm_num [assignmentMass, enrolled]
  · intro y; cases y <;> norm_num [assignmentMass, enrolled]
  · intro y; cases y <;> norm_num [yearMass, enrolled]
  · norm_num [years, yearMass, enrolled]

/-- Summing the conditional joint mass over R gives the assignment mass;
P035-T1's finite randomization. -/
theorem assignment_marginal (y : Year) (z : Bool) :
    (∑ r ∈ latentPopulation y, conditionalMass y z r) = assignmentMass y z := by
  have hL : (latentSize y : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (threshold_bounds y).1)
  calc
    (∑ r ∈ latentPopulation y, conditionalMass y z r) =
        (latentSize y : ℚ) * (assignmentMass y z / (latentSize y : ℚ)) := by
      simp [conditionalMass, latentPopulation, Nat.card_Icc, nsmul_eq_mul]
    _ = assignmentMass y z := by field_simp

/-- Summing the conditional joint mass over Z gives uniform mass on R;
P035-T1's finite randomization. -/
theorem latent_marginal (y : Year) (r : ℕ) :
    conditionalMass y false r + conditionalMass y true r = latentMass y := by
  unfold conditionalMass latentMass
  rw [← add_div, design_masses_valid.2.1 y]

/-- Within year, the joint mass factors as the product of its two marginals,
proving randomized assignment independent of R; P035-T1. -/
theorem randomized_independently (y : Year) (z : Bool) (r : ℕ) :
    conditionalMass y z r =
      (∑ s ∈ latentPopulation y, conditionalMass y z s) *
      (conditionalMass y false r + conditionalMass y true r) := by
  rw [assignment_marginal, latent_marginal]
  simp [conditionalMass, latentMass, div_eq_mul_inv]

/-- The joint masses are nonnegative and normalize to one on their finite
support; P035-T1's explicit probability space. -/
theorem joint_mass_is_probability :
    (∀ y z r, 0 ≤ jointMass y z r) ∧
    (∑ y ∈ years, ((∑ r ∈ latentPopulation y, jointMass y false r) +
      (∑ r ∈ latentPopulation y, jointMass y true r))) = 1 := by
  constructor
  · intro y z r
    unfold jointMass conditionalMass
    apply mul_nonneg (le_of_lt (design_masses_valid.2.2.1 y))
    exact div_nonneg (le_of_lt (design_masses_valid.1 y z)) (Nat.cast_nonneg _)
  · simp only [jointMass, ← Finset.mul_sum, assignment_marginal]
    simp_rw [← mul_add, design_masses_valid.2.1, mul_one]
    exact design_masses_valid.2.2.2


/-- D and C give the same entire observed law for every weighting of years,
assignments and latent children; P035-T1(v).
No independence restriction is needed for this equality. -/
theorem same_observed_law_any_mechanism (w : Year → Bool → ℕ → ℚ) :
    observedLawWith D w = observedLawWith C w := by
  funext y z b
  unfold observedLawWith
  simp_rw [observed_choices_equal]

/-- In particular the independent randomized witness has the same observed
law in both worlds; P035-T1(v). -/
theorem same_observed_law : observedLaw D = observedLaw C :=
  same_observed_law_any_mechanism jointMass

/-- The campaign effect averaged over years and raw arm shares is zero in D;
P035-T1(iv). -/
theorem D_overall_campaign_zero : overallCampaignEffect D = 0 := by
  simp [overallCampaignEffect, D_mean_campaign_zero]

/-- The raw-share illustration in C equals exactly 83755728/5240292055 and
is strictly positive; P035-T1(iv). -/
theorem C_overall_campaign_positive :
    overallCampaignEffect C =
      (96 / 1223 : ℚ) * (326 / 6555) + (157 / 1223) * (699 / 41605) +
        (192 / 1223) * (449 / 7104) ∧
    overallCampaignEffect C = (83755728 / 5240292055 : ℚ) ∧
    0 < overallCampaignEffect C := by
  have hm (y : Year) : campaignMean C y true = exactEffect y :=
    (C_obama_campaign_effect y).1
  norm_num [overallCampaignEffect, C_comparison_mean_zero, hm, years,
    yearMass, assignmentMass, enrolled, exactEffect]

/-- Even among models calibrated to all six frequencies, campaign effects
are not determined by the observed law; P035-T1(v) and P035-T2(a). -/
theorem campaign_not_identified : ¬ CampaignIdentified := by
  intro h
  have heq := h D C six_frequencies_calibrated.1 six_frequencies_calibrated.2
    same_observed_law Year.y2012
  rw [D_mean_campaign_zero] at heq
  have hpos := (C_obama_campaign_effect Year.y2012).2.2
  linarith

/-- There is no function of the observed law giving the raw-share overall
campaign effect for all calibrated models; P035-T1(v). -/
theorem overall_effect_not_function_of_law :
    ¬ ∃ f : (Year → Bool → Bool → ℚ) → ℚ,
      ∀ Y : PotentialOutcome, Calibrated Y → f (observedLaw Y) = overallCampaignEffect Y := by
  rintro ⟨f, hf⟩
  have hD := hf D six_frequencies_calibrated.1
  have hC := hf C six_frequencies_calibrated.2
  rw [same_observed_law, D_overall_campaign_zero] at hD
  have hpos := C_overall_campaign_positive.2.2
  linarith

/-- The complete concrete witness: ordered LCM populations, exact six-count
calibration, independent valid randomization, identical observed choices/laws,
zero campaign effect in D, positive specified effects in C, and nonidentification.
This is P035-T1(i--v), refuting the inference behind
the Abstract Conclusions attribution (printed p. 2/6), not its real-world truth. -/
theorem campaign_nonidentification_counterexample :
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
    (¬ CampaignIdentified) ∧
    (¬ ∃ f : (Year → Bool → Bool → ℚ) → ℚ,
      ∀ Y : PotentialOutcome, Calibrated Y → f (observedLaw Y) = overallCampaignEffect Y) := by
  refine ⟨latent_sizes_are_lcm, threshold_bounds, threshold_calibration,
    randomized_independently, joint_mass_is_probability, observed_choices_equal, ?_,
    six_frequencies_calibrated, D_porch_contrast_positive, D_individual_campaign_zero,
    C_comparison_campaign_zero,
    ?_, D_overall_campaign_zero, C_overall_campaign_positive,
    same_observed_law_any_mechanism, campaign_not_identified,
    overall_effect_not_function_of_law⟩
  · intro y z
    refine ⟨D_success_count y z, C_success_count y z, ?_⟩
    rw [← observed_mean_eq_count]
    exact six_frequencies_calibrated.1 y z
  · intro y
    exact ⟨(C_obama_campaign_effect y).1, (frequency_contrast y).2.1,
      (C_obama_campaign_effect y).2.2⟩

/-- “Campaign reinforcement is a possible explanation; the experiment does
not establish that the initiative or its health message caused the difference.”
P035-T2(a--b): the mathematical clauses of the correction to Abstract Conclusions
(p. 2/6) and “the treatment effect of her campaign” (p. 5/6).
Two calibrated, observationally identical local binary models have zero versus
positive campaign effects; in the latter the whole porch contrast is enabled
by the campaign and disappears when it is absent. The empirical first
sentence of the correction is not a theorem. -/
theorem corrected_campaign_interpretation :
    (∃ U V : PotentialOutcome,
      Calibrated U ∧ Calibrated V ∧ observedLaw U = observedLaw V ∧
      (∀ y z r, campaignDifference U y z r = 0) ∧
      (∀ y, 0 < campaignMean V y true ∧
        campaignMean V y true = releasedFrequency y true - releasedFrequency y false) ∧
      (∀ y r, V y true false r = V y false false r)) ∧
    ¬ CampaignIdentified := by
  refine ⟨⟨D, C, six_frequencies_calibrated.1, six_frequencies_calibrated.2,
    same_observed_law, D_individual_campaign_zero, ?_, ?_⟩, campaign_not_identified⟩
  · intro y
    exact ⟨(C_obama_campaign_effect y).2.2, (C_obama_campaign_effect y).2.1⟩
  · intro y r
    rw [C_absent, C_absent]

end AronowAudit.P035

