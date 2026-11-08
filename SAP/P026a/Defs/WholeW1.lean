import Mathlib
import SAP.P026a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section
open Classical

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

/-- Ordinary division as a partial operation: a zero denominator has no value. -/
def w1PartialRatio (x p : ℚ) : Option ℚ := if p = 0 then none else some (x / p)

/-- Domain of literal equation [34], before any zero-pair omission convention. -/
def w1Literal34Domain {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (D : AssignmentDesign Ω I ℚ) : Prop :=
  (∀ i, inclusion D true i ≠ 0 ∧ inclusion D false i ≠ 0) ∧
  ∀ i j, i ≠ j → jointInclusion D true false i j ≠ 0

/-- The three groups 00, 01, 11 of the first two indicators in the six-cluster witness. -/
def w1SixGroup (w : Fin 14) : Fin 3 :=
  if asymmetricSixLaw.treatment w 0 then 2 else
    if asymmetricSixLaw.treatment w 1 then 1 else 0

/-- Exact missing support certificates for counterexample B of T1.
The minima are attained, and the disagreement minimizers are the two ordered versions
of the printed unordered pair {1,2}. -/
def w1SixSupportFacts : Prop :=
  (∀ i : Fin 6, inclusion asymmetricSixLaw true i =
      (![2/7,5/7,1/2,1/2,1/2,1/2] : Fin 6 → ℚ) i ∧
    inclusion asymmetricSixLaw false i =
      (![5/7,2/7,1/2,1/2,1/2,1/2] : Fin 6 → ℚ) i) ∧
  (∀ i j : Fin 6, i ≠ j →
    (1/14 : ℚ) ≤ jointInclusion asymmetricSixLaw true true i j ∧
    (1/14 : ℚ) ≤ jointInclusion asymmetricSixLaw false false i j ∧
    (3/7 : ℚ) ≤ disagreementProbability asymmetricSixLaw i j ∧
    (disagreementProbability asymmetricSixLaw i j = 3/7 ↔
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))) ∧
  (∃ i j : Fin 6, i ≠ j ∧ jointInclusion asymmetricSixLaw true true i j = 1/14) ∧
  (∃ i j : Fin 6, i ≠ j ∧ jointInclusion asymmetricSixLaw false false i j = 1/14)

/-- Pointwise values and group sizes omitted from the restricted six-cluster witness. -/
def w1SixValueFacts : Prop :=
  (∀ g : Fin 3, ((univ : Finset (Fin 14)).filter (fun w => w1SixGroup w = g)).card =
    (![4,6,4] : Fin 3 → ℕ) g) ∧
  (∀ w : Fin 14,
    htContrast asymmetricSixLaw 6 (fun _ => 1) (fun _ => 1) w =
      (![-3/20,0,3/20] : Fin 3 → ℚ) (w1SixGroup w) ∧
    printedVarianceEstimate asymmetricSixLaw 6 (fun _ => 1) (fun _ => 1) w =
      (![-619/3600,7/54,-619/3600] : Fin 3 → ℚ) (w1SixGroup w)) ∧
  mean asymmetricSixLaw (htContrast asymmetricSixLaw 6 (fun _ => 1) (fun _ => 1)) = 0

/-- P026-T9; Appendix E, p. 152 (PDF p. 18).
The printed claim is false: for four singleton clusters with two treated uniformly,
and sharp-null outcomes (1,2,4,7), the literal Appendix E display has the six values
(-68,-52,2,-62,-20,-52) and expectation -42. Equation [34] has values
(-37,-25,-22,-22,-25,-37) and expectation -28, equal to the true covariance and
its population bound; the true treatment-total variance and its population bound
are both 28. Every marginal is 1/2 and all distinct-cluster joint probabilities
are positive (TT=CC=1/6, TC=1/3). Thus the printed display is unbiased for neither
of the quantities named in the text and on its left side. Usual measure-theoretic
conditions are assumed and hold automatically on this finite probability space. -/
def T9WholeStatement : Prop :=
  T9Statement ∧
  (∀ i : Fin 4, inclusion twoOfFourLaw true i = 1/2 ∧ inclusion twoOfFourLaw false i = 1/2) ∧
  (∀ w : Fin 6, covarianceWithZeroOmission twoOfFourLaw appendixNullOutcomes appendixNullOutcomes w =
    (![-37,-25,-22,-22,-25,-37] : Fin 6 → ℚ) w) ∧
  armPopulationBound twoOfFourLaw true appendixNullOutcomes = 28 ∧
  mean twoOfFourLaw (appendixDisplay twoOfFourLaw appendixNullOutcomes appendixNullOutcomes) ≠
    populationCovarianceBound twoOfFourLaw appendixNullOutcomes appendixNullOutcomes ∧
  mean twoOfFourLaw (appendixDisplay twoOfFourLaw appendixNullOutcomes appendixNullOutcomes) ≠
    armPopulationBound twoOfFourLaw true appendixNullOutcomes

/-- P026-T1; pp. 145-147 (PDF pp. 11-13).
The printed claim is false: the uniform sharp-null designs on 00,01,11 and on the
fourteen six-bit allocations with three treated and T1 ≤ T2 satisfy positive
marginals, positive same-arm joints and distinct cluster indicators, but have
Pr(T1=1,T2=0)=0. Literal equation [34] contains 0/0 and is outside its domain.
For the two-cluster design the marginals are (1/3,2/3) and (2/3,1/3), both
same-arm joints and disagreement are 1/3, HT=(-9/4,0,9/4), and [35]=
(57/16,3/2,57/16). Its true variance is 27/8, the expected [35] is 23/8
and the bias is -1/2; [34] with the unavailable term omitted is always -9/4,
exceeding the true covariance -13/4 by 1. For the six-cluster design the treatment
marginals are (2/7,5/7,1/2,1/2,1/2,1/2), the same-arm minimum is 1/14 and the
disagreement minimum is 3/7 at {1,2}. The 00,01,11 groups have sizes 4,6,4,
HT values -3/20,0,3/20 and [35] values -619/3600,7/54,-619/3600. The true
variance is 9/700, the expected [35] is -269/6300 and the bias is -1/18;
the covariance is 27/175 and the zero-omitted [34] has expectation 202/175.
Both covariance biases are +1. These facts refute the support deduction,
conservativeness and the stated sharp-null equalities. Usual measure-theoretic
conditions are assumed and hold automatically for these finite laws. -/
def T1WholeStatement : Prop :=
  T1Statement ∧
  (∀ i : Fin 2, inclusion asymmetricPairLaw true i = (![1/3,2/3] : Fin 2 → ℚ) i ∧
    inclusion asymmetricPairLaw false i = (![2/3,1/3] : Fin 2 → ℚ) i) ∧
  (∀ i j : Fin 2, i ≠ j → disagreementProbability asymmetricPairLaw i j = 1/3 ∧
    jointInclusion asymmetricPairLaw true true i j = 1/3 ∧
    jointInclusion asymmetricPairLaw false false i j = 1/3) ∧
  (∀ w : Fin 3, covarianceWithZeroOmission asymmetricPairLaw (fun _ => 1) (fun _ => 1) w = -9/4) ∧
  (¬ w1Literal34Domain asymmetricPairLaw) ∧
  (∀ w : Fin 3, w1PartialRatio
    (armIndicator asymmetricPairLaw true w 0 * armIndicator asymmetricPairLaw false w 1)
    (jointInclusion asymmetricPairLaw true false 0 1) = none) ∧
  w1SixSupportFacts ∧ w1SixValueFacts ∧
  (¬ w1Literal34Domain asymmetricSixLaw) ∧
  (∀ w : Fin 14, armIndicator asymmetricSixLaw true w 0 * armIndicator asymmetricSixLaw false w 1 = 0 ∧
    w1PartialRatio
      (armIndicator asymmetricSixLaw true w 0 * armIndicator asymmetricSixLaw false w 1)
      (jointInclusion asymmetricSixLaw true false 0 1) = none) ∧
  averageEffect 2 (fun _ : Fin 2 => (1 : ℚ)) (fun _ => 1) = 0 ∧
  averageEffect 6 (fun _ : Fin 6 => (1 : ℚ)) (fun _ => 1) = 0 ∧
  mean asymmetricPairLaw (printedVarianceEstimate asymmetricPairLaw 2 (fun _ => 1) (fun _ => 1)) -
    designVariance asymmetricPairLaw (htContrast asymmetricPairLaw 2 (fun _ => 1) (fun _ => 1)) = -1/2 ∧
  mean asymmetricSixLaw (printedVarianceEstimate asymmetricSixLaw 6 (fun _ => 1) (fun _ => 1)) -
    designVariance asymmetricSixLaw (htContrast asymmetricSixLaw 6 (fun _ => 1) (fun _ => 1)) = -1/18 ∧
  mean asymmetricPairLaw (covarianceWithZeroOmission asymmetricPairLaw (fun _ => 1) (fun _ => 1)) -
    designCovariance asymmetricPairLaw (htSum asymmetricPairLaw true (fun _ => 1))
      (htSum asymmetricPairLaw false (fun _ => 1)) = 1 ∧
  mean asymmetricSixLaw (covarianceWithZeroOmission asymmetricSixLaw (fun _ => 1) (fun _ => 1)) -
    designCovariance asymmetricSixLaw (htSum asymmetricSixLaw true (fun _ => 1))
      (htSum asymmetricSixLaw false (fun _ => 1)) = 1

/-- The entire set of outcomes whose individual assignment is independent of unit i. -/
def w1XorFittingSet (i : Fin 6) : Finset (Fin 6) :=
  if i.val < 2 then {2,3,4,5} else if i.val < 4 then {0,1,4,5} else {0,1,2,3}

/-- First outcome used by the six-unit nonlinear fit. -/
def w1XorInputA (i : Fin 6) : Fin 6 := if i.val < 2 then 2 else 0
/-- Second outcome used by the six-unit nonlinear fit. -/
def w1XorInputB (i : Fin 6) : Fin 6 := if i.val < 4 then 4 else 2

/-- P026-T4; p. 142 (PDF p. 8).
The printed claim is false: pairwise assignment independence does not pass through
an arbitrary nonlinear fit of several outcomes. In the six-unit complementary-XOR
design, independence holds exactly between different complementary pairs; the full
fitting sets are {3,4,5,6}, {1,2,5,6}, {1,2,3,4} for the three pairs. Each stated
fit uses two outcomes in its permitted set and equals its own treatment indicator.
The joint event that treatment and the fit are both one has probability 1/2,
while the product of their probabilities is 1/4, and their covariance is 1/4.
The generalized totals are both 3, the generalized ATE is always zero, and
HT=Delta=1. Its bias -1 agrees with [19]. In the three-unit XOR design all
distinct coordinates are independent with marginals 1/2; fitting the XOR of
the other outcomes again gives generalized ATE zero and bias -1. The alternative
product fit has covariance -1/8, expectation 7/6 and bias +1/6. All potential
outcomes and covariates are fixed as specified in the witness definitions.
Usual measure-theoretic conditions are assumed and automatic on these finite laws. -/
def T4WholeStatement : Prop :=
  T4Statement ∧
  (∀ i j : Fin 6,
    finiteIndependent xorSixLaw (fun w => xorSixLaw.treatment w i)
      (fun w => xorSixLaw.treatment w j) ↔ i.val / 2 ≠ j.val / 2) ∧
  (∀ i : Fin 6,
    (univ.filter (fun j => finiteIndependent xorSixLaw (fun w => xorSixLaw.treatment w i)
      (fun w => xorSixLaw.treatment w j))) = w1XorFittingSet i) ∧
  (∀ i : Fin 6, w1XorInputA i ∈ w1XorFittingSet i ∧ w1XorInputB i ∈ w1XorFittingSet i ∧
    ∀ w : Fin 4, xorSixFit w i =
      (if i.val % 2 = 0 then id else fun x => 1-x)
        (xorFitPolynomial (response xorSixLaw (fun _ => 1) (fun _ => 0) w (w1XorInputA i))
          (response xorSixLaw (fun _ => 1) (fun _ => 0) w (w1XorInputB i)))) ∧
  (∀ i : Fin 6,
    mean xorSixLaw (fun w => if xorSixLaw.treatment w i = true ∧ xorSixFit w i = 1 then 1 else 0) = 1/2 ∧
    mean xorSixLaw (fun w => if xorSixLaw.treatment w i = true then 1 else 0) *
      mean xorSixLaw (fun w => if xorSixFit w i = 1 then 1 else 0) = 1/4 ∧
    ¬ finiteIndependent xorSixLaw (fun w => xorSixLaw.treatment w i) (fun w => xorSixFit w i)) ∧
  mean xorSixLaw (adjustedContrast xorSixLaw 6 (fun _ => 1) (fun _ => 0) xorSixFit) -
    averageEffect 6 (fun _ : Fin 6 => (1 : ℚ)) (fun _ => 0) =
      -(∑ i : Fin 6, designCovariance xorSixLaw (fun w => armIndicator xorSixLaw true w i)
        (fun w => xorSixFit w i) *
          (1 / inclusion xorSixLaw true i + 1 / inclusion xorSixLaw false i)) / 6 ∧
  (∀ i : Fin 3, inclusion xorThreeLaw true i = 1/2 ∧ inclusion xorThreeLaw false i = 1/2) ∧
  (∀ w : Fin 4, adjustedContrast xorThreeLaw 3 (fun _ => 1) (fun _ => 0) xorThreeFit w = 0) ∧
  mean xorThreeLaw (adjustedContrast xorThreeLaw 3 (fun _ => 1) (fun _ => 0) xorThreeFit) -
    averageEffect 3 (fun _ : Fin 3 => (1 : ℚ)) (fun _ => 0) = -1 ∧
  mean xorThreeLaw (adjustedContrast xorThreeLaw 3 (fun _ => 1) (fun _ => 0) productFit) -
    averageEffect 3 (fun _ : Fin 3 => (1 : ℚ)) (fun _ => 0) = 1/6

/-- Deterministic outcome vector as a function of a fitting assignment vector. -/
def w1OutcomeMap {I : Type*} (J : Finset I) (x z : I → ℝ) (t : ↥J → Bool) : ↥J → ℝ :=
  fun j => if t j then x j else z j

/-- P026-T5; p. 142 (PDF p. 8).
Under the usual measure-theoretic conditions, independence of each focal treatment
from the whole assignment vector used by its fit, or more weakly from the whole
observed-outcome vector, passes through deterministic fitting and prediction and
gives zero covariance. If either premise holds for each unit, allowing a different
choice for each unit, both generalized totals and the ATE are unbiased. The fitting
prediction factors explicitly through the fitting assignment vector; the scalar
footnote follows for one outcome. A three-unit nonlinear fitting witness shows
that the scalar argument cannot replace vector independence in general. Pairwise independence suffices for additive
predictions with fixed coefficients, with the stated covariance expansion.
Mutually independent units justify leave-one-out fits, and independent block
vectors justify fitting on other blocks. The nonempty unit type is the guard for
the ATE denominator; finite assignment spaces make all measurability and moment
conditions automatic. Parameter fitting and fixed covariates can be absorbed in
the arbitrary deterministic real-valued map G in the unbiasedness clause. -/
def T5WholeStatement : Prop :=
  T5Statement.{u1,u2,u3,u4,u5,u6,u7,u8,u9} ∧
  (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitLaw I)
    (x z : I → ℝ) (J : I → Finset I) (G : ∀ i, (↥(J i) → ℝ) → ℝ),
    (∀ i, finiteIndependent E.assignmentDesign (fun w => w i) (fittingIndicators E.assignmentDesign (J i)) ∨
      finiteIndependent E.assignmentDesign (fun w => w i) (fittingResponses E.assignmentDesign (J i) x z)) →
    let f := fun w i => G i (fittingResponses E.assignmentDesign (J i) x z w)
    mean E.assignmentDesign (adjustedSum E.assignmentDesign true x f) = fixedTotal x ∧
    mean E.assignmentDesign (adjustedSum E.assignmentDesign false z f) = fixedTotal z ∧
    mean E.assignmentDesign (adjustedContrast E.assignmentDesign (Fintype.card I) x z f) =
      averageEffect (Fintype.card I) x z) ∧
  (∀ {I Θ : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitLaw I)
    (i : I) (J : Finset I) (x z : I → ℝ) (G : (↥J → ℝ) → Θ) (P : Θ → ℝ),
    let F := fun t => P (G (w1OutcomeMap J x z t))
    (∀ w, P (G (fittingResponses E.assignmentDesign J x z w)) = F (fittingIndicators E.assignmentDesign J w)) ∧
    (finiteIndependent E.assignmentDesign (fun w => w i) (fittingIndicators E.assignmentDesign J) →
      finiteIndependent E.assignmentDesign (fun w => w i) (fun w => F (fittingIndicators E.assignmentDesign J w)) ∧
      designCovariance E.assignmentDesign (fun w => armIndicator E.assignmentDesign true w i)
        (fun w => F (fittingIndicators E.assignmentDesign J w)) = 0)) ∧
  (∀ {I Θ : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitLaw I)
    (i j : I) (x z : I → ℝ) (G : ℝ → Θ) (P : Θ → ℝ),
    finiteIndependent E.assignmentDesign (fun w => w i) (fun w => w j) →
      finiteIndependent E.assignmentDesign (fun w => w i) (fun w => G (response E.assignmentDesign x z w j)) ∧
      finiteIndependent E.assignmentDesign (fun w => w i) (fun w => P (G (response E.assignmentDesign x z w j))) ∧
      designCovariance E.assignmentDesign (fun w => armIndicator E.assignmentDesign true w i)
        (fun w => P (G (response E.assignmentDesign x z w j))) = 0) ∧
  (∃ (D : AssignmentDesign (Fin 4) (Fin 3) ℝ) (J : Finset (Fin 3))
      (G : (↥J → ℝ) → ℝ),
    isProbability D ∧ hasPositiveMarginals D ∧
    (∀ j ∈ J, finiteIndependent D (fun w => D.treatment w 0) (fun w => D.treatment w j)) ∧
    designCovariance D (fun w => armIndicator D true w 0)
      (fun w => G (fittingResponses D J (fun _ => 1) (fun _ => 0) w)) ≠ 0)

/-- Finite real linear prediction, with unconstrained real coefficients. -/
def w1Predict {ι κ : Type*} [Fintype κ] (A : ι → κ → ℝ) (β : κ → ℝ) (i : ι) : ℝ :=
  ∑ j, A i j * β j
/-- The actual sum of squared errors. -/
def w1Loss {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (y : ι → ℝ) (β : κ → ℝ) : ℝ :=
  ∑ i, (y i - w1Predict A β i)^2
/-- Global least-squares minimization over all real coefficient vectors. -/
def w1Minimizes {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (y : ι → ℝ) (β : κ → ℝ) : Prop :=
  ∀ γ, w1Loss A y β ≤ w1Loss A y γ
/-- Full column rank, expressed without an inverse or a choice of solution. -/
def w1FullRank {ι κ : Type*} [Fintype κ] (A : ι → κ → ℝ) : Prop :=
  ∀ β, (∀ i, w1Predict A β i = 0) → β = 0
/-- Finite normal equations. -/
def w1Normal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (y : ι → ℝ) (β : κ → ℝ) : Prop :=
  ∀ j, ∑ i, A i j * (y i - w1Predict A β i) = 0

/-- Units of block 1 (false) or block 2 (true), preserving all observations. -/
def w1BlockUnits (b : Bool) : Finset (Fin 16) :=
  univ.filter (fun i => if b then 6 ≤ i.val else i.val < 6)
/-- Intercept and covariate design within one block. -/
def w1BlockDesign (b : Bool) (i : ↥(w1BlockUnits b)) : Fin 2 → ℝ :=
  ![1, (paperTableX i : ℝ)]
/-- Outcome vector in the same block. -/
def w1BlockY (b : Bool) (i : ↥(w1BlockUnits b)) : ℝ := (paperTableY i : ℝ)
/-- The coefficients fitted in block b, and used to predict the opposite block. -/
def w1BlockCoefficients (b : Bool) : Fin 2 → ℝ :=
  if b then ![1/4,1/8] else ![70/93,1/31]
/-- The actual FE design columns (intercept, treatment, block-2 indicator, X). -/
def w1FeDesign (w : Fin 6 × Fin 15) (i : Fin 16) : Fin 4 → ℝ :=
  ![1, ((armIndicator paperTableUnitDesign true w i : ℚ) : ℝ),
    (if i.val < 6 then 0 else 1), (paperTableX i : ℝ)]
/-- Explicit real FE coefficient vector in the order (intercept,T,block2,X). -/
def w1FeCoefficients (w : Fin 6 × Fin 15) : Fin 4 → ℝ :=
  let a := (5/6 : ℚ) - paperFeEstimate w * paperTableTreatmentMean w false - paperFeXCoefficient w * (5/2)
  let c := (3/5 : ℚ) - paperFeEstimate w * paperTableTreatmentMean w true - paperFeXCoefficient w * (14/5)
  ![(a : ℝ), (paperFeEstimate w : ℝ), ((c-a : ℚ) : ℝ), (paperFeXCoefficient w : ℝ)]
/-- Unit-level generalized ATE of equations [13]-[16] for the fitted prediction. -/
def w1LinearG (w : Fin 6 × Fin 15) : ℚ :=
  adjustedContrast paperTableUnitDesign 16 paperTableY paperTableY
    (fun _ => paperTableLinearPrediction) w
/-- Equation [35] on the actual residual cluster totals, with N=16. -/
def w1LinearV (w : Fin 6 × Fin 15) : ℚ :=
  printedVarianceEstimate paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual w
/-- Root mean squared error under a finite rational assignment law, embedded in ℝ. -/
def w1RMSE {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (D : AssignmentDesign Ω I ℚ) (f : Ω → ℚ) (θ : ℚ) : ℝ :=
  Real.sqrt ((mean D (fun w => (f w-θ)^2) : ℚ) : ℝ)
/-- Numerical approximation with an explicit strict error bound of 0.00000005. -/
def w1Approx7 (x c : ℝ) : Prop := |x-c| < 1/20000000

/-- P026-T6; Table 2, p. 149 (PDF p. 15); Table 1, p. 147 (PDF p. 13);
Section 7.1, p. 148 (PDF p. 14).
The printed claim is false: for the printed sixteen-unit population and its ninety
uniform allocations, the unique real OLS fits within blocks 2 and 1 are respectively
1/4+X/8 and 70/93+X/31. Opposite-block predictions have residual cluster totals
(1,7/8,1/4,-1/2,-15/31,19/93,1/3,-76/93,-76/93,-79/93).
The actual generalized estimator G has mean and bias zero, variance and expected
residual variance estimate 38307/634880 (approximately .0603374), and SE=RMSE
approximately .2456367. The residual variance estimate is unbiased and has variance
2400328658503/15687787688755200 and SE=RMSE approximately .0123696. The strict
rounding refutations for .026, .162 and .007 follow. For every allocation the OLS
regression on (1,T,block2,X) has a unique real minimizer; its treatment coefficient
is the specified residualized FE formula and both projection denominators are
positive. Its mean is approximately -.0139874, its variance .0777347, and its SE
.2788094, with the stated broad intervals and rounding refutations of -.012,
.036 and .191. Every approximation has error less than .00000005. Usual
measure-theoretic conditions are assumed and automatic for this finite law. -/
def T6WholeStatement : Prop :=
  T6Statement ∧
  isProbability paperTableDesign ∧ hasPositiveMarginals paperTableDesign ∧ directedSupport paperTableDesign ∧
  (∀ i j : Fin 10, i ≠ j → 0 < jointInclusion paperTableDesign true true i j ∧
    0 < jointInclusion paperTableDesign false false i j) ∧
  averageEffect 16 paperTableY paperTableY = 0 ∧
  (∀ b : Bool, ∀ β : Fin 2 → ℝ,
    w1Minimizes (w1BlockDesign b) (w1BlockY b) β ↔ β = w1BlockCoefficients b) ∧
  (∀ w : Fin 6 × Fin 15,
    w1LinearG w = htContrast paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual w) ∧
  (mean paperTableDesign w1LinearG = 0 ∧
    designVariance paperTableDesign w1LinearG = 38307/634880 ∧
    mean paperTableDesign w1LinearV = 38307/634880 ∧
    designVariance paperTableDesign w1LinearV = 2400328658503/15687787688755200) ∧
  mean paperTableDesign w1LinearG - averageEffect 16 paperTableY paperTableY = 0 ∧
  mean paperTableDesign w1LinearV - designVariance paperTableDesign w1LinearG = 0 ∧
  w1RMSE paperTableDesign w1LinearG 0 =
    Real.sqrt ((designVariance paperTableDesign w1LinearG : ℚ) : ℝ) ∧
  w1RMSE paperTableDesign w1LinearV (designVariance paperTableDesign w1LinearG) =
    Real.sqrt ((designVariance paperTableDesign w1LinearV : ℚ) : ℝ) ∧
  (∀ w : Fin 6 × Fin 15, ∀ β : Fin 4 → ℝ,
    w1Minimizes (w1FeDesign w) (fun i => (paperTableY i : ℝ)) β ↔ β = w1FeCoefficients w) ∧
  (∀ w : Fin 6 × Fin 15, w1FeCoefficients w 1 = (paperFeEstimate w : ℝ)) ∧
  w1Approx7 ((designVariance paperTableDesign w1LinearG : ℚ) : ℝ) (603374/10000000) ∧
  w1Approx7 (Real.sqrt ((designVariance paperTableDesign w1LinearG : ℚ) : ℝ)) (2456367/10000000) ∧
  w1Approx7 (Real.sqrt ((designVariance paperTableDesign w1LinearV : ℚ) : ℝ)) (123696/10000000) ∧
  w1Approx7 ((mean paperTableDesign paperFeEstimate : ℚ) : ℝ) (-139874/10000000) ∧
  w1Approx7 ((designVariance paperTableDesign paperFeEstimate : ℚ) : ℝ) (777347/10000000) ∧
  w1Approx7 (Real.sqrt ((designVariance paperTableDesign paperFeEstimate : ℚ) : ℝ)) (2788094/10000000) ∧
  ¬ roundsToThree (mean paperTableDesign paperFeEstimate) (-12/1000) ∧
  ¬ roundsToThree (designVariance paperTableDesign paperFeEstimate) (36/1000) ∧
  ¬ sdRoundsToThree (designVariance paperTableDesign paperFeEstimate) (191/1000)

end
end SAP.P026a
