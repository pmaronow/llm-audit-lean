import Mathlib
import SAP.P005a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a
noncomputable section
open Finset Filter
open scoped BigOperators Matrix Topology

/-- Assumptions 1--3 on a sequence starting at an arbitrary admissible size.
There is one moment constant and one pair of allocation constants for the entire
sequence. Values before the starting size have no mathematical significance. -/
def wholeStandingAssumptions (n₀ : ℕ) (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) : Prop :=
  (∀ n ≥ n₀, 1 ≤ d n ∧ d n ≤ n ∧ 0 < m n ∧ m n < n) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ n ≥ n₀,
    popMean (fun i => (P n).yT i^2) ≤ K ∧
    popMean (fun i => (P n).yC i^2) ≤ K ∧
    ∀ k, popMean (fun i => (P n).x i k^2) ≤ K) ∧
  (∀ᶠ n in atTop, standardized (P n)) ∧
  (∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧ hi < 1 ∧
    ∀ n ≥ n₀, lo < pT n (m n) ∧ pT n (m n) < hi)

/-- The actual scalar variance of an arm's first covariate. -/
def firstVariance {n : ℕ} (P : Population n 1) (A : Finset (Fin n)) : ℝ :=
  sampleCov A (fun i => P.x i 0) (fun i => P.x i 0)

/-- P005-T5; Theorem 4.1, last display, p. 1509 (PDF p. 8).
The printed claim is false: the specified six-unit population satisfies the
finite-sample assumptions, has positive variances under all fifteen assignments,
and gives 217/2500 for the third bias component while the printed formula gives
-217/2500. All individual means, moments, coefficients and expectations are
included; reversing both printed signs gives the actual component. -/
def T5WholeStatement : Prop :=
  T5Statement ∧
  popMean (fun i => signPopulation.yT i^2) = (1059/625 : ℝ) ∧
  popMean (fun i => signPopulation.yC i^2) = (17361/625 : ℝ) ∧
  popMean (fun i => signX i^2) = 1 ∧ (1 : ℝ) ≤ 28 ∧
  pT 6 2 = (1/3 : ℝ) ∧ Function.Injective signX ∧
  (∀ S ∈ design 6 2, 0 < firstVariance signPopulation S ∧
    0 < firstVariance signPopulation (control S)) ∧
  (∀ i, leverage signPopulation i = signX i^2) ∧
  popMean (leverage signPopulation) = 1 ∧
  popMean signPopulation.yT = 1 ∧ popMean signPopulation.yC = 5 ∧
  NTTT 6 2 = (1/10 : ℝ) ∧ NCCC 6 2 = -(1/80 : ℝ) ∧
  expectation 2 (fun S => dot (xMean signPopulation (control S))
    (armNu3 signPopulation (control S) signPopulation.yC)) = (217/12500 : ℝ) ∧
  expectation 2 (fun S => dot (xMean signPopulation S)
    (armNu3 signPopulation S signPopulation.yT)) = -(217/3125 : ℝ) ∧
  (-NCCC 6 2 * leverageCov signPopulation signPopulation.yC +
    NTTT 6 2 * leverageCov signPopulation signPopulation.yT) = (217/2500 : ℝ)

/-- Raw-coordinate fitted value at a = 1/n; meaningful arms below have positive variance. -/
def spikeFit (n : ℕ) (A : Finset (Fin n)) : ℝ :=
  mean A (spikeV n) + (1/(n : ℝ) - mean A (spikeA n)) *
    scalarSlope A (spikeA n) (spikeV n)

/-- Population slope in the raw a coordinate. -/
def spikeB (n : ℕ) : ℝ :=
  (∑ i, spikeZ n i * spikeV n i) / (∑ i, spikeZ n i^2)

def spikeE (n : ℕ) (i : Fin n) : ℝ := spikeV n i - spikeB n * spikeZ n i

def spikeR (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  interactedATE (spikePopulation n) S - ate (spikePopulation n) -
    armLeading (spikePopulation n) S

def spikeRate (n : ℕ) : ℝ := Real.sqrt (kappa (spikePopulation n) / n)

/-- Exact leverage, including identification of the maximizing special unit. -/
def spikeLeverageFacts : Prop :=
  ∀ n : ℕ, 6 ≤ n →
    kappa (spikePopulation n) = (1-1/(n : ℝ))^2 / (n * spikeQ n) ∧
    kappa (spikePopulation n) =
      3*n*(n-1 : ℝ)*(n-2 : ℝ) / (3*(n : ℝ)^2*(n-2 : ℝ)+1) ∧
    (∀ i j : Fin n, j.val = 0 → leverage (spikePopulation n) i ≤
      leverage (spikePopulation n) j)

/-- The sharper raw slope and prediction bounds for the arm containing unit 0. -/
def spikeHighFitFacts : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∀ A : Finset (Fin n),
    (∃ i ∈ A, i.val = 0) → 2 ≤ A.card →
    |scalarSlope A (spikeA n) (spikeV n)| ≤ 2 ∧
    (Even n → A.card = n/2 → |spikeFit n A| ≤ (25/18 : ℝ))

/-- Exact population slopes, residuals and the sharp leading-term bound. -/
def spikeProjectionFacts : Prop :=
  ∀ n : ℕ, 6 ≤ n →
    spikeB n = (n : ℝ)^2 / (3*(n : ℝ)^2*(n-2 : ℝ)+1) ∧
    0 ≤ spikeB n ∧ spikeB n ≤ (1/12 : ℝ) ∧
    (∀ k : Fin 1,
      populationSlope (spikePopulation n) (spikePopulation n).yT k =
        Real.sqrt (spikeQ n) * spikeB n ∧
      populationSlope (spikePopulation n) (spikePopulation n).yC k =
        Real.sqrt (spikeQ n) * spikeB n) ∧
    (∀ i, armResidual (spikePopulation n) (spikePopulation n).yT i = spikeE n i ∧
      armResidual (spikePopulation n) (spikePopulation n).yC i = spikeE n i ∧
      |spikeE n i| ≤ (13/12 : ℝ)) ∧
    (∀ S ∈ design n (n/2),
      armLeading (spikePopulation n) S = mean S (spikeE n) - mean (control S) (spikeE n) ∧
      |armLeading (spikePopulation n) S| ≤ (13/6 : ℝ) ∧ (13/6 : ℝ) < 3)

/-- Rate comparison, deterministic ratio bound and probability-one tails along even sizes.
The limit is a deterministic lower bound; probabilities are on separate finite spaces. -/
def spikeTailFacts : Prop :=
  (∀ n : ℕ, 6 ≤ n → 0 < spikeRate n ∧ spikeRate n ≤ 1/Real.sqrt n) ∧
  (∀ n : ℕ, 6 ≤ n → Even n → ∀ S ∈ design n (n/2),
    (n-6 : ℝ)*Real.sqrt n ≤ |spikeR n S| / spikeRate n) ∧
  Tendsto (fun j : ℕ => ((2*j : ℕ)-6 : ℝ)*Real.sqrt (2*j : ℕ)) atTop atTop ∧
  (∀ M : ℝ, ∃ N : ℕ, 6 ≤ N ∧ ∀ n ≥ N, Even n →
    probability (n/2) (fun S => |spikeR n S| > M*spikeRate n) = 1)

/-- A finite minimum is specified by a lower bound at every labelled assignment
and attainment at one assignment, avoiding any empty-infimum convention. -/
def spikeMinimum (n : ℕ) (v : ℝ) : Prop :=
  (∀ S ∈ design n (n/2), v ≤ |spikeR n S|) ∧
  ∃ S ∈ design n (n/2), |spikeR n S| = v

/-- P005-T7; Theorem 4.1, pp. 1509--1510 (PDF pp. 8--9), footnote 8.
The printed claim is false: the explicit one-covariate spike sequence satisfies
Assumptions 1--3 and every-assignment regularity, yet its remainder is not of
the printed stochastic order. The statement includes all grid identities,
pointwise bounds, exact leverage and slopes, fitted-line calculations, sharp
bounds, probability-one even-size tails and both exact finite minima. -/
def T7WholeStatement : Prop :=
  T7Statement ∧
  (∀ n : ℕ, 6 ≤ n →
    (∑ i, spikeV n i) = 0 ∧
    (∑ i, spikeV n i^2) = (n : ℝ)*(n-1 : ℝ)/(3*(n-2 : ℝ)) ∧
    popMean (spikeA n) = 1/(n : ℝ) ∧
    spikeQ n = (n-1 : ℝ)/(n : ℝ)^2*(1+1/(3*(n-2 : ℝ)*(n : ℝ)^2)) ∧
    (∀ i, |(spikePopulation n).yT i| = |(spikePopulation n).yC i| ∧
      |(spikePopulation n).yT i| ≤ 1) ∧
    (∀ S ∈ design n (n/2), 3 ≤ S.card ∧ 3 ≤ (control S).card ∧
      0 < firstVariance (spikePopulation n) S ∧
      0 < firstVariance (spikePopulation n) (control S))) ∧
  spikeLeverageFacts ∧ spikeHighFitFacts ∧ spikeProjectionFacts ∧
  (∀ n : ℕ, 6 ≤ n → ∀ A : Finset (Fin n), 2 ≤ A.card →
    mean A (spikeV n) - dot (xMean (spikePopulation n) A)
      (armBetaHat (spikePopulation n) A (spikeV n)) = spikeFit n A ∧
    ((∀ i ∈ A, i.val ≠ 0) →
      (∀ i ∈ A, spikeV n i = (n : ℝ)^2 * spikeA n i) ∧ spikeFit n A = n)) ∧
  (∀ n : ℕ, 6 ≤ n → Even n → ∀ S ∈ design n (n/2),
    (n-3 : ℝ) ≤ |interactedATE (spikePopulation n) S|) ∧
  spikeTailFacts ∧
  (design 6 3).card = 20 ∧ kappa (spikePopulation 6) = (360/433 : ℝ) ∧
  spikeB 6 = (36/433 : ℝ) ∧ spikeMinimum 6 (4357386/779833) ∧
  |(4357386/779833 : ℝ) - 559/100| < 1/200 ∧
  (design 12 6).card = 924 ∧ kappa (spikePopulation 12) = (3960/4321 : ℝ) ∧
  spikeB 12 = (144/4321 : ℝ) ∧ spikeMinimum 12 (8690712840/752921287) ∧
  |(8690712840/752921287 : ℝ) - 1154/100| < 1/200

/-- The repaired expansion on a sequence beginning at any size at least two.
Only eventual invertibility is needed for a conclusion about a tail. -/
def wholeInteractedExpansion : Prop :=
  ∀ (n₀ : ℕ), 2 ≤ n₀ → ∀ (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)), wholeStandingAssumptions n₀ d m P →
    (∀ᶠ n in atTop, interactedRegular (P n) (m n)) →
    Tendsto (fun n => kappa (P n)*Real.log (2*d n : ℕ)) atTop (nhds 0) →
    stochasticO m (fun n S => interactedATE (P n) S - ate (P n) - armLeading (P n) S)
      (fun n => Real.sqrt (kappa (P n)*d n/n))

/-- The dimension-one clause is interpreted along its possibly intermittent subsequence. -/
def mixedLogEquivalence : Prop :=
  ∀ (d : ℕ → ℕ) (κ : ℕ → ℝ),
    (∀ᶠ n in atTop, 1 ≤ d n) → (∀ᶠ n in atTop, 0 ≤ κ n) →
    (Tendsto (fun n => κ n*Real.log (2*d n : ℕ)) atTop (nhds 0) ↔
      Tendsto (fun n => κ n*Real.log (d n)) atTop (nhds 0) ∧
      Tendsto (fun n => if d n = 1 then κ n else 0) atTop (nhds 0))

/-- P005-T9; Theorem 4.1, p. 1510 (PDF p. 9), and Appendix B.3, p. 1517 (PDF p. 16).
Under Assumptions 1--3 and every-assignment invertibility, the repaired condition
kappa log(2d) tending to zero implies the full interacted expansion with remainder
O_p(sqrt(kappa d/n)). The two repaired logarithms have the stated inequalities
and equivalent limits. The repaired condition implies vanishing leverage and the
printed condition, and is equivalent to the printed condition plus vanishing
leverage on the dimension-one subsequence. -/
def T9WholeStatement : Prop := T9Statement ∧ wholeInteractedExpansion ∧ mixedLogEquivalence

/-- Inverse-free treated expression with an arbitrary covariance weight. -/
def weightExpression (c : ℝ) (S : Finset (Fin 6)) : ℝ :=
  mean S weightY - dot (xMean weightPopulation S) (armN weightPopulation S weightY) +
    c*sampleCov S (leverage weightPopulation) weightY

/-- P005-T10; Appendix B.4, last display, pp. 1518--1519 (PDF pp. 17--18).
The printed claim is false: the six-unit standardized regular population has
printed treated expectation 4913/1200 instead of 20/3, while the derived weight
is unbiased. All fifteen-assignment positivity, leverage, population covariance,
assignmentwise and expected gaps, and rational scaling identities are included. -/
def T10WholeStatement : Prop :=
  T10Statement ∧ (design 6 2).card = 15 ∧ Function.Injective weightA ∧
  (∀ S ∈ design 6 2,
    0 < firstVariance weightPopulation S ∧ 0 < firstVariance weightPopulation (control S) ∧
    firstVariance weightPopulation S = (3/20 : ℝ)*sampleCov S weightA weightA ∧
    firstVariance weightPopulation (control S) = (3/20 : ℝ)*sampleCov (control S) weightA weightA) ∧
  (∀ i, leverage weightPopulation i = (3/20 : ℝ)*weightA i^2) ∧
  popMean (fun i => weightA i^2) = (40/6 : ℝ) ∧
  popMean (leverage weightPopulation) = 1 ∧
  leverageCov weightPopulation weightY = (343/30 : ℝ) ∧
  (2 : ℝ)/((6-2)*4) = (1/8 : ℝ) ∧ (4 : ℝ)/((6-2)*2) = (1/2 : ℝ) ∧
  (∀ S : Finset (Fin 6),
    weightExpression (1/8) S - weightExpression (1/2) S =
      -(3/8 : ℝ)*sampleCov S (leverage weightPopulation) weightY ∧
    dot (xMean weightPopulation S) (armN weightPopulation S weightY) =
      (3/20 : ℝ)*mean S weightA*(mean S (fun i => weightA i*weightY i) -
        mean S weightA*mean S weightY) ∧
    sampleCov S (leverage weightPopulation) weightY =
      (3/20 : ℝ)*(mean S (fun i => weightA i^2*weightY i) -
        mean S (fun i => weightA i^2)*mean S weightY)) ∧
  expectation 2 (fun S => sampleCov S (leverage weightPopulation) weightY) =
    (3/5 : ℝ)*(343/30) ∧
  expectation 2 (weightExpression (1/8)) - expectation 2 (weightExpression (1/2)) =
    -(1029/400 : ℝ)

/-- The bracket multiplying the population leverage covariance at sample size s. -/
def armBiasCoefficient (n s : ℕ) (c : ℝ) : ℝ :=
  -((n : ℝ)-s)/((s : ℝ)*(n-1)) + NTTT n s +
    c*((s : ℝ)-1)*n/((s : ℝ)*(n-1))

/-- The arm remainder order under the canonical assumptions from any starting size. -/
def wholeArmOrder : Prop :=
  ∀ (n₀ : ℕ), 2 ≤ n₀ → ∀ (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)), wholeStandingAssumptions n₀ d m P →
    ∀ t : Arm,
    stochasticO m (fun n S =>
      let A := armSet t S
      let y := if t = .treated then (P n).yT else (P n).yC
      armDebiased (P n) A y - (mean A y - dot (xMean (P n) A) (populationSlope (P n) y)))
      (fun n => Real.sqrt (kappa (P n)/n))

/-- P005-T11; Appendix B.4, corrected last display, pp. 1518--1519 (PDF pp. 17--18).
The corrected arm expressions cancel the inverse assignmentwise, have the exact
generic expectation, and are unbiased with the derived arm-size weights. The
cancelling treated weight equals its unsimplified expression and is unique for
arms of size at least two; singleton expectations require no division by s-1.
The printed treated weight has the stated bias. Standardization gives d/n <=
kappa <= 1 and h_i <= n. Under Assumptions 1--3 both corrected arm remainders
are O_p(sqrt(kappa/n)), from any starting size, with no extra rate assumption. -/
def T11WholeStatement : Prop :=
  T11Statement ∧
  (∀ {n s : ℕ}, 3 ≤ n → 2 ≤ s → s < n →
    ((n : ℝ)-s)/(n*((s : ℝ)-1)) -
      NTTT n s * ((s : ℝ)*(n-1))/(((s : ℝ)-1)*n) =
        ((n : ℝ)-s)/((n-2 : ℝ)*s)) ∧
  (∀ {n d s : ℕ} (P : Population n d), 3 ≤ n → 0 < s → s < n →
    xMean P univ = 0 → ∀ (y : Fin n → ℝ) (c : ℝ),
    expectation s (fun A => mean A y - dot (xMean P A) (armN P A y) +
      c*sampleCov A (leverage P) y) = popMean y + armBiasCoefficient n s c * leverageCov P y ∧
    expectation s (fun A => armDebiased P A y) = popMean y ∧
    (2 ≤ s → (armBiasCoefficient n s c = 0 ↔ c = ((n : ℝ)-s)/((n-2 : ℝ)*s))) ∧
    (s = 1 → armBiasCoefficient n s c = 0)) ∧
  (∀ {n d m : ℕ} (P : Population n d), 3 ≤ n → 0 < m → m < n →
    xMean P univ = 0 → ∀ c : ℝ,
    expectation m (fun S => mean (control S) P.yC -
      dot (xMean P (control S)) (armN P (control S) P.yC) +
      c*sampleCov (control S) (leverage P) P.yC) =
      popMean P.yC + armBiasCoefficient n (n-m) c * leverageCov P P.yC ∧
    expectation m (fun S => armDebiased P (control S) P.yC) = popMean P.yC) ∧
  (∀ {n d : ℕ} (P : Population n d), 0 < n → gram P = 1 →
    (d : ℝ)/n ≤ kappa P ∧ kappa P ≤ 1 ∧ ∀ i, leverage P i ≤ n) ∧
  wholeArmOrder

end
end SAP.P005a
