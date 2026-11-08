import Mathlib
import SAP.P002a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a
noncomputable section
open Filter
open scoped BigOperators Matrix Classical Topology

/-- The equally spaced grid, including both endpoints. It is used only at sizes at least four. -/
def t6Grid (m : ℕ) (j : Fin m) : ℝ :=
  (2 * (j.val : ℝ) - (m : ℝ) + 1) / ((m : ℝ) - 1)

def t6V (m : ℕ) : ℝ := ((m : ℝ) + 1) / (3 * ((m : ℝ) - 1))
def t6Eta (m : ℕ) : ℝ := 1 / (2 : ℝ) ^ ((2 * m) ^ 2)
def t6T (m : ℕ) (i : Fin (2 * m)) : ℝ :=
  (2 * (i.val % m : ℕ) - (m : ℝ) + 1) / ((m : ℝ) - 1)
def t6X (m : ℕ) (i : Fin (2 * m)) : ℝ := (nearSingularModel m).x i 0
def t6Y (m : ℕ) (i : Fin (2 * m)) : ℝ := (nearSingularModel m).pop.y i false
def t6Gamma (m : ℕ) : ℝ := t6Eta m * t6V m / (1 + t6Eta m ^ 2 * t6V m)
def t6Error (m : ℕ) (i : Fin (2 * m)) : ℝ := t6Y m i - t6Gamma m * t6X m i
def t6Coef (a b : ℝ) : Option (Fin 1) → ℝ
  | none => a
  | some _ => b
def t6Block (m : ℕ) : Finset (Fin (2 * m)) := Finset.univ.filter (fun i => i.val < m)

/-- Uniform reassignment variance of the feasible, re-estimated statistic. -/
def t6Variance (m : ℕ) : ℝ :=
  designVariance (nearSingularModel m).pop (adjustedTau (nearSingularModel m) (t6Y m))

/-- The explicit upper bound, written with nonnegative natural exponents. -/
def t6RatioBound (m : ℕ) : ℝ :=
  5 * (2 : ℝ) ^ (2 * m) / (8 * ((2 * m : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (2 * m) ^ 2))

/-- Even models and the odd grid extension, at their actual sample sizes. -/
def t6SequenceModel (n : ℕ) : CovPopulation n 1 :=
  if h : 2 * (n / 2) = n then h ▸ nearSingularModel (n / 2) else oddNearModel n

def t6FailureProbability (j : ℕ) : ℝ :=
  let m := j + 4
  probability (nearSingularModel m).pop (fun T =>
    |adjustedSigma2 (nearSingularModel m) (t6Y m) T / t6Variance m - 1| ≥ 1 / 2)

/-- Grid identities and bounds; no empty or singleton grid is used in the whole statement. -/
def T6GridFacts (m : ℕ) : Prop :=
  mean (t6Grid m) = 0 ∧
  mean (fun j => t6Grid m j ^ 2) = t6V m ∧
  mean (fun j => t6Grid m j ^ 3) = 0 ∧
  (∀ j, |t6Grid m j| ≤ 1) ∧ 1 / 3 ≤ t6V m ∧ t6V m ≤ 1

/-- The even model satisfies the standing assumptions with the claimed constants. -/
def T6EvenModelFacts (m : ℕ) : Prop :=
  let P := nearSingularModel m
  Xi P 0 (1 / 4) 16 5 (1 / 3) ∧ late P.pop = 0 ∧
  compliers P.pop = Finset.univ ∧ P.pop.n1 = m ∧ controlSize P.pop = m ∧
  fraction P.pop = 1 / 2 ∧
  (∀ i a, P.pop.d i a = a ∧
    P.pop.y i a = t6T m i + (1 / 10) * (t6T m i ^ 2 - t6V m)) ∧
  (∀ i, P.x i 0 = (if i.val < m then 1 else -1) + t6Eta m * t6T m i) ∧
  (∀ S, observedW P.pop 0 S = t6Y m)

def T6EvenMomentFacts (m : ℕ) : Prop :=
  (∑ i, t6X m i) = 0 ∧ mean (t6X m) = 0 ∧ mean (t6Y m) = 0 ∧
  (∀ i, |t6X m i| ≤ 5 / 4) ∧ (∀ i, |t6Y m i| ≤ 11 / 10) ∧
  mean (fun i => t6X m i ^ 4) ≤ 16 ∧
  mean (fun i => t6X m i ^ 2) = 1 + t6Eta m ^ 2 * t6V m ∧
  1 / 4 ≤ mean (fun i => t6X m i ^ 2) ∧
  mean (fun i => t6X m i * t6Y m i) = t6Eta m * t6V m

def T6EvenRegressionFacts (m : ℕ) : Prop :=
  let P := nearSingularModel m
  (∀ a, psi P a 0 = t6Coef 0 (t6Gamma m) ∧ residual P a 0 = t6Error m) ∧
  mean (t6Error m) = 0 ∧ (∀ i, |t6Error m i| ≤ 27 / 20) ∧
  1 / 6 ≤ mean (fun i => t6Error m i ^ 2) ∧
  0 ≤ popCov (t6Error m) (t6Error m) ∧
  fourthNorm (t6Error m) ≤ 5 * Real.sqrt (popVar (t6Error m)) ∧
  Function.Injective (t6X m) ∧
  (∀ T ∈ assignments P.pop, (gram P.x T).det ≠ 0 ∧ (gram P.x Tᶜ).det ≠ 0)

def T6RareBlockFacts (m : ℕ) : Prop :=
  let P := nearSingularModel m
  t6Block m ∈ assignments P.pop ∧ (t6Block m)ᶜ ∈ assignments P.pop ∧
  (∀ a, (fitted P (t6Y m) (t6Block m) a) (some 0) = 1 / t6Eta m) ∧
  adjustedTau P (t6Y m) (t6Block m) = -2 / t6Eta m ∧
  adjustedTau P (t6Y m) (t6Block m)ᶜ = 2 / t6Eta m ∧
  (∀ T, adjustedTau P (t6Y m) Tᶜ = -adjustedTau P (t6Y m) T) ∧
  expectation P.pop (adjustedTau P (t6Y m)) = 0

def T6VarianceFacts (m : ℕ) : Prop :=
  0 < t6Variance m ∧
  8 / (((2 * m).choose m : ℝ) * t6Eta m ^ 2) ≤ t6Variance m ∧
  8 * (2 : ℝ) ^ (2 * (2 * m) ^ 2) / (2 : ℝ) ^ (2 * m) ≤
    8 / (((2 * m).choose m : ℝ) * t6Eta m ^ 2)

def T6EstimatorFacts (m : ℕ) : Prop :=
  let P := nearSingularModel m
  (∀ T ∈ assignments P.pop,
    0 ≤ adjustedSigma2 P (t6Y m) T ∧
    adjustedSigma2 P (t6Y m) T ≤ (∑ i, t6Y m i ^ 2) / (m : ℝ) ^ 2) ∧
  (∑ i, t6Y m i ^ 2) / (m : ℝ) ^ 2 ≤ 121 / (25 * ((2 * m : ℕ) : ℝ)) ∧
  121 / (25 * ((2 * m : ℕ) : ℝ)) < 5 / ((2 * m : ℕ) : ℝ)

def T6FailureFacts (m : ℕ) : Prop :=
  let P := nearSingularModel m
  t6RatioBound m < 1 / 2 ∧
  (∀ S ∈ assignments P.pop,
    let q := observedW P.pop (late P.pop) S
    (∀ T ∈ assignments P.pop,
      0 ≤ adjustedSigma2 P q T / designVariance P.pop (adjustedTau P q) ∧
      adjustedSigma2 P q T / designVariance P.pop (adjustedTau P q) ≤ t6RatioBound m) ∧
    probability P.pop (fun T =>
      |adjustedSigma2 P q T / designVariance P.pop (adjustedTau P q) - 1| ≥ 1 / 2) = 1)

def T6OddFacts (n : ℕ) : Prop :=
  let P := oddNearModel n
  Xi P 0 (1 / 4) 16 5 (1 / 3) ∧ late P.pop = 0 ∧
  compliers P.pop = Finset.univ ∧ P.pop.n1 = n / 2 ∧
  (∀ i a, P.pop.d i a = a ∧
    P.pop.y i a = (1 / 10) * (P.x i 0 ^ 2 - mean (fun j => P.x j 0 ^ 2))) ∧
  (∀ i, P.x i 0 = 2 * (i.val : ℝ) / ((n : ℝ) - 1) - 1 ∧ |P.x i 0| ≤ 1) ∧
  Function.Injective (fun i => P.x i 0) ∧
  (∀ i j, P.x j 0 - P.x i 0 = 2 * ((j.val : ℝ) - (i.val : ℝ)) / ((n : ℝ) - 1))

/-- The printed claim is false: P002-T6; Supplement p. 42 (Supplement PDF p. 22),
Lemma 20, claim 4, display (E.61), with the feasible statistic in the denominator.
With k = 1, delta = 0, epsilon = 1/4, A = 16, B = 5 and r = 1/3, the explicit
even near-singular family and odd equally spaced extension satisfy the standing
assumptions at every size n >= 8. All units comply and the LATE is zero. The even
family has the stated centered moments, covariate and residual bounds, common
population OLS fit, and distinct covariates, so every arm fit has full rank.
The two pure-block reassignments have slopes 1/eta and statistics -2/eta and 2/eta.
Arm complementation gives zero expectation. The feasible reassignment variance
is at least 8/(choose(n,n/2) eta^2), at least 8*2^(2n^2)/2^n, whereas every variance
estimate is between zero and sum(y_i^2)/(n/2)^2 <= 121/(25n) < 5/n. Their ratio is
at most 5*2^n/(8n*2^(2n^2)) < 1/2 for every original and reassigned assignment.
Consequently the conditional error probability at kappa = 1/2 is identically one
along the even subsequence and tends to one, contradicting the printed zero limit.
The odd extension has distinct equally spaced covariates in [-1,1] and the same
constants. Statements (E.58)-(E.60) are context, not assertions of this counterexample. -/
def T6WholeStatement : Prop :=
  (∀ m, 4 ≤ m →
    T6GridFacts m ∧ T6EvenModelFacts m ∧ T6EvenMomentFacts m ∧
    T6EvenRegressionFacts m ∧ T6RareBlockFacts m ∧ T6VarianceFacts m ∧
    T6EstimatorFacts m ∧ T6FailureFacts m) ∧
  (∀ n, 9 ≤ n → Odd n → T6OddFacts n) ∧
  (∀ n, 8 ≤ n → Xi (t6SequenceModel n) 0 (1 / 4) 16 5 (1 / 3)) ∧
  (∀ m, t6SequenceModel (2 * m) = nearSingularModel m) ∧
  (∀ n, Odd n → t6SequenceModel n = oddNearModel n) ∧
  Tendsto t6FailureProbability atTop (nhds 1) ∧
  ¬Tendsto t6FailureProbability atTop (nhds 0)

end
end SAP.P002a
