import Mathlib
import SAP.P005b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005b

noncomputable section
open scoped BigOperators Matrix
open Finset Filter

/-- Assumptions 1–3 for the p. 1514 contraction, allowing dimension zero.
The finitely many sizes below three do not affect any order assertion. -/
def wholeW1Standing (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)) : Prop :=
  (∀ n, 3 ≤ n → d n ≤ n ∧ 0 < m n ∧ m n < n) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ n, 3 ≤ n →
    popMean (fun i => (P n).yT i^2) ≤ K ∧
    popMean (fun i => (P n).yC i^2) ≤ K ∧
    ∀ k, popMean (fun i => (P n).x i k^2) ≤ K) ∧
  (∀ᶠ n in atTop, standardized (P n)) ∧
  (∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧ hi < 1 ∧
    ∀ n, 3 ≤ n → lo < pT n (m n) ∧ pT n (m n) < hi)

/-- The residual difference in Appendix B.1.1. -/
def wholeW1Delta {n d : ℕ} (P : Population n d) (m : ℕ) (i : Fin n) : ℝ :=
  commonResidual P m P.yT i - commonResidual P m P.yC i

/-- The centered matrix in the first variance bound on p. 1514. -/
def wholeW1Kernel {n d : ℕ} (P : Population n d) (δ : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => dot (P.x i) (fun k => P.x j k * δ j - populationSlope P δ k)

/-- The p. 1514 term (*), with the actual common-slope residuals. -/
def wholeW1Star {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  residualStarTerm P S (commonResidual P m P.yT) (commonResidual P m P.yC)

/-- The coefficient preceding the centered double sum on p. 1514. -/
def wholeW1VarianceCoefficient (n m : ℕ) : ℝ :=
  (1 / (pC n m * m * n))^2 * ((m : ℝ) * (n-m) / ((n : ℝ) * (n-1)))

/-- P005-T17; Appendix B.1.1, p. 1514 (PDF p. 13), corrected matching summation index.
The variance of the actual common-residual term (*) is bounded by the centered
double sum, then by the raw contraction. The exact Gram contraction and leverage
bound give deterministic order O(kappa/n), with bounded residual-difference second
moments, and (*) is O_p(sqrt(kappa*d/n)), including dimension zero. -/
def T17WholeStatement : Prop :=
  T17Statement ∧
  (∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n →
    standardized P →
    variance m (wholeW1Star P m) ≤ wholeW1VarianceCoefficient n m *
      (∑ i, ∑ j, (wholeW1Kernel P (wholeW1Delta P m) i j)^2) ∧
    wholeW1VarianceCoefficient n m *
      (∑ i, ∑ j, (wholeW1Kernel P (wholeW1Delta P m) i j)^2) ≤
    wholeW1VarianceCoefficient n m *
      (∑ i, ∑ j, (dot (P.x i) (P.x j) * wholeW1Delta P m j)^2)) ∧
  (∀ (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)),
    wholeW1Standing d m P →
    stochasticO m (fun n => wholeW1Star (P n) (m n))
      (fun n => Real.sqrt (kappa (P n) * d n / n)))

/-- Observed outcome for regression (1). -/
def wholeW1Observed {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (i : Fin n) : ℝ := if i ∈ S then P.yT i else P.yC i

/-- Fitted value in the regression with intercept, treatment and covariates. -/
def wholeW1Fit {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (a t : ℝ) (b : Fin d → ℝ) (i : Fin n) : ℝ :=
  a + t * indicator S i + dot (P.x i) b

/-- The finite least-squares objective, with its ordinary sum convention. -/
def wholeW1Loss {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (a t : ℝ) (b : Fin d → ℝ) : ℝ :=
  ∑ i, (wholeW1Observed P S i - wholeW1Fit P S a t b i)^2

/-- The intercept corresponding to the displayed closed-form OLS coefficients. -/
def wholeW1Intercept {n d : ℕ} (P : Population n d) (m : ℕ)
    (S : Finset (Fin n)) : ℝ :=
  mean (control S) P.yC - dot (xMean P (control S)) (betaHat P m S)

/-- The closed-form coefficients are the unique least-squares minimizer. -/
def wholeW1OLS {n d : ℕ} (P : Population n d) (m : ℕ)
    (S : Finset (Fin n)) : Prop :=
  ∀ (a t : ℝ) (b : Fin d → ℝ),
    wholeW1Loss P S (wholeW1Intercept P m S) (adjustedATE P m S) (betaHat P m S) ≤
      wholeW1Loss P S a t b ∧
    (wholeW1Loss P S a t b =
      wholeW1Loss P S (wholeW1Intercept P m S) (adjustedATE P m S) (betaHat P m S) →
      a = wholeW1Intercept P m S ∧ t = adjustedATE P m S ∧ b = betaHat P m S)

/-- P005-T21; Theorem 3.2, pp. 1508–1509 (PDF pp. 7–8); proof in Appendix B.2.
The printed noninteracted bias estimator is exactly unbiased for the bias, and
its correction is exactly unbiased for the ATE. The closed-form coefficients
are the unique OLS minimizer. The inverse-free formula, bias decomposition,
inverse-component identity and both population component expectations hold for
all nonempty arms. Expressions (11) and (12), their expectations and their
collection into (7) require only their presupposed nonzero arm-size denominators. -/
def T21WholeStatement : Prop :=
  T21Statement ∧
  (∀ {n d m : ℕ} (P : Population n d), 3 ≤ n → 0 < m → m < n →
    standardized P → noninteractedRegular P m →
    (∀ S ∈ design n m, wholeW1OLS P m S) ∧
    expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu1 P m S)) =
      (leverageCov P P.yC-leverageCov P P.yT)/(n-1 : ℝ) ∧
    expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu3 P m S)) =
      (pT n m/pC n m)*NTTT n m*leverageCov P P.yT -
        (pT n m/pC n m)*NTTC n m*leverageCov P P.yC)

/-- The p. 1516 term (*), distinct from the p. 1514 residual term. -/
def wholeW1DebiasedStar {n d : ℕ} (P : Population n d) (m : ℕ)
    (S : Finset (Fin n)) : ℝ :=
  -dot (xMean P S-xMean P (control S)) (Nhat P m S-N P m) +
    sampleCov S (leverage P) P.yT/(n-2 : ℝ) -
    sampleCov (control S) (leverage P) P.yC/(n-2 : ℝ)

/-- P005-T26; Theorem 3.2, p. 1509 (PDF p. 8); Appendix B.2, pp. 1516–1517.
The debiased noninteracted remainder equals the p. 1516 term (*) exactly and is
O_p(sqrt(kappa/n)) under Assumptions 1–3, without leverage decay. If kappa tends
to zero, this gives the printed common-slope expansion with o_p(n^(-1/2)) error. -/
def T26WholeStatement : Prop :=
  T26Statement ∧
  (∀ (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)), standingAssumptions d m P →
    (∀ᶠ n in atTop, noninteractedRegular (P n) (m n)) →
    stochasticO m
      (fun n S => debiasedATE (P n) (m n) S-ate (P n)-commonLeading (P n) (m n) S)
      (fun n => Real.sqrt (kappa (P n)/n))) ∧
  (∀ {n d m : ℕ} (P : Population n d), 3 ≤ n → 0 < m → m < n →
    standardized P → ∀ S ∈ design n m, (Lhat P m S).det ≠ 0 →
    debiasedATE P m S-ate P-commonLeading P m S = wholeW1DebiasedStar P m S)

/-- P005-T27; Theorem 4.2, p. 1510 (PDF p. 9); Appendix B.4, pp. 1518–1519.
The debiased interacted remainder is O_p(sqrt(kappa/n)) under Assumptions 1–3,
without leverage decay. If kappa tends to zero, the printed arm-specific linear
expansion has o_p(n^(-1/2)) error. -/
def T27WholeStatement : Prop :=
  T27Statement ∧
  (∀ (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)), standingAssumptions d m P →
    (∀ᶠ n in atTop, interactedRegular (P n) (m n)) →
    stochasticO m
      (fun n S => interactedDebiasedATE (P n) (m n) S-ate (P n)-armLeading (P n) S)
      (fun n => Real.sqrt (kappa (P n)/n)))

end
end SAP.P005b
