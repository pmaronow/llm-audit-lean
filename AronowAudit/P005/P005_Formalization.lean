import Mathlib

namespace AronowAudit.P005

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

/-! All units are indexed by `Fin n` (unit 0 is the paper's unit 1).
    Randomization is the actual uniform finite set of size-m subsets. -/

/-- "n_T out of n subjects are randomly assigned" (p. 1505, Section 2).
The complete randomization support, with each subset counted exactly once. -/
def design (n m : ℕ) : Finset (Finset (Fin n)) := univ.powersetCard m

/-- "[C] ... similarly" (p. 1505): the control arm is the complement of [T]. -/
def control {n : ℕ} (S : Finset (Fin n)) : Finset (Fin n) := univ \ S

/-- "population average" and "treatment group average" (p. 1505).
This scalar average uses the size of the supplied finite set as divisor. -/
def mean {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) : ℝ :=
  (∑ i ∈ S, a i) / S.card

/-- "bar a = (1/n) sum a_i" (p. 1505): the population average. -/
def popMean {n : ℕ} (a : Fin n → ℝ) : ℝ := mean univ a

/-- "Random assignment is the sole source of randomness" (p. 1505).
Expectation is a uniform average over all size-m treatment subsets. -/
def expectation {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) : ℝ :=
  (∑ S ∈ design n m, f S) / (design n m).card

/-- Variance under the randomization distribution (Lemma A.1, p. 1511):
the uniform average of squared deviations from the randomization mean. -/
def variance {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) : ℝ :=
  expectation m (fun S => (f S - expectation m f)^2)

/-- Randomization probability, as used in the order symbols on pp. 1507–1510:
the fraction of size-m assignments satisfying the event. -/
def probability {n : ℕ} (m : ℕ) (event : Finset (Fin n) → Prop) : ℝ :=
  by
    classical
    exact ((design n m).filter event).card / ((design n m).card : ℝ)

/-- "Covhat_t(a,b) = bar(ab)_t - bar a_t bar b_t"
(Appendix A.2, p. 1510). The same object is used in every target. -/
def sampleCov {n : ℕ} (S : Finset (Fin n)) (a b : Fin n → ℝ) : ℝ :=
  mean S (fun i => a i * b i) - mean S a * mean S b

/-- "bar(ab) - bar a bar b" (Lemma A.1, p. 1511), divisor n. -/
def popCov {n : ℕ} (a b : Fin n → ℝ) : ℝ := sampleCov univ a b

/-- "y_i^*(t) = y_i(t) - bar y(t)" (p. 1506); the correction to
Lemma A.1 (P005-T2) uses this centering operation for arbitrary vectors. -/
def centered {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ := a i - popMean a

/-- The variance right-hand side printed in Lemma A.1 (p. 1511),
with no centering of its two arguments. -/
def covarianceBound {n : ℕ} (m : ℕ) (a b : Fin n → ℝ) : ℝ :=
  2 * ((n : ℝ) - m) / ((m : ℝ) * (n - 1)) *
    popMean (fun i => (a i * b i - popMean (fun j => a j * b j))^2) +
  2 * ((n : ℝ) - m) * n / ((m : ℝ)^3 * (n - 1)) *
    popMean (fun i => a i^2) * popMean (fun i => b i^2)

/-- "t in {T,C}" (Lemma A.1, p. 1511). -/
inductive Arm | treated | control deriving DecidableEq

/-- The arm set [T] or [C] (p. 1505). -/
def armSet {n : ℕ} (t : Arm) (S : Finset (Fin n)) : Finset (Fin n) :=
  match t with | .treated => S | .control => control S

/-- "n_C = n - n_T" (p. 1505), with `m` representing n_T. -/
def armSize (n m : ℕ) (t : Arm) : ℕ :=
  match t with | .treated => m | .control => n - m

/-- The six-unit population support, for exact enumeration of the witnesses. -/
theorem univ_six : (univ : Finset (Fin 6)) = {0,1,2,3,4,5} := by decide

/-- P005-T1's first fixed vector for Lemma A.1 (P005-E002). -/
def witnessA : Fin 6 → ℝ := ![0, -3, -1, 2, -4, -3]
/-- P005-T1's second fixed vector (P005-E002). -/
def witnessB : Fin 6 → ℝ := ![2, 1, 3, -3, 1, 1]

/-- Complete size-four randomization for the six-unit witness (P005-T1).
This is only an explicit enumeration of `design 6 4`, not a different design. -/
def assignmentsSixFour : Finset (Finset (Fin 6)) :=
  {{0,1,2,3}, {0,1,2,4}, {0,1,2,5}, {0,1,3,4}, {0,1,3,5},
   {0,1,4,5}, {0,2,3,4}, {0,2,3,5}, {0,2,4,5}, {0,3,4,5},
   {1,2,3,4}, {1,2,3,5}, {1,2,4,5}, {1,3,4,5}, {2,3,4,5}}

/-- P005-T1: all fifteen size-four subsets are present, with no repetitions. -/
theorem design_six_four : design 6 4 = assignmentsSixFour := by decide

/-- The uniform expectation over the actual fifteen assignments is their
explicit arithmetic average (P005-T1; complete randomization, p. 1505). -/
theorem expectation_six_four (f : Finset (Fin 6) → ℝ) :
    expectation 4 f = (f {0,1,2,3} + (f {0,1,2,4} + (f {0,1,2,5} + (f {0,1,3,4} + (f {0,1,3,5} + (f {0,1,4,5} + (f {0,2,3,4} + (f {0,2,3,5} + (f {0,2,4,5} + (f {0,3,4,5} + (f {1,2,3,4} + (f {1,2,3,5} + (f {1,2,4,5} + (f {1,3,4,5} + (f {2,3,4,5})))))))))))))))/15 := by
  unfold expectation
  rw [design_six_four]
  have hc : assignmentsSixFour.card = 15 := by decide
  rw [hc]
  unfold assignmentsSixFour
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton] <;> norm_num


/-- P005-T1: the exact six-unit counterexample to the uncentered variance
bound of Lemma A.1 (p. 1511), including its means and variance. -/
theorem covariance_counterexample :
    4 ≤ (6 : ℕ) ∧ 1 ≤ (4 : ℕ) ∧ (4 : ℕ) < 6 ∧
    (design 6 4).card = 15 ∧
    popMean witnessA = -(3/2 : ℝ) ∧ popMean witnessB = (5/6 : ℝ) ∧
    popCov witnessA witnessB = -(23/12 : ℝ) ∧
    expectation 4 (fun S => sampleCov S witnessA witnessB) = -(69/40 : ℝ) ∧
    variance 4 (fun S => sampleCov S witnessA witnessB) = (16607/4800 : ℝ) ∧
    covarianceBound 4 witnessA witnessB = (3829/1440 : ℝ) ∧
    covarianceBound 4 witnessA witnessB < variance 4 (fun S => sampleCov S witnessA witnessB) := by
  have hE : expectation 4 (fun S => sampleCov S witnessA witnessB) = -(69/40 : ℝ) := by
    rw [expectation_six_four]
    norm_num [sampleCov, mean, witnessA, witnessB]
  have hV : variance 4 (fun S => sampleCov S witnessA witnessB) = (16607/4800 : ℝ) := by
    rw [variance, hE, expectation_six_four]
    norm_num [sampleCov, mean, witnessA, witnessB]
  have hc : (design 6 4).card = 15 := by decide
  simp only [hE, hV, hc]
  norm_num [covarianceBound, popCov, sampleCov, mean, popMean,
    witnessA, witnessB, univ_six]





/-- "For each subject ... a column vector of covariates ... two potential
outcomes y_i(1) and y_i(0)" (Section 2, p. 1504). They are fixed real arrays. -/
structure Population (n d : ℕ) where
  x : Fin n → Fin d → ℝ
  yT : Fin n → ℝ
  yC : Fin n → ℝ

/-- A transpose times a column vector, as in (3), p. 1506: Euclidean dot product. -/
def dot {d : ℕ} (u v : Fin d → ℝ) : ℝ := ∑ k, u k * v k

/-- Vector-valued arm averages, using the paper's coordinatewise average (p. 1505). -/
def xMean {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) : Fin d → ℝ :=
  fun k => mean S (fun i => P.x i k)

/-- "bar(xx') = (1/n) sum x_i x_i'" (p. 1505). -/
def gram {n d : ℕ} (P : Population n d) : Matrix (Fin d) (Fin d) ℝ :=
  fun k l => popMean (fun i => P.x i k * P.x i l)

/-- Assumption 2 at a fixed population size (p. 1505): centered, normalized covariates. -/
def standardized {n d : ℕ} (P : Population n d) : Prop :=
  xMean P univ = 0 ∧ gram P = 1

/-- "h_i = ||x_i||_2^2" (p. 1506). -/
def leverage {n d : ℕ} (P : Population n d) (i : Fin n) : ℝ := dot (P.x i) (P.x i)

/-- "kappa = max_i h_i/n" (equation (4), p. 1506).
For n>0 the finite range is nonempty, so its real supremum is its maximum. -/
def kappa {n d : ℕ} (P : Population n d) : ℝ :=
  sSup (Set.range (fun i => leverage P i / n))

/-- "ATE = bar y(1) - bar y(0)" (p. 1505). -/
def ate {n d : ℕ} (P : Population n d) : ℝ := popMean P.yT - popMean P.yC

/-- Inclusion fractions "p_T = n_T/n" and "p_C = n_C/n" (p. 1505). -/
def pT (n m : ℕ) : ℝ := (m : ℝ) / n
/-- Control inclusion fraction, p. 1505. Subtraction is in the reals. -/
def pC (n m : ℕ) : ℝ := ((n : ℝ) - m) / n

/-- "N_T = bar y(1)x", "N_C = bar y(0)x" (p. 1509).
Under Assumption 2 these are the population within-arm slope vectors. -/
def populationSlope {n d : ℕ} (P : Population n d) (y : Fin n → ℝ) : Fin d → ℝ :=
  fun k => popMean (fun i => y i * P.x i k)

/-- "N = p_T bar y(1)x + p_C bar y(0)x" and beta*=N (p. 1506). -/
def N {n d : ℕ} (P : Population n d) (m : ℕ) : Fin d → ℝ :=
  pT n m • populationSlope P P.yT + pC n m • populationSlope P P.yC

/-- "Lhat_t = bar(xx')_t - bar x_t bar x_t'" (p. 1509). -/
def armL {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) : Matrix (Fin d) (Fin d) ℝ :=
  fun k l => mean S (fun i => P.x i k * P.x i l) - xMean P S k * xMean P S l

/-- "Nhat_t = bar y(t)x_t - bar y(t)_t bar x_t" (p. 1509). -/
def armN {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (y : Fin n → ℝ) : Fin d → ℝ :=
  fun k => mean S (fun i => y i * P.x i k) - mean S y * xMean P S k

/-- "Lhat = I_d - p_T bar x_T bar x_T' - p_C bar x_C bar x_C'"
(Section 3, p. 1506), under the normalization Assumption 2. -/
def Lhat {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) :
    Matrix (Fin d) (Fin d) ℝ :=
  1 - pT n m • Matrix.vecMulVec (xMean P S) (xMean P S) -
    pC n m • Matrix.vecMulVec (xMean P (control S)) (xMean P (control S))

/-- "Nhat = p_T (...) + p_C (...)" (p. 1506). -/
def Nhat {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : Fin d → ℝ :=
  pT n m • armN P S P.yT + pC n m • armN P (control S) P.yC

/-- "betahat = Lhat^{-1} Nhat" (p. 1506). The matrix inverse is Mathlib's
total nonsingular inverse; invertibility hypotheses are explicit where needed. -/
def betaHat {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : Fin d → ℝ :=
  (Lhat P m S)⁻¹ *ᵥ Nhat P m S

/-- "betahat_{I,t} = Lhat_t^{-1} Nhat_t" (p. 1509): within-arm slope,
using the Section 4 definition rather than the interaction coefficient in (2). -/
def armBetaHat {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (y : Fin n → ℝ) : Fin d → ℝ := (armL P S)⁻¹ *ᵥ armN P S y

/-- "all design matrices ... are invertible" (footnote 4, p. 1506):
noninteracted design, under every possible assignment. -/
def noninteractedRegular {n d : ℕ} (P : Population n d) (m : ℕ) : Prop :=
  ∀ S ∈ design n m, (Lhat P m S).det ≠ 0

/-- Footnote 4 for the interacted estimator: both within-arm matrices are
invertible under every assignment (p. 1506 and Section 4). -/
def interactedRegular {n d : ℕ} (P : Population n d) (m : ℕ) : Prop :=
  ∀ S ∈ design n m, (armL P S).det ≠ 0 ∧ (armL P (control S)).det ≠ 0

/-- Equation (3) (p. 1506): the noninteracted OLS-adjusted ATE estimator. -/
def adjustedATE {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  mean S P.yT - mean (control S) P.yC - dot (xMean P S - xMean P (control S)) (betaHat P m S)

/-- Interacted regression-adjusted ATE estimator (Section 4, p. 1509). -/
def interactedATE {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) : ℝ :=
  mean S P.yT - mean (control S) P.yC -
    (dot (xMean P S) (armBetaHat P S P.yT) -
      dot (xMean P (control S)) (armBetaHat P (control S) P.yC))

/-- "nu_{1t} = bar y*(t)x_t - bar y*(t)x" (Theorem 4.1, p. 1509). -/
def armNu1 {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) (y : Fin n → ℝ) :
    Fin d → ℝ := fun k => mean S (fun i => centered y i * P.x i k) -
      popMean (fun i => centered y i * P.x i k)

/-- "nu_{2t} = (Lhat_t^{-1} - I_d^{-1}) Nhat_t" (Theorem 4.1, p. 1509). -/
def armNu2 {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) (y : Fin n → ℝ) :
    Fin d → ℝ := ((armL P S)⁻¹ - 1) *ᵥ armN P S y

/-- "nu_{3t} = -(bar x_t bar y*(t)_t)" (Theorem 4.1, p. 1509).
The minus sign is retained for the sign correction P005-T6. -/
def armNu3 {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) (y : Fin n → ℝ) :
    Fin d → ℝ := fun k => -(xMean P S k * mean S (centered y))

/-- nu_1 of Theorem 3.1 (p. 1507), weighted arm fluctuations. -/
def nu1 {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : Fin d → ℝ :=
  pT n m • armNu1 P S P.yT + pC n m • armNu1 P (control S) P.yC
/-- nu_2 of Theorem 3.1 (p. 1507), the inverse-matrix component. -/
def nu2 {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : Fin d → ℝ :=
  ((Lhat P m S)⁻¹ - 1) *ᵥ Nhat P m S
/-- nu_3 of Theorem 3.1 (p. 1507), the centered outcome-mean component. -/
def nu3 {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : Fin d → ℝ :=
  pT n m • armNu3 P S P.yT + pC n m • armNu3 P (control S) P.yC

/-- Equations (7)–(8) (Theorem 3.2, p. 1508): the printed bias estimator. -/
def biasEstimate {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  (sampleCov (control S) (leverage P) P.yC - sampleCov S (leverage P) P.yT) / (n - 2 : ℝ) +
  dot (xMean P (control S) - xMean P S) (nu2 P m S)

/-- "ATEhat_Debiased = ATEhat - Biashat" (Theorem 3.2, pp. 1508–1509). -/
def debiasedATE {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  adjustedATE P m S - biasEstimate P m S

/-- Bias estimator of Theorem 4.2 (p. 1510), with its printed correct arm weights. -/
def interactedBiasEstimate {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  (m : ℝ) / ((n - 2 : ℝ) * (n - m)) * sampleCov (control S) (leverage P) P.yC +
    dot (xMean P (control S)) (armNu2 P (control S) P.yC) -
  ((n : ℝ) - m) / ((n - 2 : ℝ) * m) * sampleCov S (leverage P) P.yT -
    dot (xMean P S) (armNu2 P S P.yT)

/-- "ATEhat_{I,Debiased} = ATEhat_I - Biashat_I" (Theorem 4.2, p. 1510). -/
def interactedDebiasedATE {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  interactedATE P S - interactedBiasEstimate P m S

/-- The covariance S_t := bar(hy(t)) - bar h bar y(t), divisor n,
used in (5), (6) and Theorem 4.1 (pp. 1507, 1509); S denotes this covariance. -/
def leverageCov {n d : ℕ} (P : Population n d) (y : Fin n → ℝ) : ℝ := popCov (leverage P) y

/-- "N_TTT = (n-n_T)(n-2n_T)/((n-1)(n-2)n_T^2)"
(Appendix A.1, p. 1510); all differences are real differences. -/
def NTTT (n m : ℕ) : ℝ :=
  ((n : ℝ) - m) * (n - 2 * m : ℝ) / ((n - 1 : ℝ) * (n - 2 : ℝ) * (m : ℝ)^2)
/-- N_CCC (Appendix A.1, p. 1510), the mirror of N_TTT. -/
def NCCC (n m : ℕ) : ℝ := NTTT n (n - m)
/-- N_TTC (Appendix A.1, p. 1510), the mixed third-moment coefficient. -/
def NTTC (n m : ℕ) : ℝ := -(n - 2 * m : ℝ) / ((n - 1 : ℝ) * (n - 2 : ℝ) * m)

/-- Arm population residual "y_i(t) - bar y(t) - x_i' beta_{I,t}"
(Theorem 4.1, pp. 1509–1510). -/
def armResidual {n d : ℕ} (P : Population n d) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  centered y i - dot (P.x i) (populationSlope P y)
/-- Noninteracted residual "y_i(t) - bar y(t) - x_i' beta*"
(Theorem 3.1, p. 1507). -/
def commonResidual {n d : ℕ} (P : Population n d) (m : ℕ) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  centered y i - dot (P.x i) (N P m)

/-- The leading linear term in Theorems 3.1–3.2 (pp. 1507–1509). -/
def commonLeading {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  mean S (commonResidual P m P.yT) - mean (control S) (commonResidual P m P.yC)
/-- The leading linear term in Theorems 4.1–4.2 (p. 1510). -/
def armLeading {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) : ℝ :=
  mean S (armResidual P P.yT) - mean (control S) (armResidual P P.yC)

/-- O_p(r_n), read as randomization tightness: for each epsilon>0, a finite
positive M and a tail on which Pr(|R_n|>M r_n)<epsilon (pp. 1507–1510).
The varying sample spaces are the actual designs for population size n. -/
def stochasticO (m : ℕ → ℕ) (R : (n : ℕ) → Finset (Fin n) → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∃ n₀ : ℕ,
    ∀ n ≥ n₀, probability (m n) (fun S => |R n S| > M * r n) < ε

/-- o_p(r_n), the randomization probability Pr(|R_n|>delta r_n) tends to
zero for every delta>0 (Theorems 3.2 and 4.2, pp. 1509–1510). -/
def stochasticLittleO (m : ℕ → ℕ) (R : (n : ℕ) → Finset (Fin n) → ℝ)
    (r : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → Tendsto (fun n => probability (m n) (fun S => |R n S| > δ * r n)) atTop (nhds 0)

/-- The finite-population sequence interpretation of Assumptions 1–3 (p. 1505).
The harmless initial sizes 0,1,2 are excluded; all actual sizes n>=3 are present.
K and the allocation bounds are one set of constants for the whole sequence. -/
def standingAssumptions (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)) : Prop :=
  (∀ n, 3 ≤ n → 1 ≤ d n ∧ d n ≤ n ∧ 0 < m n ∧ m n < n) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ n, 3 ≤ n →
    popMean (fun i => (P n).yT i^2) ≤ K ∧
    popMean (fun i => (P n).yC i^2) ≤ K ∧
    ∀ k, popMean (fun i => (P n).x i k^2) ≤ K) ∧
  (∀ᶠ n in atTop, standardized (P n)) ∧
  (∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧ hi < 1 ∧
    ∀ n, 3 ≤ n → lo < pT n (m n) ∧ pT n (m n) < hi)


/-- Linearity of the arm average (p. 1505), used in the corrected expansions. -/
theorem mean_sub {n : ℕ} (S : Finset (Fin n)) (a b : Fin n → ℝ) :
    mean S (fun i => a i - b i) = mean S a - mean S b := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

/-- Scalar multiplication commutes with the paper's finite average (p. 1505). -/
theorem mean_mul {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) (c : ℝ) :
    mean S (fun i => c * a i) = c * mean S a := by
  unfold mean
  rw [← Finset.mul_sum]
  ring

/-- A constant has its own arm mean when the arm is nonempty (p. 1505). -/
theorem mean_const {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (c : ℝ) :
    mean S (fun _ => c) = c := by
  have h : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  simp [mean, nsmul_eq_mul, h]

/-- Averaging a scalar projection equals projecting the vector average (p. 1505). -/
theorem mean_dot {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) (v : Fin d → ℝ) :
    mean S (fun i => dot (P.x i) v) = dot (xMean P S) v := by
  simp only [mean, dot, xMean, div_mul_eq_mul_div, Finset.sum_div, Finset.sum_mul]
  exact Finset.sum_comm

/-- P005-T2(a): centering both vectors leaves the sample covariance unchanged
(Lemma A.1 proof, p. 1511), for every nonempty arm. -/
theorem covariance_location_invariant {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (a b : Fin n → ℝ) (c e : ℝ) :
    sampleCov S (fun i => a i - c) (fun i => b i - e) = sampleCov S a b := by
  have ha := mean_sub S a (fun _ => c)
  have hb := mean_sub S b (fun _ => e)
  have hp : mean S (fun i => (a i-c)*(b i-e)) =
      mean S (fun i => a i*b i) - e*mean S a - c*mean S b + c*e := by
    have hf : (fun i => (a i-c)*(b i-e)) =
        (fun i => (a i*b i - e*a i) - (c*b i - c*e)) := by funext i; ring
    rw [hf, mean_sub, mean_sub, mean_sub, mean_mul, mean_mul, mean_const S hS]
    ring
  simp only [sampleCov]
  rw [hp, ha, hb, mean_const S hS, mean_const S hS]
  ring

/-- P005-T11(a): the corrected treated-arm display on p. 1518.
The inverse terms cancel for every assignment and every covariance weight c. -/
theorem treated_arm_cancellation {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (y : Fin n → ℝ) (c : ℝ)
    (hn : 3 ≤ n) (hS : S.Nonempty) (hinv : (armL P S).det ≠ 0) :
    mean S y - dot (xMean P S) (armBetaHat P S y) -
      (-dot (xMean P S) (armNu2 P S y) - c * sampleCov S (leverage P) y) =
      mean S y - dot (xMean P S) (armN P S y) + c * sampleCov S (leverage P) y ∧
    mean S y - dot (xMean P S) (armN P S y) + c * sampleCov S (leverage P) y =
      mean S y - dot (xMean P S) (populationSlope P y) -
        dot (xMean P S) (armN P S y - populationSlope P y) + c * sampleCov S (leverage P) y := by
  simp only [armBetaHat, armNu2, Matrix.sub_mulVec, Matrix.one_mulVec,
    dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  constructor <;> ring

/-- P005-T14(a)–(c): corrected p. 1516 expansion, with transposes and the
control sum over [C]. These are exact algebraic identities for every assignment. -/
theorem noninteracted_debiased_expansion {n d : ℕ} (P : Population n d) (m : ℕ)
    (S : Finset (Fin n)) (v : Fin d → ℝ) (hn : 3 ≤ n) (hm : 0 < m)
    (hmn : m < n) (hS : S ∈ design n m) (hinv : (Lhat P m S).det ≠ 0) :
    debiasedATE P m S =
      mean S P.yT - mean (control S) P.yC -
        dot (xMean P S - xMean P (control S)) (Nhat P m S) +
        sampleCov S (leverage P) P.yT / (n - 2 : ℝ) -
        sampleCov (control S) (leverage P) P.yC / (n - 2 : ℝ) ∧
    debiasedATE P m S =
      mean S (fun i => P.yT i - dot (P.x i) v) -
        mean (control S) (fun i => P.yC i - dot (P.x i) v) -
        dot (xMean P S - xMean P (control S)) (Nhat P m S - v) +
        sampleCov S (leverage P) P.yT / (n - 2 : ℝ) -
        sampleCov (control S) (leverage P) P.yC / (n - 2 : ℝ) := by
  simp only [mean_sub, mean_dot]
  simp only [debiasedATE, adjustedATE, biasEstimate, betaHat,
    nu2, Matrix.sub_mulVec, Matrix.one_mulVec, dot, Pi.sub_apply,
    sub_mul, mul_sub, Finset.sum_sub_distrib, sub_div]
  constructor <;> ring

/-- P005-T22(ii), finite algebra: the interacted debiased estimator equals
the difference of the two inverse-free arm expressions (Theorem 4.2, p. 1510). -/
theorem interacted_debiased_cancellation {n d : ℕ} (P : Population n d) (m : ℕ)
    (S : Finset (Fin n)) :
    interactedDebiasedATE P m S =
      (mean S P.yT - dot (xMean P S) (armN P S P.yT) +
        ((n : ℝ)-m) / ((n-2 : ℝ)*m) * sampleCov S (leverage P) P.yT) -
      (mean (control S) P.yC - dot (xMean P (control S)) (armN P (control S) P.yC) +
        (m : ℝ) / ((n-2 : ℝ)*(n-m)) * sampleCov (control S) (leverage P) P.yC) := by
  simp only [interactedDebiasedATE, interactedATE, interactedBiasEstimate,
    armBetaHat, armNu2, Matrix.sub_mulVec, Matrix.one_mulVec,
    dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

/-- P005-T15(a)–(c): collecting the two coefficients of equations (11) and
(12) gives the control covariance minus the treatment covariance over n-2
(Appendix B.2, p. 1516, corrected control covariance expression). -/
theorem collected_covariance_coefficients (t c : ℕ) (ht : 2 ≤ t) (hc : 2 ≤ c)
    (A B : ℝ) :
    (1 / ((t+c : ℕ) - 1 : ℝ) *
       ((c : ℝ)*((t+c : ℕ)-1 : ℝ) / (((c : ℝ)-1)*(t+c : ℕ))) -
      NTTC (t+c) t * ((t : ℝ)*((t+c : ℕ)-1 : ℝ) / (((c : ℝ)-1)*(t+c : ℕ)))) =
        1 / ((t+c : ℕ)-2 : ℝ) ∧
    (-1 / ((t+c : ℕ)-1 : ℝ) *
       ((t : ℝ)*((t+c : ℕ)-1 : ℝ) / (((t : ℝ)-1)*(t+c : ℕ))) +
      NTTT (t+c) t * ((t : ℝ)^2*((t+c : ℕ)-1 : ℝ) /
        ((c : ℝ)*((t : ℝ)-1)*(t+c : ℕ)))) = -1 / ((t+c : ℕ)-2 : ℝ) ∧
    (1 / ((t+c : ℕ)-1 : ℝ) *
       ((c : ℝ)*((t+c : ℕ)-1 : ℝ) / (((c : ℝ)-1)*(t+c : ℕ)) * B -
        (t : ℝ)*((t+c : ℕ)-1 : ℝ) / (((t : ℝ)-1)*(t+c : ℕ)) * A) +
      NTTT (t+c) t * ((t : ℝ)^2*((t+c : ℕ)-1 : ℝ) /
        ((c : ℝ)*((t : ℝ)-1)*(t+c : ℕ))) * A -
      NTTC (t+c) t * ((t : ℝ)*((t+c : ℕ)-1 : ℝ) /
        (((c : ℝ)-1)*(t+c : ℕ))) * B) =
      B / ((t+c : ℕ)-2 : ℝ) - A / ((t+c : ℕ)-2 : ℝ) := by
  have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hc' : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have t0 : (t : ℝ) ≠ 0 := by linarith
  have c0 : (c : ℝ) ≠ 0 := by linarith
  have t1 : (t : ℝ)-1 ≠ 0 := by linarith
  have c1 : (c : ℝ)-1 ≠ 0 := by linarith
  have n0 : (t : ℝ)+c ≠ 0 := by linarith
  have n1 : (t : ℝ)+c-1 ≠ 0 := by linarith
  have n2 : (t : ℝ)+c-2 ≠ 0 := by linarith
  dsimp [NTTT, NTTC]
  push_cast
  constructor
  · field_simp [t0, c0, t1, c1, n0, n1, n2]
    <;> ring
  constructor
  · field_simp [t0, c0, t1, c1, n0, n1, n2]
    <;> ring
  · field_simp [t0, c0, t1, c1, n0, n1, n2]
    <;> ring


/-- P005-T9(a): comparison of the two repaired logarithms at every d>=1. -/
theorem repaired_log_bounds (d : ℕ) (hd : 1 ≤ d) :
    Real.log (max d 2 : ℕ) ≤ Real.log (2*d : ℕ) ∧
    Real.log (2*d : ℕ) ≤ 2 * Real.log (max d 2 : ℕ) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : (0 : ℝ) < (max d 2 : ℕ) := by positivity
  constructor
  · apply Real.log_le_log hpos
    exact_mod_cast (show max d 2 ≤ 2*d by omega)
  · rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by linarith)]
    have h1 : Real.log 2 ≤ Real.log (max d 2 : ℕ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast le_max_right d 2)
    have h2 : Real.log (d : ℝ) ≤ Real.log (max d 2 : ℕ) :=
      Real.log_le_log (by linarith) (by exact_mod_cast le_max_left d 2)
    linarith

/-- P005-T9(b),(c): equivalence of the two repaired limit conditions, their
implication kappa -> 0, and equivalence to the printed condition if d>=2 eventually. -/
theorem repaired_log_conditions (d : ℕ → ℕ) (κ : ℕ → ℝ)
    (hd : ∀ᶠ n in atTop, 1 ≤ d n) (hκ : ∀ᶠ n in atTop, 0 ≤ κ n) :
    (Tendsto (fun n => κ n * Real.log (2*d n : ℕ)) atTop (nhds 0) ↔
      Tendsto (fun n => κ n * Real.log (max (d n) 2 : ℕ)) atTop (nhds 0)) ∧
    (Tendsto (fun n => κ n * Real.log (2*d n : ℕ)) atTop (nhds 0) →
      Tendsto κ atTop (nhds 0) ∧
      Tendsto (fun n => κ n * Real.log (d n)) atTop (nhds 0)) ∧
    ((∀ᶠ n in atTop, 2 ≤ d n) →
      (Tendsto (fun n => κ n * Real.log (d n)) atTop (nhds 0) ↔
        Tendsto (fun n => κ n * Real.log (2*d n : ℕ)) atTop (nhds 0))) := by
  let A := fun n => κ n * Real.log (max (d n) 2 : ℕ)
  let B := fun n => κ n * Real.log (2*d n : ℕ)
  have hb : ∀ᶠ n in atTop, 0 ≤ A n ∧ 0 ≤ B n ∧ A n ≤ B n ∧ B n ≤ 2*A n := by
    filter_upwards [hd, hκ] with n hdn hkn
    have hh := repaired_log_bounds (d n) hdn
    have ha : 0 ≤ Real.log (max (d n) 2 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ max (d n) 2 by omega))
    have hbb : 0 ≤ Real.log (2*d n : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*d n by omega))
    dsimp only [A, B]
    refine ⟨mul_nonneg hkn ha, mul_nonneg hkn hbb,
      mul_le_mul_of_nonneg_left hh.1 hkn, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hh.2 hkn]
  have heq : Tendsto B atTop (nhds 0) ↔ Tendsto A atTop (nhds 0) := by
    constructor
    · intro hB
      exact squeeze_zero' (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2.2.1) hB
    · intro hA
      have h2 : Tendsto (fun n => 2*A n) atTop (nhds 0) := by
        simpa using hA.const_mul (2 : ℝ)
      exact squeeze_zero' (hb.mono fun _ h => h.2.1) (hb.mono fun _ h => h.2.2.2) h2
  have hcons : Tendsto B atTop (nhds 0) → Tendsto κ atTop (nhds 0) ∧
      Tendsto (fun n => κ n*Real.log (d n)) atTop (nhds 0) := by
    intro hB
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hbound : ∀ᶠ n in atTop, κ n ≤ B n/Real.log 2 := by
      filter_upwards [hd, hκ] with n hdn hkn
      apply (le_div_iff₀ hlog2).mpr
      have hh : Real.log 2 ≤ Real.log (2*d n : ℕ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ 2*d n by omega))
      exact mul_le_mul_of_nonneg_left hh hkn
    have hg : Tendsto (fun n => B n/Real.log 2) atTop (nhds 0) := by
      simpa using hB.div_const (Real.log 2)
    have hk0 := squeeze_zero' hκ hbound hg
    have hp : ∀ᶠ n in atTop, 0 ≤ κ n*Real.log (d n) ∧ κ n*Real.log (d n) ≤ B n := by
      filter_upwards [hd, hκ] with n hdn hkn
      have hd' : (1 : ℝ) ≤ d n := by exact_mod_cast hdn
      refine ⟨mul_nonneg hkn (Real.log_nonneg hd'), ?_⟩
      have hh : Real.log (d n : ℝ) ≤ Real.log (2*d n : ℕ) :=
        Real.log_le_log (by linarith) (by exact_mod_cast (show d n ≤ 2*d n by omega))
      exact mul_le_mul_of_nonneg_left hh hkn
    exact ⟨hk0, squeeze_zero' (hp.mono fun _ h => h.1) (hp.mono fun _ h => h.2) hB⟩
  refine ⟨heq, hcons, ?_⟩
  intro hd2
  constructor
  · intro hprinted
    apply heq.mpr
    apply hprinted.congr'
    filter_upwards [hd2] with n hn
    dsimp [A]
    rw [max_eq_left hn]
  · intro hB
    exact (hcons hB).2


/-- The corrected inverse-free arm estimator from Appendix B.4 (p. 1518).
Its covariance coefficient is (n-m)/((n-2)m), for an arm of size m. -/
def armDebiased {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (y : Fin n → ℝ) : ℝ :=
  mean S y - dot (xMean P S) (armN P S y) +
    ((n : ℝ)-S.card) / ((n-2 : ℝ)*S.card) * sampleCov S (leverage P) y


/-- D_i is the binary treatment indicator (Section 2, pp. 1504–1505). -/
def indicator {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ S then 1 else 0

/-- The repeated-pair contribution sum_{i,j!=i} D_i D_j a_i b_i c_j
in Lemma A.2's proof (p. 1511). -/
def repeatedPair {n : ℕ} (S : Finset (Fin n)) (a b c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ univ.erase i, indicator S i * indicator S j * a i * b i * c j

/-- The all-distinct contribution in the proof of Lemma A.2 (pp. 1511–1512).
Every index ranges over Fin n; the printed upper limit N is repaired to n. -/
def distinctTriple {n : ℕ} (S : Finset (Fin n)) (a b c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j,
    indicator S i * indicator S j * indicator S k * a i * b j * c k


/-- P005-T16(d): simplification of the third-moment coefficient, with
n>=3, m>0, over the complete printed domain (Lemma A.2, p. 1512). -/
theorem third_moment_coefficient (n m : ℕ) (hn : 3 ≤ n) (hm : 0 < m) :
    (1/(m : ℝ)^3) * ((m : ℝ)/n - 3*(m : ℝ)*(m-1)/((n : ℝ)*(n-1)) +
      2*(m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))) = (1/(n : ℝ))*NTTT n m := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have n0 : (n : ℝ) ≠ 0 := by linarith
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  have n2 : (n : ℝ)-2 ≠ 0 := by linarith
  have m0 : (m : ℝ) ≠ 0 := ne_of_gt hm'
  dsimp [NTTT]
  field_simp [n0, n1, n2, m0]
  <;> ring






/-- Complete size-two randomization for the six-unit witnesses in P005-T5,
P005-T10 and P005-T12. Equal to the powerset-card design, not a new distribution. -/
def assignmentsSixTwo : Finset (Finset (Fin 6)) :=
  {{0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {1,2}, {1,3}, {1,4}, {1,5},
   {2,3}, {2,4}, {2,5}, {3,4}, {3,5}, {4,5}}

/-- Exact enumeration of all fifteen treatment pairs for the six-unit witnesses. -/
theorem design_six_two : design 6 2 = assignmentsSixTwo := by decide

/-- The uniform expectation over the actual fifteen assignments is their
explicit arithmetic average (P005-T5; complete randomization, p. 1505). -/
theorem expectation_six_two (f : Finset (Fin 6) → ℝ) :
    expectation 2 f = (f {0,1} + (f {0,2} + (f {0,3} + (f {0,4} + (f {0,5} + (f {1,2} + (f {1,3} + (f {1,4} + (f {1,5} + (f {2,3} + (f {2,4} + (f {2,5} + (f {3,4} + (f {3,5} + (f {4,5})))))))))))))))/15 := by
  unfold expectation
  rw [design_six_two]
  have hc : assignmentsSixTwo.card = 15 := by decide
  rw [hc]
  unfold assignmentsSixTwo
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton] <;> norm_num


/-- P005-T5's covariate vector (P005-E003). -/
def signX : Fin 6 → ℝ := ![-8/5, -1, 0, 3/5, 4/5, 6/5]
/-- P005-T5's fixed potential outcomes and one-dimensional covariates. -/
def signPopulation : Population 6 1 where
  x := fun i _ => signX i
  yT := fun i => signX i^2
  yC := fun i => 2*signX i^2 + 3

/-- P005-T5: a concrete normalized, fully invertible population contradicts
the printed third-component signs (Theorem 4.1, p. 1509). -/
theorem interacted_sign_counterexample :
    standardized signPopulation ∧ interactedRegular signPopulation 2 ∧
    popMean (fun i => signPopulation.yT i^2) ≤ 28 ∧
    popMean (fun i => signPopulation.yC i^2) ≤ 28 ∧
    (1/4 : ℝ) < pT 6 2 ∧ pT 6 2 < (3/4 : ℝ) ∧
    (design 6 2).card = 15 ∧
    leverageCov signPopulation signPopulation.yT = (434/625 : ℝ) ∧
    leverageCov signPopulation signPopulation.yC = (868/625 : ℝ) ∧
    expectation 2 (fun S => dot (xMean signPopulation (control S))
      (armNu3 signPopulation (control S) signPopulation.yC)) -
      expectation 2 (fun S => dot (xMean signPopulation S)
        (armNu3 signPopulation S signPopulation.yT)) = (217/2500 : ℝ) ∧
    NCCC 6 2 * leverageCov signPopulation signPopulation.yC -
      NTTT 6 2 * leverageCov signPopulation signPopulation.yT = -(217/2500 : ℝ) ∧
    expectation 2 (fun S => dot (xMean signPopulation (control S))
      (armNu3 signPopulation (control S) signPopulation.yC)) -
      expectation 2 (fun S => dot (xMean signPopulation S)
        (armNu3 signPopulation S signPopulation.yT)) ≠
      NCCC 6 2 * leverageCov signPopulation signPopulation.yC -
        NTTT 6 2 * leverageCov signPopulation signPopulation.yT := by
  have hstd : standardized signPopulation := by
    constructor
    · funext k
      fin_cases k
      norm_num [xMean, signPopulation, signX, mean, univ_six]
    · ext k l
      fin_cases k
      fin_cases l
      norm_num [gram, signPopulation, signX, popMean, mean, univ_six]
  have hreg : interactedRegular signPopulation 2 := by
    unfold interactedRegular
    intro S hS
    rw [design_six_two] at hS
    simp only [assignmentsSixTwo, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [armL, signPopulation, signX, xMean, popMean, mean, control,
      univ_six, Matrix.det_unique, Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, Finset.filter_empty]
  refine ⟨hstd, hreg, ?_⟩
  have hc : (design 6 2).card = 15 := by decide
  norm_num [hc, signPopulation, signX, xMean, dot, armNu3, centered,
    leverage, leverageCov, sampleCov, popCov, popMean, mean, expectation_six_two,
    pT, NCCC, NTTT, control, univ_six, Finset.sdiff_eq_filter,
    Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty, Fin.sum_univ_succ]

/-- A one-covariate population, allowing an exact change of scale in the
witnesses of P005-T3, P005-T10 and P005-T12 (Section 2, p. 1504). -/
def scalarPopulation {n : ℕ} (a yT yC : Fin n → ℝ) (s : ℝ) : Population n 1 where
  x := fun i _ => s*a i
  yT := yT
  yC := yC

/-- Scaling a scalar covariate by s scales its sample covariance with y by s
(Appendix A.2, p. 1510); used to connect rational computations to sqrt-scaled x. -/
theorem sampleCov_scale_left {n : ℕ} (S : Finset (Fin n)) (a y : Fin n → ℝ) (s : ℝ) :
    sampleCov S (fun i => s*a i) y = s * sampleCov S a y := by
  have hf : (fun i => (s*a i)*y i) = (fun i => s*(a i*y i)) := by funext i; ring
  simp only [sampleCov, hf, mean_mul]
  ring

/-- Scaling both scalar vectors scales their sample covariance by s^2
(Appendix A.2, p. 1510). -/
theorem sampleCov_scale_both {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) (s : ℝ) :
    sampleCov S (fun i => s*a i) (fun i => s*a i) = s^2 * sampleCov S a a := by
  have hf : (fun i => (s*a i)*(s*a i)) = (fun i => s^2*(a i*a i)) := by funext i; ring
  simp only [sampleCov, hf, mean_mul]
  ring

/-- In one dimension, scaling the covariate by `s` multiplies `bar x' Nhat`
by `s²`. For P005-T10, `s = sqrt(3/20)` gives the rational factor `3/20`.
This identity ties the rational formula to the actual paper objects. -/
theorem scalar_dot_armN {n : ℕ} (a yT yC y : Fin n → ℝ) (s : ℝ)
    (S : Finset (Fin n)) :
    dot (xMean (scalarPopulation a yT yC s) S)
      (armN (scalarPopulation a yT yC s) S y) =
        s^2 * mean S a * sampleCov S a y := by
  have hf : (fun i => y i*(s*a i)) = (fun i => s*(a i*y i)) := by funext i; ring
  simp only [dot, Fin.sum_univ_succ, Finset.sum_empty, add_zero,
    xMean, armN, scalarPopulation, hf, mean_mul, sampleCov]
  ring

/-- The actual leverage of the scaled one-covariate population is s^2 a_i^2
(equation (4), p. 1506). -/
theorem scalar_leverage {n : ℕ} (a yT yC : Fin n → ℝ) (s : ℝ) :
    leverage (scalarPopulation a yT yC s) = fun i => s^2*a i^2 := by
  funext i
  simp [leverage, dot, scalarPopulation, Fin.sum_univ_succ]
  ring

/-- The one-dimensional within-arm OLS slope is Covhat(x,y)/Covhat(x,x)
(Section 4, p. 1509). This is the scalar version of Lhat^{-1}Nhat. -/
def scalarSlope {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → ℝ) : ℝ :=
  sampleCov S x y / sampleCov S x x

/-- In one dimension, the determinant of the actual arm covariance matrix
is the scalar sample variance, including the square of the covariate scale. -/
theorem scalar_armL_det {n : ℕ} (a yT yC : Fin n → ℝ) (s : ℝ) (S : Finset (Fin n)) :
    (armL (scalarPopulation a yT yC s) S).det = s^2 * sampleCov S a a := by
  rw [Matrix.det_unique]
  change sampleCov S (fun i => s*a i) (fun i => s*a i) = _
  exact sampleCov_scale_both S a s

/-- A centered scalar covariate with unit second moment satisfies exactly
Assumption 2 (p. 1505), as a one-column population. -/
theorem standardized_scalar {n : ℕ} (a yT yC : Fin n → ℝ) (s : ℝ)
    (h0 : popMean a = 0) (h2 : s^2 * popMean (fun i => a i^2) = 1) :
    standardized (scalarPopulation a yT yC s) := by
  constructor
  · funext k
    change mean univ (fun i => s*a i) = 0
    rw [mean_mul]
    change s*popMean a = 0
    rw [h0, mul_zero]
  · ext k l
    fin_cases k
    fin_cases l
    have hf : (fun i => (s*a i)*(s*a i)) = (fun i => s^2*a i^2) := by funext i; ring
    change popMean (fun i => (s*a i)*(s*a i)) = 1
    rw [hf]
    change mean univ (fun i => s^2*a i^2) = 1
    rw [mean_mul]
    exact h2

/-- The scalar product bar x times the OLS slope is invariant to a nonzero
covariate scale; this connects P005-T12's rational calculation to x=sqrt(3/20)a. -/
theorem scalar_slope_product_scale {n : ℕ} (S : Finset (Fin n)) (a y : Fin n → ℝ)
    (s : ℝ) (hs : s ≠ 0) :
    mean S (fun i => s*a i) * scalarSlope S (fun i => s*a i) y =
      mean S a * sampleCov S a y / sampleCov S a a := by
  unfold scalarSlope
  rw [sampleCov_scale_both]
  simp only [sampleCov_scale_left, mean_mul]
  calc
    (s*mean S a)*(s*sampleCov S a y/(s^2*sampleCov S a a)) =
        s^2*(mean S a*sampleCov S a y)/(s^2*sampleCov S a a) := by ring
    _ = _ := mul_div_mul_left _ _ (pow_ne_zero 2 hs)

/-- In the scalar inverse component bar x_C(Lhat_t^{-1}-1)Nhat_C,
the square root scale cancels only from the inverse part (p. 1518). -/
theorem scalar_inverse_product_scale {n : ℕ} (S H : Finset (Fin n)) (a y : Fin n → ℝ)
    (s : ℝ) (hs : s ≠ 0) :
    mean S (fun i => s*a i) * ((sampleCov H (fun i => s*a i) (fun i => s*a i))⁻¹-1) *
      sampleCov S (fun i => s*a i) y =
    mean S a*sampleCov S a y/sampleCov H a a - s^2*mean S a*sampleCov S a y := by
  rw [sampleCov_scale_both]
  simp only [sampleCov_scale_left, mean_mul]
  calc
    (s*mean S a)*((s^2*sampleCov H a a)⁻¹-1)*(s*sampleCov S a y) =
        s^2*(mean S a*sampleCov S a y)/(s^2*sampleCov H a a) - s^2*mean S a*sampleCov S a y := by
      rw [div_eq_mul_inv]
      ring
    _ = _ := by rw [mul_div_mul_left _ _ (pow_ne_zero 2 hs)]


/-- P005-T10 and P005-T12's unscaled rational covariates. -/
def weightA : Fin 6 → ℝ := ![-3, -2, -1, 0, 1, 5]
/-- P005-T10 and P005-T12's nonzero potential outcome a_i^2. -/
def weightY : Fin 6 → ℝ := fun i => weightA i^2
/-- P005-T10's actual standardized covariate scale sqrt(3/20). -/
def weightScale : ℝ := Real.sqrt (3/20)
/-- P005-T10's population: y(1)=a^2, y(0)=0, x=sqrt(3/20)a. -/
def weightPopulation : Population 6 1 := scalarPopulation weightA weightY (fun _ => 0) weightScale

/-- P005-T10: the printed weight n_T/((n-2)n_C) gives the wrong treated
expectation, while the derived weight n_C/((n-2)n_T) is unbiased (p. 1518). -/
theorem interacted_weight_counterexample :
    standardized weightPopulation ∧ interactedRegular weightPopulation 2 ∧
    popMean (fun i => weightY i^2) ≤ 121 ∧
    (1/4 : ℝ) < pT 6 2 ∧ pT 6 2 < (3/4 : ℝ) ∧
    expectation 2 (fun S => mean S weightY - dot (xMean weightPopulation S) (armN weightPopulation S weightY) +
      (1/8 : ℝ)*sampleCov S (leverage weightPopulation) weightY) = (4913/1200 : ℝ) ∧
    expectation 2 (fun S => mean S weightY - dot (xMean weightPopulation S) (armN weightPopulation S weightY) +
      (1/2 : ℝ)*sampleCov S (leverage weightPopulation) weightY) = (20/3 : ℝ) ∧
    popMean weightY = (20/3 : ℝ) ∧
    expectation 2 (fun S => mean S weightY - dot (xMean weightPopulation S) (armN weightPopulation S weightY) +
      (1/8 : ℝ)*sampleCov S (leverage weightPopulation) weightY) ≠ popMean weightY := by
  have hs : weightScale^2 = (3/20 : ℝ) := Real.sq_sqrt (by norm_num)
  have h0 : popMean weightA = 0 := by
    norm_num [popMean, mean, weightA, univ_six]
  have h2 : weightScale^2*popMean (fun i => weightA i^2) = 1 := by
    norm_num [hs, popMean, mean, weightA, univ_six]
  have hstd : standardized weightPopulation := standardized_scalar _ _ _ _ h0 h2
  have hreg : interactedRegular weightPopulation 2 := by
    unfold interactedRegular
    simp only [weightPopulation, scalar_armL_det, hs]
    intro S hS
    rw [design_six_two] at hS
    simp only [assignmentsSixTwo, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [sampleCov, mean, weightA,
      control, univ_six, Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, Finset.filter_empty]
  refine ⟨hstd, hreg, ?_⟩
  simp only [weightPopulation, scalar_dot_armN, scalar_leverage, hs]
  norm_num [weightA, weightY, pT, expectation_six_two, sampleCov, mean, popMean, univ_six]


/-- P005-T12's actual covariates, x=sqrt(3/20)a. -/
def weightX (i : Fin 6) : ℝ := weightScale * weightA i

/-- P005-T12: the expression printed with Lhat_T^{-1} does not estimate
the control bias, while the repaired Lhat_C^{-1} expression does (p. 1518).
In dimension one the matrix inverse is written as reciprocal sample variance. -/
theorem interacted_inverse_counterexample :
    popMean weightX = 0 ∧ popMean (fun i => weightX i^2) = 1 ∧
    (∀ S ∈ design 6 2, 0 < sampleCov S weightX weightX ∧
      0 < sampleCov (control S) weightX weightX) ∧
    popMean (fun i => weightY i^2) ≤ 121 ∧
    (1/4 : ℝ) < pT 6 2 ∧ pT 6 2 < (3/4 : ℝ) ∧
    expectation 2 (fun S => mean (control S) weightX * scalarSlope (control S) weightX weightY) =
      (31085815448171/17062566567774 : ℝ) ∧
    expectation 2 (fun S => (1/8 : ℝ)*sampleCov (control S) (fun i => weightX i^2) weightY +
      mean (control S) weightX * ((sampleCov S weightX weightX)⁻¹ - 1) * sampleCov (control S) weightX weightY) =
      (12010469/846720 : ℝ) ∧
    expectation 2 (fun S => (1/8 : ℝ)*sampleCov (control S) (fun i => weightX i^2) weightY +
      mean (control S) weightX * ((sampleCov (control S) weightX weightX)⁻¹ - 1) *
        sampleCov (control S) weightX weightY) = (31085815448171/17062566567774 : ℝ) ∧
    expectation 2 (fun S => mean (control S) weightX * scalarSlope (control S) weightX weightY) ≠
      expectation 2 (fun S => (1/8 : ℝ)*sampleCov (control S) (fun i => weightX i^2) weightY +
        mean (control S) weightX * ((sampleCov S weightX weightX)⁻¹ - 1) * sampleCov (control S) weightX weightY) := by
  have hs : weightScale^2 = (3/20 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : weightScale ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  have hxx : (fun i => weightX i^2) = (fun i => (3/20 : ℝ)*weightA i^2) := by
    funext i
    dsimp only [weightX]
    rw [mul_pow, hs]
  have h0 : popMean weightX = 0 := by
    change mean univ (fun i => weightScale*weightA i) = 0
    rw [mean_mul]
    have h0a : mean univ weightA = 0 := by norm_num [mean, weightA, univ_six]
    rw [h0a, mul_zero]
  have h2 : popMean (fun i => weightX i^2) = 1 := by
    rw [hxx]
    norm_num [popMean, mean_mul, mean, weightA, univ_six]
  have hreg : ∀ S ∈ design 6 2, 0 < sampleCov S weightX weightX ∧
      0 < sampleCov (control S) weightX weightX := by
    change ∀ S ∈ design 6 2,
      0 < sampleCov S (fun i => weightScale*weightA i) (fun i => weightScale*weightA i) ∧
      0 < sampleCov (control S) (fun i => weightScale*weightA i) (fun i => weightScale*weightA i)
    simp only [sampleCov_scale_both, hs]
    intro S hS
    rw [design_six_two] at hS
    simp only [assignmentsSixTwo, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [sampleCov, mean, weightA,
      control, univ_six, Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, Finset.filter_empty]
  refine ⟨h0, h2, hreg, ?_⟩
  have hslope : ∀ S : Finset (Fin 6),
      mean S weightX*scalarSlope S weightX weightY =
        mean S weightA*sampleCov S weightA weightY/sampleCov S weightA weightA := by
    intro S
    exact scalar_slope_product_scale S weightA weightY weightScale hs0
  have hinverse : ∀ S H : Finset (Fin 6),
      mean S weightX*((sampleCov H weightX weightX)⁻¹-1)*sampleCov S weightX weightY =
        mean S weightA*sampleCov S weightA weightY/sampleCov H weightA weightA -
          weightScale^2*mean S weightA*sampleCov S weightA weightY := by
    intro S H
    exact scalar_inverse_product_scale S H weightA weightY weightScale hs0
  simp only [hslope, hinverse, hxx, hs]
  norm_num [weightA, weightY, pT, expectation_six_two, sampleCov, mean, popMean,
    control, univ_six, Finset.sdiff_eq_filter, Finset.filter_insert,
    Finset.filter_singleton, Finset.filter_empty]

/-- P005-T3's unscaled covariate magnitudes and signs (P005-E002).
Two high-leverage units followed by seven pairs (1,-1). -/
def leverageA : Fin 16 → ℝ := ![8,-8,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1]
/-- P005-T3's fixed treated potential outcomes. -/
def leverageY : Fin 16 → ℝ := fun i => if i.val < 2 then 1/64 else 1
/-- P005-T3's population, x=sqrt(8/71)a, y(0)=0 (P005-E002). -/
def leveragePopulation : Population 16 1 :=
  scalarPopulation leverageA leverageY (fun _ => 0) (Real.sqrt (8/71))


/-- P005-T7's v-vector: special unit has outcome zero; ordinary units have
an evenly spaced grid in [-1,1] (P005-E001). -/
def spikeV (n : ℕ) (i : Fin n) : ℝ :=
  if i.val = 0 then 0 else -1 + 2*(i.val-1 : ℕ)/(n-2 : ℝ)
/-- P005-T7's a-vector: 1 at unit 1 and epsilon v_i elsewhere,
with epsilon=n^{-2} (P005-E001). -/
def spikeA (n : ℕ) (i : Fin n) : ℝ :=
  if i.val = 0 then 1 else spikeV n i/(n : ℝ)^2
/-- P005-T7's z_i=a_i-1/n (P005-E001). -/
def spikeZ (n : ℕ) (i : Fin n) : ℝ := spikeA n i - 1/(n : ℝ)
/-- P005-T7's q=n^{-1}sum z_i^2 (P005-E001). -/
def spikeQ (n : ℕ) : ℝ := popMean (fun i => spikeZ n i^2)
/-- P005-T7's exact sequence, x_i=z_i/sqrt(q), y_i(1)=y_i(0)=v_i.
All populations, outcomes and covariates are explicitly specified. -/
def spikePopulation (n : ℕ) : Population n 1 where
  x := fun i _ => spikeZ n i / Real.sqrt (spikeQ n)
  yT := spikeV n
  yC := spikeV n


/-- P005-T7(ii), finite: at d=1 the printed kappa log d condition is
identically zero, regardless of the leverage sequence (p. 1510). -/
theorem univariate_printed_condition (κ : ℕ → ℝ) :
    (∀ n, κ n * Real.log (1 : ℝ) = 0) ∧
    Tendsto (fun n => κ n * Real.log (1 : ℝ)) atTop (nhds 0) := by
  simp only [Real.log_one, mul_zero]
  exact ⟨fun _ => trivial, tendsto_const_nhds⟩


/-- Linearity under addition for the paper's finite averages (p. 1505). -/
theorem mean_add {n : ℕ} (S : Finset (Fin n)) (a b : Fin n → ℝ) :
    mean S (fun i => a i+b i) = mean S a + mean S b := by
  simp [mean, Finset.sum_add_distrib, add_div]

/-- The mean of nonnegative real entries is nonnegative (p. 1505 notation). -/
theorem mean_nonneg {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) : 0 ≤ mean S a := by
  exact div_nonneg (Finset.sum_nonneg ha) (Nat.cast_nonneg S.card)

/-- An entrywise bound is preserved by the paper's finite average (p. 1505). -/
theorem mean_mono {n : ℕ} (S : Finset (Fin n)) (a b : Fin n → ℝ)
    (h : ∀ i ∈ S, a i ≤ b i) : mean S a ≤ mean S b := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg S.card)

/-- P005-T4(b),(c),(d) and P005-T17(a): subtracting a mean reduces the
mean square. This is an exact finite identity. -/
theorem mean_square_centering {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (a : Fin n → ℝ) :
    mean S (fun i => (a i-mean S a)^2) = mean S (fun i => a i^2) - (mean S a)^2 ∧
    mean S (fun i => (a i-mean S a)^2) ≤ mean S (fun i => a i^2) := by
  have hf : (fun i => (a i-mean S a)^2) =
      (fun i => (a i^2 - (2*mean S a)*a i) + (mean S a)^2) := by funext i; ring
  have he : mean S (fun i => (a i-mean S a)^2) =
      mean S (fun i => a i^2) - (mean S a)^2 := by
    rw [hf, mean_add, mean_sub, mean_mul, mean_const S hS]
    ring
  exact ⟨he, by rw [he]; linarith [sq_nonneg (mean S a)]⟩

/-- P005-T2(d): Var(U-V) <= 2 Var U + 2 Var V, over the actual finite
randomization distribution (Lemma A.1 proof, p. 1511). -/
theorem variance_difference_bound {n : ℕ} (m : ℕ) (f g : Finset (Fin n) → ℝ) :
    variance m (fun S => f S-g S) ≤ 2*variance m f + 2*variance m g := by
  have hE : expectation m (fun S => f S-g S) = expectation m f-expectation m g := by
    simp [expectation, Finset.sum_sub_distrib, sub_div]
  unfold variance
  rw [hE]
  simp only [expectation]
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S hS
  have hh := sq_nonneg ((f S-expectation m f)+(g S-expectation m g))
  simp only [expectation] at hh
  nlinarith [hh]

/-- P005-T17(b): the contraction identity with matching leverage and
residual indices, under sum_i x_i x_i' = n I_d (p. 1514, corrected third line). -/
theorem covariate_contraction {n d : ℕ} (P : Population n d) (hn : 0 < n)
    (hG : gram P = 1) (a : Fin n → ℝ) :
    (∑ i, ∑ j, (dot (P.x i) (P.x j) * a j)^2) =
      (n : ℝ) * ∑ j, a j^2 * leverage P j := by
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hg : ∀ k l : Fin d, (∑ i, P.x i k*P.x i l) = (n : ℝ)*(if k=l then 1 else 0) := by
    intro k l
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M k l) hG
    have hh : (∑ i, P.x i k*P.x i l)/(n : ℝ) = if k=l then 1 else 0 := by
      simpa [gram, popMean, mean, Matrix.one_apply] using h
    have := (div_eq_iff n0).mp hh
    simpa [mul_comm] using this
  have projection : ∀ v : Fin d → ℝ,
      (∑ i, (dot (P.x i) v)^2) = (n : ℝ)*dot v v := by
    intro v
    have hexpand : ∀ i, (dot (P.x i) v)^2 =
        ∑ k, ∑ l, (P.x i k*v k)*(P.x i l*v l) := by
      intro i
      simp only [dot, pow_two]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    simp_rw [hexpand]
    unfold dot
    calc
      (∑ i, ∑ k, ∑ l, (P.x i k*v k)*(P.x i l*v l)) =
          ∑ k, ∑ l, ∑ i, (P.x i k*v k)*(P.x i l*v l) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_comm]
      _ = ∑ k, ∑ l, (∑ i, P.x i k*P.x i l)*v k*v l := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (n : ℝ)*∑ k, v k*v k := by
        simp_rw [hg]
        simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ i, (dot (P.x i) (P.x j)*a j)^2) =
        a j^2 * ∑ i, (dot (P.x i) (P.x j))^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (n : ℝ)*(a j^2*leverage P j) := by
      rw [projection]
      simp only [leverage]
      ring

/-- P005-T18: the bracketed-vector identities in the corrected three-line
p. 1514 display, under precisely its weighted population normal equation. -/
theorem corrected_residual_brackets {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (S : Finset (Fin n)) (hS : S.card = m)
    (eT eC : Fin n → ℝ)
    (he : pT n m • populationSlope P eT + pC n m • populationSlope P eC = 0) :
    let A := populationSlope P (fun i => eT i-eC i)
    let B := populationSlope P eC
    let U := fun k => (∑ i ∈ S, P.x i k*(eT i-eC i))/(n : ℝ)
    B = -pT n m • A ∧
    U+B = (fun k => (∑ i ∈ S, (P.x i k*(eT i-eC i) + (1/pT n m)*B k))/(n : ℝ)) ∧
    U+B = (fun k => (∑ i ∈ S, (P.x i k*(eT i-eC i) - A k))/(n : ℝ)) ∧
    (1/pC n m)*dot (xMean P S) (U+B) =
      (1/pC n m)*dot (xMean P S)
        (fun k => (∑ i ∈ S, (P.x i k*(eT i-eC i) - A k))/(n : ℝ)) := by
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have m0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have pt0 : pT n m ≠ 0 := div_ne_zero m0 n0
  have hp : pT n m + pC n m = 1 := by
    dsimp [pT, pC]
    field_simp [n0]
    ring
  have hA : populationSlope P (fun i => eT i-eC i) =
      populationSlope P eT - populationSlope P eC := by
    funext k
    simp [populationSlope, popMean, mul_sub, sub_mul, mean_sub, mul_comm]
  have hB : populationSlope P eC = -pT n m • populationSlope P (fun i => eT i-eC i) := by
    rw [hA]
    funext k
    have hk := congrArg (fun v : Fin d → ℝ => v k) he
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have hpc : pC n m = 1-pT n m := by linarith [hp]
    rw [hpc] at hk
    nlinarith [hk]
  have hfirst : (fun k => (∑ i ∈ S, P.x i k*(eT i-eC i))/(n : ℝ)) + populationSlope P eC =
      (fun k => (∑ i ∈ S, (P.x i k*(eT i-eC i) + (1/pT n m)*populationSlope P eC k))/(n : ℝ)) := by
    funext k
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hS]
    dsimp [pT]
    field_simp [n0, m0]
    <;> ring
  have hsecond : (fun k => (∑ i ∈ S, P.x i k*(eT i-eC i))/(n : ℝ)) + populationSlope P eC =
      (fun k => (∑ i ∈ S, (P.x i k*(eT i-eC i) - populationSlope P (fun j => eT j-eC j) k))/(n : ℝ)) := by
    rw [hfirst]
    funext k
    apply congrArg (fun z : ℝ => z/(n : ℝ))
    apply Finset.sum_congr rfl
    intro i hi
    have hb := congrArg (fun v : Fin d → ℝ => v k) hB
    simp only [Pi.smul_apply, smul_eq_mul] at hb
    rw [hb]
    field_simp [pt0]
    <;> ring
  dsimp only
  exact ⟨hB, hfirst, hsecond, congrArg (fun v => (1/pC n m)*dot (xMean P S) v) hsecond⟩


/-- The probability of including a specified set of r units under complete
randomization (Section 2, p. 1505; Lemma A.2 proof, pp. 1511–1512).
This count lemma supplies the elementary sampling fact from first principles. -/
theorem inclusion_count {n m : ℕ} (R : Finset (Fin n)) (hR : R.card ≤ m) :
    expectation m (fun S => if R ⊆ S then 1 else 0) =
      ((n-R.card).choose (m-R.card) : ℝ) / (n.choose m : ℝ) := by
  classical
  have hc := Finset.card_filter_powersetCard_subset R (univ : Finset (Fin n)) m
    (Finset.subset_univ R) hR
  simpa [expectation, design, Finset.sum_boole, Finset.card_powersetCard] using
    congrArg (fun k : ℕ => (k : ℝ)/(n.choose m : ℝ)) hc

/-- First inclusion moment E D_i=m/n (Section 2, p. 1505), under the
uniform fixed-size design. No limiting or superpopulation argument is used. -/
theorem indicator_expectation {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (i : Fin n) : expectation m (fun S => indicator S i) = (m : ℝ)/n := by
  have hinc := inclusion_count (m := m) {i} (by simp only [Finset.card_singleton]; omega)
  have hc : n * (n-1).choose (m-1) = n.choose m * m := by
    simpa [Nat.sub_add_cancel (show 1 ≤ n by omega),
      Nat.sub_add_cancel (show 1 ≤ m by omega)] using Nat.add_one_mul_choose_eq (n-1) (m-1)
  have hc' : (n : ℝ) * ((n-1).choose (m-1) : ℝ) = (n.choose m : ℝ)*m := by
    exact_mod_cast hc
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have C0 : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hmn)
  have hh : expectation m (fun S => indicator S i) =
      ((n-1).choose (m-1) : ℝ)/(n.choose m : ℝ) := by
    simpa [indicator] using hinc
  rw [hh]
  field_simp [n0, C0]
  nlinarith [hc']

/-- Expectation commutes with finite sums (p. 1505 randomization convention).
This is a finite-sum identity independent of moment and matrix hypotheses. -/
theorem expectation_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (m : ℕ) (f : ι → Finset (Fin n) → ℝ) :
    expectation m (fun S => ∑ i, f i S) = ∑ i, expectation m (f i) := by
  simp only [expectation, Finset.sum_div]
  exact Finset.sum_comm

/-- Multiplication by a fixed scalar commutes with design expectation (p. 1505). -/
theorem expectation_mul {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) (c : ℝ) :
    expectation m (fun S => c*f S) = c*expectation m f := by
  unfold expectation
  rw [← Finset.mul_sum]
  ring

/-- Replacing a random variable by a pointwise equal one on the design
support leaves its expectation unchanged (p. 1505). -/
theorem expectation_congr {n : ℕ} (m : ℕ) (f g : Finset (Fin n) → ℝ)
    (h : ∀ S ∈ design n m, f S = g S) : expectation m f = expectation m g := by
  unfold expectation
  rw [Finset.sum_congr rfl h]

/-- Summing D_i a_i over the population is summing a_i over [T]
(Section 2, pp. 1504–1505). -/
theorem indicator_sum {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) :
    (∑ i, indicator S i * a i) = ∑ i ∈ S, a i := by
  calc
    (∑ i, indicator S i*a i) = ∑ i ∈ S, indicator S i*a i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i hi hnot
      simp [indicator, hnot]
    _ = ∑ i ∈ S, a i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [indicator, hi]

/-- The simple-random-sample mean is unbiased (Section 2, p. 1505;
finite lemma for Theorems 3.1, 3.2, 4.1 and 4.2). -/
theorem mean_unbiased {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (a : Fin n → ℝ) : expectation m (fun S => mean S a) = popMean a := by
  have hform : ∀ S ∈ design n m,
      mean S a = (1/(m : ℝ)) * ∑ i, a i * indicator S i := by
    intro S hS
    have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
    rw [mean, hs, ← indicator_sum S a]
    have hsum : (∑ i, indicator S i*a i) = ∑ i, a i*indicator S i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    ring
  rw [expectation_congr m _ _ hform, expectation_mul, expectation_sum]
  simp_rw [expectation_mul, indicator_expectation hn hm hmn]
  simp only [popMean, mean, Finset.card_univ, Fintype.card_fin,
    ← Finset.sum_mul]
  have m0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp [m0, n0]
  <;> ring


/-- h_i is a sum of squares, hence nonnegative (equation (4), p. 1506). -/
theorem leverage_nonneg {n d : ℕ} (P : Population n d) (i : Fin n) : 0 ≤ leverage P i := by
  unfold leverage dot
  apply Finset.sum_nonneg
  intro k hk
  exact mul_self_nonneg (P.x i k)

/-- P005-T4(a), finite: h_i<=n kappa for the actual finite maximum in (4). -/
theorem leverage_le_maximum {n d : ℕ} (P : Population n d) (hn : 0 < n) (i : Fin n) :
    leverage P i ≤ (n : ℝ)*kappa P := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : BddAbove (Set.range (fun j => leverage P j/(n : ℝ))) := (Set.finite_range _).bddAbove
  have h := le_csSup hb (Set.mem_range_self i)
  have hh : leverage P i ≤ kappa P*(n : ℝ) := (div_le_iff₀ hn').mp h
  simpa [mul_comm] using hh

/-- P005-T4(a): mean h = tr(bar xx') = d under Assumption 2 (p. 1517). -/
theorem leverage_population_mean {n d : ℕ} (P : Population n d) (hG : gram P = 1) :
    popMean (leverage P) = d := by
  have hh : ∀ k : Fin d, popMean (fun i => P.x i k*P.x i k) = 1 := by
    intro k
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M k k) hG
    simpa [gram] using h
  calc
    popMean (leverage P) = ∑ k, popMean (fun i => P.x i k*P.x i k) := by
      simp only [popMean, leverage, dot, mean, Finset.sum_div]
      exact Finset.sum_comm
    _ = ∑ _k : Fin d, (1 : ℝ) := Finset.sum_congr rfl (fun k _ => hh k)
    _ = d := by simp

/-- P005-T4(a)–(d): all deterministic bounds in the centered leverage
repair, under the actual centered/normalized covariates and outcome moment bound. -/
theorem centered_leverage_moment_bounds {n d : ℕ} (P : Population n d) (hn : 0 < n)
    (hG : gram P = 1) (y : Fin n → ℝ) (K : ℝ) (hK : popMean (fun i => y i^2) ≤ K) :
    let u := fun i => leverage P i-(d : ℝ)
    let v := centered y
    (d : ℝ) ≤ n*kappa P ∧
    (∀ i, |u i| ≤ n*kappa P) ∧
    popMean (fun i => u i^2) = popMean (fun i => leverage P i^2)-(d : ℝ)^2 ∧
    popMean (fun i => u i^2) ≤ n*kappa P*d ∧
    popMean (fun i => v i^2) = popMean (fun i => y i^2)-popMean y^2 ∧
    popMean (fun i => v i^2) ≤ K ∧
    popMean (fun i => (u i*v i-popMean (fun j => u j*v j))^2) ≤
      popMean (fun i => u i^2*v i^2) ∧
    popMean (fun i => u i^2*v i^2) ≤ (n : ℝ)^2*kappa P^2*K := by
  have hS : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩, mem_univ _⟩
  have hmean := leverage_population_mean P hG
  have hdl : (d : ℝ) ≤ n*kappa P := by
    rw [← hmean]
    have hh := mean_mono univ (leverage P) (fun _ => (n : ℝ)*kappa P)
      (fun i _ => leverage_le_maximum P hn i)
    rwa [mean_const univ hS] at hh
  have hN : 0 ≤ (n : ℝ)*kappa P := le_trans (Nat.cast_nonneg d) hdl
  have hu : ∀ i, |leverage P i-(d : ℝ)| ≤ n*kappa P := by
    intro i
    apply abs_le.mpr
    constructor <;> linarith [leverage_nonneg P i, leverage_le_maximum P hn i]
  have hcH := mean_square_centering univ hS (leverage P)
  have huEq : popMean (fun i => (leverage P i-(d : ℝ))^2) =
      popMean (fun i => leverage P i^2)-(d : ℝ)^2 := by
    have hcheq := hcH.1
    change popMean (fun i => (leverage P i-popMean (leverage P))^2) =
      popMean (fun i => leverage P i^2)-popMean (leverage P)^2 at hcheq
    simpa only [hmean] using hcheq
  have hraw : popMean (fun i => leverage P i^2) ≤ n*kappa P*d := by
    calc
      popMean (fun i => leverage P i^2) ≤ popMean (fun i => ((n : ℝ)*kappa P)*leverage P i) := by
        apply mean_mono
        intro i hi
        nlinarith [mul_le_mul_of_nonneg_right (leverage_le_maximum P hn i) (leverage_nonneg P i)]
      _ = n*kappa P*d := by rw [popMean, mean_mul]; change _*popMean (leverage P)=_; rw [hmean]
  have hv := mean_square_centering univ hS y
  have hvEq : popMean (fun i => centered y i^2) = popMean (fun i => y i^2)-popMean y^2 := by
    simpa only [centered, popMean] using hv.1
  have hvK : popMean (fun i => centered y i^2) ≤ K := by
    rw [hvEq]
    linarith [sq_nonneg (popMean y)]
  have hp := mean_square_centering univ hS (fun i => (leverage P i-(d : ℝ))*centered y i)
  have hpbound : popMean (fun i => (leverage P i-(d : ℝ))^2*centered y i^2) ≤
      (n : ℝ)^2*kappa P^2*K := by
    have hsquared : ∀ i, (leverage P i-(d : ℝ))^2 ≤ ((n : ℝ)*kappa P)^2 := by
      intro i
      have hh := (sq_le_sq₀ (abs_nonneg _) hN).mpr (hu i)
      simpa only [sq_abs] using hh
    calc
      popMean (fun i => (leverage P i-(d : ℝ))^2*centered y i^2) ≤
          popMean (fun i => ((n : ℝ)*kappa P)^2*centered y i^2) := by
        apply mean_mono
        intro i hi
        exact mul_le_mul_of_nonneg_right (hsquared i) (sq_nonneg _)
      _ = ((n : ℝ)*kappa P)^2*popMean (fun i => centered y i^2) := mean_mul _ _ _
      _ ≤ ((n : ℝ)*kappa P)^2*K := mul_le_mul_of_nonneg_left hvK (sq_nonneg _)
      _ = (n : ℝ)^2*kappa P^2*K := by ring
  dsimp only
  refine ⟨hdl, hu, huEq, ?_, hvEq, hvK, ?_, hpbound⟩
  · rw [huEq]
    linarith [sq_nonneg (d : ℝ)]
  · simpa only [popMean, mul_pow] using hp.2


/-- Averaging x_i a_i and then projecting is the same as averaging the
projected products (p. 1505); used in the p. 1514 centering correction. -/
theorem dot_population_slope {n d : ℕ} (P : Population n d)
    (v : Fin d → ℝ) (a : Fin n → ℝ) :
    dot v (populationSlope P a) = popMean (fun i => dot v (P.x i)*a i) := by
  simp only [dot, populationSlope, popMean, mean, mul_div_assoc,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- P005-T17(a)–(d): the entire corrected deterministic variance-bound
chain with a matched dummy index (Appendix B.1.1, p. 1514). -/
theorem corrected_contraction_chain {n d m : ℕ} (P : Population n d)
    (hn : 2 ≤ n) (hm : 0 < m) (hmn : m < n) (hG : gram P = 1) (δ : Fin n → ℝ) :
    let μ := populationSlope P δ
    (∀ i, (∑ j, (dot (P.x i) (fun k => P.x j k*δ j-μ k))^2) ≤
      ∑ j, (dot (P.x i) (P.x j)*δ j)^2) ∧
    ((1/(pC n m*m*n))^2 * ((m : ℝ)*(n-m)/((n : ℝ)*(n-1))) *
      (∑ i, ∑ j, (dot (P.x i) (P.x j)*δ j)^2)) =
      ((1/(pC n m*m*n))^2 * (n : ℝ)^2 * ((m : ℝ)*(n-m)/((n : ℝ)*(n-1))) *
        (∑ j, (1/(n : ℝ))*leverage P j*δ j^2)) ∧
    ((1/(pC n m*m*n))^2 * ((m : ℝ)*(n-m)/((n : ℝ)*(n-1))) *
      (∑ i, ∑ j, (dot (P.x i) (P.x j)*δ j)^2)) =
      1/(pT n m*pC n m*n*(n-1)) * popMean (fun j => leverage P j*δ j^2) ∧
    1/(pT n m*pC n m*n*(n-1)) * popMean (fun j => leverage P j*δ j^2) ≤
      kappa P/(pT n m*pC n m*(n-1)) * popMean (fun j => δ j^2) := by
  have hnNat : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  have hnc' : (0 : ℝ) < (n : ℝ)-m := by linarith
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1' : (0 : ℝ) < (n : ℝ)-1 := by linarith
  have n0 : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have n1 : (n : ℝ)-1 ≠ 0 := ne_of_gt hn1'
  have m0 : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have nc0 : (n : ℝ)-m ≠ 0 := ne_of_gt hnc'
  have hpt : 0 < pT n m := by dsimp [pT]; positivity
  have hpc : 0 < pC n m := by dsimp [pC]; positivity
  have pc0 : pC n m ≠ 0 := ne_of_gt hpc
  have hS : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hnNat⟩, mem_univ _⟩
  have hc := covariate_contraction P hnNat hG δ
  have hsum : (∑ j, (1/(n : ℝ))*leverage P j*δ j^2) =
      (1/(n : ℝ)) * ∑ j, δ j^2*leverage P j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hsum' : (∑ j, leverage P j*δ j^2) = ∑ j, δ j^2*leverage P j := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hf : ∀ j, dot (P.x i) (fun k => P.x j k*δ j-populationSlope P δ k) =
        dot (P.x i) (P.x j)*δ j-popMean (fun l => dot (P.x i) (P.x l)*δ l) := by
      intro j
      calc
        dot (P.x i) (fun k => P.x j k*δ j-populationSlope P δ k) =
            dot (P.x i) (P.x j)*δ j-dot (P.x i) (populationSlope P δ) := by
          simp [dot, mul_sub, mul_assoc, Finset.sum_sub_distrib, Finset.sum_mul]
        _ = _ := by rw [dot_population_slope]
    simp_rw [hf]
    have hh := (mean_square_centering univ hS (fun j => dot (P.x i) (P.x j)*δ j)).2
    have hh' : ((∑ j, (dot (P.x i) (P.x j)*δ j-popMean (fun l => dot (P.x i) (P.x l)*δ l))^2)/(n : ℝ)) ≤
        (∑ j, (dot (P.x i) (P.x j)*δ j)^2)/(n : ℝ) := by
      simpa only [mean, popMean, Finset.card_univ, Fintype.card_fin] using hh
    exact (div_le_div_iff_of_pos_right hn').mp hh'
  · rw [hc, hsum]
    field_simp [n0, pc0, m0]
    <;> ring
  · rw [hc]
    simp only [pT, pC, popMean, mean, Finset.card_univ, Fintype.card_fin]
    rw [hsum']
    field_simp [n0, n1, m0, nc0]
    <;> ring
  · have hb : popMean (fun j => leverage P j*δ j^2) ≤
        ((n : ℝ)*kappa P)*popMean (fun j => δ j^2) := by
      calc
        popMean (fun j => leverage P j*δ j^2) ≤ popMean (fun j => ((n : ℝ)*kappa P)*δ j^2) := by
          apply mean_mono
          intro j hj
          exact mul_le_mul_of_nonneg_right (leverage_le_maximum P hnNat j) (sq_nonneg _)
        _ = _ := mean_mul _ _ _
    have hcoef : 0 ≤ 1/(pT n m*pC n m*n*(n-1)) := by positivity
    calc
      1/(pT n m*pC n m*n*(n-1))*popMean (fun j => leverage P j*δ j^2) ≤
          1/(pT n m*pC n m*n*(n-1))*(((n : ℝ)*kappa P)*popMean (fun j => δ j^2)) :=
        mul_le_mul_of_nonneg_left hb hcoef
      _ = _ := by
        dsimp [pT, pC]
        field_simp [n0, n1, m0, nc0]
        <;> ring


/-- The common slope cancels from the difference e_i(T)-e_i(C), whose
population second moment is at most 4K under Assumption 1 (p. 1514). -/
theorem common_residual_difference_second_moment {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (K : ℝ) (hT : popMean (fun i => P.yT i^2) ≤ K)
    (hC : popMean (fun i => P.yC i^2) ≤ K) :
    popMean (fun i => (commonResidual P m P.yT i-commonResidual P m P.yC i)^2) ≤ 4*K := by
  have hS : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩, mem_univ _⟩
  have hf : (fun i => (commonResidual P m P.yT i-commonResidual P m P.yC i)^2) =
      (fun i => (centered P.yT i-centered P.yC i)^2) := by
    funext i
    dsimp only [commonResidual]
    ring
  rw [hf]
  have ht : popMean (fun i => centered P.yT i^2) ≤ K :=
    le_trans (by simpa only [centered, popMean] using (mean_square_centering univ hS P.yT).2) hT
  have hc : popMean (fun i => centered P.yC i^2) ≤ K :=
    le_trans (by simpa only [centered, popMean] using (mean_square_centering univ hS P.yC).2) hC
  calc
    popMean (fun i => (centered P.yT i-centered P.yC i)^2) ≤
        popMean (fun i => 2*centered P.yT i^2+2*centered P.yC i^2) := by
      apply mean_mono
      intro i hi
      nlinarith [sq_nonneg (centered P.yT i+centered P.yC i)]
    _ = 2*popMean (fun i => centered P.yT i^2)+2*popMean (fun i => centered P.yC i^2) := by
      unfold popMean
      rw [mean_add, mean_mul, mean_mul]
    _ ≤ 4*K := by linarith

/-- P005-T17(e): the corrected contracted expression is O(kappa/n) along
populations with Assumptions 1–3 and the paper's common-slope residuals (p. 1514). -/
theorem corrected_contraction_order (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P) :
    Asymptotics.IsBigO atTop
      (fun n => 1/(pT n (m n)*pC n (m n)*n*(n-1)) *
        popMean (fun i => leverage (P n) i *
          (commonResidual (P n) (m n) (P n).yT i-commonResidual (P n) (m n) (P n).yC i)^2))
      (fun n => kappa (P n)/n) := by
  rcases h with ⟨hsize, ⟨K,hK,hym⟩, hstd, ⟨lo,hi,hlo,hlohi,hhi,halloc⟩⟩
  let L := lo*(1-hi)
  have hL : 0 < L := mul_pos hlo (sub_pos.mpr hhi)
  apply Asymptotics.IsBigO.of_bound (8*K/L)
  filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with n hn
  have hnNat : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ)-1 := by linarith
  have n0 : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have n1 : (n : ℝ)-1 ≠ 0 := ne_of_gt hn1
  have hp := halloc n hn
  have hpt : 0 < pT n (m n) := lt_trans hlo hp.1
  have hsum : pT n (m n)+pC n (m n) = 1 := by
    dsimp [pT,pC]
    field_simp [n0]
    <;> ring
  have hpcLower : 1-hi ≤ pC n (m n) := by linarith [hp.2]
  have hpc : 0 < pC n (m n) := lt_of_lt_of_le (sub_pos.mpr hhi) hpcLower
  have pt0 := ne_of_gt hpt
  have pc0 := ne_of_gt hpc
  have hκ : 0 ≤ kappa (P n) := by
    have hu := leverage_le_maximum (P n) hnNat ⟨0,hnNat⟩
    have hl := leverage_nonneg (P n) ⟨0,hnNat⟩
    nlinarith
  let δ := fun i => commonResidual (P n) (m n) (P n).yT i-commonResidual (P n) (m n) (P n).yC i
  have hQ : popMean (fun i => δ i^2) ≤ 4*K :=
    common_residual_difference_second_moment (P n) hnNat K (hym n hn).1 (hym n hn).2.1
  have hQ0 : 0 ≤ popMean (fun i => leverage (P n) i*δ i^2) :=
    mean_nonneg _ _ (fun i _ => mul_nonneg (leverage_nonneg (P n) i) (sq_nonneg _))
  have hweighted : popMean (fun i => leverage (P n) i*δ i^2) ≤
      ((n : ℝ)*kappa (P n))*popMean (fun i => δ i^2) := by
    calc
      _ ≤ popMean (fun i => ((n : ℝ)*kappa (P n))*δ i^2) := by
        apply mean_mono
        intro i hi
        exact mul_le_mul_of_nonneg_right (leverage_le_maximum (P n) hnNat i) (sq_nonneg _)
      _ = _ := mean_mul _ _ _
  have hden : L*((n : ℝ)/2) ≤ pT n (m n)*pC n (m n)*(n-1) := by
    have hproduct : L ≤ pT n (m n)*pC n (m n) :=
      mul_le_mul (le_of_lt hp.1) hpcLower (le_of_lt (sub_pos.mpr hhi)) (le_of_lt hpt)
    have hhalf : (n : ℝ)/2 ≤ n-1 := by linarith
    exact mul_le_mul hproduct hhalf (by positivity) (le_of_lt (mul_pos hpt hpc))
  have hcoeff : kappa (P n)/(pT n (m n)*pC n (m n)*(n-1)) ≤
      2/L * (kappa (P n)/n) := by
    calc
      _ ≤ kappa (P n)/(L*((n : ℝ)/2)) :=
        div_le_div_of_nonneg_left hκ (by positivity) hden
      _ = _ := by field_simp [n0,ne_of_gt hL] <;> ring
  have hf0 : 0 ≤ 1/(pT n (m n)*pC n (m n)*n*(n-1))*
      popMean (fun i => leverage (P n) i*δ i^2) := mul_nonneg (by positivity) hQ0
  have hf : 1/(pT n (m n)*pC n (m n)*n*(n-1))*
      popMean (fun i => leverage (P n) i*δ i^2) ≤ (8*K/L)*(kappa (P n)/n) := by
    calc
      _ ≤ 1/(pT n (m n)*pC n (m n)*n*(n-1))*
          (((n : ℝ)*kappa (P n))*popMean (fun i => δ i^2)) :=
        mul_le_mul_of_nonneg_left hweighted (by positivity)
      _ = kappa (P n)/(pT n (m n)*pC n (m n)*(n-1))*popMean (fun i => δ i^2) := by
        field_simp [n0,n1,pt0,pc0]
        <;> ring
      _ ≤ kappa (P n)/(pT n (m n)*pC n (m n)*(n-1))*(4*K) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
      _ ≤ (2/L*(kappa (P n)/n))*(4*K) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = _ := by ring
  change ‖1/(pT n (m n)*pC n (m n)*n*(n-1))*
      popMean (fun i => leverage (P n) i*δ i^2)‖ ≤ (8*K/L)*‖kappa (P n)/n‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg hf0,
    abs_of_nonneg (div_nonneg hκ (le_of_lt hn'))] using hf

/-- Under Assumption 2, Nhat_t = N_t + nu_1t + nu_3t, for any nonempty
arm (finite identity in Theorem 4.1, p. 1509). -/
theorem armN_decomposition {n d : ℕ} (P : Population n d) (hP : standardized P)
    (S : Finset (Fin n)) (hS : S.Nonempty) (y : Fin n → ℝ) :
    armN P S y = populationSlope P y + armNu1 P S y + armNu3 P S y := by
  funext k
  have hx : popMean (fun i => P.x i k) = 0 := by
    simpa only [xMean, popMean, Pi.zero_apply] using
      congrArg (fun v : Fin d → ℝ => v k) hP.1
  have hf : (fun i => centered y i*P.x i k) =
      (fun i => y i*P.x i k-popMean y*P.x i k) := by
    funext i
    dsimp [centered]
    ring
  have hs : mean S (fun i => centered y i*P.x i k) =
      mean S (fun i => y i*P.x i k)-popMean y*xMean P S k := by
    rw [hf, mean_sub, mean_mul]
    rfl
  have hp : popMean (fun i => centered y i*P.x i k) = populationSlope P y k := by
    unfold popMean
    rw [hf, mean_sub, mean_mul]
    change populationSlope P y k-popMean y*popMean (fun i => P.x i k) = _
    rw [hx]
    ring
  have hc : mean S (centered y) = mean S y-popMean y := by
    unfold centered
    rw [mean_sub, mean_const S hS]
  simp only [armN, armNu1, armNu3, Pi.add_apply]
  rw [hs, hp, hc]
  ring

/-- The exact within-arm slope decomposition beta_I,t = beta_I,t(population)
+ nu_1t + nu_2t + nu_3t (Theorem 4.1, p. 1509), under its normalization
and inverse assumptions.  -/
theorem arm_slope_decomposition {n d : ℕ} (P : Population n d) (hP : standardized P)
    (S : Finset (Fin n)) (hS : S.Nonempty) (y : Fin n → ℝ)
    (hinv : (armL P S).det ≠ 0) :
    armBetaHat P S y = populationSlope P y + armNu1 P S y + armNu2 P S y + armNu3 P S y := by
  have hb : armBetaHat P S y = armN P S y+armNu2 P S y := by
    simp only [armBetaHat, armNu2, Matrix.sub_mulVec, Matrix.one_mulVec]
    <;> abel
  rw [hb, armN_decomposition P hP S hS y]
  funext k
  simp only [Pi.add_apply]
  ring

/-- The exact noninteracted slope decomposition betaHat = beta* + nu_1
+ nu_2 + nu_3 (Theorem 3.1, p. 1507), on every assignment of its actual
complete-randomization design. No sampling moment is assumed to prove it. -/
theorem noninteracted_slope_decomposition {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : noninteractedRegular P m) :
    ∀ S ∈ design n m, betaHat P m S = N P m+nu1 P m S+nu2 P m S+nu3 P m S := by
  intro S hS
  have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hsN : S.Nonempty := Finset.card_pos.mp (by rw [hs]; exact hm)
  have hc : (control S).card = n-m := by
    rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [hs]
  have hcN : (control S).Nonempty :=
    Finset.card_pos.mp (by rw [hc]; exact Nat.sub_pos_of_lt hmn)
  have ht := armN_decomposition P hP S hsN P.yT
  have hc' := armN_decomposition P hP (control S) hcN P.yC
  have hnh : Nhat P m S = N P m+nu1 P m S+nu3 P m S := by
    unfold Nhat
    rw [ht,hc']
    funext k
    simp only [N, nu1, nu3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hb : betaHat P m S = Nhat P m S+nu2 P m S := by
    simp only [betaHat, nu2, Matrix.sub_mulVec, Matrix.one_mulVec]
    <;> abel
  rw [hb,hnh]
  funext k
  simp only [Pi.add_apply]
  ring

/-- Finite coordinate summation commutes with the population average
(p. 1505), used in the residual normal equation of p. 1513. -/
theorem popMean_sum {n : ℕ} {ι : Type*} [Fintype ι] (f : ι → Fin n → ℝ) :
    popMean (fun i => ∑ k, f k i) = ∑ k, popMean (f k) := by
  simp only [popMean, mean, Finset.sum_div]
  exact Finset.sum_comm

/-- Under xbar=0, centering an outcome leaves its population slope
unchanged (p. 1506 and the residual definition on p. 1513). -/
theorem populationSlope_centered {n d : ℕ} (P : Population n d)
    (hx : xMean P univ = 0) (y : Fin n → ℝ) :
    populationSlope P (centered y) = populationSlope P y := by
  funext k
  have hxk : popMean (fun i => P.x i k) = 0 := by
    simpa only [xMean, popMean, Pi.zero_apply] using
      congrArg (fun v : Fin d → ℝ => v k) hx
  have hf : (fun i => centered y i*P.x i k) =
      (fun i => y i*P.x i k-popMean y*P.x i k) := by
    funext i
    dsimp [centered]
    ring
  change mean univ (fun i => centered y i*P.x i k) = _
  rw [hf, mean_sub, mean_mul]
  change populationSlope P y k-popMean y*popMean (fun i => P.x i k) = _
  rw [hxk]
  ring

/-- Normalization bar(xx')=I makes the population slope of x_i'v equal
v (Assumption 2, p. 1505; residual normal equation, p. 1513). -/
theorem populationSlope_projection {n d : ℕ} (P : Population n d)
    (hG : gram P = 1) (v : Fin d → ℝ) :
    populationSlope P (fun i => dot (P.x i) v) = v := by
  funext k
  have hf : (fun i => dot (P.x i) v*P.x i k) =
      (fun i => ∑ l, v l*(P.x i l*P.x i k)) := by
    funext i
    unfold dot
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  change popMean (fun i => dot (P.x i) v*P.x i k) = v k
  rw [hf, popMean_sum]
  have hm : ∀ l, popMean (fun i => v l*(P.x i l*P.x i k)) =
      v l*popMean (fun i => P.x i l*P.x i k) := fun l => mean_mul univ _ _
  have hg : ∀ l, popMean (fun i => P.x i l*P.x i k) = if l=k then 1 else 0 := by
    intro l
    simpa only [gram, Matrix.one_apply] using
      congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M l k) hG
  simp_rw [hm,hg]
  simp [mul_ite]

/-- Each common-slope residual has population slope N_t-beta*,
as used in the weighted normal equation on p. 1513. -/
theorem populationSlope_common_residual {n d m : ℕ} (P : Population n d)
    (hP : standardized P) (y : Fin n → ℝ) :
    populationSlope P (commonResidual P m y) = populationSlope P y-N P m := by
  funext k
  have hf : (fun i => commonResidual P m y i*P.x i k) =
      (fun i => centered y i*P.x i k-dot (P.x i) (N P m)*P.x i k) := by
    funext i
    dsimp only [commonResidual]
    ring
  change mean univ (fun i => commonResidual P m y i*P.x i k) = _
  rw [hf, mean_sub]
  change populationSlope P (centered y) k-
      populationSlope P (fun i => dot (P.x i) (N P m)) k = _
  rw [populationSlope_centered P hP.1 y, populationSlope_projection P hP.2 (N P m)]
  <;> rfl

/-- P005-T18(c): the actual common-slope residuals satisfy the weighted
population normal equation printed on p. 1514. -/
theorem common_residual_normal_equation {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hP : standardized P) :
    pT n m • populationSlope P (commonResidual P m P.yT) +
      pC n m • populationSlope P (commonResidual P m P.yC) = 0 := by
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp : pT n m+pC n m = 1 := by
    dsimp [pT,pC]
    field_simp [n0]
    <;> ring
  rw [populationSlope_common_residual P hP P.yT, populationSlope_common_residual P hP P.yC]
  calc
    _ = (pT n m • populationSlope P P.yT+pC n m • populationSlope P P.yC)-
        (pT n m+pC n m) • N P m := by
      simp only [smul_sub, add_smul]
      abel
    _ = N P m-N P m := by rw [hp, one_smul] <;> rfl
    _ = 0 := sub_self _

/-- P005-T18(c): xbar=0 implies xbar_T-xbar_C=(1/p_C)xbar_T
for every size-n_T assignment (first sentence on p. 1514). -/
theorem complement_x_mean_identity {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (S : Finset (Fin n)) (hS : S ∈ design n m) :
    xMean P S-xMean P (control S) = (1/pC n m) • xMean P S := by
  have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hc : (control S).card = n-m := by
    rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [hs]
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have m0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  have nc0 : (n : ℝ)-m ≠ 0 := ne_of_gt (sub_pos.mpr hmn')
  funext k
  have hzero : (∑ i, P.x i k) = 0 := by
    have hh := congrArg (fun v : Fin d → ℝ => v k) hx
    have hz : (∑ i, P.x i k)/(n : ℝ) = 0 := by
      simpa only [xMean, mean, Pi.zero_apply, Finset.card_univ, Fintype.card_fin] using hh
    simpa using (div_eq_iff n0).mp hz
  have hcomp : (∑ i ∈ control S, P.x i k) = -(∑ i ∈ S, P.x i k) := by
    rw [control, Finset.sum_sdiff_eq_sub (Finset.subset_univ S), hzero]
    ring
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, xMean, mean, hs, hc]
  rw [hcomp, Nat.cast_sub (le_of_lt hmn)]
  dsimp [pC]
  field_simp [n0,m0,nc0]
  <;> ring

/-- "e_i(D_i)" (p. 1513): the fixed treated or control residual selected
by the actual assignment indicator D_i. -/
def observedResidual {n : ℕ} (S : Finset (Fin n)) (eT eC : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i ∈ S then eT i else eC i

/-- "(*) = (bar x_T-bar x_C)' (1/n) sum_i x_i e_i(D_i)"
(Appendix B.1.1, pp. 1513–1514), before the corrected bracket expansion. -/
def residualStarTerm {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (eT eC : Fin n → ℝ) : ℝ :=
  dot (xMean P S-xMean P (control S)) (populationSlope P (observedResidual S eT eC))

/-- Selecting e_i(D_i) gives the full control residual sum plus the
selected treated-minus-control residual sum (p. 1514). -/
theorem observed_residual_slope {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (eT eC : Fin n → ℝ) :
    populationSlope P (observedResidual S eT eC) =
      (fun k => (∑ i ∈ S, P.x i k*(eT i-eC i))/(n : ℝ))+populationSlope P eC := by
  funext k
  have hf : (fun i => observedResidual S eT eC i*P.x i k) =
      (fun i => indicator S i*(P.x i k*(eT i-eC i))+eC i*P.x i k) := by
    funext i
    by_cases hi : i ∈ S <;> simp [observedResidual, indicator, hi] <;> ring
  simp only [populationSlope, popMean, mean, Pi.add_apply, Finset.card_univ, Fintype.card_fin]
  rw [hf, Finset.sum_add_distrib, add_div, indicator_sum]

/-- P005-T18(c): with the actual residuals of p. 1513, the weighted normal
equation holds and the term (*) equals the first line of the corrected
p. 1514 display. Together with corrected_residual_brackets this covers (a)–(c). -/
theorem corrected_residual_term_identification {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (S : Finset (Fin n)) (hS : S ∈ design n m) :
    let eT := commonResidual P m P.yT
    let eC := commonResidual P m P.yC
    let U := fun k => (∑ i ∈ S, P.x i k*(eT i-eC i))/(n : ℝ)
    let B := populationSlope P eC
    xMean P S-xMean P (control S) = (1/pC n m) • xMean P S ∧
    pT n m • populationSlope P eT+pC n m • populationSlope P eC = 0 ∧
    residualStarTerm P S eT eC = (1/pC n m)*dot (xMean P S) (U+B) := by
  dsimp only
  have hx := complement_x_mean_identity P hn hm hmn hP.1 S hS
  refine ⟨hx,common_residual_normal_equation P hn hP,?_⟩
  unfold residualStarTerm
  rw [hx,observed_residual_slope]
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]


/-- P005-T14(d): the two correctly transposed control-minus-treatment
covariate mean identities on p. 1515, for every actual assignment. -/
theorem control_minus_treated_mean_identities {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (S : Finset (Fin n)) (hS : S ∈ design n m) :
    xMean P (control S)-xMean P S = (1/pT n m) • xMean P (control S) ∧
    xMean P (control S)-xMean P S = (-(1/pC n m)) • xMean P S := by
  have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hc : (control S).card = n-m := by
    rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [hs]
  have hcDesign : control S ∈ design n (n-m) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hc⟩
  have hcc : control (control S) = S := by
    ext i
    simp [control]
  have hmirror : pC n (n-m) = pT n m := by
    dsimp [pC,pT]
    rw [Nat.cast_sub (le_of_lt hmn)]
    ring
  have hfirst := complement_x_mean_identity P hn (Nat.sub_pos_of_lt hmn)
    (Nat.sub_lt hn hm) hx (control S) hcDesign
  rw [hcc,hmirror] at hfirst
  have hsecond := complement_x_mean_identity P hn hm hmn hx S hS
  refine ⟨hfirst,?_⟩
  calc
    _ = -(xMean P S-xMean P (control S)) := by abel
    _ = -((1/pC n m) • xMean P S) := by rw [hsecond]
    _ = _ := by rw [neg_smul]

/-- "Y_i = y_i(1) ... treatment ... Y_i = y_i(0) ... control"
(Section 2, p. 1504). Only the observed arm outcome is selected. -/
def observedOutcome {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) : Fin n → ℝ :=
  observedResidual S P.yT P.yC

/-- A finite arm average depends only on values on that arm (p. 1505);
used to formalize the computability assertion of Remark 2, p. 1507. -/
theorem mean_congr {n : ℕ} (S : Finset (Fin n)) (a b : Fin n → ℝ)
    (h : ∀ i ∈ S, a i=b i) : mean S a = mean S b := by
  unfold mean
  rw [Finset.sum_congr rfl h]

/-- P005-T14(e): Remark 2's nu_2 correction is a function of the assignment,
covariates and observed outcomes only. The function is chosen before the
population, so it cannot depend on unobserved potential outcomes (p. 1507). -/
theorem inverse_component_observable (n d m : ℕ) (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) :
    ∃ F : Finset (Fin n) → (Fin n → Fin d → ℝ) → (Fin n → ℝ) → ℝ,
      ∀ P : Population n d, standardized P → ∀ S ∈ design n m,
      (Lhat P m S).det ≠ 0 →
      dot (xMean P (control S)-xMean P S) (nu2 P m S) = F S P.x (observedOutcome P S) := by
  refine ⟨fun S x Y =>
    let Q : Population n d := { x := x, yT := Y, yC := Y }
    dot (xMean Q (control S)-xMean Q S) (nu2 Q m S),?_⟩
  intro P _hP S _hS _hinv
  let Q : Population n d := { x := P.x, yT := observedOutcome P S, yC := observedOutcome P S }
  have ht : mean S (observedOutcome P S) = mean S P.yT := by
    apply mean_congr
    intro i hi
    simp [observedOutcome,observedResidual,hi]
  have hc : mean (control S) (observedOutcome P S) = mean (control S) P.yC := by
    apply mean_congr
    intro i hi
    have hnot : i ∉ S := (Finset.mem_sdiff.mp hi).2
    simp [observedOutcome,observedResidual,hnot]
  have htx : ∀ k, mean S (fun i => observedOutcome P S i*P.x i k) =
      mean S (fun i => P.yT i*P.x i k) := by
    intro k
    apply mean_congr
    intro i hi
    simp [observedOutcome,observedResidual,hi]
  have hcx : ∀ k, mean (control S) (fun i => observedOutcome P S i*P.x i k) =
      mean (control S) (fun i => P.yC i*P.x i k) := by
    intro k
    apply mean_congr
    intro i hi
    have hnot : i ∉ S := (Finset.mem_sdiff.mp hi).2
    simp [observedOutcome,observedResidual,hnot]
  have hN : Nhat Q m S = Nhat P m S := by
    funext k
    simp only [Nhat,armN,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    change pT n m*(mean S (fun i => observedOutcome P S i*P.x i k)-mean S (observedOutcome P S)*xMean P S k) +
      pC n m*(mean (control S) (fun i => observedOutcome P S i*P.x i k)-
        mean (control S) (observedOutcome P S)*xMean P (control S) k) = _
    rw [ht,hc,htx k,hcx k]
  have hnu : nu2 Q m S = nu2 P m S := by
    simp only [nu2,hN]
    <;> rfl
  change dot (xMean P (control S)-xMean P S) (nu2 P m S) =
    dot (xMean P (control S)-xMean P S) (nu2 Q m S)
  rw [hnu]

/-- Transposing the two scalar arguments of x_i'x_j leaves the dot product
unchanged (column-vector convention, p. 1505). -/
theorem dot_comm {d : ℕ} (u v : Fin d → ℝ) : dot u v = dot v u := by
  unfold dot
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Under bar(xx')=I, every leverage h_i is at most n (Assumption 2,
used in the stated kappa interval on p. 1516). -/
theorem leverage_le_population_size {n d : ℕ} (P : Population n d)
    (hn : 0 < n) (hG : gram P = 1) (i : Fin n) : leverage P i ≤ n := by
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := dot_population_slope P (P.x i) (fun j => dot (P.x j) (P.x i))
  rw [populationSlope_projection P hG (P.x i)] at hh
  have hf : (fun j => dot (P.x i) (P.x j)*dot (P.x j) (P.x i)) =
      (fun j => (dot (P.x j) (P.x i))^2) := by
    funext j
    rw [dot_comm (P.x i) (P.x j),pow_two]
  rw [hf] at hh
  have hm : (∑ j, (dot (P.x j) (P.x i))^2)/(n : ℝ) = leverage P i := by
    simpa only [leverage,popMean,mean,Finset.card_univ,Fintype.card_fin] using hh.symm
  have hsum : (∑ j, (dot (P.x j) (P.x i))^2) = (n : ℝ)*leverage P i := by
    simpa only [mul_comm] using (div_eq_iff n0).mp hm
  have hs : (leverage P i)^2 ≤ ∑ j, (dot (P.x j) (P.x i))^2 := by
    simpa only [leverage] using
      (Finset.single_le_sum (fun j _ => sq_nonneg (dot (P.x j) (P.x i)))
        (Finset.mem_univ i))
  rw [hsum] at hs
  by_contra hbad
  have hgt : (n : ℝ) < leverage P i := lt_of_not_ge hbad
  have hp : 0 < leverage P i := lt_trans hn' hgt
  have hprod : (n : ℝ)*leverage P i < leverage P i*leverage P i :=
    mul_lt_mul_of_pos_right hgt hp
  nlinarith

/-- P005-T11(c)'s finite supporting fact: kappa lies in [d/n,1], exactly
as used on pp. 1516 and 1519, under normalized population covariates. -/
theorem kappa_bounds {n d : ℕ} (P : Population n d) (hn : 0 < n) (hG : gram P = 1) :
    (d : ℝ)/n ≤ kappa P ∧ kappa P ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,mem_univ _⟩
  have hd : (d : ℝ) ≤ (n : ℝ)*kappa P := by
    have hm := mean_mono univ (leverage P) (fun _ => (n : ℝ)*kappa P)
      (fun i _ => leverage_le_maximum P hn i)
    change popMean (leverage P) ≤ mean univ (fun _ => (n : ℝ)*kappa P) at hm
    rw [leverage_population_mean P hG,mean_const univ hS] at hm
    exact hm
  constructor
  · apply (div_le_iff₀ hn').mpr
    nlinarith [hd]
  · unfold kappa
    apply csSup_le
    · exact ⟨_,Set.mem_range_self (⟨0,hn⟩ : Fin n)⟩
    · intro r hr
      rcases hr with ⟨i,rfl⟩
      apply (div_le_iff₀ hn').mpr
      simpa only [one_mul] using leverage_le_population_size P hn hG i

end
end AronowAudit.P005
