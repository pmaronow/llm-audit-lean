import Mathlib

/-!
Formalization of chapter 16, "Estimating Causal Effects in Experiments with Network
Spillovers", printed pp. 209–222.
The chapter has no numbered theorems and does not display its estimators.
Estimator formulas below are supplied mathematical models of the interference
package's estimators. Agreement of the package's estimator and smoothing outputs
with `htMean`, `htContrast`, `varianceEstimate`, `smoothedWeight`, and `smoothedJoint`
is an external assumption. Lean does not verify that correspondence.
-/
namespace AronowAudit.P044

open Finset
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- "The ... vector of treatments ... z=(z₁,...,z_N)'" (p. 210).
`false` is control (0), `true` is treatment (1). Units are numbered from 0 here. -/
abbrev Assignment (N : ℕ) := Fin N → Bool

/-- The four labels "Direct + Indirect", "Isolated Direct", "Indirect", and
"No Exposure" in the display on p. 211. -/
inductive Exposure where
  | d11 | d10 | d01 | d00
  deriving DecidableEq, Repr

instance : Fintype Exposure := ⟨{.d11, .d10, .d01, .d00}, by intro d; cases d <;> simp⟩

/-- "N × N adjacency matrix ... entries ... 0 or 1 (and ... 0's on the diagonal)"
(p. 210). Boolean entries encode the binary version of that definition. -/
abbrev Adjacency (N : ℕ) := Fin N → Fin N → Bool

/-- The corrected scalar θᵢ z = ∑ⱼ θᵢⱼ zⱼ in the p. 211 display (T9).
This is the number of treated network peers. -/
def peerCount {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N) : ℕ :=
  ∑ j, if A i j && z j then 1 else 0

/-- "... whether ... they are treated ... [or] any one of their network peers
is treated" (pp. 211–212). The corrected four-condition exposure mapping. -/
def exposure {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N) : Exposure :=
  if z i then (if 0 < peerCount A z i then .d11 else .d10)
  else (if 0 < peerCount A z i then .d01 else .d00)

/-- "... assigns some probability, p_z, to a treatment profile" (pp. 210–211).
A finite index type Ω indexes randomization atoms; zero masses are permitted. -/
structure FiniteDesign (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

/-- Randomization expectation: the finite sum ∑_z p_z T(z), using p. 211's
Pr(Z=z)=p_z. Also used over rational fields for exact numerical witnesses. -/
def expect {Ω K : Type*} [Fintype Ω] [CommSemiring K] (p : Ω → K) (t : Ω → K) : K :=
  ∑ ω, p ω * t ω

/-- Randomization variance E[T²]−E[T]², valid when the
nonnegative masses sum to one. It is not squared error about the estimand. -/
def designVariance {Ω K : Type*} [Fintype Ω] [CommRing K]
    (p : Ω → K) (t : Ω → K) : K := expect p (fun ω => t ω ^ 2) - (expect p t) ^ 2

/-- "yᵢ(·) is a real-valued function" of assignments (p. 211), translated
by a correctly specified mapping into the exposure-indexed schedule (pp. 211–212).
The scalar type is ℝ in general statements and ℚ in numerical witnesses. -/
abbrev OutcomeSchedule (N : ℕ) (D K : Type*) := Fin N → D → K

/-- "... will reveal the associated potential outcome, yᵢ(d)" (p. 212).
Observed outcomes are Yᵢ=yᵢ(Dᵢ), with population and outcome schedule fixed. -/
def observed {Ω D K : Type*} {N : ℕ} (f : Ω → Fin N → D)
    (y : OutcomeSchedule N D K) (ω : Ω) (i : Fin N) : K := y i (f ω i)

/-- "τ(d,d') = 1/N ∑ᵢ (yᵢ(d)−yᵢ(d'))" (display, p. 212).
Outcomes are fixed exposure-indexed real values; rational witnesses use the
identical formula in ℚ. -/
def tau {N : ℕ} {D K : Type*} [Field K] (y : Fin N → D → K) (a b : D) : K :=
  (∑ i, (y i a - y i b)) / N

/-- πᵢ(d)=Pr(Dᵢ=d), the exposure probability of pp. 212, 216.
`f ω i` is Dᵢ on the randomization atom ω. -/
def marginal {Ω D K : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → D) (i : Fin N) (a : D) : K :=
  ∑ ω, if f ω i = a then p ω else 0

/-- πᵢⱼ(d,e)=Pr(Dᵢ=d,Dⱼ=e), the joint probability for shared-peer dependencies
(p. 213). Ordered pairs, including diagonal pairs, are retained. -/
def joint {Ω D K : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → D) (i j : Fin N) (a b : D) : K :=
  ∑ ω, if f ω i = a ∧ f ω j = b then p ω else 0

/-- The HT unit contribution I(Dᵢ=d)Yᵢ/wᵢ(d) (pp. 212, 216).
By correct specification Yᵢ=yᵢ(Dᵢ), this is the displayed conditional expression. Lean's total division is not a support assumption. -/
def htTerm {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a : D) (ω : Ω) (i : Fin N) : K :=
  if f ω i = a then y i a / w i a else 0

/-- μ̂_HT(d)=N⁻¹∑ᵢ I(Dᵢ=d)Yᵢ/wᵢ(d).
The estimator is not displayed in the chapter; the prose is on pp. 212,216. -/
def htMean {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a : D) (ω : Ω) : K :=
  (∑ i, htTerm f y w a ω i) / N

/-- The modeled effect estimate μ̂(k)−μ̂(l), for the p. 212 estimand. -/
def htContrast {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a b : D) (ω : Ω) : K :=
  htMean f y w a ω - htMean f y w b ω

/-- The modeled total variance estimate V̂_d; ordered positive-joint terms
include i=j; zero-joint squared-outcome adjustment excludes i=j. -/
def totalVarianceEstimate {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K)
    (q : Fin N → Fin N → D → D → K) (a : D) (ω : Ω) : K :=
  ∑ i, ∑ j, (
    (if 0 < q i j a a then
      (if f ω i = a ∧ f ω j = a then
        y i a * y j a * (1 / (w i a * w j a) - 1 / q i j a a) else 0)
    else 0) +
    (if i ≠ j ∧ q i j a a = 0 then
      (if f ω i = a then y i a ^ 2 / (2 * w i a) else 0) +
      (if f ω j = a then y j a ^ 2 / (2 * w j a) else 0)
    else 0))

/-- The modeled total covariance estimate Ĉ_kl. The cross zero adjustment
has a minus sign and includes every i=j pair. -/
def totalCovarianceEstimate {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K)
    (q : Fin N → Fin N → D → D → K) (a b : D) (ω : Ω) : K :=
  ∑ i, ∑ j, (
    (if 0 < q i j a b then
      (if f ω i = a ∧ f ω j = b then
        y i a * y j b * (1 / (w i a * w j b) - 1 / q i j a b) else 0)
    else 0) -
    (if q i j a b = 0 then
      (if f ω i = a then y i a ^ 2 / (2 * w i a) else 0) +
      (if f ω j = b then y j b ^ 2 / (2 * w j b) else 0)
    else 0))

/-- V̂(k,l)=(V̂_k+V̂_l−2 Ĉ_kl)/N², the supplied HT variance functional
modeling the "conservative approximations" on p. 217. -/
def varianceEstimate {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K)
    (q : Fin N → Fin N → D → D → K) (a b : D) (ω : Ω) : K :=
  (totalVarianceEstimate f y w q a ω + totalVarianceEstimate f y w q b ω -
    2 * totalCovarianceEstimate f y w q a b ω) / (N : K) ^ 2

/-- The exact structural-zero surplus in T2(a), from the repair of p. 217:
within-exposure squares use i≠j; cross squares include i=j. -/
def zeroSurplus {N : ℕ} {D : Type*} [DecidableEq D]
    (y : Fin N → D → ℝ) (q : Fin N → Fin N → D → D → ℝ) (a b : D) : ℝ :=
  ((∑ i, ∑ j, if i ≠ j ∧ q i j a a = 0 then (y i a + y j a) ^ 2 / 2 else 0) +
   (∑ i, ∑ j, if i ≠ j ∧ q i j b b = 0 then (y i b + y j b) ^ 2 / 2 else 0) +
   (∑ i, ∑ j, if q i j a b = 0 then (y i a - y j b) ^ 2 else 0)) / (N : ℝ) ^ 2

/-- Finite linearity used in the p. 212 unbiasedness and p. 217 variance
correction: expectation commutes with a fixed finite population sum. -/
theorem expect_sum {Ω I K : Type*} [Fintype Ω] [Field K] (p : Ω → K) (s : Finset I)
    (u : Ω → I → K) : expect p (fun ω => ∑ i ∈ s, u ω i) = ∑ i ∈ s, expect p (fun ω => u ω i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Finite expectation of a scalar multiple, used in the variance correction. -/
theorem expect_mul_const {Ω K : Type*} [Fintype Ω] [Field K] (p u : Ω → K) (c : K) :
    expect p (fun ω => u ω * c) = expect p u * c := by
  simp [expect, Finset.sum_mul, mul_assoc]

/-- Finite expectation of a difference, used in the p. 217 variance correction. -/
theorem expect_sub {Ω K : Type*} [Fintype Ω] [Field K] (p u v : Ω → K) :
    expect p (fun ω => u ω - v ω) = expect p u - expect p v := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

/-- Finite expectation of a sum, used in the p. 217 variance correction. -/
theorem expect_add {Ω K : Type*} [Fintype Ω] [Field K] (p u v : Ω → K) :
    expect p (fun ω => u ω + v ω) = expect p u + expect p v := by
  simp [expect, mul_add, Finset.sum_add_distrib]

/-- Finite expectation of a fixed-denominator quotient. -/
theorem expect_div {Ω K : Type*} [Fintype Ω] [Field K] (p u : Ω → K) (c : K) :
    expect p (fun ω => u ω / c) = expect p u / c := by
  simp only [expect, ← mul_div_assoc, ← Finset.sum_div]

/-- A single exposure event times a fixed outcome constant has expectation
πᵢ(a)c. This finite identity underlies both corrected estimator statements. -/
theorem expect_event {Ω D K : Type*} {N : ℕ} [Fintype Ω] [Field K] [DecidableEq D]
    (p : Ω → K) (f : Ω → Fin N → D) (i : Fin N) (a : D) (c : K) :
    expect p (fun ω => if f ω i = a then c else 0) = marginal p f i a * c := by
  unfold expect marginal
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs with hh <;> simp [hh]

/-- An ordered joint exposure event times a fixed outcome constant has
expectation πᵢⱼ(a,b)c, including i=j. Finite lemma for T2. -/
theorem expect_joint_event {Ω D K : Type*} {N : ℕ} [Fintype Ω] [Field K] [DecidableEq D]
    (p : Ω → K) (f : Ω → Fin N → D) (i j : Fin N) (a b : D) (c : K) :
    expect p (fun ω => if f ω i = a ∧ f ω j = b then c else 0) = joint p f i j a b * c := by
  unfold expect joint
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs with hh <;> simp [hh]

/-- T2 finite lemma: the expected product of two HT contributions is the
joint exposure probability times the fixed outcome product divided by the
two marginal weights. Arbitrary fixed weights are permitted in this identity. -/
theorem htTerm_product_expectation {Ω D K : Type*} {N : ℕ} [Fintype Ω] [Field K] [DecidableEq D]
    (p : Ω → K) (f : Ω → Fin N → D) (y w : Fin N → D → K)
    (i j : Fin N) (a b : D) :
    expect p (fun ω => htTerm f y w a ω i * htTerm f y w b ω j) =
      joint p f i j a b * (y i a * y j b / (w i a * w j b)) := by
  have he : (fun ω => htTerm f y w a ω i * htTerm f y w b ω j) =
      (fun ω => if f ω i = a ∧ f ω j = b then y i a * y j b / (w i a * w j b) else 0) := by
    funext ω
    unfold htTerm
    by_cases hi : f ω i = a <;> by_cases hj : f ω j = b <;>
      simp [hi, hj, div_eq_mul_inv] <;> ring
  rw [he, expect_joint_event]

/-- T2 finite algebra: the second moment of the population average expands into
all ordered pairs, divided by N², with no independence requirement. -/
theorem expect_square_sum {Ω K : Type*} {N : ℕ} [Fintype Ω] [Field K]
    (p : Ω → K) (u : Ω → Fin N → K) :
    expect p (fun ω => ((∑ i, u ω i) / N) ^ 2) =
      (∑ i, ∑ j, expect p (fun ω => u ω i * u ω j)) / (N : K) ^ 2 := by
  simp_rw [div_pow, pow_two, Finset.sum_mul_sum, expect_div, expect_sum]

/-- T2 finite second moment: the squared HT contrast expands into the two
same-exposure and both ordered cross-exposure joint probabilities. -/
theorem htContrast_second_moment {Ω D K : Type*} {N : ℕ} [Fintype Ω] [Field K] [DecidableEq D]
    (p : Ω → K) (f : Ω → Fin N → D) (y w : Fin N → D → K) (a b : D) :
    expect p (fun ω => htContrast f y w a b ω ^ 2) =
      (∑ i, ∑ j,
        (joint p f i j a a * (y i a * y j a / (w i a * w j a)) +
        joint p f i j b b * (y i b * y j b / (w i b * w j b)) -
        joint p f i j a b * (y i a * y j b / (w i a * w j b)) -
        joint p f i j b a * (y i b * y j a / (w i b * w j a)))) / (N : K) ^ 2 := by
  have hc : (fun ω => htContrast f y w a b ω) =
      (fun ω => (∑ i, (htTerm f y w a ω i - htTerm f y w b ω i)) / N) := by
    funext ω
    simp [htContrast, htMean, Finset.sum_sub_distrib, sub_div]
  rw [show (fun ω => htContrast f y w a b ω ^ 2) =
    (fun ω => ((∑ i, (htTerm f y w a ω i - htTerm f y w b ω i)) / N) ^ 2) by
      funext ω
      exact congrArg (fun v : K => v ^ 2) (congrFun hc ω)]
  rw [expect_square_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun ω => (htTerm f y w a ω i - htTerm f y w b ω i) *
      (htTerm f y w a ω j - htTerm f y w b ω j)) =
    (fun ω => htTerm f y w a ω i * htTerm f y w a ω j +
      htTerm f y w b ω i * htTerm f y w b ω j -
      htTerm f y w a ω i * htTerm f y w b ω j -
      htTerm f y w b ω i * htTerm f y w a ω j) := by funext ω; ring
  rw [he, expect_sub, expect_sub, expect_add]
  simp only [htTerm_product_expectation]

/-- Expected same-exposure variance functional with observation probabilities
m,J and arbitrary fixed estimator inputs w,q. This is `totalVarianceEstimate`
with each exposure indicator (or product) replaced by its randomization expectation. -/
def expectedTotalVariance {N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K]
    (m : Fin N → D → K) (J : Fin N → Fin N → D → D → K)
    (y w : Fin N → D → K) (q : Fin N → Fin N → D → D → K) (a : D) : K :=
  ∑ i, ∑ j, ((if 0 < q i j a a then
    J i j a a * (y i a * y j a * (1 / (w i a * w j a) - 1 / q i j a a)) else 0) +
    (if i ≠ j ∧ q i j a a = 0 then
      m i a * (y i a ^ 2 / (2 * w i a)) + m j a * (y j a ^ 2 / (2 * w j a)) else 0))

/-- Expected cross-exposure covariance functional with observation law m,J,
retaining all ordered zero pairs including the diagonal (T2 finite lemma). -/
def expectedTotalCovariance {N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K]
    (m : Fin N → D → K) (J : Fin N → Fin N → D → D → K)
    (y w : Fin N → D → K) (q : Fin N → Fin N → D → D → K) (a b : D) : K :=
  ∑ i, ∑ j, ((if 0 < q i j a b then
    J i j a b * (y i a * y j b * (1 / (w i a * w j b) - 1 / q i j a b)) else 0) -
    (if q i j a b = 0 then
      m i a * (y i a ^ 2 / (2 * w i a)) + m j b * (y j b ^ 2 / (2 * w j b)) else 0))

/-- Expected HT contrast variance estimate from observation marginals and
joints. The two probability arrays need not equal the estimator's inputs. -/
def expectedVariance {N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K]
    (m : Fin N → D → K) (J : Fin N → Fin N → D → D → K)
    (y w : Fin N → D → K) (q : Fin N → Fin N → D → D → K) (a b : D) : K :=
  (expectedTotalVariance m J y w q a + expectedTotalVariance m J y w q b -
    2 * expectedTotalCovariance m J y w q a b) / (N : K) ^ 2

/-- Finite expectation of a constant multiple on the left. -/
theorem expect_const_mul {Ω K : Type*} [Fintype Ω] [Field K]
    (p u : Ω → K) (c : K) : expect p (fun ω => c * u ω) = c * expect p u := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Finite expectation commutes with a fixed conditional expression. -/
theorem expect_ite {Ω K : Type*} [Fintype Ω] [Field K] (p u v : Ω → K)
    (h : Prop) [Decidable h] :
    expect p (fun ω => if h then u ω else v ω) = if h then expect p u else expect p v := by
  by_cases hh : h <;> simp [hh]

/-- T2 finite identity: the expectation of `varianceEstimate` is its
explicit marginal/joint formula. It holds also for finite simulated inputs;
with such inputs, this identity alone does not establish conservativeness. -/
theorem varianceEstimate_expectation {Ω D K : Type*} {N : ℕ}
    [Fintype Ω] [DecidableEq D] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : Ω → K) (f : Ω → Fin N → D) (y w : Fin N → D → K)
    (q : Fin N → Fin N → D → D → K) (a b : D) :
    expect p (varianceEstimate f y w q a b) =
      expectedVariance (marginal p f) (joint p f) y w q a b := by
  unfold varianceEstimate expectedVariance
  simp only [expect_div, expect_sub, expect_add, expect_const_mul,
    totalVarianceEstimate, totalCovarianceEstimate, expect_sum, expect_ite,
    expect_joint_event, expect_event, expectedTotalVariance, expectedTotalCovariance]
  simp [expect]

/-- T4(a), T8(ii): the expectation of a single HT term with fixed weight
is yᵢ(d)πᵢ(d)/wᵢ(d). No independence or positive joint support is needed
(pp. 212,216, corrected). -/
theorem htTerm_expectation {Ω D K : Type*} {N : ℕ} [Fintype Ω] [Field K] [DecidableEq D]
    (p : Ω → K) (f : Ω → Fin N → D) (y w : Fin N → D → K) (a : D) (i : Fin N) :
    expect p (fun ω => htTerm f y w a ω i) = y i a * marginal p f i a / w i a := by
  dsimp only [expect, htTerm]
  calc
    (∑ ω, p ω * (if f ω i = a then y i a / w i a else 0)) =
        (∑ ω, if f ω i = a then p ω else 0) * (y i a / w i a) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> ring
    _ = y i a * marginal p f i a / w i a := by unfold marginal; ring

/-- T8(ii): arbitrary fixed positive weights give the average of
 yᵢ(d)πᵢ(d)/wᵢ(d), rather than necessarily the population mean.
The formula itself also holds for Lean's total division at zero. -/
theorem htMean_expectation {Ω D K : Type*} {N : ℕ} [Fintype Ω] [Field K] [DecidableEq D]
    (p : Ω → K) (f : Ω → Fin N → D) (y w : Fin N → D → K) (a : D) :
    expect p (htMean f y w a) = (∑ i, y i a * marginal p f i a / w i a) / N := by
  dsimp only [expect, htMean]
  calc
    (∑ ω, p ω * ((∑ i, htTerm f y w a ω i) / N)) =
        (∑ ω, ∑ i, p ω * htTerm f y w a ω i) / N := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω _
      rw [← mul_div_assoc, Finset.mul_sum]
    _ = (∑ i, ∑ ω, p ω * htTerm f y w a ω i) / N := by rw [Finset.sum_comm]
    _ = (∑ i, y i a * marginal p f i a / w i a) / N := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact htTerm_expectation p f y w a i

/-- T4(a): true positive marginal exposure probabilities give unbiased
unit contributions, population means, and the p. 212 population contrast.
This is the support-qualified correction of pp. 212 and 216. -/
theorem ht_unbiased {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (hN : 0 < N) (P : FiniteDesign Ω) (f : Ω → Fin N → D)
    (y : Fin N → D → ℝ) (a b : D) (hab : a ≠ b)
    (ha : ∀ i, 0 < marginal P.mass f i a) (hb : ∀ i, 0 < marginal P.mass f i b) :
    (∀ i, expect P.mass (fun ω => htTerm f y (marginal P.mass f) a ω i) = y i a) ∧
    expect P.mass (htMean f y (marginal P.mass f) a) = (∑ i, y i a) / N ∧
    expect P.mass (htMean f y (marginal P.mass f) b) = (∑ i, y i b) / N ∧
    expect P.mass (htContrast f y (marginal P.mass f) a b) = tau y a b := by
  have ht (e : D) (he : ∀ i, 0 < marginal P.mass f i e) :
      expect P.mass (htMean f y (marginal P.mass f) e) = (∑ i, y i e) / N := by
    rw [htMean_expectation]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact mul_div_cancel_right₀ _ (ne_of_gt (he i))
  refine ⟨?_, ht a ha, ht b hb, ?_⟩
  · intro i
    rw [htTerm_expectation]
    exact mul_div_cancel_right₀ _ (ne_of_gt (ha i))
  · unfold htContrast
    simp only [expect, mul_sub, Finset.sum_sub_distrib]
    change expect P.mass (htMean f y (marginal P.mass f) a) -
      expect P.mass (htMean f y (marginal P.mass f) b) = _
    rw [ht a ha, ht b hb]
    simp [tau, Finset.sum_sub_distrib, sub_div]

/-- "S={i:πᵢ(d)>0,πᵢ(d')>0}" in the T4 correction: a fixed target subset
of the original population, with exposures calculated on the original network. -/
noncomputable def commonSupport {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (p : Ω → ℝ) (f : Ω → Fin N → D) (a b : D) : Finset (Fin N) :=
  {i | 0 < marginal p f i a ∧ 0 < marginal p f i b}

/-- T4(c): using the same whole-network exposures and design, HT restricted
to a nonempty fixed common-support set is unbiased for its own |S| denominator.
Repair of pp. 212,216; it does not recover unsupported units' outcomes. -/
theorem common_support_unbiased {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (P : FiniteDesign Ω) (f : Ω → Fin N → D) (y : Fin N → D → ℝ)
    (a b : D) (hab : a ≠ b) (hS : (commonSupport P.mass f a b).Nonempty) :
    expect P.mass (fun ω =>
      ((commonSupport P.mass f a b).sum (fun i : Fin N =>
        htTerm f y (marginal P.mass f) a ω i -
        htTerm f y (marginal P.mass f) b ω i)) /
        (commonSupport P.mass f a b).card) =
      ((commonSupport P.mass f a b).sum (fun i : Fin N => y i a - y i b)) /
        (commonSupport P.mass f a b).card := by
  classical
  dsimp only [expect]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  simp_rw [Finset.mul_sum, mul_sub]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hs : 0 < marginal P.mass f i a ∧ 0 < marginal P.mass f i b := by
    simpa [commonSupport] using hi
  rw [Finset.sum_sub_distrib]
  change expect P.mass (fun ω => htTerm f y (marginal P.mass f) a ω i) -
    expect P.mass (fun ω => htTerm f y (marginal P.mass f) b ω i) = _
  rw [htTerm_expectation, htTerm_expectation,
    mul_div_cancel_right₀ _ (ne_of_gt hs.1), mul_div_cancel_right₀ _ (ne_of_gt hs.2)]

/-- "yᵢ(zᵢ;z₋ᵢ)" (p. 211), with the corrected second-argument type.
The subtype of indices j≠i is a canonically ordered set of N−1 coordinates. -/
def insertOwn {N : ℕ} (i : Fin N) (a : Bool) (u : {j : Fin N // j ≠ i} → Bool) :
    Assignment N := fun j => if h : j = i then a else u ⟨j, h⟩

/-- Corrected "no interference" (p. 211, T9): all other treatments may vary
while holding the unit's own treatment fixed, for every unit. -/
def NoInterference {N : ℕ} (y : Fin N → Assignment N → ℝ) : Prop :=
  ∀ i a u v, y i (insertOwn i a u) = y i (insertOwn i a v)

/-- Corrected "interference" (p. 211, T9): some unit, own-treatment value,
and two other-unit profiles give different outcomes. -/
def Interference {N : ℕ} (y : Fin N → Assignment N → ℝ) : Prop :=
  ∃ i a u v, y i (insertOwn i a u) ≠ y i (insertOwn i a v)

/-- T9(i): interference is exactly the failure of the corrected universal
no-interference condition in the p. 211 paragraph. -/
theorem interference_iff_not {N : ℕ} (y : Fin N → Assignment N → ℝ) :
    Interference y ↔ ¬NoInterference y := by
  classical
  simp only [Interference, NoInterference, not_forall]

/-- T9(i): the corrected split-profile definition is equivalent to requiring
equal outcomes for any two full assignments with equal own treatment (p. 211). -/
theorem noInterference_iff_same_own {N : ℕ} (y : Fin N → Assignment N → ℝ) :
    NoInterference y ↔ ∀ i z z', z i = z' i → y i z = y i z' := by
  constructor
  · intro h i z z' hz
    have hzi : insertOwn i (z i) (fun j => z j.val) = z := by
      funext j
      by_cases hj : j = i <;> simp [insertOwn, hj]
    have hzj : insertOwn i (z i) (fun j => z' j.val) = z' := by
      funext j
      by_cases hj : j = i <;> simp [insertOwn, hj, hz]
    simpa [hzi, hzj] using h i (z i) (fun j => z j.val) (fun j => z' j.val)
  · intro h i a u v
    apply h i
    simp [insertOwn]

/-- T9(iii): the corrected four-case display defines precisely one exposure.
The four equivalences characterize all labels, so exclusivity and exhaustion
are expressed without introducing an additional substantive assumption. -/
theorem exposure_cases {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N) :
    (exposure A z i = .d11 ↔ z i = true ∧ 0 < peerCount A z i) ∧
    (exposure A z i = .d10 ↔ z i = true ∧ peerCount A z i = 0) ∧
    (exposure A z i = .d01 ↔ z i = false ∧ 0 < peerCount A z i) ∧
    (exposure A z i = .d00 ↔ z i = false ∧ peerCount A z i = 0) := by
  cases h : z i <;> by_cases hp : 0 < peerCount A z i <;>
    simp [exposure, h, hp, Nat.eq_zero_of_not_pos, ne_of_gt]

/-- T9(ii): zero diagonal means the scalar treated-peer count is unaffected
by changing own treatment. Repair of the row-times-column display, p. 211. -/
theorem peerCount_own_independent {N : ℕ} (A : Adjacency N) (i : Fin N)
    (hdiag : A i i = false) (z z' : Assignment N)
    (hother : ∀ j, j ≠ i → z j = z' j) : peerCount A z i = peerCount A z' i := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    simp [hdiag]
  · rw [hother j hj]

/-- The complete-random-assignment support "exactly N₁ units ... treatment"
(p. 211), represented by treated subsets of size M. -/
def completeProfiles (N M : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powersetCard M

/-- Complete random assignment uses equal probability on every M-treated
profile (p. 211). Exposure probabilities are finite counts divided by the
number of supported profiles. -/
def completeProbability (N M : ℕ) (A : Adjacency N) (i : Fin N) (a : Exposure) : ℚ :=
  ((completeProfiles N M).filter (fun s => exposure A (fun j => decide (j ∈ s)) i = a)).card /
    ((completeProfiles N M).card : ℚ)

/-- T4(d) finite counting lemma: a treated subset produces zero treated
peers for i precisely when it is contained in i's nonpeer set (p. 211). -/
theorem zeroPeer_subset {N : ℕ} (A : Adjacency N) (i : Fin N) (s : Finset (Fin N)) :
    peerCount A (fun j => decide (j ∈ s)) i = 0 ↔
      s ⊆ Finset.univ.filter (fun j => A i j = false) := by
  unfold peerCount
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  constructor
  · intro h j hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩
    have hz := h j (Finset.mem_univ j)
    cases ha : A i j <;> simp_all
  · intro h j _
    by_cases hj : j ∈ s
    · have ha := (Finset.mem_filter.mp (h hj)).2
      simp [ha]
    · simp [hj]

/-- T4(d) finite counting lemma: complete random assignment gives the
printed repair's two no-peer exposure probabilities, as exact binomial
counts divided by the total number of M-treated profiles. -/
theorem complete_no_peer_probabilities (N M : ℕ) (hM : 1 ≤ M)
    (A : Adjacency N) (hdiag : ∀ i, A i i = false) (i : Fin N) :
    let k := (Finset.univ.filter (fun j => A i j)).card
    completeProbability N M A i .d10 = ((N - 1 - k).choose (M - 1) : ℚ) / (N.choose M) ∧
    completeProbability N M A i .d00 = ((N - 1 - k).choose M : ℚ) / (N.choose M) := by
  let k := (Finset.univ.filter (fun j => A i j)).card
  let U := Finset.univ.filter (fun j => A i j = false)
  let V := Finset.univ.filter (fun j => j ≠ i ∧ A i j = false)
  have hi : i ∈ U := by simp [U, hdiag]
  have hcard : U.card + k = N := by
    simpa [U, k, Bool.not_eq_true, Nat.add_comm] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun j => A i j = true)
  have hV : V = U.erase i := by
    ext j
    simp only [V, U, Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, true_and]
  have hVcard : V.card = N - 1 - k := by
    rw [hV, Finset.card_erase_of_mem hi]
    have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have h10 : (completeProfiles N M).filter (fun s => exposure A (fun j => decide (j ∈ s)) i = .d10) =
      (U.powersetCard M).filter (fun s => {i} ⊆ s) := by
    ext s
    simp only [Finset.mem_filter, completeProfiles, Finset.mem_powersetCard,
      (exposure_cases A (fun j => decide (j ∈ s)) i).2.1,
      decide_eq_true_eq, zeroPeer_subset, Finset.singleton_subset_iff]
    change ((s ⊆ Finset.univ ∧ s.card = M) ∧ i ∈ s ∧ s ⊆ U) ↔
      (s ⊆ U ∧ s.card = M) ∧ i ∈ s
    constructor
    · rintro ⟨⟨_, hs⟩, hi', hu⟩
      exact ⟨⟨hu, hs⟩, hi'⟩
    · rintro ⟨⟨hu, hs⟩, hi'⟩
      exact ⟨⟨Finset.subset_univ _, hs⟩, hi', hu⟩
  have h00 : (completeProfiles N M).filter (fun s => exposure A (fun j => decide (j ∈ s)) i = .d00) =
      V.powersetCard M := by
    ext s
    simp only [Finset.mem_filter, completeProfiles, Finset.mem_powersetCard,
      (exposure_cases A (fun j => decide (j ∈ s)) i).2.2.2,
      decide_eq_false_iff_not, zeroPeer_subset]
    change ((s ⊆ Finset.univ ∧ s.card = M) ∧ i ∉ s ∧ s ⊆ U) ↔ s ⊆ V ∧ s.card = M
    constructor
    · rintro ⟨⟨_, hs⟩, hi', hu⟩
      refine ⟨?_, hs⟩
      intro j hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_, (Finset.mem_filter.mp (hu hj)).2⟩
      intro he
      subst j
      exact hi' hj
    · rintro ⟨hv, hs⟩
      refine ⟨⟨Finset.subset_univ _, hs⟩, ?_, ?_⟩
      · intro his
        exact (Finset.mem_filter.mp (hv his)).2.1 rfl
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp (hv hj)).2.2⟩
  unfold completeProbability
  rw [h10, h00]
  have ht : (completeProfiles N M).card = N.choose M := by simp [completeProfiles]
  rw [ht, Finset.card_filter_powersetCard_subset ({i} : Finset (Fin N)) U M
    (by simpa only [Finset.singleton_subset_iff] using hi) (by simpa using hM),
    Finset.card_powersetCard, hVcard]
  simp only [Finset.card_singleton]
  have hu : U.card - 1 = N - 1 - k := by omega
  rw [hu]
  exact ⟨rfl, rfl⟩

/-- T4(d) finite support lemma: with 0≤M≤N and the uniform complete-design
law, positive exposure probability is exactly existence of an M-treated
profile giving that exposure. Zero probabilities are not numerical failures. -/
theorem complete_probability_pos_iff (N M : ℕ) (hMN : M ≤ N)
    (A : Adjacency N) (i : Fin N) (a : Exposure) :
    0 < completeProbability N M A i a ↔
      ∃ s : Finset (Fin N), s.card = M ∧ exposure A (fun j => decide (j ∈ s)) i = a := by
  have hd : (0 : ℚ) < (completeProfiles N M).card := by
    exact_mod_cast (show 0 < (completeProfiles N M).card by
      simpa [completeProfiles] using Nat.choose_pos hMN)
  unfold completeProbability
  rw [div_pos_iff_of_pos_right hd, Nat.cast_pos, Finset.card_pos, Finset.Nonempty]
  simp only [Finset.mem_filter, completeProfiles, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]

/-- T4(d) finite counting identity: under complete assignment, the treated
and control exposure pairs have total probabilities M/N and (N−M)/N. -/
theorem complete_own_probability (N M : ℕ) (hN : 0 < N) (hM : 1 ≤ M) (hMN : M ≤ N - 1)
    (A : Adjacency N) (i : Fin N) :
    completeProbability N M A i .d11 + completeProbability N M A i .d10 = (M : ℚ) / N ∧
    completeProbability N M A i .d01 + completeProbability N M A i .d00 = ((N - M : ℕ) : ℚ) / N := by
  let S := completeProfiles N M
  have hp11 (s : Finset (Fin N)) :
      exposure A (fun j => decide (j ∈ s)) i = .d11 ↔ i ∈ s ∧ 0 < peerCount A (fun j => decide (j ∈ s)) i := by
    simpa only [decide_eq_true_eq] using (exposure_cases A (fun j => decide (j ∈ s)) i).1
  have hp10 (s : Finset (Fin N)) :
      exposure A (fun j => decide (j ∈ s)) i = .d10 ↔ i ∈ s ∧ ¬0 < peerCount A (fun j => decide (j ∈ s)) i := by
    simpa only [decide_eq_true_eq, not_lt, Nat.le_zero] using
      (exposure_cases A (fun j => decide (j ∈ s)) i).2.1
  have hp01 (s : Finset (Fin N)) :
      exposure A (fun j => decide (j ∈ s)) i = .d01 ↔ i ∉ s ∧ 0 < peerCount A (fun j => decide (j ∈ s)) i := by
    simpa only [decide_eq_false_iff_not] using (exposure_cases A (fun j => decide (j ∈ s)) i).2.2.1
  have hp00 (s : Finset (Fin N)) :
      exposure A (fun j => decide (j ∈ s)) i = .d00 ↔ i ∉ s ∧ ¬0 < peerCount A (fun j => decide (j ∈ s)) i := by
    simpa only [decide_eq_false_iff_not, not_lt, Nat.le_zero] using
      (exposure_cases A (fun j => decide (j ∈ s)) i).2.2.2
  have htreated :
      (S.filter (fun s => exposure A (fun j => decide (j ∈ s)) i = .d11)).card +
      (S.filter (fun s => exposure A (fun j => decide (j ∈ s)) i = .d10)).card =
      (S.filter (fun s => i ∈ s)).card := by
    simpa only [Finset.filter_filter, hp11, hp10] using
      Finset.card_filter_add_card_filter_not (s := S.filter (fun s => i ∈ s))
        (fun s => 0 < peerCount A (fun j => decide (j ∈ s)) i)
  have hcontrol :
      (S.filter (fun s => exposure A (fun j => decide (j ∈ s)) i = .d01)).card +
      (S.filter (fun s => exposure A (fun j => decide (j ∈ s)) i = .d00)).card =
      (S.filter (fun s => i ∉ s)).card := by
    simpa only [Finset.filter_filter, hp01, hp00] using
      Finset.card_filter_add_card_filter_not (s := S.filter (fun s => i ∉ s))
        (fun s => 0 < peerCount A (fun j => decide (j ∈ s)) i)
  have htcard : (S.filter (fun s => i ∈ s)).card = (N - 1).choose (M - 1) := by
    simpa [S, completeProfiles, Finset.singleton_subset_iff] using
      Finset.card_filter_powersetCard_subset ({i} : Finset (Fin N)) Finset.univ M
        (Finset.subset_univ _) (by simpa using hM)
  have heq : S.filter (fun s => i ∉ s) = (Finset.univ.erase i).powersetCard M := by
    ext s
    simp only [S, completeProfiles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨hc, hn⟩
      exact ⟨fun j hj => Finset.mem_erase.mpr ⟨by intro h; subst j; exact hn hj, Finset.mem_univ j⟩, hc⟩
    · rintro ⟨hs, hc⟩
      exact ⟨hc, by intro hi; exact (Finset.mem_erase.mp (hs hi)).1 rfl⟩
  have hccard : (S.filter (fun s => i ∉ s)).card = (N - 1).choose M := by
    rw [heq, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have htotal : S.card = N.choose M := by simp [S, completeProfiles]
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hd : (N.choose M : ℚ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero (by omega : M ≤ N)
  have htMul : (N : ℚ) * ((N - 1).choose (M - 1) : ℚ) = (N.choose M : ℚ) * M := by
    have h := Nat.add_one_mul_choose_eq (N - 1) (M - 1)
    have hn' : N - 1 + 1 = N := by omega
    have hm' : M - 1 + 1 = M := by omega
    rw [hn', hm'] at h
    exact_mod_cast h
  have hcMul : ((N - 1).choose M : ℚ) * N = (N.choose M : ℚ) * (N - M : ℕ) := by
    have h := Nat.choose_mul_succ_eq (N - 1) M
    have hn' : N - 1 + 1 = N := by omega
    rw [hn'] at h
    exact_mod_cast h
  constructor
  · unfold completeProbability
    rw [← add_div, ← Nat.cast_add, htreated, htcard, htotal]
    apply (div_eq_div_iff hd hn).2
    nlinarith [htMul]
  · unfold completeProbability
    rw [← add_div, ← Nat.cast_add, hcontrol, hccard, htotal]
    apply (div_eq_div_iff hd hn).2
    nlinarith [hcMul]

/-- T4(d) finite support criterion: complete random assignment supports all
four exposures exactly when M≥2 and 1≤kᵢ≤N−M−1. This is the precise reason
that having no isolates does not suffice (pp. 212,216, corrected). -/
theorem complete_all_positive_iff (N M : ℕ) (hN : 0 < N) (hM : 1 ≤ M) (hMN : M ≤ N - 1)
    (A : Adjacency N) (hdiag : ∀ i, A i i = false) (i : Fin N) :
    let k := (Finset.univ.filter (fun j => A i j)).card
    (∀ a, 0 < completeProbability N M A i a) ↔ 2 ≤ M ∧ 1 ≤ k ∧ k ≤ N - M - 1 := by
  let B := Finset.univ.filter (fun j => A i j)
  let k := B.card
  change (∀ a, 0 < completeProbability N M A i a) ↔ 2 ≤ M ∧ 1 ≤ k ∧ k ≤ N - M - 1
  have hkN : k ≤ N - 1 := by
    have hs : B ⊆ Finset.univ.erase i := by
      intro j hj
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ j⟩
      intro he
      subst j
      simpa [B, hdiag] using hj
    have hc := Finset.card_le_card hs
    simpa [k] using hc
  have hd : (0 : ℚ) < N.choose M := by exact_mod_cast Nat.choose_pos (by omega : M ≤ N)
  have hex (a : Exposure) := complete_probability_pos_iff N M (by omega) A i a
  have hPeer (s : Finset (Fin N)) (hp : 0 < peerCount A (fun j => decide (j ∈ s)) i) :
      ∃ j ∈ s, A i j = true := by
    by_contra h
    push_neg at h
    have hz : peerCount A (fun j => decide (j ∈ s)) i = 0 := by
      apply (zeroPeer_subset A i s).2
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, Bool.eq_false_iff.mpr (h j hj)⟩
    omega
  have hcount (s : Finset (Fin N)) (j : Fin N) (hj : j ∈ s) (ha : A i j = true) :
      0 < peerCount A (fun t => decide (t ∈ s)) i := by
    have hs := Finset.single_le_sum (s := Finset.univ)
      (f := fun t => if A i t && decide (t ∈ s) then (1 : ℕ) else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [ha, hj, decide_true, Bool.and_self, ite_true] at hs
    exact lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hs
  constructor
  · intro hall
    obtain ⟨s, hs, he⟩ := (hex .d11).1 (hall .d11)
    have hobs := (exposure_cases A (fun j => decide (j ∈ s)) i).1.mp he
    have hi : i ∈ s := of_decide_eq_true hobs.1
    obtain ⟨j, hj, ha⟩ := hPeer s hobs.2
    have hji : j ≠ i := by intro h; subst j; simpa [hdiag i] using ha
    have htwo : 2 ≤ s.card := by
      have hsub : ({i,j} : Finset (Fin N)) ⊆ s :=
        Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hj⟩
      simpa [hji, Ne.symm hji] using Finset.card_le_card hsub
    have hkp : 1 ≤ k := by
      have hp : 0 < B.card := Finset.card_pos.mpr ⟨j, by simp [B, ha]⟩
      exact hp
    have h00 := (complete_no_peer_probabilities N M hM A hdiag i).2
    have hcpos : (0 : ℚ) < ((N - 1 - k).choose M : ℚ) := by
      have hp := hall .d00
      rw [h00] at hp
      exact (div_pos_iff_of_pos_right hd).1 hp
    have hcap : M ≤ N - 1 - k := Nat.choose_ne_zero_iff.mp (ne_of_gt (Nat.cast_pos.mp hcpos))
    exact ⟨by omega, hkp, by omega⟩
  · rintro ⟨hm2, hk1, hkcap⟩
    have hcap : M ≤ N - 1 - k := by omega
    have hnp : M ≤ N := by omega
    obtain ⟨j, hj⟩ : B.Nonempty := Finset.card_pos.mp hk1
    have haj : A i j = true := (Finset.mem_filter.mp hj).2
    have hji : j ≠ i := by intro h; subst j; simpa [hdiag i] using haj
    have hd11 : 0 < completeProbability N M A i .d11 := by
      obtain ⟨s, htwo, _, hs⟩ := Finset.exists_subsuperset_card_eq
        (s := ({i,j} : Finset (Fin N))) (t := Finset.univ)
        (Finset.subset_univ _) (by simpa [hji, Ne.symm hji] using hm2)
        (by simpa using hnp)
      have his : i ∈ s := htwo (by simp)
      have hjs : j ∈ s := htwo (by simp)
      apply (hex .d11).2
      exact ⟨s, hs, (exposure_cases A (fun t => decide (t ∈ s)) i).1.mpr
        ⟨by simpa using his, hcount s j hjs haj⟩⟩
    have hd01 : 0 < completeProbability N M A i .d01 := by
      obtain ⟨s, hjs, hsub, hs⟩ := Finset.exists_subsuperset_card_eq
        (s := ({j} : Finset (Fin N))) (t := Finset.univ.erase i)
        (by simp [hji]) (by simpa using hM) (by simpa using hMN)
      have his : i ∉ s := by intro h; exact (Finset.mem_erase.mp (hsub h)).1 rfl
      have hj' : j ∈ s := hjs (by simp)
      apply (hex .d01).2
      exact ⟨s, hs, (exposure_cases A (fun t => decide (t ∈ s)) i).2.2.1.mpr
        ⟨by simpa using his, hcount s j hj' haj⟩⟩
    have hnop := complete_no_peer_probabilities N M hM A hdiag i
    intro a
    cases a
    · exact hd11
    · rw [hnop.1]
      exact div_pos (by exact_mod_cast Nat.choose_pos (by omega : M - 1 ≤ N - 1 - k)) hd
    · exact hd01
    · rw [hnop.2]
      exact div_pos (by exact_mod_cast Nat.choose_pos hcap) hd

/-- T4(d): the exact four exposure probabilities under complete random
assignment, and the necessary and sufficient degree condition for all four
to be positive. Repair of the missing support condition, pp. 212,216. -/
theorem complete_randomization_support (N M : ℕ) (hN : 0 < N)
    (hM : 1 ≤ M) (hMN : M ≤ N - 1) (A : Adjacency N)
    (hsym : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = false) (i : Fin N) :
    let k := (Finset.univ.filter (fun j => A i j)).card
    completeProbability N M A i .d10 = ((N - 1 - k).choose (M - 1) : ℚ) / (N.choose M) ∧
    completeProbability N M A i .d00 = ((N - 1 - k).choose M : ℚ) / (N.choose M) ∧
    completeProbability N M A i .d11 = (M : ℚ) / N - completeProbability N M A i .d10 ∧
    completeProbability N M A i .d01 = ((N - M : ℕ) : ℚ) / N - completeProbability N M A i .d00 ∧
    ((∀ a, 0 < completeProbability N M A i a) ↔ 2 ≤ M ∧ 1 ≤ k ∧ k ≤ N - M - 1) := by
  have hnp := complete_no_peer_probabilities N M hM A hdiag i
  have hop := complete_own_probability N M hN hM hMN A i
  refine ⟨hnp.1, hnp.2, ?_, ?_, complete_all_positive_iff N M hN hM hMN A hdiag i⟩
  · linarith [hop.1]
  · linarith [hop.2]

/-- The star adjacency in T3: vertex 0 is adjacent to all three leaves;
there are no loops and no isolated vertices. -/
def starAdj : Adjacency 4 := fun i j => decide (i ≠ j ∧ (i = 0 ∨ j = 0))

/-- The six equiprobable complete-randomization assignments in T3, in the
order printed in the fixed target list; all have exactly two treated units. -/
def starAssignments : Fin 6 → Assignment 4 :=
  ![![false,false,true,true], ![false,true,false,true], ![false,true,true,false],
    ![true,false,false,true], ![true,false,true,false], ![true,true,false,false]]

/-- Schedule A of T3: all sixteen exposure potential outcomes are 1. -/
def starA : Fin 4 → Exposure → ℚ := fun _ _ => 1

/-- Schedule B of T3: only the unsupported center no-exposure outcome
changes, from 1 to 5. Real outcomes on every binary profile are defined by
composition with the p. 211 exposure mapping. -/
def starB : Fin 4 → Exposure → ℚ := fun i a => if i = 0 ∧ a = .d00 then 5 else 1

/-- T3(i)–(iii),(v): the nonisolated four-unit star under complete assignment
of two treatments has the stated probabilities, identical observed outcomes,
different population contrasts, and biased observed-exposure HT contrasts. -/
theorem star_counterexample :
    (∀ i, ∃ j, starAdj i j = true) ∧
    (∀ r, (Finset.univ.filter (fun i => starAssignments r i)).card = 2) ∧
    (∀ i a, marginal (fun _ : Fin 6 => (1/6 : ℚ))
      (fun r => exposure starAdj (starAssignments r)) i a =
      if i = 0 then (match a with | .d11 => 1/2 | .d10 => 0 | .d01 => 1/2 | .d00 => 0)
      else (match a with | .d11 => 1/6 | .d10 => 1/3 | .d01 => 1/3 | .d00 => 1/6)) ∧
    (∀ r i, starA i (exposure starAdj (starAssignments r) i) = 1 ∧
      starB i (exposure starAdj (starAssignments r) i) = 1) ∧
    tau starA .d11 .d00 = 0 ∧ tau starB .d11 .d00 = -1 ∧
    (∀ flag : Bool, let y := if flag then starA else starB;
      expect (fun _ : Fin 6 => (1/6 : ℚ))
        (htMean (fun r => exposure starAdj (starAssignments r)) y
          (marginal (fun _ : Fin 6 => (1/6 : ℚ)) (fun r => exposure starAdj (starAssignments r)))
          .d11) = 1 ∧
      expect (fun _ : Fin 6 => (1/6 : ℚ))
        (htMean (fun r => exposure starAdj (starAssignments r)) y
          (marginal (fun _ : Fin 6 => (1/6 : ℚ)) (fun r => exposure starAdj (starAssignments r)))
          .d00) = 3/4 ∧
      expect (fun _ : Fin 6 => (1/6 : ℚ))
        (htContrast (fun r => exposure starAdj (starAssignments r)) y
          (marginal (fun _ : Fin 6 => (1/6 : ℚ)) (fun r => exposure starAdj (starAssignments r)))
          .d11 .d00) = 1/4 ∧
      expect (fun _ : Fin 6 => (1/6 : ℚ))
        (htContrast (fun r => exposure starAdj (starAssignments r)) y
          (marginal (fun _ : Fin 6 => (1/6 : ℚ)) (fun r => exposure starAdj (starAssignments r)))
          .d11 .d00) - tau y .d11 .d00 = if flag then 1/4 else 5/4) := by
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 0 in
      decide +kernel

/-- T3(iv): every real-valued estimator of the assignment, exposure vector,
and outcome vector has equal expectation under the two star schedules;
it cannot be unbiased for both population effects 0 and −1 (p. 212 claim).
The design and network are known fixed arguments of the estimator. -/
theorem star_nonidentification
    (T : Assignment 4 → (Fin 4 → Exposure) → (Fin 4 → ℝ) → ℝ) :
    let f := fun r => exposure starAdj (starAssignments r)
    let TA := fun r => T (starAssignments r) (f r) (fun i => (starA i (f r i) : ℝ))
    let TB := fun r => T (starAssignments r) (f r) (fun i => (starB i (f r i) : ℝ))
    expect (fun _ : Fin 6 => (1/6 : ℝ)) TA = expect (fun _ : Fin 6 => (1/6 : ℝ)) TB ∧
    ¬(expect (fun _ : Fin 6 => (1/6 : ℝ)) TA = 0 ∧
      expect (fun _ : Fin 6 => (1/6 : ℝ)) TB = -1) := by
  dsimp only
  have hy : ∀ r i, starA i (exposure starAdj (starAssignments r) i) =
      starB i (exposure starAdj (starAssignments r) i) := by decide +kernel
  have hfun : (fun r => T (starAssignments r) (exposure starAdj (starAssignments r))
      (fun i => (starA i (exposure starAdj (starAssignments r) i) : ℝ))) =
    (fun r => T (starAssignments r) (exposure starAdj (starAssignments r))
      (fun i => (starB i (exposure starAdj (starAssignments r) i) : ℝ))) := by
    funext r
    congr 1
    funext i
    exact congrArg (fun q : ℚ => (q : ℝ)) (hy r i)
  refine ⟨congrArg (expect (fun _ : Fin 6 => (1/6 : ℝ))) hfun, ?_⟩
  intro h
  have he := congrArg (expect (fun _ : Fin 6 => (1/6 : ℝ))) hfun
  linarith [h.1, h.2]

/-- The eight-cycle in T7, with an edge between consecutive vertices modulo 8. -/
def cycle8Adj : Adjacency 8 := fun i j => decide
  ((i.val + 1) % 8 = j.val ∨ (j.val + 1) % 8 = i.val)

/-- T7's design is uniform on the eight cyclic rotations of (1,1,0,1,0,0,0,0).
Using left rotations fixes the same design and the stated base assignment. -/
def cycle8Assignments (r : Fin 8) : Assignment 8 := fun i =>
  decide ((i.val + r.val) % 8 ∈ ({0,1,3} : Finset ℕ))

/-- Exposure counts cᵢ(a) over an enumerated table, used in the p. 214 recipe
and the supplied model of `make_exposure_prob` inputs. -/
def exposureCount {R N : ℕ} {D : Type*} [DecidableEq D]
    (f : Fin R → Fin N → D) (i : Fin N) (a : D) : ℕ :=
  (Finset.univ.filter (fun r => f r i = a)).card

/-- Joint counts cᵢⱼ(a,b) over the same table. -/
def jointCount {R N : ℕ} {D : Type*} [DecidableEq D]
    (f : Fin R → Fin N → D) (i j : Fin N) (a b : D) : ℕ :=
  (Finset.univ.filter (fun r => f r i = a ∧ f r j = b)).card

/-- Returned marginal weights (cᵢ(a)+1)/(R+1), rather than counts/R:
the package's `make_exposure_prob`, used on pp. 216,218 (T8 correction). -/
def smoothedWeight {R N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    (f : Fin R → Fin N → D) (i : Fin N) (a : D) : K :=
  ((exposureCount f i a : K) + 1) / ((R : K) + 1)

/-- Returned joint weights: same-exposure entries add the diagonal identity
then divide by R+1; cross-exposure entries divide by R (T8 correction). -/
def smoothedJoint {R N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    (f : Fin R → Fin N → D) (i j : Fin N) (a b : D) : K :=
  if a = b then ((jointCount f i j a b : K) + if i = j then 1 else 0) / ((R : K) + 1)
  else (jointCount f i j a b : K) / R

/-- The constant potential-outcome schedule (2,3/2,5/4,1) in T7. -/
def cycle8Y : Fin 8 → Exposure → ℚ := fun _ a =>
  match a with | .d11 => 2 | .d10 => 3/2 | .d01 => 5/4 | .d00 => 1

/-- T7(i)–(v): exhaustive enumeration on the nonisolated eight-cycle gives
positive exact probabilities but smoothed weights summing to 4/3, constant
biased HT means, and inconsistent marginal/joint weights. Refutes the
finite-bank exact-unbiasedness reading of pp. 212,216. -/
theorem cycle8_smoothing_counterexample :
    let f := fun r => exposure cycle8Adj (cycle8Assignments r)
    let p := marginal (fun _ : Fin 8 => (1/8 : ℚ)) f
    let q := fun i a => (smoothedWeight f i a : ℚ)
    (∀ i, ∃ j, cycle8Adj i j = true) ∧
    Function.Injective cycle8Assignments ∧
    (∀ i a, exposureCount f i a = match a with | .d11 => 2 | .d10 => 1 | .d01 => 3 | .d00 => 2) ∧
    (∀ i a, p i a = match a with | .d11 => 1/4 | .d10 => 1/8 | .d01 => 3/8 | .d00 => 1/4) ∧
    (∀ i a, q i a = match a with | .d11 => 1/3 | .d10 => 2/9 | .d01 => 4/9 | .d00 => 1/3) ∧
    (∀ i, ∑ a, q i a = 4/3) ∧
    (∀ r a, htMean f cycle8Y q a r =
      match a with | .d11 => 3/2 | .d10 => 27/32 | .d01 => 135/128 | .d00 => 3/4) ∧
    (∀ r a, htMean f cycle8Y p a r = cycle8Y 0 a) ∧
    (∑ b, (smoothedJoint f (0 : Fin 8) (1 : Fin 8) .d11 b : ℚ)) = 17/72 ∧
    q 0 .d11 = 1/3 ∧ (17/72 : ℚ) ≠ 1/3 ∧
    expect (fun _ : Fin 8 => (1/8 : ℚ)) (htContrast f cycle8Y q .d11 .d00) = 3/4 ∧
    tau cycle8Y .d11 .d00 = 1 := by
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 0 in
      decide +kernel

/-- T8(i): an exhaustive equally likely list gives exact marginal and joint
exposure probabilities by counts/R, including same-exposure diagonals.
Repair of the exposure-probability recipe, pp. 212,214,216. -/
theorem exhaustive_probabilities {R N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    (hR : 0 < R) (f : Fin R → Fin N → D) (i j : Fin N) (a b : D) :
    marginal (fun _ : Fin R => (1 / R : K)) f i a = exposureCount f i a / (R : K) ∧
    joint (fun _ : Fin R => (1 / R : K)) f i j a b = jointCount f i j a b / (R : K) := by
  have aux (test : Fin R → Prop) [DecidablePred test] :
      (∑ r, if test r then (1 / R : K) else 0) =
        ((Finset.univ.filter test).card : K) / R := by
    rw [Finset.sum_ite]
    simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  exact ⟨aux (fun r => f r i = a), aux (fun r => f r i = a ∧ f r j = b)⟩

/-- T8(iii), scalar identity: the exact probability divided by its returned
smoothed weight, minus 1, is (c−R)/(R(c+1)). For c<R its sign is negative.
Repair of the finite-enumeration unbiasedness claim (pp. 212,216). -/
theorem smoothing_bias_multiplier (R c : ℕ) (hR : 0 < R) :
    ((c : ℝ) / R) / (((c : ℝ) + 1) / ((R : ℝ) + 1)) - 1 =
      ((c : ℝ) - R) / ((R : ℝ) * ((c : ℝ) + 1)) ∧
    (c < R → ((c : ℝ) - R) / ((R : ℝ) * ((c : ℝ) + 1)) < 0) := by
  have hr : (R : ℝ) ≠ 0 := by positivity
  have hc : (c : ℝ) + 1 ≠ 0 := by positivity
  have hr1 : (R : ℝ) + 1 ≠ 0 := by positivity
  constructor
  · field_simp
    <;> ring
  · intro h
    apply div_neg_of_neg_of_pos
    · exact sub_neg.mpr (by exact_mod_cast h)
    · positivity

/-- T8(iii): smoothed marginal values sum to (R+K)/(R+1)>1 for K≥2,
because mutually exclusive exhaustive exposures have counts summing to R.
Repair of the p. 216 identification of these values with probabilities. -/
theorem smoothed_not_distribution {D : Type*} [Fintype D]
    (R : ℕ) (c : D → ℕ) (hcounts : ∑ a, c a = R) (hK : 2 ≤ Fintype.card D) :
    (∑ a, ((c a : ℝ) + 1) / ((R : ℝ) + 1)) =
      ((R : ℝ) + Fintype.card D) / ((R : ℝ) + 1) ∧
    1 < (∑ a, ((c a : ℝ) + 1) / ((R : ℝ) + 1)) := by
  have heq : (∑ a, ((c a : ℝ) + 1) / ((R : ℝ) + 1)) =
      ((R : ℝ) + Fintype.card D) / ((R : ℝ) + 1) := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    simp [← Nat.cast_sum, hcounts]
  refine ⟨heq, ?_⟩
  rw [heq, lt_div_iff₀ (by positivity)]
  have hk : (2 : ℝ) ≤ Fintype.card D := by exact_mod_cast hK
  linarith


/-- kᵢ=∑ⱼ Aᵢⱼ, the first-neighbor degree used by the outcome generator
(p. 216). -/
def degree {N : ℕ} (A : Adjacency N) (i : Fin N) : ℕ :=
  ∑ j, if A i j then 1 else 0

/-- qᵢ=#{j≠i:(A²)ᵢⱼ>0}, "second-order degree" in the p. 216 generator,
from the package's `make_dilated_out` generator. Counts two-edge walks' reachable
vertices, not shortest-path distance exactly two. -/
def twoWalkDegree {N : ℕ} (A : Adjacency N) (i : Fin N) : ℕ :=
  (Finset.univ.filter (fun j => j ≠ i ∧ ∃ k, A i k = true ∧ A k j = true)).card

/-- aᵢ=kᵢ+qᵢ+kᵢqᵢ, the degree-dependent baseline coefficient
(correction T6 to p. 216). -/
def degreeScale {N : ℕ} (A : Adjacency N) (i : Fin N) : ℕ :=
  degree A i + twoWalkDegree A i + degree A i * twoWalkDegree A i

/-- Corrected baseline Bᵢ=aᵢ|Gᵢ|+Eᵢ, with standard-normal G and
N(1,1/16) noise E conditional on the fixed network (T6; p. 216). -/
def baseline (a g e : ℝ) : ℝ := a * |g| + e

/-- "multipliers ... (2,1.5,1.25)" (p. 216): the four fixed realized
exposure potential outcomes from a baseline vector. -/
def dilatedOutcomes {N : ℕ} (B : Fin N → ℝ) : Fin N → Exposure → ℝ :=
  fun i d => (match d with | .d11 => 2 | .d10 => 3/2 | .d01 => 5/4 | .d00 => 1) * B i

/-- Independent conditional normal ingredients for one unit of T5/T6.
The product of N(0,1) and N(1,1/16) represents G and E for the fixed graph. -/
noncomputable def normalPair : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 1 (1/16))

/-- The corrected baseline law in T6, the image of the independent normal
pair under (g,e)↦a|g|+e. -/
noncomputable def baselineLaw (a : ℝ) : Measure ℝ :=
  normalPair.map (fun x => baseline a x.1 x.2)

/-- "absolute standard normal distribution" (p. 216): the law of |G|
for G~N(0,1), which is supported on nonnegative reals (T5/T13). -/
noncomputable def halfNormalLaw : Measure ℝ := (gaussianReal 0 1).map (fun g => |g|)

/-- T5(i): exact triangle, coefficient 8 and dyadic normal-draw witness
produce the baseline vector (−5/8,9,21/4), including a negative baseline.
This arithmetic witness has probability zero by itself; T5's distributional
refutation is stated separately below. -/
theorem triangle_baseline_witness :
    (∀ i : Fin 3, degree (fun i j => decide (i ≠ j)) i = 2 ∧
      twoWalkDegree (fun i j => decide (i ≠ j)) i = 2 ∧
      degreeScale (fun i j => decide (i ≠ j)) i = 8) ∧
    (∀ i : Fin 3, baseline 8 (![1/64,1,-1/2] i) (![-3/4,1,5/4] i) = ![-5/8,9,21/4] i) ∧
    baseline 8 (1/64) (-3/4) < 0 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · intro i
    fin_cases i <;> norm_num [baseline]
  · norm_num [baseline]

/-- T5(ii), finite inequality: for any nonnegative degree coefficient,
|g|<1/[4(a+1)] and −1<e<−1/2 force a|g|+e<−1/4. -/
theorem negative_baseline_event (a g e : ℝ) (ha : 0 ≤ a)
    (hg : |g| < 1 / (4 * (a + 1))) (he0 : -1 < e) (he : e < -1/2) :
    baseline a g e < -1/4 := by
  have hd : 0 < 4 * (a + 1) := by positivity
  have hg' := (lt_div_iff₀ hd).mp hg
  have habs := abs_nonneg g
  unfold baseline
  nlinarith

/-- T5(ii)–(iii): the generator's baseline law assigns positive probability
to negative values for every a≥0, whereas |G| never is negative. Thus the
printed absolute-standard-normal description on p. 216 is false for this law. -/
theorem baseline_not_halfNormal (a : ℝ) (ha : 0 ≤ a) :
    0 < baselineLaw a (Set.Iio 0) ∧ halfNormalLaw (Set.Iio 0) = 0 ∧
      baselineLaw a ≠ halfNormalLaw := by
  letI : Measure.IsOpenPosMeasure (gaussianReal (0 : ℝ) 1) :=
    (gaussianReal_absolutelyContinuous' (μ := 0) (v := 1) (by norm_num)).isOpenPosMeasure
  letI : Measure.IsOpenPosMeasure (gaussianReal (1 : ℝ) (1/16)) :=
    (gaussianReal_absolutelyContinuous' (μ := 1) (v := 1/16) (by norm_num)).isOpenPosMeasure
  haveI : Measure.IsOpenPosMeasure normalPair := by unfold normalPair; infer_instance
  have hc : Continuous (fun x : ℝ × ℝ => baseline a x.1 x.2) := by
    unfold baseline
    fun_prop
  have hpre : 0 < normalPair ((fun x : ℝ × ℝ => baseline a x.1 x.2) ⁻¹' Set.Iio 0) :=
    (isOpen_Iio.preimage hc).measure_pos normalPair ⟨(0,-1), by simp [baseline]⟩
  have hneg : 0 < baselineLaw a (Set.Iio 0) := by
    simpa only [baselineLaw, Measure.map_apply hc.measurable measurableSet_Iio] using hpre
  have hhalf : halfNormalLaw (Set.Iio 0) = 0 := by
    unfold halfNormalLaw
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
    have he : (fun g : ℝ => |g|) ⁻¹' Set.Iio 0 = ∅ := by
      ext g
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
      exact not_lt.mpr (abs_nonneg g)
    rw [he, measure_empty]
  refine ⟨hneg, hhalf, ?_⟩
  intro heq
  rw [heq, hhalf] at hneg
  exact (lt_irrefl _ hneg)

/-- T6(iii): the true realized population effects for the default multipliers
are mean(B), half mean(B), and quarter mean(B), for arbitrary real baselines.
The estimand is the one displayed on p. 212. -/
theorem dilated_effects {N : ℕ} (B : Fin N → ℝ) :
    tau (dilatedOutcomes B) .d11 .d00 = (∑ i, B i) / N ∧
    tau (dilatedOutcomes B) .d10 .d00 = (1/2 : ℝ) * ((∑ i, B i) / N) ∧
    tau (dilatedOutcomes B) .d01 .d00 = (1/4 : ℝ) * ((∑ i, B i) / N) := by
  simp only [tau, dilatedOutcomes]
  have h (c : ℝ) : (∑ i, (c * B i - 1 * B i)) = (c - 1) * ∑ i, B i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h 2, h (3/2), h (5/4)]
  constructor
  · ring
  · constructor <;> ring

/-- T6(iv): on graphs without isolates the mean baseline shift is at least
1 above the half-normal mean. The scalar inequality is the finite step of
the correction's scale comparison. -/
theorem baseline_mean_shift (a : ℝ) (ha : 1 ≤ a) :
    1 ≤ (a * Real.sqrt (2 / Real.pi) + 1) - Real.sqrt (2 / Real.pi) := by
  have hs := Real.sqrt_nonneg (2 / Real.pi)
  nlinarith

/-- Identity-block Bernoulli edge probabilities in T10: the source premise
(default beta=0) sets P to the community identity. This is not a proof of
randnet's implementation; it expresses its supplied mathematical semantics. -/
def blockEdgeProbability {N : ℕ} {C : Type*} [DecidableEq C]
    (s : ℝ) (t : Fin N → ℝ) (c : Fin N → C) (i j : Fin N) : ℝ :=
  s * t i * t j * (if c i = c j then 1 else 0)

/-- T10(i), deterministic probability calculation: different communities
have edge probability zero under the supplied identity-block semantics.
Correction of the 0.7 edge-share description on p. 214. -/
theorem crossCommunity_probability_zero {N : ℕ} {C : Type*} [DecidableEq C]
    (s : ℝ) (t : Fin N → ℝ) (c : Fin N → C) (i j : Fin N) (h : c i ≠ c j) :
    blockEdgeProbability s t c i j = 0 := by simp [blockEdgeProbability, h]

/-- Edges within a community, as unordered edges of the simple graph in
T10 (pp. 214–215). The edge-share calculation is conditional on the stated
source-code semantics; no claim of termination of the rejection loop is made. -/
noncomputable def withinEdges {N : ℕ} {C : Type*} (G : SimpleGraph (Fin N))
    (c : Fin N → C) : Finset (Sym2 (Fin N)) := by
  classical
  exact G.edgeFinset.filter (fun e => ∃ i j, e = s(i,j) ∧ c i = c j)

/-- T10(ii)–(iii): a finite nonisolated simple graph has at least N/2 edges.
If every edge stays within a community, the within-community share is
exactly 1, a difference of 3/10 from the printed 0.7. Correction of p. 214. -/
theorem within_community_share {N : ℕ} {C : Type*} (hN : 0 < N)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (c : Fin N → C)
    (hdegree : ∀ i, 0 < G.degree i) (hwithin : ∀ i j, G.Adj i j → c i = c j) :
    N ≤ 2 * G.edgeFinset.card ∧ 0 < G.edgeFinset.card ∧
    (withinEdges G c).card = G.edgeFinset.card ∧
    ((withinEdges G c).card : ℝ) / G.edgeFinset.card = 1 ∧
    ((withinEdges G c).card : ℝ) / G.edgeFinset.card - 7/10 = 3/10 := by
  classical
  have hbound : N ≤ 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc N = ∑ _i : Fin N, 1 := by simp
         _ ≤ ∑ i, G.degree i := Finset.sum_le_sum (fun i _ => hdegree i)
  have hpos : 0 < G.edgeFinset.card := by omega
  have heq : withinEdges G c = G.edgeFinset := by
    ext e
    simp only [withinEdges, Finset.mem_filter]
    constructor
    · exact fun h => by simpa only [SimpleGraph.mem_edgeFinset] using h.1
    · intro he
      refine ⟨by simpa only [SimpleGraph.mem_edgeFinset] using he, ?_⟩
      induction e using Sym2.inductionOn with
      | hf i j => exact ⟨i, j, rfl, hwithin i j (by simpa using he)⟩
  refine ⟨hbound, hpos, congrArg Finset.card heq, ?_, ?_⟩
  · rw [heq]
    exact div_self (by exact_mod_cast (ne_of_gt hpos))
  · rw [heq, div_self (by exact_mod_cast (ne_of_gt hpos))]
    norm_num

/-- T12: the mathematical unbiasedness assertion as printed on pp. 212,216,
with no unitwise support requirement, encoded as a proposition rather than
an axiom. Division at zero means unsupported terms are dropped. -/
def PrintedUnbiasedness : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (P : FiniteDesign (Assignment N))
    (A : Adjacency N) (_hdiag : ∀ i, A i i = false)
    (y : Fin N → Exposure → ℝ) (a b : Exposure) (_hab : a ≠ b)
    (_possible_a : ∃ i, 0 < marginal P.mass (fun z => exposure A z) i a)
    (_possible_b : ∃ i, 0 < marginal P.mass (fun z => exposure A z) i b),
    expect P.mass (htContrast (fun z => exposure A z) y
      (marginal P.mass (fun z => exposure A z)) a b) = tau y a b


/-- When R does not exceed the number of positive-mass design profiles, this is
the law of R distinct simulated profiles obtained by successive design draws
with repeat profiles rejected. For an injective ordered bank, its mass
is the product of remaining-support conditional probabilities. For complete
random assignment it is uniform over the supported ordered distinct banks.
If R exceeds the positive support size, the definition has total mass zero. -/
noncomputable def distinctBankMass {N R : ℕ} (P : FiniteDesign (Assignment N))
    (bank : Fin R → Assignment N) : ℝ := by
  classical
  exact if Function.Injective bank then
    ∏ r, P.mass (bank r) /
      (1 - ∑ j ∈ (Finset.univ.filter (fun j : Fin R => j < r)), P.mass (bank j))
    else 0

/-- T11: the p. 217 HT conservativeness assertion at the recipe's simulated
inputs, for arbitrary finite designs and fixed real outcomes. It asserts
both an independent experiment and seed reuse (the first bank profile).
The positivity hypotheses isolate the probability-approximation issue from
T3. This proposition records the printed claim; T1 refutes it. -/
def PrintedSimulatedConservativeness : Prop :=
  ∀ (N R : ℕ) (_hN : 0 < N) (hR : 0 < R)
    (P : FiniteDesign (Assignment N))
    (_hbank : R ≤ (Finset.univ.filter (fun z => 0 < P.mass z)).card)
    (A : Adjacency N) (_hdiag : ∀ i, A i i = false)
    (y : Fin N → Exposure → ℝ) (a b : Exposure) (_hab : a ≠ b)
    (_ha : ∀ i, 0 < marginal P.mass (fun z => exposure A z) i a)
    (_hb : ∀ i, 0 < marginal P.mass (fun z => exposure A z) i b),
    let w := fun bank : Fin R → Assignment N =>
      smoothedWeight (fun r => exposure A (bank r))
    let q := fun bank : Fin R → Assignment N =>
      smoothedJoint (fun r => exposure A (bank r))
    let independentMass := fun x : (Fin R → Assignment N) × Assignment N =>
      distinctBankMass P x.1 * P.mass x.2
    let independentT := fun x => htContrast (fun z => exposure A z) y (w x.1) a b x.2
    let independentV := fun x => varianceEstimate (fun z => exposure A z) y (w x.1) (q x.1) a b x.2
    let includedT := fun bank => htContrast (fun z => exposure A z) y (w bank) a b (bank ⟨0,hR⟩)
    let includedV := fun bank => varianceEstimate (fun z => exposure A z) y (w bank) (q bank) a b (bank ⟨0,hR⟩)
    designVariance independentMass independentT ≤ expect independentMass independentV ∧
    designVariance (distinctBankMass P) includedT ≤ expect (distinctBankMass P) includedV

/-- T4(b): changing only an outcome in a zero-probability exposure leaves
all observed-data estimator expectations unchanged and shifts the population
contrast by δ/N. Hence no estimator can be unbiased under both schedules.
This is the necessity part of the pp. 212,216 support correction. -/
theorem support_necessary {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (hN : 0 < N) (P : FiniteDesign Ω) (z : Ω → Assignment N)
    (f : Ω → Fin N → D) (y : Fin N → D → ℝ) (a b : D) (hab : a ≠ b)
    (j : Fin N) (hzero : marginal P.mass f j a = 0) (δ : ℝ) (hδ : δ ≠ 0)
    (T : Assignment N → (Fin N → D) → (Fin N → ℝ) → ℝ) :
    let y' := fun i e => if i = j ∧ e = a then y i e + δ else y i e
    let TA := fun ω => T (z ω) (f ω) (fun i => y i (f ω i))
    let TB := fun ω => T (z ω) (f ω) (fun i => y' i (f ω i))
    (∀ ω, 0 < P.mass ω → ∀ i, y i (f ω i) = y' i (f ω i)) ∧
    expect P.mass TA = expect P.mass TB ∧
    tau y' a b - tau y a b = δ / N ∧
    ¬(expect P.mass TA = tau y a b ∧ expect P.mass TB = tau y' a b) := by
  dsimp only
  let y' := fun i e => if i = j ∧ e = a then y i e + δ else y i e
  have hnot (ω : Ω) (hp : 0 < P.mass ω) : f ω j ≠ a := by
    intro he
    have hle : (if f ω j = a then P.mass ω else 0) ≤ marginal P.mass f j a :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun ω' => if f ω' j = a then P.mass ω' else 0)
        (fun ω' _ => by split_ifs <;> simp [P.nonneg]) (Finset.mem_univ ω)
    rw [if_pos he, hzero] at hle
    linarith
  have hobs (ω : Ω) (hp : 0 < P.mass ω) (i : Fin N) : y i (f ω i) = y' i (f ω i) := by
    by_cases hi : i = j
    · subst i
      simp [y', hnot ω hp]
    · simp [y', hi]
  have heq : expect P.mass (fun ω => T (z ω) (f ω) (fun i => y i (f ω i))) =
      expect P.mass (fun ω => T (z ω) (f ω) (fun i => y' i (f ω i))) := by
    apply Finset.sum_congr rfl
    intro ω _
    dsimp only
    by_cases hp : P.mass ω = 0
    · simp [hp]
    · have hpos : 0 < P.mass ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hp)
      have he : (fun i => y i (f ω i)) = (fun i => y' i (f ω i)) := funext (hobs ω hpos)
      rw [he]
  have hshift : tau y' a b - tau y a b = δ / N := by
    unfold tau
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    calc
      (∑ i, ((y' i a - y' i b) - (y i a - y i b))) = ∑ i, if i = j then δ else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = j <;> simp [y', hi, Ne.symm hab] <;> ring
      _ = δ := by simp
  refine ⟨hobs, heq, hshift, ?_⟩
  intro h
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hne : δ / (N : ℝ) ≠ 0 := div_ne_zero hδ hn
  apply hne
  linarith [h.1, h.2]

/-- Conditional on the network, all 2N normal draws in the T6 correction
are independent: one independent normal pair for every vertex. The product
is over a fixed finite population, not over the assignment distribution. -/
noncomputable def normalPopulation (N : ℕ) : Measure (Fin N → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin N => normalPair)

/-- T6 corrected baseline vector, with the network's k+q+kq coefficients.
This definition describes the generator invoked on pp. 216–217. -/
def generatedBaselines {N : ℕ} (A : Adjacency N) (x : Fin N → ℝ × ℝ) : Fin N → ℝ :=
  fun i => baseline (degreeScale A i) (x i).1 (x i).2

/-- T1's complete randomization atoms: all 66 ordered-increasing treated
pairs on twelve vertices, enumerating the two-element subsets. -/
def cliquePairs : Fin 66 → Fin 12 × Fin 12 :=
  ![(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (0,9), (0,10), (0,11), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (1,10), (1,11), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10), (2,11), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (4,5), (4,6), (4,7), (4,8), (4,9), (4,10), (4,11), (5,6), (5,7), (5,8), (5,9), (5,10), (5,11), (6,7), (6,8), (6,9), (6,10), (6,11), (7,8), (7,9), (7,10), (7,11), (8,9), (8,10), (8,11), (9,10), (9,11), (10,11)]

/-- T1's binary treatment profile associated with each pair, exactly two
treated vertices, uniform mass 1/66. -/
def cliqueAssignments (r : Fin 66) : Assignment 12 := fun i =>
  decide (i = (cliquePairs r).1 ∨ i = (cliquePairs r).2)

/-- T1's three disjoint four-cliques (vertices 0–3,4–7,8–11), an undirected
zero-diagonal network with no isolates. -/
def cliqueAdj : Adjacency 12 := fun i j => decide (i ≠ j ∧ i.val / 4 = j.val / 4)

/-- The p. 211 four-condition mapping for T1's explicit network and design. -/
def cliqueF (r : Fin 66) (i : Fin 12) : Exposure :=
  let u := (cliquePairs r).1
  let v := (cliquePairs r).2
  if i = u ∨ i = v then
    (if u.val / 4 = v.val / 4 then .d11 else .d10)
  else (if i.val / 4 = u.val / 4 ∨ i.val / 4 = v.val / 4 then .d01 else .d00)


/-- T1 finite counting ingredient: exactly two treated vertices contribute
one peer indicator each when the vertices are distinct. This implements the
corrected row-times-column treated-peer count of p. 211. -/
theorem peerCount_two_treated {N : ℕ} (A : Adjacency N) (i u v : Fin N) (huv : u ≠ v) :
    peerCount A (fun j => decide (j = u ∨ j = v)) i =
      (if A i u then 1 else 0) + (if A i v then 1 else 0) := by
  have he (j : Fin N) :
      (if A i j && decide (j = u ∨ j = v) then (1 : ℕ) else 0) =
        (if j = u then (if A i u then 1 else 0) else 0) +
        (if j = v then (if A i v then 1 else 0) else 0) := by
    by_cases hju : j = u
    · subst j
      simp [huv]
    · by_cases hjv : j = v
      · subst j
        simp [huv, Ne.symm huv]
      · simp [hju, hjv]
  unfold peerCount
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

/-- The explicit treat-two enumeration never repeats a treated vertex;
this small exact check is used by the general treated-peer counting lemma. -/
theorem clique_pair_distinct (r : Fin 66) : (cliquePairs r).1 ≠ (cliquePairs r).2 := by
  fin_cases r <;> decide +kernel

/-- T1 finite exposure calculation: the efficient treatment-pair formula is
exactly the corrected four-condition mapping on three four-cliques. -/
theorem cliqueF_is_exposure : cliqueF = fun r => exposure cliqueAdj (cliqueAssignments r) := by
  funext r i
  have hc := peerCount_two_treated cliqueAdj i (cliquePairs r).1 (cliquePairs r).2 (clique_pair_distinct r)
  unfold cliqueF exposure cliqueAssignments
  rw [hc]
  unfold cliqueAdj
  by_cases hiu : i = (cliquePairs r).1
  · subst i
    by_cases hb : (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 <;>
      simp [clique_pair_distinct r, hb]
  · by_cases hiv : i = (cliquePairs r).2
    · subst i
      by_cases hb : (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 <;>
        simp [Ne.symm (clique_pair_distinct r), hb, eq_comm]
    · by_cases hb1 : i.val / 4 = (cliquePairs r).1.val / 4 <;>
      by_cases hb2 : i.val / 4 = (cliquePairs r).2.val / 4 <;>
      simp [hiu, hiv, hb1, hb2]
/-- T1's fixed outcome schedule is one at every unit and all four exposures. -/
def cliqueY : Fin 12 → Exposure → ℚ := fun _ _ => 1

/-- T1's R=65 distinct simulated assignments omit exactly atom t. Index r
skips t in the complete enumeration. Taking t uniform gives exactly the
uniform law on all retained 65-element tables. -/
def retainedAssignments (t : Fin 66) (r : Fin 65) : Assignment 12 :=
  cliqueAssignments (t.succAbove r)

/-- T1's actual exposure counts over the retained bank, not assumed true
probabilities. Used in the package smoothing definitions above. -/
def retainedF (t : Fin 66) : Fin 65 → Fin 12 → Exposure :=
  fun r => cliqueF (t.succAbove r)

/-- T1 full-design marginal counts: 3,8,27,28 in exposure order. Their
identification with enumeration is a separately stated count lemma. -/
def cliqueFullCount (a : Exposure) : ℕ :=
  match a with | .d11 => 3 | .d10 => 8 | .d01 => 27 | .d00 => 28

/-- T1 full-design joint counts for the two contrasted exposures, including
the same-exposure marginals on the diagonal. -/
def cliqueFullJoint (i j : Fin 12) (a b : Exposure) : ℕ :=
  if i = j then (if a = b then cliqueFullCount a else 0)
  else match a,b with
    | .d01,.d01 => if i.val / 4 = j.val / 4 then 17 else 9
    | .d00,.d00 => if i.val / 4 = j.val / 4 then 28 else 6
    | .d01,.d00 | .d00,.d01 => if i.val / 4 = j.val / 4 then 0 else 15
    | _,_ => jointCount cliqueF i j a b

/-- T1's retained marginal counts are full counts minus the omitted event.
The package adds one and divides by R+1=66. -/
def cliqueWeights (t : Fin 66) (i : Fin 12) (a : Exposure) : ℚ :=
  ((cliqueFullCount a - if cliqueF t i = a then 1 else 0 : ℕ) + 1 : ℕ) / (66 : ℚ)

/-- T1's retained joint counts are full counts minus the omitted joint event.
Same-exposure entries add the diagonal identity and divide by 66; cross
entries divide by R=65, as in `smoothedJoint`. -/
def cliqueJoints (t : Fin 66) (i j : Fin 12) (a b : Exposure) : ℚ :=
  let c := cliqueFullJoint i j a b - if cliqueF t i = a ∧ cliqueF t j = b then 1 else 0
  if a = b then ((c + if i = j then 1 else 0 : ℕ) : ℚ) / 66 else (c : ℚ) / 65


/-- Deleting one randomization atom subtracts its event indicator from the
finite count. This exact counting identity avoids treating an approximate
probability as exact in the twelve-unit counterexample. -/
theorem count_delete_atom {n : ℕ} (t : Fin (n + 1)) (test : Fin (n + 1) → Prop)
    [DecidablePred test] :
    (Finset.univ.filter (fun r : Fin n => test (t.succAbove r))).card =
      (Finset.univ.filter test).card - if test t then 1 else 0 := by
  have h : (Finset.univ.filter test).card =
      (if test t then 1 else 0) +
        (Finset.univ.filter (fun r : Fin n => test (t.succAbove r))).card := by
    simpa only [Finset.sum_boole, Nat.cast_id] using
      Fin.sum_univ_succAbove (fun r => if test r then (1 : ℕ) else 0) t
  omega


/-- T1 point estimator T(S,z) with all outcomes one and the package's
returned positive marginal inputs, for omitted assignment t. -/
def cliqueT (t z : Fin 66) : ℚ :=
  htContrast cliqueF cliqueY (cliqueWeights t) .d01 .d00 z

/-- T1 variance functional at the package's returned marginal and joint
inputs from the same bank. This definition reuses `varianceEstimate`. -/
def cliqueV (t z : Fin 66) : ℚ :=
  varianceEstimate cliqueF cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00 z

/-- The two T1 joint laws: independent actual assignment has 4356 equally
likely (t,z) pairs; an actual assignment in the bank has 4290 equally likely
pairs with z≠t, zero mass on z=t. -/
def cliqueJointMass (included : Bool) (x : Fin 66 × Fin 66) : ℚ :=
  if included then (if x.1 = x.2 then 0 else 1/4290) else 1/4356


/-- Observation law for T1 conditional on the omitted profile t: uniform on
all 66 profiles if independent, or on the 65 retained profiles if included. -/
def cliqueObservationMass (t : Fin 66) (included : Bool) (z : Fin 66) : ℚ :=
  if included then (if z = t then 0 else 1/65) else 1/66

/-- T1 finite probability law: an independent observation is uniform on
all 66 complete-randomization atoms, for every omitted profile. -/
theorem clique_observation_independent_mass (t : Fin 66) :
    cliqueObservationMass t false = (fun _ : Fin 66 => (1/66 : ℚ)) := by
  funext z
  rfl

/-- Conditional observation marginals in T1, separate from the package's
smoothed estimator inputs. The included law uses unsmoothed counts/65. -/
def cliqueObservationMarginal (t : Fin 66) (included : Bool) (i : Fin 12) (a : Exposure) : ℚ :=
  if included then ((cliqueFullCount a - if cliqueF t i = a then 1 else 0 : ℕ) : ℚ) / 65
  else (cliqueFullCount a : ℚ) / 66

/-- Conditional observation joints in T1. These are actual probabilities,
including unsmoothed same-exposure diagonals, not the estimated inputs. -/
def cliqueObservationJoint (t : Fin 66) (included : Bool) (i j : Fin 12) (a b : Exposure) : ℚ :=
  if included then ((cliqueFullJoint i j a b - if cliqueF t i = a ∧ cliqueF t j = b then 1 else 0 : ℕ) : ℚ) / 65
  else (cliqueFullJoint i j a b : ℚ) / 66


/-- T1 conditional first moment, computed from the true observation
marginals and the smoothed marginal inputs. -/
def cliqueConditionalMean (t : Fin 66) (included : Bool) : ℚ :=
  ((∑ i, cliqueObservationMarginal t included i .d01 / cliqueWeights t i .d01) -
    (∑ i, cliqueObservationMarginal t included i .d00 / cliqueWeights t i .d00)) / 12

/-- T1 conditional second moment, computed from the true observation joints
and smoothed marginal inputs. -/
def cliqueConditionalSecond (t : Fin 66) (included : Bool) : ℚ :=
  (∑ i, ∑ j,
    (cliqueObservationJoint t included i j .d01 .d01 / (cliqueWeights t i .d01 * cliqueWeights t j .d01) +
     cliqueObservationJoint t included i j .d00 .d00 / (cliqueWeights t i .d00 * cliqueWeights t j .d00) -
     cliqueObservationJoint t included i j .d01 .d00 / (cliqueWeights t i .d01 * cliqueWeights t j .d00) -
     cliqueObservationJoint t included i j .d00 .d01 / (cliqueWeights t i .d00 * cliqueWeights t j .d01))) / 144

/-- T1 conditional expected variance estimate, computed from true observation
marginals/joints and the different, smoothed package inputs. -/
def cliqueConditionalV (t : Fin 66) (included : Bool) : ℚ :=
  expectedVariance (cliqueObservationMarginal t included) (cliqueObservationJoint t included)
    cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00


/-- T1 joint expectation decomposes into the uniform omitted-profile law
and the actual conditional observation law. This retains the bank's random
mean, which is essential for unconditional variance. -/
theorem clique_joint_expectation (included : Bool) (u : Fin 66 → Fin 66 → ℚ) :
    expect (cliqueJointMass included) (fun x => u x.1 x.2) =
      expect (fun _ : Fin 66 => (1/66 : ℚ))
        (fun t => expect (cliqueObservationMass t included) (u t)) := by
  have hm (t z : Fin 66) : cliqueJointMass included (t,z) =
      (1/66 : ℚ) * cliqueObservationMass t included z := by
    cases included
    · norm_num [cliqueJointMass, cliqueObservationMass]
    · by_cases h : t = z
      · subst z
        norm_num [cliqueJointMass, cliqueObservationMass]
      · norm_num [cliqueJointMass, cliqueObservationMass, h, Ne.symm h]
  simp only [expect, Fintype.sum_prod_type]
  simp_rw [hm, mul_assoc, Finset.mul_sum]


/-- T8(iii), complete bias formula: when the design is uniform on the
exhaustive table, smoothed inputs produce the average of yᵢ(a) times
(cᵢ(a)−R)/(R(cᵢ(a)+1)), rather than exact unbiasedness (pp. 212,216). -/
theorem exhaustive_smoothing_bias {R N : ℕ} {D : Type*} [DecidableEq D]
    (hR : 0 < R) (f : Fin R → Fin N → D) (y : Fin N → D → ℝ) (a : D) :
    expect (fun _ : Fin R => (1 / R : ℝ)) (htMean f y (smoothedWeight f) a) -
      (∑ i, y i a) / N =
    (∑ i, y i a * (((exposureCount f i a : ℝ) - R) /
      ((R : ℝ) * ((exposureCount f i a : ℝ) + 1)))) / N := by
  rw [htMean_expectation, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [(exhaustive_probabilities hR f i i a a).1]
  unfold smoothedWeight
  have hm := (smoothing_bias_multiplier R (exposureCount f i a) hR).1
  calc
    y i a * (exposureCount f i a / (R : ℝ)) /
        (((exposureCount f i a : ℝ) + 1) / ((R : ℝ) + 1)) - y i a =
      y i a * ((exposureCount f i a / (R : ℝ)) /
        (((exposureCount f i a : ℝ) + 1) / ((R : ℝ) + 1)) - 1) := by ring
    _ = _ := by rw [hm]

/-- T10(iii), both meanings of expected within-community proportion: for
any law of returned graphs satisfying no isolates and no cross-community
edges, E[W/M]=1 and E[W]/E[M]=1. The source-code link is an external premise. -/
theorem returned_graph_expectations {Ω C : Type*} {N : ℕ} [Fintype Ω]
    (hN : 0 < N) (P : FiniteDesign Ω) (G : Ω → SimpleGraph (Fin N))
    [∀ ω, DecidableRel (G ω).Adj] (c : Ω → Fin N → C)
    (hdegree : ∀ ω i, 0 < (G ω).degree i)
    (hwithin : ∀ ω i j, (G ω).Adj i j → c ω i = c ω j) :
    expect P.mass (fun ω => ((withinEdges (G ω) (c ω)).card : ℝ) / (G ω).edgeFinset.card) = 1 ∧
    expect P.mass (fun ω => ((withinEdges (G ω) (c ω)).card : ℝ)) /
      expect P.mass (fun ω => ((G ω).edgeFinset.card : ℝ)) = 1 := by
  have hs := fun ω => within_community_share hN (G ω) (c ω) (hdegree ω) (hwithin ω)
  have hm : 1 ≤ expect P.mass (fun ω => ((G ω).edgeFinset.card : ℝ)) := by
    calc
      1 = ∑ ω, P.mass ω * 1 := by simpa using P.total.symm
      _ ≤ _ := Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left
        (by exact_mod_cast (hs ω).2.1) (P.nonneg ω))
  constructor
  · have he : (fun ω => ((withinEdges (G ω) (c ω)).card : ℝ) / (G ω).edgeFinset.card) =
        (fun _ => (1 : ℝ)) := funext (fun ω => (hs ω).2.2.2.1)
    rw [he]
    simpa [expect] using P.total
  · have he : (fun ω => ((withinEdges (G ω) (c ω)).card : ℝ)) =
        (fun ω => ((G ω).edgeFinset.card : ℝ)) :=
      funext (fun ω => congrArg (fun n : ℕ => (n : ℝ)) (hs ω).2.2.1)
    rw [he]
    exact div_self (by linarith)


/-- T9(ii): the corrected row-times-column scalar counts precisely the
vertices whose adjacency entry and treatment entry are both one (p. 211). -/
theorem peerCount_is_count {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N) :
    peerCount A z i = (Finset.univ.filter (fun j => A i j = true ∧ z j = true)).card := by
  unfold peerCount
  simp [Bool.and_eq_true, Finset.sum_boole]

/-- T6(iii), numerical instance: the three triangle baselines in T5 yield
mean 109/24 and effects 109/24,109/48,109/96 at the p. 212 estimand. -/
theorem triangle_realized_effects :
    let B : Fin 3 → ℝ := ![-5/8,9,21/4]
    tau (dilatedOutcomes B) .d11 .d00 = 109/24 ∧
    tau (dilatedOutcomes B) .d10 .d00 = 109/48 ∧
    tau (dilatedOutcomes B) .d01 .d00 = 109/96 := by
  norm_num [tau, dilatedOutcomes, Fin.sum_univ_succ]

/-- True randomization covariance of two supported HT totals, written as
an ordered-pair sum. This is the finite kernel of the p. 217 repair. -/
def trueTotalCovariance {N : ℕ} {D : Type*} [DecidableEq D]
    (m : Fin N → D → ℝ) (J : Fin N → Fin N → D → D → ℝ)
    (y : Fin N → D → ℝ) (a b : D) : ℝ :=
  ∑ i, ∑ j, (J i j a b * (y i a * y j b / (m i a * m j b)) - y i a * y j b)

/-- Exact joint probabilities are nonnegative for a finite randomization law. -/
theorem joint_nonneg {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (P : FiniteDesign Ω) (f : Ω → Fin N → D) (i j : Fin N) (a b : D) :
    0 ≤ joint P.mass f i j a b := by
  unfold joint
  apply Finset.sum_nonneg
  intro ω _
  split_ifs <;> simp [P.nonneg]

/-- Same-unit, same-exposure joint probability is the marginal. -/
theorem joint_diagonal {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (p : Ω → ℝ) (f : Ω → Fin N → D) (i : Fin N) (a : D) :
    joint p f i i a a = marginal p f i a := by simp [joint, marginal]

/-- Swapping the ordered units and their exposures preserves a joint probability. -/
theorem joint_swap {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (p : Ω → ℝ) (f : Ω → Fin N → D) (i j : Fin N) (a b : D) :
    joint p f i j a b = joint p f j i b a := by simp [joint, and_comm]

/-- T2 finite same-exposure identity: exact inputs reproduce the true total
variance plus the within-exposure structural-zero squares, for any outcomes. -/
theorem exact_totalVariance {N : ℕ} {D : Type*} [DecidableEq D]
    (m : Fin N → D → ℝ) (J : Fin N → Fin N → D → D → ℝ)
    (y : Fin N → D → ℝ) (a : D) (hm : ∀ i, 0 < m i a)
    (hJ : ∀ i j, 0 ≤ J i j a a) (hdiag : ∀ i, J i i a a = m i a) :
    expectedTotalVariance m J y m J a = trueTotalCovariance m J y a a +
      ∑ i, ∑ j, if i ≠ j ∧ J i j a a = 0 then (y i a + y j a) ^ 2 / 2 else 0 := by
  unfold expectedTotalVariance trueTotalCovariance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hp : 0 < J i j a a
  · simp [hp, ne_of_gt hp]
    field_simp [ne_of_gt (hm i), ne_of_gt (hm j), ne_of_gt hp]
    <;> ring
  · have hz : J i j a a = 0 := le_antisymm (le_of_not_gt hp) (hJ i j)
    have hij : i ≠ j := by
      intro he
      subst j
      rw [hdiag] at hz
      linarith [hm i]
    simp [hp, hz, hij]
    field_simp [ne_of_gt (hm i), ne_of_gt (hm j)]
    <;> ring

/-- T2 finite cross-exposure identity: the adjusted covariance has exact
expectation equal to the true covariance minus half the zero-pair squares.
The ordered cross diagonal is included. -/
theorem exact_totalCovariance {N : ℕ} {D : Type*} [DecidableEq D]
    (m : Fin N → D → ℝ) (J : Fin N → Fin N → D → D → ℝ)
    (y : Fin N → D → ℝ) (a b : D)
    (ha : ∀ i, 0 < m i a) (hb : ∀ i, 0 < m i b)
    (hJ : ∀ i j, 0 ≤ J i j a b) :
    expectedTotalCovariance m J y m J a b = trueTotalCovariance m J y a b -
      (∑ i, ∑ j, if J i j a b = 0 then (y i a - y j b) ^ 2 else 0) / 2 := by
  unfold expectedTotalCovariance trueTotalCovariance
  simp_rw [Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hp : 0 < J i j a b
  · simp [hp, ne_of_gt hp]
    field_simp [ne_of_gt (ha i), ne_of_gt (hb j), ne_of_gt hp]
    <;> ring
  · have hz : J i j a b = 0 := le_antisymm (le_of_not_gt hp) (hJ i j)
    simp [hp, hz]
    field_simp [ne_of_gt (ha i), ne_of_gt (hb j)]
    <;> ring

/-- T2 finite variance identity: with supported exact weights, the HT contrast
variance is the sum of two total variances minus twice the total covariance,
divided by N². No unit-level independence or joint positivity is assumed. -/
theorem htVariance_pair_expansion {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (hN : 0 < N) (P : FiniteDesign Ω) (f : Ω → Fin N → D)
    (y : Fin N → D → ℝ) (a b : D) (hab : a ≠ b)
    (ha : ∀ i, 0 < marginal P.mass f i a) (hb : ∀ i, 0 < marginal P.mass f i b) :
    designVariance P.mass (htContrast f y (marginal P.mass f) a b) =
      (trueTotalCovariance (marginal P.mass f) (joint P.mass f) y a a +
       trueTotalCovariance (marginal P.mass f) (joint P.mass f) y b b -
       2 * trueTotalCovariance (marginal P.mass f) (joint P.mass f) y a b) / (N : ℝ) ^ 2 := by
  let m := marginal P.mass f
  let J := joint P.mass f
  have hcross : (∑ i, ∑ j, J i j b a * (y i b * y j a / (m i b * m j a))) =
      (∑ i, ∑ j, J i j a b * (y i a * y j b / (m i a * m j b))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show J j i b a = J i j a b from joint_swap P.mass f j i b a]
    ring
  have hcrossy : (∑ i, ∑ j, y i b * y j a) = (∑ i, ∑ j, y i a * y j b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsquare : (∑ i, (y i a - y i b)) ^ 2 =
      ∑ i, ∑ j, (y i a * y j a + y i b * y j b - y i a * y j b - y i b * y j a) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold designVariance
  rw [htContrast_second_moment, (ht_unbiased hN P f y a b hab ha hb).2.2.2]
  unfold tau trueTotalCovariance
  rw [div_pow, hsquare]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  change ((∑ i, ∑ j, J i j a a * (y i a * y j a / (m i a * m j a))) +
    (∑ i, ∑ j, J i j b b * (y i b * y j b / (m i b * m j b))) -
    (∑ i, ∑ j, J i j a b * (y i a * y j b / (m i a * m j b))) -
    (∑ i, ∑ j, J i j b a * (y i b * y j a / (m i b * m j a)))) / (N : ℝ)^2 -
    ((∑ i, ∑ j, y i a * y j a) + (∑ i, ∑ j, y i b * y j b) -
      (∑ i, ∑ j, y i a * y j b) - (∑ i, ∑ j, y i b * y j a)) / (N : ℝ)^2 = _
  rw [hcross, hcrossy]
  ring

/-- T2(a): with any finite design, correctly specified exposures, fixed real
outcomes and positive marginals for the two distinct exposures, the expectation
of the exact-input HT variance estimate minus the design variance equals
the structural-zero squared-outcome surplus. Repair of p. 217. -/
theorem exact_variance_surplus {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (hN : 0 < N) (P : FiniteDesign Ω) (f : Ω → Fin N → D)
    (y : Fin N → D → ℝ) (a b : D) (hab : a ≠ b)
    (ha : ∀ i, 0 < marginal P.mass f i a) (hb : ∀ i, 0 < marginal P.mass f i b) :
    expect P.mass (varianceEstimate f y (marginal P.mass f) (joint P.mass f) a b) -
      designVariance P.mass (htContrast f y (marginal P.mass f) a b) =
      zeroSurplus y (joint P.mass f) a b := by
  rw [varianceEstimate_expectation, htVariance_pair_expansion hN P f y a b hab ha hb]
  unfold expectedVariance
  rw [exact_totalVariance _ _ y a ha (fun i j => joint_nonneg P f i j a a)
        (fun i => joint_diagonal P.mass f i a),
      exact_totalVariance _ _ y b hb (fun i j => joint_nonneg P f i j b b)
        (fun i => joint_diagonal P.mass f i b),
      exact_totalCovariance _ _ y a b ha hb (fun i j => joint_nonneg P f i j a b)]
  unfold zeroSurplus
  ring

/-- T2 finite algebra: the within-exposure zero adjustment exceeds the missing
variance term by (x+y)²/2; the cross adjustment after −2 gives (x−y)².
These are the two terms in the corrected p. 217 variance proof. -/
theorem zero_pair_algebra (x y : ℝ) :
    (x ^ 2 + y ^ 2) / 2 - (-x * y) = (x + y) ^ 2 / 2 ∧
    -2 * (-(x ^ 2 + y ^ 2) / 2 - (-x * y)) = (x - y) ^ 2 := by
  constructor <;> ring

/-- T2 finite inequality: every structural-zero surplus is nonnegative,
including the cross diagonal contribution. Repair of p. 217. -/
theorem zeroSurplus_nonneg {N : ℕ} {D : Type*} [DecidableEq D]
    (y : Fin N → D → ℝ) (q : Fin N → Fin N → D → D → ℝ) (a b : D) :
    0 ≤ zeroSurplus y q a b := by
  unfold zeroSurplus
  positivity

/-- T2(b): exact design marginals and joints, with positive marginal support,
make the HT contrast variance construction conservative in expectation.
There is no claim here for the Hajek linearization. Repair of p. 217. -/
theorem exact_variance_conservative {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (hN : 0 < N) (P : FiniteDesign Ω) (f : Ω → Fin N → D)
    (y : Fin N → D → ℝ) (a b : D) (hab : a ≠ b)
    (ha : ∀ i, 0 < marginal P.mass f i a) (hb : ∀ i, 0 < marginal P.mass f i b) :
    designVariance P.mass (htContrast f y (marginal P.mass f) a b) ≤
      expect P.mass (varianceEstimate f y (marginal P.mass f) (joint P.mass f) a b) := by
  have h := exact_variance_surplus hN P f y a b hab ha hb
  have hpos := zeroSurplus_nonneg y (joint P.mass f) a b
  linarith


/-- T5(iv)/T6(ii), the finite moment ingredient |G|²=G²: the absolute
standard normal has second moment one. This uses Mathlib's Gaussian variance
and mean, without assuming a half-normal moment axiom. -/
theorem halfNormal_second_moment : (∫ g : ℝ, |g| ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa only [integral_id_gaussianReal, sub_zero, sq_abs, NNReal.coe_one] using h


/-- T6 analytic lemma: the first Gaussian-density moment on the positive
half-line is one before the density normalization. -/
theorem gaussian_halfline_moment :
    (∫ x : ℝ in Set.Ioi 0, x * Real.exp (-(1/2 : ℝ) * x ^ 2)) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1/2 : ℂ)) (by norm_num)
  have he (x : ℝ) : ((x * Real.exp (-(1/2 : ℝ) * x^2) : ℝ) : ℂ) =
      (x : ℂ) * Complex.exp (-(1/2 : ℂ) * (x : ℂ)^2) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_pow,
      Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
  have hc : (∫ x : ℝ in Set.Ioi 0, ((x * Real.exp (-(1/2 : ℝ) * x^2) : ℝ) : ℂ)) = (1 : ℂ) := by
    calc
      _ = ∫ x : ℝ in Set.Ioi 0, (x : ℂ) * Complex.exp (-(1/2 : ℂ) * (x : ℂ)^2) := by
        apply integral_congr_ae
        exact ae_of_all _ he
      _ = (2 * (1/2 : ℂ))⁻¹ := h
      _ = 1 := by norm_num
  have hi := integral_complex_ofReal (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (f := fun x : ℝ => x * Real.exp (-(1/2 : ℝ) * x^2))
  exact Complex.ofReal_injective (hi.symm.trans hc)


/-- T6 analytic lemma: the mean of |G| for a standard Gaussian is √(2/π).
This is proved from the density integral, rather than introduced as an axiom. -/
theorem halfNormal_mean : (∫ g : ℝ, |g| ∂gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
  have hInt : Integrable (fun g : ℝ => g) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x * x⁺ =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (Set.Ioi 0).indicator (fun x : ℝ => x * Real.exp (-(1/2 : ℝ) * x^2)) x := by
    by_cases hx : 0 < x
    · simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr hx), PosPart.posPart, max_eq_left hx.le,
        gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
      have he : -(x^2) / 2 = -(1/2 : ℝ) * x^2 := by ring
      rw [he]
      ring
    · simp only [Set.indicator_of_notMem (show x ∉ Set.Ioi (0 : ℝ) from hx), PosPart.posPart,
        max_eq_right (le_of_not_gt hx), mul_zero]
  have hPos : (∫ g : ℝ, g⁺ ∂gaussianReal 0 1) = (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1)
      (f := fun g : ℝ => g⁺) (by norm_num : (1 : NNReal) ≠ 0)]
    simp only [smul_eq_mul, hpdf]
    rw [integral_const_mul, integral_indicator measurableSet_Ioi, gaussian_halfline_moment,
      mul_one]
  rw [integral_abs_eq_two_mul_integral_posPart_sub_integral hInt, hPos,
    integral_id_gaussianReal, sub_zero]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hq : 0 ≤ 2 / Real.pi := by positivity
  have hr := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
  have hrq := Real.sq_sqrt hq
  have hnonneg := Real.sqrt_nonneg (2 / Real.pi)
  have he : (2 * (Real.sqrt (2 * Real.pi))⁻¹) ^ 2 = 2 / Real.pi := by
    rw [mul_pow, inv_pow, hr]
    field_simp
    <;> ring
  nlinarith [inv_pos.mpr hs]

/-- T6 analytic lemma: the variance of the absolute standard Gaussian is
1−2/π; its second moment equals the standard Gaussian's second moment. -/
theorem halfNormal_variance :
    ProbabilityTheory.variance (fun g : ℝ => |g|) (gaussianReal 0 1) = 1 - 2 / Real.pi := by
  have hG := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).abs
  change MemLp (fun g : ℝ => |g|) 2 (gaussianReal 0 1) at hG
  rw [variance_eq_sub hG]
  change (∫ g : ℝ, |g|^2 ∂gaussianReal 0 1) - (∫ g : ℝ, |g| ∂gaussianReal 0 1)^2 = _
  rw [halfNormal_second_moment, halfNormal_mean, Real.sq_sqrt (by positivity)]

/-- T6(ii): the degree-scaled absolute normal plus independent N(1,1/16)
noise has mean a√(2/π)+1 and variance a²(1−2/π)+1/16. Correction to p. 216. -/
theorem corrected_baseline_moments (a : ℝ) (ha : 0 ≤ a) :
    (∫ x, baseline a x.1 x.2 ∂normalPair) = a * Real.sqrt (2 / Real.pi) + 1 ∧
    ProbabilityTheory.variance (fun x : ℝ × ℝ => baseline a x.1 x.2) normalPair =
      a ^ 2 * (1 - 2 / Real.pi) + 1/16 := by
  have hG : MemLp (fun g : ℝ => a * |g|) 2 (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).abs.const_mul a
  have hE : MemLp (fun e : ℝ => e) 2 (gaussianReal 1 (1/16)) :=
    memLp_id_gaussianReal 2
  constructor
  · unfold normalPair baseline
    rw [integral_add ((hG.integrable (by norm_num)).comp_fst _)
      ((hE.integrable (by norm_num)).comp_snd _),
      integral_fun_fst (μ := gaussianReal 0 1) (ν := gaussianReal 1 (1/16)) (fun g : ℝ => a * |g|),
      integral_fun_snd (μ := gaussianReal 0 1) (ν := gaussianReal 1 (1/16)) (fun e : ℝ => e)]
    simp only [probReal_univ, one_smul, integral_const_mul,
      halfNormal_mean, integral_id_gaussianReal]
  · unfold normalPair baseline
    rw [variance_add_prod hG hE, variance_const_mul, halfNormal_variance]
    have he := variance_fun_id_gaussianReal (μ := 1) (v := (1/16 : NNReal))
    change variance (fun e : ℝ => e) (gaussianReal 1 (1/16)) = (1/16 : ℝ) at he
    rw [he]

/-- T6 finite-population integrability: every degree-scaled baseline has a
finite second moment under its independent pair of Gaussian draws. -/
theorem baseline_memLp (a : ℝ) :
    MemLp (fun x : ℝ × ℝ => baseline a x.1 x.2) 2 normalPair := by
  unfold normalPair baseline
  exact (((memLp_id_gaussianReal (μ := 0) (v := 1) 2).abs.const_mul a).comp_fst _).add
    ((memLp_id_gaussianReal (μ := 1) (v := (1/16 : NNReal)) 2).comp_snd _)

/-- T6(iv), general conditional mean: for every fixed zero-diagonal
network on a nonempty finite population, including networks with isolates,
the expected direct-plus-indirect effect equals
1 + √(2/π) * (average degree coefficient). Correction to the p. 216 generator. -/
theorem generated_effect_mean {N : ℕ} (hN : 0 < N) (A : Adjacency N)
    (hdiag : ∀ i, A i i = false) :
    (∫ x, tau (dilatedOutcomes (generatedBaselines A x)) .d11 .d00 ∂normalPopulation N) =
      1 + Real.sqrt (2 / Real.pi) * ((∑ i, (degreeScale A i : ℝ)) / N) := by
  letI : IsProbabilityMeasure normalPair := by unfold normalPair; infer_instance
  have hInt (i : Fin N) : Integrable (fun x => generatedBaselines A x i) (normalPopulation N) := by
    exact integrable_comp_eval (μ := fun _ : Fin N => normalPair) (i := i)
      ((baseline_memLp (degreeScale A i)).integrable (by norm_num))
  have hc (i : Fin N) : (∫ x, generatedBaselines A x i ∂normalPopulation N) =
      (degreeScale A i : ℝ) * Real.sqrt (2 / Real.pi) + 1 := by
    unfold normalPopulation generatedBaselines
    rw [integral_comp_eval (μ := fun _ : Fin N => normalPair) (i := i)
      (f := fun x : ℝ × ℝ => baseline (degreeScale A i) x.1 x.2)
      (baseline_memLp (degreeScale A i)).aestronglyMeasurable]
    exact (corrected_baseline_moments (degreeScale A i) (by positivity)).1
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hmean : (∫ x, tau (dilatedOutcomes (generatedBaselines A x)) .d11 .d00 ∂normalPopulation N) =
      1 + Real.sqrt (2 / Real.pi) * ((∑ i, (degreeScale A i : ℝ)) / N) := by
    have heff : (fun x => tau (dilatedOutcomes (generatedBaselines A x)) .d11 .d00) =
        (fun x => (∑ i, generatedBaselines A x i) / N) := by
      funext x
      exact (dilated_effects (generatedBaselines A x)).1
    rw [heff, integral_div, integral_finsetSum Finset.univ (fun i _ => hInt i)]
    simp_rw [hc]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
    <;> ring
  exact hmean

/-- T6(iv): the expected direct-plus-indirect population effect is
1 plus √(2/π) times the average degree coefficient. On a nonisolated graph
it is at least 1+√(2/π), whereas half-normal baselines would give √(2/π)<1.
Corrected scale of the p. 216 simulation inputs; not a design expectation. -/
theorem generated_effect_scale {N : ℕ} (hN : 0 < N) (A : Adjacency N)
    (hdiag : ∀ i, A i i = false) (hiso : ∀ i, 1 ≤ degree A i) :
    (∫ x, tau (dilatedOutcomes (generatedBaselines A x)) .d11 .d00 ∂normalPopulation N) =
      1 + Real.sqrt (2 / Real.pi) * ((∑ i, (degreeScale A i : ℝ)) / N) ∧
    1 + Real.sqrt (2 / Real.pi) ≤
      (∫ x, tau (dilatedOutcomes (generatedBaselines A x)) .d11 .d00 ∂normalPopulation N) ∧
    Real.sqrt (2 / Real.pi) < 1 := by
  have hmean := generated_effect_mean hN A hdiag
  have hcoeff (i : Fin N) : 1 ≤ (degreeScale A i : ℝ) := by
    have hk := hiso i
    exact_mod_cast (show 1 ≤ degreeScale A i by unfold degreeScale; omega)
  have hsum : (N : ℝ) ≤ ∑ i, (degreeScale A i : ℝ) := by
    calc (N : ℝ) = ∑ _i : Fin N, (1 : ℝ) := by simp
         _ ≤ ∑ i, (degreeScale A i : ℝ) := Finset.sum_le_sum (fun i _ => hcoeff i)
  have hnpos : (0 : ℝ) < N := by exact_mod_cast hN
  have havg : 1 ≤ (∑ i, (degreeScale A i : ℝ)) / N := by
    apply (le_div_iff₀ hnpos).2
    simpa using hsum
  refine ⟨hmean, ?_, ?_⟩
  · rw [hmean]
    nlinarith [Real.sqrt_nonneg (2 / Real.pi)]
  · have hq : 2 / Real.pi < 1 := (div_lt_one Real.pi_pos).2 (by linarith [Real.pi_gt_three])
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 / Real.pi), Real.sqrt_nonneg (2 / Real.pi)]

/-- Correct specification makes the selected HT potential outcome equal to
its observed outcome. This identifies the finite definitions with the
I(Dᵢ=d)Yᵢ/wᵢ(d) terms invoked on pp. 212,216. -/
theorem htTerm_observed {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a : D) (ω : Ω) (i : Fin N) :
    htTerm f y w a ω i = if f ω i = a then observed f y ω i / w i a else 0 := by
  by_cases h : f ω i = a <;> simp [htTerm, observed, h]

/-- T7's three exposure contrasts and their exact biases with exhaustive
smoothed inputs: (3/4,3/32,39/128), biases (−1/4,−13/32,7/128), at every
realized assignment. No Monte Carlo argument is used. -/
theorem cycle8_contrast_biases :
    let f := fun r => exposure cycle8Adj (cycle8Assignments r)
    let q := fun i a => (smoothedWeight f i a : ℚ)
    (∀ r a, (Finset.univ.filter (fun i => f r i = a)).card =
      match a with | .d11 => 2 | .d10 => 1 | .d01 => 3 | .d00 => 2) ∧
    (∀ r, htContrast f cycle8Y q .d11 .d00 r = 3/4 ∧
      htContrast f cycle8Y q .d10 .d00 r = 3/32 ∧
      htContrast f cycle8Y q .d01 .d00 r = 39/128 ∧
      htContrast f cycle8Y q .d11 .d00 r - tau cycle8Y .d11 .d00 = -1/4 ∧
      htContrast f cycle8Y q .d10 .d00 r - tau cycle8Y .d10 .d00 = -13/32 ∧
      htContrast f cycle8Y q .d01 .d00 r - tau cycle8Y .d01 .d00 = 7/128) := by
  decide +kernel

/-- T5(i): the triangle's two-walk matrix A² is the stated matrix, and the
baseline witness gives every entry of the four potential-outcome vectors.
This is an exact arithmetic counterexample to the nonnegative-baseline prose. -/
theorem triangle_outcome_vectors :
    (∀ i j : Fin 3, (∑ k : Fin 3, if (i ≠ k ∧ k ≠ j) then (1 : ℕ) else 0) =
      if i = j then 2 else 1) ∧
    (let B : Fin 3 → ℝ := ![-5/8,9,21/4]
     (∀ i, dilatedOutcomes B i .d11 = ![-5/4,18,21/2] i) ∧
     (∀ i, dilatedOutcomes B i .d10 = ![-15/16,27/2,63/8] i) ∧
     (∀ i, dilatedOutcomes B i .d01 = ![-25/32,45/4,105/16] i) ∧
     (∀ i, dilatedOutcomes B i .d00 = ![-5/8,9,21/4] i)) := by
  constructor
  · decide +kernel
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i <;> fin_cases i <;> norm_num [dilatedOutcomes]

/-- T5(ii): the explicit negative-baseline rectangle is nonempty and has
positive probability under the independent Gaussian pair; every point in
it has baseline below −1/4. This is a positive-probability witness, not
just a single draw of measure zero. -/
theorem negative_baseline_rectangle (a : ℝ) (ha : 0 ≤ a) :
    0 < normalPair {x : ℝ × ℝ | |x.1| < 1 / (4 * (a + 1)) ∧ -1 < x.2 ∧ x.2 < -1/2} ∧
    (∀ x : ℝ × ℝ, |x.1| < 1 / (4 * (a + 1)) ∧ -1 < x.2 ∧ x.2 < -1/2 →
      baseline a x.1 x.2 < -1/4) := by
  letI : Measure.IsOpenPosMeasure (gaussianReal (0 : ℝ) 1) :=
    (gaussianReal_absolutelyContinuous' (μ := 0) (v := 1) (by norm_num)).isOpenPosMeasure
  letI : Measure.IsOpenPosMeasure (gaussianReal (1 : ℝ) (1/16)) :=
    (gaussianReal_absolutelyContinuous' (μ := 1) (v := 1/16) (by norm_num)).isOpenPosMeasure
  haveI : Measure.IsOpenPosMeasure normalPair := by unfold normalPair; infer_instance
  have h1 := isOpen_lt (f := fun x : ℝ × ℝ => |x.1|)
    (g := fun _ => 1 / (4 * (a + 1))) (by fun_prop) continuous_const
  have h2 := isOpen_lt (f := fun _ : ℝ × ℝ => (-1 : ℝ)) (g := fun x => x.2)
    continuous_const continuous_snd
  have h3 := isOpen_lt (f := fun x : ℝ × ℝ => x.2) (g := fun _ => (-1/2 : ℝ))
    continuous_snd continuous_const
  have ho : IsOpen {x : ℝ × ℝ | |x.1| < 1 / (4 * (a + 1)) ∧ -1 < x.2 ∧ x.2 < -1/2} :=
    h1.inter (h2.inter h3)
  constructor
  · apply ho.measure_pos normalPair
    refine ⟨(0,-3/4), ?_⟩
    change |(0 : ℝ)| < 1 / (4 * (a + 1)) ∧ (-1 : ℝ) < -3/4 ∧ (-3/4 : ℝ) < -1/2
    refine ⟨?_, by norm_num, by norm_num⟩
    simp only [abs_zero]
    positivity
  · intro x hx
    exact negative_baseline_event a x.1 x.2 ha hx.1 hx.2.1 hx.2.2

/-- T10(i): in a finite random-graph law, zero crossing-edge marginals
force every positive-probability graph to have no crossing edge. This
formalizes the probability-one consequence of the identity block matrix;
independence of edges is not needed for this consequence. -/
theorem no_cross_edges_on_support {Ω C : Type*} {N : ℕ} [Fintype Ω] [DecidableEq C]
    (P : FiniteDesign Ω) (G : Ω → SimpleGraph (Fin N)) [∀ ω, DecidableRel (G ω).Adj]
    (c : Ω → Fin N → C)
    (hzero : ∀ i j, (∑ ω, if (G ω).Adj i j ∧ c ω i ≠ c ω j then P.mass ω else 0) = 0) :
    ∀ ω, 0 < P.mass ω → ∀ i j, (G ω).Adj i j → c ω i = c ω j := by
  classical
  intro ω hp i j he
  by_contra hc
  have hle : (if (G ω).Adj i j ∧ c ω i ≠ c ω j then P.mass ω else 0) ≤
      ∑ ω', if (G ω').Adj i j ∧ c ω' i ≠ c ω' j then P.mass ω' else 0 :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun ω' => if (G ω').Adj i j ∧ c ω' i ≠ c ω' j then P.mass ω' else 0)
      (fun ω' _ => by split_ifs <;> simp [P.nonneg]) (Finset.mem_univ ω)
  rw [if_pos ⟨he, hc⟩, hzero i j] at hle
  exact (not_le_of_gt hp) hle


/-- T1 probability-law verification: both (omitted,realized) laws are
nonnegative and sum to one. The omitted-profile law is uniform; conditional
on it, the included observation is uniform on exactly the 65 retained atoms. -/
theorem clique_probability_laws :
    (∀ included x, 0 ≤ cliqueJointMass included x) ∧
    (∀ included, ∑ x, cliqueJointMass included x = (1 : ℚ)) ∧
    (∀ t included, ∑ z, cliqueObservationMass t included z = (1 : ℚ)) := by
  constructor
  · intro included x
    cases included
    · norm_num [cliqueJointMass]
    · by_cases hx : x.1 = x.2 <;> norm_num [cliqueJointMass, hx]
  · constructor
    · intro included
      have h : expect (cliqueJointMass included) (fun _ => (1 : ℚ)) = 1 := by
        rw [clique_joint_expectation included (fun _ _ => 1)]
        have hc (t : Fin 66) : expect (cliqueObservationMass t included) (fun _ => (1 : ℚ)) = 1 := by
          cases included
          · norm_num [expect, cliqueObservationMass]
          · unfold expect cliqueObservationMass
            rw [Fin.sum_univ_succAbove _ t]
            simp [Fin.succAbove_ne]
        simp_rw [hc]
        norm_num [expect]
      simpa [expect] using h
    · intro t included
      cases included
      · norm_num [cliqueObservationMass]
      · rw [Fin.sum_univ_succAbove _ t]
        simp [cliqueObservationMass, Fin.succAbove_ne]


/-- A two-point permutation used in T1's explicit symmetry witness: first
swap 0 to a, then send the resulting image of 1 to b. On the three- and
four-element sets used below, distinct a,b give the desired two images. -/
def twoImagePerm {n : ℕ} [NeZero n] (a b : Fin n) : Equiv.Perm (Fin n) :=
  let e := Equiv.swap 0 a
  e.trans (Equiv.swap (e 1) b)

/-- Permute the three clique labels, and independently permute the four
vertices of each source clique. This explicit product equivalence verifies
the two representative-bank classes (T1(vi)). -/
def cliqueProductPerm (e : Equiv.Perm (Fin 3)) (u : Fin 3 → Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin 3 × Fin 4) where
  toFun x := (e x.1, u x.1 x.2)
  invFun x := (e.symm x.1, (u (e.symm x.1)).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- The explicit network-preserving relabeling that sends the representative
omitted pair (0,1) or (0,4) to the pair omitted by t in T1. -/
def cliqueRelabeling (t : Fin 66) : Equiv.Perm (Fin 12) :=
  let h := (finProdFinEquiv (m := 3) (n := 4)).symm
  let a := h (cliquePairs t).1
  let b := h (cliquePairs t).2
  let e := if a.1 = b.1 then Equiv.swap 0 a.1 else twoImagePerm a.1 b.1
  let u : Fin 3 → Equiv.Perm (Fin 4) := if a.1 = b.1 then fun _ => twoImagePerm a.2 b.2
    else fun r => if r = 0 then Equiv.swap 0 a.2 else if r = 1 then Equiv.swap 0 b.2 else Equiv.refl _
  h.trans ((cliqueProductPerm e u).trans h.symm)


/-- T4(c), star instance: the original star design's common support for
(d₁₁,d₀₀) is precisely the three leaves, with target effect and HT expectation
zero under both outcome schedules. No network vertex or exposure is removed. -/
theorem star_common_support :
    let f := fun r => exposure starAdj (starAssignments r)
    let p := marginal (fun _ : Fin 6 => (1/6 : ℚ)) f
    let S := Finset.univ.filter (fun i => 0 < p i .d11 ∧ 0 < p i .d00)
    S = {1,2,3} ∧
    (∀ flag : Bool, let y := if flag then starB else starA
      ((∑ i ∈ S, (y i .d11 - y i .d00)) / S.card = 0) ∧
      expect (fun _ : Fin 6 => (1/6 : ℚ))
        (fun r => (∑ i ∈ S, (htTerm f y p .d11 r i - htTerm f y p .d00 r i)) / S.card) = 0) := by
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 0 in
      decide +kernel

/-- T4(d), printed-example specialization: with N=1000 and M=100, the
complete-assignment criterion is exactly 1≤kᵢ≤899. -/
theorem complete_support_1000_100 (k : ℕ) :
    (2 ≤ (100 : ℕ) ∧ 1 ≤ k ∧ k ≤ 1000 - 100 - 1) ↔ 1 ≤ k ∧ k ≤ 899 := by
  norm_num

/-- T5(iv): the triangle's mean and variance equal the corrected moments,
and exceed their absolute-standard-normal counterparts by precisely
7√(2/π)+1>0 and 63(1−2/π)+1/16>0. -/
theorem triangle_moment_comparison :
    (∫ x, baseline 8 x.1 x.2 ∂normalPair) = 8 * Real.sqrt (2 / Real.pi) + 1 ∧
    variance (fun x : ℝ × ℝ => baseline 8 x.1 x.2) normalPair = 64 * (1 - 2 / Real.pi) + 1/16 ∧
    (∫ x, baseline 8 x.1 x.2 ∂normalPair) - (∫ g : ℝ, |g| ∂gaussianReal 0 1) =
      7 * Real.sqrt (2 / Real.pi) + 1 ∧
    variance (fun x : ℝ × ℝ => baseline 8 x.1 x.2) normalPair -
      variance (fun g : ℝ => |g|) (gaussianReal 0 1) = 63 * (1 - 2 / Real.pi) + 1/16 ∧
    0 < 7 * Real.sqrt (2 / Real.pi) + 1 ∧ 0 < 63 * (1 - 2 / Real.pi) + 1/16 := by
  have h8 := corrected_baseline_moments 8 (by norm_num)
  refine ⟨h8.1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [show (8 : ℝ)^2 = 64 by norm_num] using h8.2
  · rw [h8.1, halfNormal_mean]
    ring
  · rw [h8.2, halfNormal_variance]
    ring
  · positivity
  · have hq : 2 / Real.pi < 1 := (div_lt_one Real.pi_pos).2 (by linarith [Real.pi_gt_three])
    linarith

/-- T5(iv): on a nonisolated network every actual generator baseline mean
exceeds the absolute-standard-normal mean by at least one. -/
theorem nonisolated_baseline_mean_shift {N : ℕ} (A : Adjacency N)
    (hiso : ∀ i, 1 ≤ degree A i) (i : Fin N) :
    1 ≤ (∫ x, baseline (degreeScale A i) x.1 x.2 ∂normalPair) -
      (∫ g : ℝ, |g| ∂gaussianReal 0 1) := by
  rw [(corrected_baseline_moments (degreeScale A i) (by positivity)).1, halfNormal_mean]
  apply baseline_mean_shift
  have hk := hiso i
  exact_mod_cast (show 1 ≤ degreeScale A i by unfold degreeScale; omega)

/-- The exact rational randomization expectation agrees with the real
paper expectation after canonical embedding. This certifies the scalar
model used by the numerical counterexamples in T1, T3 and T7. -/
theorem ratCast_expect {Ω : Type*} [Fintype Ω] (p t : Ω → ℚ) :
    expect (fun ω => (p ω : ℝ)) (fun ω => (t ω : ℝ)) = ((expect p t : ℚ) : ℝ) := by
  simp only [expect, Rat.cast_sum, Rat.cast_mul]

/-- Rational randomization variance embeds as the identical real variance,
including the square of the unconditional randomization mean (T1). -/
theorem ratCast_designVariance {Ω : Type*} [Fintype Ω] (p t : Ω → ℚ) :
    designVariance (fun ω => (p ω : ℝ)) (fun ω => (t ω : ℝ)) = ((designVariance p t : ℚ) : ℝ) := by
  unfold designVariance
  simp only [Rat.cast_sub, Rat.cast_pow, ← ratCast_expect]

/-- Marginal exposure probabilities in a rational numerical witness are
exactly the real marginal probabilities after embedding. -/
theorem ratCast_marginal {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (p : Ω → ℚ) (f : Ω → Fin N → D) (i : Fin N) (a : D) :
    marginal (fun ω => (p ω : ℝ)) f i a = ((marginal p f i a : ℚ) : ℝ) := by
  simp only [marginal, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp only [Rat.cast_zero]

/-- Joint exposure probabilities also embed exactly, preserving ordered
and diagonal pairs (T1/T7). -/
theorem ratCast_joint {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (p : Ω → ℚ) (f : Ω → Fin N → D) (i j : Fin N) (a b : D) :
    joint (fun ω => (p ω : ℝ)) f i j a b = ((joint p f i j a b : ℚ) : ℝ) := by
  simp only [joint, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp only [Rat.cast_zero]

/-- HT unit contributions in rational witnesses are exactly the real
paper contributions after embedding, including the explicit dropped-term
convention used by the support counterexample (T3). -/
theorem ratCast_htTerm {Ω D : Type*} {N : ℕ} [DecidableEq D]
    (f : Ω → Fin N → D) (y w : Fin N → D → ℚ) (a : D) (ω : Ω) (i : Fin N) :
    htTerm f (fun i d => (y i d : ℝ)) (fun i d => (w i d : ℝ)) a ω i =
      ((htTerm f y w a ω i : ℚ) : ℝ) := by
  unfold htTerm
  split_ifs <;> simp only [Rat.cast_div, Rat.cast_zero]

/-- The HT exposure mean commutes with the rational-to-real embedding,
with the original population denominator N. -/
theorem ratCast_htMean {Ω D : Type*} {N : ℕ} [DecidableEq D]
    (f : Ω → Fin N → D) (y w : Fin N → D → ℚ) (a : D) (ω : Ω) :
    htMean f (fun i d => (y i d : ℝ)) (fun i d => (w i d : ℝ)) a ω =
      ((htMean f y w a ω : ℚ) : ℝ) := by
  simp only [htMean, ratCast_htTerm, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]

/-- The HT effect contrast in rational witnesses equals the real `htContrast`
at canonically embedded outcomes and probability inputs. -/
theorem ratCast_htContrast {Ω D : Type*} {N : ℕ} [DecidableEq D]
    (f : Ω → Fin N → D) (y w : Fin N → D → ℚ) (a b : D) (ω : Ω) :
    htContrast f (fun i d => (y i d : ℝ)) (fun i d => (w i d : ℝ)) a b ω =
      ((htContrast f y w a b ω : ℚ) : ℝ) := by
  simp only [htContrast, ratCast_htMean, Rat.cast_sub]

/-- `varianceEstimate` commutes with rational-to-real embedding, preserving
the positive-joint and structural-zero guards and all denominators (T1). -/
theorem ratCast_varianceEstimate {Ω D : Type*} {N : ℕ} [DecidableEq D]
    (f : Ω → Fin N → D) (y w : Fin N → D → ℚ)
    (q : Fin N → Fin N → D → D → ℚ) (a b : D) (ω : Ω) :
    varianceEstimate f (fun i d => (y i d : ℝ)) (fun i d => (w i d : ℝ))
      (fun i j d e => (q i j d e : ℝ)) a b ω = ((varianceEstimate f y w q a b ω : ℚ) : ℝ) := by
  simp only [varianceEstimate, totalVarianceEstimate, totalCovarianceEstimate,
    Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_add,
    Rat.cast_sub, Rat.cast_mul, Rat.cast_one, Rat.cast_zero, Rat.cast_ofNat,
    apply_ite, Rat.cast_pos, Rat.cast_eq_zero]


/-- T7 construction verification: each rotation treats exactly three units,
and its four realized exposure-group sizes are (2,1,3,2). All four totals
used in this counterexample are populated. -/
theorem cycle8_profile_counts :
    (∀ r, (Finset.univ.filter (fun i => cycle8Assignments r i)).card = 3) ∧
    (∀ r a, (Finset.univ.filter (fun i => exposure cycle8Adj (cycle8Assignments r) i = a)).card =
      match a with | .d11 => 2 | .d10 => 1 | .d01 => 3 | .d00 => 2) := by
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 0 in
      decide +kernel

/-- Φ, the standard normal cumulative distribution function in T5(ii),
used for the explicit rectangle probability in the p. 216 correction. -/
def standardNormalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- T5(ii) probability ingredient: for a continuous real probability law,
the probability of (a,b) is the difference of its two CDF values. -/
theorem continuous_interval_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (a b : ℝ) (hab : a ≤ b) :
    μ.real (Set.Ioo a b) = cdf μ b - cdf μ a := by
  rw [measureReal_congr (Ioo_ae_eq_Ioc (μ := μ))]
  have hi : Set.Ioc a b = Set.Iic b \ Set.Iic a := by
    ext x
    simp only [Set.mem_Ioc, Set.mem_sdiff, Set.mem_Iic, not_le]
    tauto
  rw [hi, measureReal_sdiff (Set.Iic_subset_Iic.mpr hab) measurableSet_Iic,
    ← cdf_eq_real, ← cdf_eq_real]

/-- T5(ii), the triangle's explicit positive-probability rectangle:
Pr(−1/32<G<1/32,−1<E<−1/2) equals
[Φ(1/32)−Φ(−1/32)][Φ(−6)−Φ(−8)]>0.
The independent N(0,1) and N(1,1/16) laws are the generator premise. -/
theorem triangle_rectangle_cdf :
    normalPair.real (Set.Ioo (-1/32 : ℝ) (1/32) ×ˢ Set.Ioo (-1 : ℝ) (-1/2)) =
      (standardNormalCDF (1/32) - standardNormalCDF (-1/32)) *
        (standardNormalCDF (-6) - standardNormalCDF (-8)) ∧
    0 < (standardNormalCDF (1/32) - standardNormalCDF (-1/32)) *
        (standardNormalCDF (-6) - standardNormalCDF (-8)) := by
  letI : NullSingletonClass (gaussianReal (0 : ℝ) 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  letI : Measure.IsOpenPosMeasure (gaussianReal (0 : ℝ) 1) :=
    (gaussianReal_absolutelyContinuous' (μ := 0) (v := 1) (by norm_num)).isOpenPosMeasure
  have hnoise : (gaussianReal (0 : ℝ) 1).map (fun g : ℝ => g / 4 + 1) =
      gaussianReal 1 (1/16) := by
    change (gaussianReal (0 : ℝ) 1).map ((fun g : ℝ => g + 1) ∘ (fun g => g / 4)) = _
    rw [← Measure.map_map (by fun_prop : Measurable (fun g : ℝ => g + 1))
        (by fun_prop : Measurable (fun g : ℝ => g / 4)), gaussianReal_map_div_const,
      gaussianReal_map_add_const]
    congr 1
    · norm_num
    · apply NNReal.coe_injective
      norm_num
  have hpre : (fun g : ℝ => g / 4 + 1) ⁻¹' Set.Ioo (-1 : ℝ) (-1/2) = Set.Ioo (-8 : ℝ) (-6) := by
    ext g
    change (-1 < g / 4 + 1 ∧ g / 4 + 1 < -1/2) ↔ -8 < g ∧ g < -6
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have he : (gaussianReal (1 : ℝ) (1/16)).real (Set.Ioo (-1 : ℝ) (-1/2)) =
      (gaussianReal (0 : ℝ) 1).real (Set.Ioo (-8 : ℝ) (-6)) := by
    rw [← hnoise, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Ioo,
      hpre]
    rfl
  have h := continuous_interval_probability (gaussianReal 0 1)
  constructor
  · unfold normalPair standardNormalCDF
    rw [measureReal_prod_prod, he, h _ _ (by norm_num), h _ _ (by norm_num)]
  · unfold standardNormalCDF
    rw [← h (-1/32) (1/32) (by norm_num), ← h (-8) (-6) (by norm_num)]
    apply mul_pos
    · exact ENNReal.toReal_pos
        (ne_of_gt ((Measure.measure_Ioo_pos (gaussianReal 0 1)).2 (by norm_num))) (by finiteness)
    · exact ENNReal.toReal_pos
        (ne_of_gt ((Measure.measure_Ioo_pos (gaussianReal 0 1)).2 (by norm_num))) (by finiteness)

/-- T3 construction check: the star adjacency is symmetric with zero
diagonal, and the six listed assignments are precisely the complete
randomization support treating two of four units (p. 212 counterexample). -/
theorem star_design_verified :
    (∀ i j, starAdj i j = starAdj j i) ∧
    (∀ i, starAdj i i = false) ∧
    Function.Injective starAssignments ∧
    (∀ z : Assignment 4, (Finset.univ.filter (fun i => z i)).card = 2 ↔
      ∃ r : Fin 6, starAssignments r = z) := by
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 0 in
      decide +kernel

/-- T5(i): the triangle's squared binary adjacency has diagonal 2 and
all off-diagonal entries 1, as in the exact witness to p. 216. -/
theorem triangle_two_walk_matrix :
    ∀ i j : Fin 3, (∑ k : Fin 3,
      (if i ≠ k then (1 : ℕ) else 0) * (if k ≠ j then 1 else 0)) =
        if i = j then 2 else 1 := by
  decide +kernel

/-- The paper's finite-population contrast also commutes with the canonical
rational-to-real embedding, so rational witness effects are the same real
effects (display, p. 212; numerical counterexamples T1/T3/T7). -/
theorem ratCast_tau {D : Type*} {N : ℕ} (y : Fin N → D → ℚ) (a b : D) :
    tau (fun i d => (y i d : ℝ)) a b = ((tau y a b : ℚ) : ℝ) := by
  simp only [tau, Rat.cast_sum, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast]

/-- T5(ii): every point of the triangle's stated CDF rectangle forces
8|G|+E<−1/4. Its probability is formalized separately in triangle_rectangle_cdf;
the rectangle width 1/32 here differs from the general sufficient width 1/36. -/
theorem triangle_cdf_rectangle_negative (g e : ℝ)
    (hg : g ∈ Set.Ioo (-1/32 : ℝ) (1/32))
    (he : e ∈ Set.Ioo (-1 : ℝ) (-1/2)) : baseline 8 g e < -1/4 := by
  have hab : |g| < (1/32 : ℝ) := by
    apply abs_lt.mpr
    simpa only [Set.mem_Ioo, neg_div] using hg
  unfold baseline
  have he' := he.2
  nlinarith

/-- T6(iv), comparison to the p. 216 printed baseline law: if each
unit's baseline has the absolute-standard-normal law, the expected
population direct-plus-indirect effect is √(2/π)<1. No independence
between units is assumed for this mean comparison. -/
theorem halfNormal_population_effect {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Fin N → ℝ) (hLaw : ∀ i, HasLaw (fun ω => B ω i) halfNormalLaw P) :
    (∫ ω, tau (dilatedOutcomes (B ω)) .d11 .d00 ∂P) = Real.sqrt (2 / Real.pi) ∧
    Real.sqrt (2 / Real.pi) < 1 := by
  have hStd : Integrable (fun g : ℝ => |g|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).abs).integrable (by norm_num)
  have hHalf : Integrable id halfNormalLaw := by
    unfold halfNormalLaw
    exact (integrable_map_measure aestronglyMeasurable_id (by fun_prop)).2 hStd
  have hHalfMean : (∫ b : ℝ, b ∂halfNormalLaw) = Real.sqrt (2 / Real.pi) := by
    unfold halfNormalLaw
    change (∫ b : ℝ, id b ∂(gaussianReal 0 1).map (fun g : ℝ => |g|)) = _
    rw [integral_map (φ := fun g : ℝ => |g|) (f := id) (by fun_prop) aestronglyMeasurable_id]
    exact halfNormal_mean
  have hInt (i : Fin N) : Integrable (fun ω => B ω i) P := (hLaw i).integrable hHalf
  have hc (i : Fin N) : (∫ ω, B ω i ∂P) = Real.sqrt (2 / Real.pi) :=
    (hLaw i).integral_eq.trans hHalfMean
  constructor
  · have he : (fun ω => tau (dilatedOutcomes (B ω)) .d11 .d00) =
        (fun ω => (∑ i, B ω i) / N) := by
      funext ω
      exact (dilated_effects (B ω)).1
    rw [he, integral_div, integral_finsetSum Finset.univ (fun i _ => hInt i)]
    simp_rw [hc]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
    field_simp
  · have hq : 2 / Real.pi < 1 := (div_lt_one Real.pi_pos).2 (by linarith [Real.pi_gt_three])
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 / Real.pi), Real.sqrt_nonneg (2 / Real.pi)]

end

end AronowAudit.P044

