import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.BigOperators

/-!
P045-T32/T33: exact and simulated exposure-probability HT variance.
Adapted from this repository's related P044 formalization. All definitions and theorems are local
to this file. Fixed real potential outcomes and normalized finite design masses are
used for the general correction; the concrete witness uses canonically embedded
rational arithmetic.
-/

namespace AronowAudit.P045.ExposureVariance
open Finset
open scoped BigOperators
noncomputable section

/-- "The ... vector of treatments ... z=(z₁,...,z_N)'" (p. 292).
`false` is control (0), `true` is treatment (1). Units are numbered from 0 here. -/
abbrev Assignment (N : ℕ) := Fin N → Bool

/-- The four labels "Direct + Indirect", "Isolated Direct", "Indirect", and
"No Exposure" in the display on p. 294. -/
inductive Exposure where
  | d11 | d10 | d01 | d00
  deriving DecidableEq, Repr

instance : Fintype Exposure := ⟨{.d11, .d10, .d01, .d00}, by intro d; cases d <;> simp⟩

/-- "N × N adjacency matrix ... entries ... 0 or 1 (and ... 0's on the diagonal)"
(p. 292). Boolean entries encode the binary version of that definition. -/
abbrev Adjacency (N : ℕ) := Fin N → Fin N → Bool

/-- The corrected scalar θᵢ z = ∑ⱼ θᵢⱼ zⱼ in the p. 294 display (P045-T32).
This is the number of treated network peers. -/
def peerCount {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N) : ℕ :=
  ∑ j, if A i j && z j then 1 else 0

/-- "... whether ... they are treated ... [or] any one of their network peers
is treated" (pp. 294–295). The corrected four-condition exposure mapping. -/
def exposure {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N) : Exposure :=
  if z i then (if 0 < peerCount A z i then .d11 else .d10)
  else (if 0 < peerCount A z i then .d01 else .d00)

/-- "... assigns some probability, p_z, to a treatment profile" (pp. 292–294).
A finite index type Ω indexes randomization atoms; zero masses are permitted. -/
structure FiniteDesign (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

/-- Randomization expectation: the finite sum ∑_z p_z T(z), using p. 294's
Pr(Z=z)=p_z. Also used over rational fields for exact numerical witnesses. -/
def expect {Ω K : Type*} [Fintype Ω] [CommSemiring K] (p : Ω → K) (t : Ω → K) : K :=
  ∑ ω, p ω * t ω

/-- Randomization variance E[T²]−E[T]² (notation P045-T32/T33), valid when the
nonnegative masses sum to one. It is not squared error about the estimand. -/
def designVariance {Ω K : Type*} [Fintype Ω] [CommRing K]
    (p : Ω → K) (t : Ω → K) : K := expect p (fun ω => t ω ^ 2) - (expect p t) ^ 2


/-- "τ(d,d') = 1/N ∑ᵢ (yᵢ(d)−yᵢ(d'))" (display, p. 297).
Outcomes are fixed exposure-indexed real values; rational witnesses use the
identical formula in ℚ. -/
def tau {N : ℕ} {D K : Type*} [Field K] (y : Fin N → D → K) (a b : D) : K :=
  (∑ i, (y i a - y i b)) / N

/-- πᵢ(d)=Pr(Dᵢ=d), the exposure probability of pp. 297–298 (notation P045-T32/T33).
`f ω i` is Dᵢ on the randomization atom ω. -/
def marginal {Ω D K : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → D) (i : Fin N) (a : D) : K :=
  ∑ ω, if f ω i = a then p ω else 0

/-- πᵢⱼ(d,e)=Pr(Dᵢ=d,Dⱼ=e), notation P045-T32/T33 for shared-peer dependencies
(p. 294). Ordered pairs, including diagonal pairs, are retained. -/
def joint {Ω D K : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → D) (i j : Fin N) (a b : D) : K :=
  ∑ ω, if f ω i = a ∧ f ω j = b then p ω else 0

/-- The HT unit contribution I(Dᵢ=d)Yᵢ/wᵢ(d) (P045-T32/T33; pp. 297–298). By correct specification Yᵢ=yᵢ(Dᵢ), this is the displayed
conditional expression. Lean's total division is not a support assumption. -/
def htTerm {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a : D) (ω : Ω) (i : Fin N) : K :=
  if f ω i = a then y i a / w i a else 0

/-- μ̂_HT(d)=N⁻¹∑ᵢ I(Dᵢ=d)Yᵢ/wᵢ(d) (P045-T32/T33).
This is the HT exposure-total estimator of p. 297 divided by N. -/
def htMean {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a : D) (ω : Ω) : K :=
  (∑ i, htTerm f y w a ω i) / N

/-- The implemented effect estimate μ̂(k)−μ̂(l), for the p. 297 estimand
(P045-T32/T33). -/
def htContrast {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a b : D) (ω : Ω) : K :=
  htMean f y w a ω - htMean f y w b ω

/-- V̂_d from P045-T32/T33; ordered positive-joint terms
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

/-- Ĉ_kl from P045-T32/T33. The cross zero adjustment
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

/-- V̂(k,l)=(V̂_k+V̂_l−2 Ĉ_kl)/N², the HT variance functional used by
"conservative approximations" on p. 298 (P045-T32/T33). -/
def varianceEstimate {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K)
    (q : Fin N → Fin N → D → D → K) (a b : D) (ω : Ω) : K :=
  (totalVarianceEstimate f y w q a ω + totalVarianceEstimate f y w q b ω -
    2 * totalCovarianceEstimate f y w q a b ω) / (N : K) ^ 2

/-- The exact structural-zero surplus in T33(a), with the exact-probability scope of p. 298 explicit:
within-exposure squares use i≠j; cross squares include i=j. -/
def zeroSurplus {N : ℕ} {D : Type*} [DecidableEq D]
    (y : Fin N → D → ℝ) (q : Fin N → Fin N → D → D → ℝ) (a b : D) : ℝ :=
  ((∑ i, ∑ j, if i ≠ j ∧ q i j a a = 0 then (y i a + y j a) ^ 2 / 2 else 0) +
   (∑ i, ∑ j, if i ≠ j ∧ q i j b b = 0 then (y i b + y j b) ^ 2 / 2 else 0) +
   (∑ i, ∑ j, if q i j a b = 0 then (y i a - y j b) ^ 2 else 0)) / (N : ℝ) ^ 2

/-- Finite linearity used in the p. 297 unbiasedness and p. 298 variance
correction: expectation commutes with a fixed finite population sum. -/
theorem expect_sum {Ω I K : Type*} [Fintype Ω] [Field K] (p : Ω → K) (s : Finset I)
    (u : Ω → I → K) : expect p (fun ω => ∑ i ∈ s, u ω i) = ∑ i ∈ s, expect p (fun ω => u ω i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]


/-- Finite expectation of a difference, used in the p. 298 variance correction. -/
theorem expect_sub {Ω K : Type*} [Fintype Ω] [Field K] (p u v : Ω → K) :
    expect p (fun ω => u ω - v ω) = expect p u - expect p v := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

/-- Finite expectation of a sum, used in the p. 298 variance correction. -/
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
expectation πᵢⱼ(a,b)c, including i=j. Finite lemma for T33. -/
theorem expect_joint_event {Ω D K : Type*} {N : ℕ} [Fintype Ω] [Field K] [DecidableEq D]
    (p : Ω → K) (f : Ω → Fin N → D) (i j : Fin N) (a b : D) (c : K) :
    expect p (fun ω => if f ω i = a ∧ f ω j = b then c else 0) = joint p f i j a b * c := by
  unfold expect joint
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs with hh <;> simp [hh]

/-- T33 finite lemma: the expected product of two HT contributions is the
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

/-- T33 finite algebra: the second moment of the population average expands into
all ordered pairs, divided by N², with no independence requirement. -/
theorem expect_square_sum {Ω K : Type*} {N : ℕ} [Fintype Ω] [Field K]
    (p : Ω → K) (u : Ω → Fin N → K) :
    expect p (fun ω => ((∑ i, u ω i) / N) ^ 2) =
      (∑ i, ∑ j, expect p (fun ω => u ω i * u ω j)) / (N : K) ^ 2 := by
  simp_rw [div_pow, pow_two, Finset.sum_mul_sum, expect_div, expect_sum]

/-- T33 finite second moment: the squared HT contrast expands into the two
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
m,J and arbitrary fixed estimator inputs w,q. This is P045-T32/T33 with each exposure
indicator (or product) replaced by its randomization expectation. -/
def expectedTotalVariance {N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K]
    (m : Fin N → D → K) (J : Fin N → Fin N → D → D → K)
    (y w : Fin N → D → K) (q : Fin N → Fin N → D → D → K) (a : D) : K :=
  ∑ i, ∑ j, ((if 0 < q i j a a then
    J i j a a * (y i a * y j a * (1 / (w i a * w j a) - 1 / q i j a a)) else 0) +
    (if i ≠ j ∧ q i j a a = 0 then
      m i a * (y i a ^ 2 / (2 * w i a)) + m j a * (y j a ^ 2 / (2 * w j a)) else 0))

/-- Expected cross-exposure covariance functional with observation law m,J,
retaining all ordered zero pairs including the diagonal (T33 finite lemma). -/
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

/-- T33 finite identity: the expectation of the P045-T32/T33 variance functional is its
explicit marginal/joint formula. It holds also for finite simulated inputs;
conservativeness then requires additional equalities of those inputs. -/
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

/-- T33(a), T32(ii): the expectation of a single HT term with fixed weight
is yᵢ(d)πᵢ(d)/wᵢ(d). No independence or positive joint support is needed
(pp. 297–298, corrected). -/
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

/-- T32(ii): arbitrary fixed positive weights give the average of
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

/-- T33(a): true positive marginal exposure probabilities give unbiased
unit contributions, population means, and the p. 297 population contrast.
This is the support-qualified correction of pp. 297–298. -/
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

/-- Exposure counts cᵢ(a) over an enumerated table, the p. 296 recipe and
P045-T32/T33's make_exposure_prob inputs. -/
def exposureCount {R N : ℕ} {D : Type*} [DecidableEq D]
    (f : Fin R → Fin N → D) (i : Fin N) (a : D) : ℕ :=
  (Finset.univ.filter (fun r => f r i = a)).card

/-- Joint counts cᵢⱼ(a,b) over the same table (P045-T32/T33). -/
def jointCount {R N : ℕ} {D : Type*} [DecidableEq D]
    (f : Fin R → Fin N → D) (i j : Fin N) (a b : D) : ℕ :=
  (Finset.univ.filter (fun r => f r i = a ∧ f r j = b)).card

/-- Returned marginal weights (cᵢ(a)+1)/(R+1), rather than counts/R:
the package's `make_exposure_prob`, used on pp. 298–299 (T32 correction). -/
def smoothedWeight {R N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    (f : Fin R → Fin N → D) (i : Fin N) (a : D) : K :=
  ((exposureCount f i a : K) + 1) / ((R : K) + 1)

/-- Returned joint weights: same-exposure entries add the diagonal identity
then divide by R+1; cross-exposure entries divide by R (P045-T32/T33; T32 correction). -/
def smoothedJoint {R N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    (f : Fin R → Fin N → D) (i j : Fin N) (a b : D) : K :=
  if a = b then ((jointCount f i j a b : K) + if i = j then 1 else 0) / ((R : K) + 1)
  else (jointCount f i j a b : K) / R

/-- T32(i): an exhaustive equally likely list gives exact marginal and joint
exposure probabilities by counts/R, including same-exposure diagonals.
Exact-input exposure-probability identity, pp. 296–298. -/
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

/-- True randomization covariance of two supported HT totals, written as
an ordered-pair sum. This is the finite kernel of the p. 298 exact-probability clarification. -/
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

/-- Same-unit, same-exposure joint probability is the marginal (P045-T32/T33). -/
theorem joint_diagonal {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (p : Ω → ℝ) (f : Ω → Fin N → D) (i : Fin N) (a : D) :
    joint p f i i a a = marginal p f i a := by simp [joint, marginal]

/-- Swapping the ordered units and their exposures preserves a joint probability. -/
theorem joint_swap {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (p : Ω → ℝ) (f : Ω → Fin N → D) (i j : Fin N) (a b : D) :
    joint p f i j a b = joint p f j i b a := by simp [joint, and_comm]

/-- T33 finite same-exposure identity: exact inputs reproduce the true total
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

/-- T33 finite cross-exposure identity: the adjusted covariance has exact
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

/-- T33 finite variance identity: with supported exact weights, the HT contrast
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

/-- T33(a): with any finite design, correctly specified exposures, fixed real
outcomes and positive marginals for the two distinct exposures, the expected
exact-input HT variance estimate exceeds the design variance by precisely
the structural-zero squared-outcome surplus. Exact-probability clarification of p. 298. -/
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


/-- T33 finite inequality: every structural-zero surplus is nonnegative,
including the cross diagonal contribution. Exact-probability clarification of p. 298. -/
theorem zeroSurplus_nonneg {N : ℕ} {D : Type*} [DecidableEq D]
    (y : Fin N → D → ℝ) (q : Fin N → Fin N → D → D → ℝ) (a b : D) :
    0 ≤ zeroSurplus y q a b := by
  unfold zeroSurplus
  positivity

/-- T33(b): exact design marginals and joints, with positive marginal support,
make the HT contrast variance construction conservative in expectation.
There is no claim here for the Hajek linearization. Exact-probability clarification of p. 298. -/
theorem exact_variance_conservative {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (hN : 0 < N) (P : FiniteDesign Ω) (f : Ω → Fin N → D)
    (y : Fin N → D → ℝ) (a b : D) (hab : a ≠ b)
    (ha : ∀ i, 0 < marginal P.mass f i a) (hb : ∀ i, 0 < marginal P.mass f i b) :
    designVariance P.mass (htContrast f y (marginal P.mass f) a b) ≤
      expect P.mass (varianceEstimate f y (marginal P.mass f) (joint P.mass f) a b) := by
  have h := exact_variance_surplus hN P f y a b hab ha hb
  have hpos := zeroSurplus_nonneg y (joint P.mass f) a b
  linarith


/-- T32's complete randomization atoms: all 66 ordered-increasing treated
pairs on twelve vertices. The table below is just a computable enumeration
of the two-element subsets. -/
def cliquePairs : Fin 66 → Fin 12 × Fin 12 :=
  ![(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (0,9), (0,10), (0,11), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (1,10), (1,11), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10), (2,11), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (4,5), (4,6), (4,7), (4,8), (4,9), (4,10), (4,11), (5,6), (5,7), (5,8), (5,9), (5,10), (5,11), (6,7), (6,8), (6,9), (6,10), (6,11), (7,8), (7,9), (7,10), (7,11), (8,9), (8,10), (8,11), (9,10), (9,11), (10,11)]

/-- T32's binary treatment profile associated with each pair, exactly two
treated vertices, uniform mass 1/66. -/
def cliqueAssignments (r : Fin 66) : Assignment 12 := fun i =>
  decide (i = (cliquePairs r).1 ∨ i = (cliquePairs r).2)

/-- T32's three disjoint four-cliques (vertices 0–3,4–7,8–11), an undirected
zero-diagonal network with no isolates. -/
def cliqueAdj : Adjacency 12 := fun i j => decide (i ≠ j ∧ i.val / 4 = j.val / 4)

/-- The p. 294 four-condition mapping for T32's explicit network and design. -/
def cliqueF (r : Fin 66) (i : Fin 12) : Exposure :=
  let u := (cliquePairs r).1
  let v := (cliquePairs r).2
  if i = u ∨ i = v then
    (if u.val / 4 = v.val / 4 then .d11 else .d10)
  else (if i.val / 4 = u.val / 4 ∨ i.val / 4 = v.val / 4 then .d01 else .d00)


/-- T32 finite counting ingredient: exactly two treated vertices contribute
one peer indicator each when the vertices are distinct. This implements the
corrected row-times-column treated-peer count of p. 294. -/
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

/-- T32 finite exposure calculation: the efficient treatment-pair formula is
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
/-- T32's fixed outcome schedule is one at every unit and all four exposures. -/
def cliqueY : Fin 12 → Exposure → ℚ := fun _ _ => 1

/-- T32's R=65 distinct simulated assignments omit exactly atom t. Index r
skips t in the complete enumeration. Taking t uniform gives exactly the
uniform law on all retained 65-element tables. -/
def retainedAssignments (t : Fin 66) (r : Fin 65) : Assignment 12 :=
  cliqueAssignments (t.succAbove r)

/-- T32's actual exposure counts over the retained bank, not assumed true
probabilities. Used in the package smoothing definitions above. -/
def retainedF (t : Fin 66) : Fin 65 → Fin 12 → Exposure :=
  fun r => cliqueF (t.succAbove r)

/-- T32 full-design marginal counts: 3,8,27,28 in exposure order. Their
identification with enumeration is a separately stated count lemma. -/
def cliqueFullCount (a : Exposure) : ℕ :=
  match a with | .d11 => 3 | .d10 => 8 | .d01 => 27 | .d00 => 28

/-- T32 full-design joint counts for the two contrasted exposures, including
the same-exposure marginals on the diagonal. -/
def cliqueFullJoint (i j : Fin 12) (a b : Exposure) : ℕ :=
  if i = j then (if a = b then cliqueFullCount a else 0)
  else match a,b with
    | .d01,.d01 => if i.val / 4 = j.val / 4 then 17 else 9
    | .d00,.d00 => if i.val / 4 = j.val / 4 then 28 else 6
    | .d01,.d00 | .d00,.d01 => if i.val / 4 = j.val / 4 then 0 else 15
    | _,_ => jointCount cliqueF i j a b

/-- T32's retained marginal counts are full counts minus the omitted event.
The package adds one and divides by R+1=66. -/
def cliqueWeights (t : Fin 66) (i : Fin 12) (a : Exposure) : ℚ :=
  ((cliqueFullCount a - if cliqueF t i = a then 1 else 0 : ℕ) + 1 : ℕ) / (66 : ℚ)

/-- T32's retained joint counts are full counts minus the omitted joint event.
Same-exposure entries add the diagonal identity and divide by 66; cross
entries divide by R=65, exactly as in P045-T32/T33. -/
def cliqueJoints (t : Fin 66) (i j : Fin 12) (a b : Exposure) : ℚ :=
  let c := cliqueFullJoint i j a b - if cliqueF t i = a ∧ cliqueF t j = b then 1 else 0
  if a = b then ((c + if i = j then 1 else 0 : ℕ) : ℚ) / 66 else (c : ℚ) / 65

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- T32 finite count verification: the stated marginal and joint counts come
from the explicit network and all 66 complete-randomization assignments. -/
theorem clique_full_counts :
    (∀ i a, exposureCount cliqueF i a = cliqueFullCount a) ∧
    (∀ i j a b, (a = Exposure.d01 ∨ a = .d00) → (b = Exposure.d01 ∨ b = .d00) →
      jointCount cliqueF i j a b = cliqueFullJoint i j a b) := by
  constructor
  · intro i a
    fin_cases i <;> cases a <;> decide +kernel
  · intro i j a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals (fin_cases i <;> fin_cases j <;> decide +kernel)

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

/-- T32 finite bank verification: subtracting the omitted indicators yields
exactly the package weights from the 65 retained distinct assignments. -/
theorem clique_retained_weights :
    (∀ t i a, cliqueWeights t i a = (smoothedWeight (retainedF t) i a : ℚ)) ∧
    (∀ t i j a b, (a = Exposure.d01 ∨ a = .d00) → (b = Exposure.d01 ∨ b = .d00) →
      cliqueJoints t i j a b = (smoothedJoint (retainedF t) i j a b : ℚ)) := by
  have hc (t : Fin 66) (i : Fin 12) (a : Exposure) :
      exposureCount (retainedF t) i a = cliqueFullCount a - if cliqueF t i = a then 1 else 0 := by
    change (Finset.univ.filter (fun r : Fin 65 => cliqueF (t.succAbove r) i = a)).card = _
    rw [count_delete_atom t (fun r : Fin 66 => cliqueF r i = a)]
    rw [← clique_full_counts.1 i a]
    rfl
  have hj (t : Fin 66) (i j : Fin 12) (a b : Exposure)
      (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
      jointCount (retainedF t) i j a b = cliqueFullJoint i j a b -
        if cliqueF t i = a ∧ cliqueF t j = b then 1 else 0 := by
    change (Finset.univ.filter (fun r : Fin 65 =>
      cliqueF (t.succAbove r) i = a ∧ cliqueF (t.succAbove r) j = b)).card = _
    rw [count_delete_atom t (fun r : Fin 66 => cliqueF r i = a ∧ cliqueF r j = b)]
    rw [← clique_full_counts.2 i j a b ha hb]
    rfl
  constructor
  · intro t i a
    unfold cliqueWeights smoothedWeight
    rw [hc]
    push_cast
    norm_num
  · intro t i j a b ha hb
    unfold cliqueJoints smoothedJoint
    rw [hj t i j a b ha hb]
    by_cases he : a = b <;> by_cases hij : i = j <;> simp [he, hij, Nat.cast_add] <;> norm_num

/-- T32 point estimator T(S,z) with all outcomes one and the package's
returned positive marginal inputs, for omitted assignment t. -/
def cliqueT (t z : Fin 66) : ℚ :=
  htContrast cliqueF cliqueY (cliqueWeights t) .d01 .d00 z

/-- T32 variance functional at the package's returned marginal and joint
inputs from the same bank. This definition reuses the general P045-T32/T33 formula. -/
def cliqueV (t z : Fin 66) : ℚ :=
  varianceEstimate cliqueF cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00 z

/-- The two T32 joint laws: independent actual assignment has 4356 equally
likely (t,z) pairs; an actual assignment in the bank has 4290 equally likely
pairs with z≠t, zero mass on z=t. -/
def cliqueJointMass (included : Bool) (x : Fin 66 × Fin 66) : ℚ :=
  if included then (if x.1 = x.2 then 0 else 1/4290) else 1/4356

/-- Observation law for T32 conditional on the omitted profile t: uniform on
all 66 profiles if independent, or on the 65 retained profiles if included. -/
def cliqueObservationMass (t : Fin 66) (included : Bool) (z : Fin 66) : ℚ :=
  if included then (if z = t then 0 else 1/65) else 1/66

/-- T32 finite probability law: an independent observation is uniform on
all 66 complete-randomization atoms, for every omitted profile. -/
theorem clique_observation_independent_mass (t : Fin 66) :
    cliqueObservationMass t false = (fun _ : Fin 66 => (1/66 : ℚ)) := by
  funext z
  rfl

/-- Conditional observation marginals in T32, separate from the package's
smoothed estimator inputs. The included law uses unsmoothed counts/65. -/
def cliqueObservationMarginal (t : Fin 66) (included : Bool) (i : Fin 12) (a : Exposure) : ℚ :=
  if included then ((cliqueFullCount a - if cliqueF t i = a then 1 else 0 : ℕ) : ℚ) / 65
  else (cliqueFullCount a : ℚ) / 66

/-- Conditional observation joints in T32. These are actual probabilities,
including unsmoothed same-exposure diagonals, not the estimated inputs. -/
def cliqueObservationJoint (t : Fin 66) (included : Bool) (i j : Fin 12) (a b : Exposure) : ℚ :=
  if included then ((cliqueFullJoint i j a b - if cliqueF t i = a ∧ cliqueF t j = b then 1 else 0 : ℕ) : ℚ) / 65
  else (cliqueFullJoint i j a b : ℚ) / 66

/-- T32 finite probability verification: actual observation marginals equal
the complete or retained event counts divided by their support sizes. -/
theorem clique_observation_marginal (t : Fin 66) (included : Bool) (i : Fin 12) (a : Exposure) :
    marginal (cliqueObservationMass t included) cliqueF i a = cliqueObservationMarginal t included i a := by
  cases included
  · calc
      marginal (cliqueObservationMass t false) cliqueF i a = (exposureCount cliqueF i a : ℚ) / 66 := by
        rw [clique_observation_independent_mass]
        simpa using
          (exhaustive_probabilities (K := ℚ) (by decide : 0 < 66) cliqueF i i a a).1
      _ = cliqueObservationMarginal t false i a := by
        rw [clique_full_counts.1 i a]
        rfl
  · have he : marginal (cliqueObservationMass t true) cliqueF i a =
        marginal (fun _ : Fin 65 => (1/65 : ℚ)) (retainedF t) i a := by
      unfold marginal cliqueObservationMass retainedF
      rw [Fin.sum_univ_succAbove _ t]
      simp [Fin.succAbove_ne]
    calc
      marginal (cliqueObservationMass t true) cliqueF i a =
          (exposureCount (retainedF t) i a : ℚ) / 65 := by
        rw [he]
        simpa using (exhaustive_probabilities (K := ℚ) (by decide : 0 < 65) (retainedF t) i i a a).1
      _ = cliqueObservationMarginal t true i a := by
        change ((Finset.univ.filter (fun r : Fin 65 => cliqueF (t.succAbove r) i = a)).card : ℚ) / 65 = _
        rw [count_delete_atom t (fun r : Fin 66 => cliqueF r i = a)]
        rw [show (Finset.univ.filter (fun r => cliqueF r i = a)).card = cliqueFullCount a
          from clique_full_counts.1 i a]
        rfl

/-- T32 finite probability verification for the four relevant ordered joint
exposure events, for either observation law. -/
theorem clique_observation_joint (t : Fin 66) (included : Bool) (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    joint (cliqueObservationMass t included) cliqueF i j a b = cliqueObservationJoint t included i j a b := by
  cases included
  · calc
      joint (cliqueObservationMass t false) cliqueF i j a b = (jointCount cliqueF i j a b : ℚ) / 66 := by
        rw [clique_observation_independent_mass]
        simpa using
          (exhaustive_probabilities (K := ℚ) (by decide : 0 < 66) cliqueF i j a b).2
      _ = cliqueObservationJoint t false i j a b := by
        rw [clique_full_counts.2 i j a b ha hb]
        rfl
  · have he : joint (cliqueObservationMass t true) cliqueF i j a b =
        joint (fun _ : Fin 65 => (1/65 : ℚ)) (retainedF t) i j a b := by
      unfold joint cliqueObservationMass retainedF
      rw [Fin.sum_univ_succAbove _ t]
      simp [Fin.succAbove_ne]
    calc
      joint (cliqueObservationMass t true) cliqueF i j a b =
          (jointCount (retainedF t) i j a b : ℚ) / 65 := by
        rw [he]
        simpa using (exhaustive_probabilities (K := ℚ) (by decide : 0 < 65) (retainedF t) i j a b).2
      _ = cliqueObservationJoint t true i j a b := by
        change ((Finset.univ.filter (fun r : Fin 65 =>
          cliqueF (t.succAbove r) i = a ∧ cliqueF (t.succAbove r) j = b)).card : ℚ) / 65 = _
        rw [count_delete_atom t (fun r : Fin 66 => cliqueF r i = a ∧ cliqueF r j = b)]
        rw [show (Finset.univ.filter (fun r => cliqueF r i = a ∧ cliqueF r j = b)).card =
          cliqueFullJoint i j a b from clique_full_counts.2 i j a b ha hb]
        rfl

/-- T32 conditional first moment, computed from the true observation
marginals and the smoothed marginal inputs. -/
def cliqueConditionalMean (t : Fin 66) (included : Bool) : ℚ :=
  ((∑ i, cliqueObservationMarginal t included i .d01 / cliqueWeights t i .d01) -
    (∑ i, cliqueObservationMarginal t included i .d00 / cliqueWeights t i .d00)) / 12

/-- T32 conditional second moment, computed from the true observation joints
and smoothed marginal inputs. -/
def cliqueConditionalSecond (t : Fin 66) (included : Bool) : ℚ :=
  (∑ i, ∑ j,
    (cliqueObservationJoint t included i j .d01 .d01 / (cliqueWeights t i .d01 * cliqueWeights t j .d01) +
     cliqueObservationJoint t included i j .d00 .d00 / (cliqueWeights t i .d00 * cliqueWeights t j .d00) -
     cliqueObservationJoint t included i j .d01 .d00 / (cliqueWeights t i .d01 * cliqueWeights t j .d00) -
     cliqueObservationJoint t included i j .d00 .d01 / (cliqueWeights t i .d00 * cliqueWeights t j .d01))) / 144

/-- T32 conditional expected variance estimate, computed from true observation
marginals/joints and the different, smoothed package inputs. -/
def cliqueConditionalV (t : Fin 66) (included : Bool) : ℚ :=
  expectedVariance (cliqueObservationMarginal t included) (cliqueObservationJoint t included)
    cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00

/-- T32's marginal and joint moment formulas are exact finite expectations;
there is no assumption that the package's inputs equal true probabilities. -/
theorem clique_conditional_moments (t : Fin 66) (included : Bool) :
    expect (cliqueObservationMass t included) (cliqueT t) = cliqueConditionalMean t included ∧
    expect (cliqueObservationMass t included) (fun z => cliqueT t z ^ 2) = cliqueConditionalSecond t included ∧
    expect (cliqueObservationMass t included) (cliqueV t) = cliqueConditionalV t included := by
  have hkk := fun i j => clique_observation_joint t included i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
  have hll := fun i j => clique_observation_joint t included i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
  have hkl := fun i j => clique_observation_joint t included i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  have hlk := fun i j => clique_observation_joint t included i j .d00 .d01 (Or.inr rfl) (Or.inl rfl)
  refine ⟨?_, ?_, ?_⟩
  · unfold cliqueT htContrast
    rw [expect_sub, htMean_expectation, htMean_expectation]
    simp only [cliqueY, one_mul]
    simp_rw [clique_observation_marginal]
    unfold cliqueConditionalMean
    ring
  · unfold cliqueT
    rw [htContrast_second_moment]
    simp_rw [hkk, hll, hkl, hlk]
    simp [cliqueY, cliqueConditionalSecond, div_eq_mul_inv, mul_inv_rev] <;> norm_num
  · unfold cliqueV
    rw [varianceEstimate_expectation]
    unfold expectedVariance cliqueConditionalV expectedVariance expectedTotalVariance expectedTotalCovariance
    simp_rw [hkk, hll, hkl, clique_observation_marginal]

/-- T32 joint expectation decomposes into the uniform omitted-profile law
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

/-- T32's certificate of the ordinal of an increasing treat-two pair
in the 66-profile enumeration. This is an indexing aid, not a model premise. -/
def cliquePairOrdinal (p : Fin 12 × Fin 12) : ℕ :=
  p.1.val * (23-p.1.val)/2 + p.2.val-p.1.val-1

/-- T32: the computed pair ordinal recovers the profile index. -/
theorem clique_pair_ordinal : ∀ r : Fin 66, cliquePairOrdinal (cliquePairs r)=r.val := by
  intro r
  fin_cases r <;> decide +kernel

/-- T32: every profile is represented once. The proof uses its two
increasing treated vertices and their certified ordinal, without
enumerating equality of two twelve-coordinate assignment functions. -/
theorem clique_assignment_injective : Function.Injective cliqueAssignments := by
  have hord : ∀ r : Fin 66, (cliquePairs r).1 < (cliquePairs r).2 := by
    intro r
    fin_cases r <;> decide +kernel
  intro r s hrs
  have hp : ({(cliquePairs r).1, (cliquePairs r).2} : Set (Fin 12)) =
      {(cliquePairs s).1, (cliquePairs s).2} := by
    ext i
    have he := congrFun hrs i
    change decide (i=(cliquePairs r).1 ∨ i=(cliquePairs r).2) =
      decide (i=(cliquePairs s).1 ∨ i=(cliquePairs s).2) at he
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (decide_eq_decide.mp he)
  rcases Set.pair_eq_pair_iff.mp hp with he | he
  · have hpair : cliquePairs r=cliquePairs s := Prod.ext he.1 he.2
    apply Fin.ext
    rw [← clique_pair_ordinal r, ← clique_pair_ordinal s, hpair]
  · have hr := hord r
    have hs := hord s
    rw [he.1,he.2] at hr
    exact False.elim ((not_lt_of_ge hs.le) hr)

/-- T32 construction verification: the enumeration consists of distinct
complete treat-two assignments, its clique network is symmetric with zero
diagonal and no isolates, and both relevant exposures occur in every profile.
There are 18 same-block profiles and 48 profiles in different blocks. -/
theorem clique_structure :
    Function.Injective cliqueAssignments ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueAssignments r i)).card = 2) ∧
    (∀ i j, cliqueAdj i j = cliqueAdj j i) ∧
    (∀ i, cliqueAdj i i = false ∧ ∃ j, cliqueAdj i j = true) ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueF r i = .d01)).card =
        if (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 then 2 else 6) ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueF r i = .d00)).card =
        if (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 then 8 else 4) ∧
    (Finset.univ.filter (fun r => (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4)).card = 18 ∧
    (Finset.univ.filter (fun r => (cliquePairs r).1.val / 4 ≠ (cliquePairs r).2.val / 4)).card = 48 := by
  refine ⟨clique_assignment_injective, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    fin_cases r <;> decide +kernel
  · intro i j
    simp [cliqueAdj, ne_comm, eq_comm]
  · intro i
    fin_cases i <;> decide +kernel
  · intro r
    fin_cases r <;> decide +kernel
  · intro r
    fin_cases r <;> decide +kernel
  · decide +kernel
  · decide +kernel

/-- T32 construction verification: each retained bank is precisely 65
distinct profiles, excluding its omitted profile. -/
theorem clique_retained_injective (t : Fin 66) :
    Function.Injective (retainedAssignments t) ∧
      ∀ r, retainedAssignments t r ≠ cliqueAssignments t := by
  have hinj := clique_structure.1
  constructor
  · exact hinj.comp Fin.succAbove_right_injective
  · intro r he
    exact Fin.succAbove_ne t r (hinj he)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- T32(ii) finite arithmetic for exact probabilities: the first two moments
of the point estimate and the mean of the variance functional, computed
from true marginals and joints, give equality at 6050/11907. -/
theorem clique_exact_reduced_arithmetic :
    let m := cliqueObservationMarginal 0 false
    let J := cliqueObservationJoint 0 false
    let M := ((∑ i, m i .d01 / m i .d01) - (∑ i, m i .d00 / m i .d00)) / 12
    let S := (∑ i, ∑ j,
      (J i j .d01 .d01 / (m i .d01 * m j .d01) +
       J i j .d00 .d00 / (m i .d00 * m j .d00) -
       J i j .d01 .d00 / (m i .d01 * m j .d00) -
       J i j .d00 .d01 / (m i .d00 * m j .d01))) / 144
    M = 0 ∧ S - M^2 = 6050/11907 ∧ expectedVariance m J cliqueY m J .d01 .d00 = 6050/11907 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- T32(ii): with exact design probabilities, the clique estimator is
−220/189 on same-block profiles and 55/126 otherwise. -/
theorem clique_exact_profile_estimates :
    let m := cliqueObservationMarginal 0 false
    ∀ r, htContrast cliqueF cliqueY m .d01 .d00 r =
      if (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 then -220/189 else 55/126 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- T32(vi) finite arithmetic after conditional-moment reduction: the two
fixed representative banks have the stated variances and expected variance
estimates, and their exact strict differences. -/
theorem clique_fixed_reduced_arithmetic :
    cliqueConditionalSecond 0 false - (cliqueConditionalMean 0 false)^2 = 2810528137/5767941312 ∧
    cliqueConditionalV 0 false = 267260522663/634473544320 ∧
    cliqueConditionalV 0 false < cliqueConditionalSecond 0 false - (cliqueConditionalMean 0 false)^2 ∧
    cliqueConditionalSecond 3 false - (cliqueConditionalMean 3 false)^2 = 937589375/1922647104 ∧
    cliqueConditionalV 3 false = 4830430961/10574559072 ∧
    cliqueConditionalV 3 false < cliqueConditionalSecond 3 false - (cliqueConditionalMean 3 false)^2 ∧
    cliqueConditionalV 0 false - (cliqueConditionalSecond 0 false - (cliqueConditionalMean 0 false)^2) =
      -1551761941/23499020160 ∧
    cliqueConditionalV 3 false - (cliqueConditionalSecond 3 false - (cliqueConditionalMean 3 false)^2) =
      -72513467/2349902016 := by
  decide +kernel

/-- T32(vi): the two representative fixed banks, omitting (0,1) or (0,4),
have precisely the stated variances and expected variance estimates, and
both strictly underestimate the design variance. These are exact finite
counterexamples conditional on a table, using the same P045-T32/T33 functional. -/
theorem clique_fixed_table_counterexamples :
    designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 0) = 2810528137/5767941312 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 0) = 267260522663/634473544320 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 0) <
      designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 0) ∧
    designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 3) = 937589375/1922647104 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 3) = 4830430961/10574559072 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 3) <
      designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 3) := by
  have hM (t : Fin 66) : expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT t) = cliqueConditionalMean t false := by
    simpa only [clique_observation_independent_mass] using (clique_conditional_moments t false).1
  have hS (t : Fin 66) : expect (fun _ : Fin 66 => (1/66 : ℚ)) (fun z => cliqueT t z ^ 2) =
      cliqueConditionalSecond t false := by
    simpa only [clique_observation_independent_mass] using (clique_conditional_moments t false).2.1
  have hV (t : Fin 66) : expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV t) = cliqueConditionalV t false := by
    simpa only [clique_observation_independent_mass] using (clique_conditional_moments t false).2.2
  unfold designVariance
  simp_rw [hS, hM, hV]
  have h := clique_fixed_reduced_arithmetic
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- T32(ii): the exact design probabilities give zero HT mean, design
variance 6050/11907, and expected variance estimate equal to that variance.
This bridges the kernel arithmetic to actual finite randomization moments. -/
theorem clique_exact_moments :
    let p := fun _ : Fin 66 => (1/66 : ℚ)
    let m := marginal p cliqueF
    let J := joint p cliqueF
    let T := htContrast cliqueF cliqueY m .d01 .d00
    expect p T = 0 ∧ designVariance p T = 6050/11907 ∧
      expect p (varianceEstimate cliqueF cliqueY m J .d01 .d00) = 6050/11907 := by
  let p := fun _ : Fin 66 => (1/66 : ℚ)
  let m := cliqueObservationMarginal 0 false
  let J := cliqueObservationJoint 0 false
  let M := ((∑ i, m i .d01 / m i .d01) - (∑ i, m i .d00 / m i .d00)) / 12
  let S := (∑ i, ∑ j,
    (J i j .d01 .d01 / (m i .d01 * m j .d01) +
     J i j .d00 .d00 / (m i .d00 * m j .d00) -
     J i j .d01 .d00 / (m i .d01 * m j .d00) -
     J i j .d00 .d01 / (m i .d00 * m j .d01))) / 144
  have hm : marginal p cliqueF = m := by
    funext i a
    simpa only [p, m, clique_observation_independent_mass] using clique_observation_marginal 0 false i a
  have hkk (i j) : joint p cliqueF i j .d01 .d01 = J i j .d01 .d01 := by
    simpa only [p, J, clique_observation_independent_mass] using
      clique_observation_joint 0 false i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
  have hll (i j) : joint p cliqueF i j .d00 .d00 = J i j .d00 .d00 := by
    simpa only [p, J, clique_observation_independent_mass] using
      clique_observation_joint 0 false i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
  have hkl (i j) : joint p cliqueF i j .d01 .d00 = J i j .d01 .d00 := by
    simpa only [p, J, clique_observation_independent_mass] using
      clique_observation_joint 0 false i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  have hlk (i j) : joint p cliqueF i j .d00 .d01 = J i j .d00 .d01 := by
    simpa only [p, J, clique_observation_independent_mass] using
      clique_observation_joint 0 false i j .d00 .d01 (Or.inr rfl) (Or.inl rfl)
  have hmean : expect p (htContrast cliqueF cliqueY (marginal p cliqueF) .d01 .d00) = M := by
    unfold htContrast
    rw [expect_sub, htMean_expectation, htMean_expectation, hm]
    simp only [cliqueY, one_mul]
    unfold M
    ring
  have hsecond : expect p (fun r => htContrast cliqueF cliqueY (marginal p cliqueF) .d01 .d00 r ^ 2) = S := by
    rw [htContrast_second_moment, hm]
    simp_rw [hkk, hll, hkl, hlk]
    simp [cliqueY, S, div_eq_mul_inv, mul_inv_rev] <;> norm_num
  have hv : expect p (varianceEstimate cliqueF cliqueY (marginal p cliqueF) (joint p cliqueF) .d01 .d00) =
      expectedVariance m J cliqueY m J .d01 .d00 := by
    rw [varianceEstimate_expectation, hm]
    unfold expectedVariance expectedTotalVariance expectedTotalCovariance
    simp_rw [hkk, hll, hkl]
  have hnum : M = 0 ∧ S - M^2 = 6050/11907 ∧ expectedVariance m J cliqueY m J .d01 .d00 = 6050/11907 :=
    clique_exact_reduced_arithmetic
  refine ⟨hmean.trans hnum.1, ?_, hv.trans hnum.2.2⟩
  unfold designVariance
  rw [hsecond, hmean]
  exact hnum.2.1

/-- T32 probability-law verification: both (omitted,realized) laws are
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

/-- T32 enumeration verification: the list has exactly one occurrence of
 every increasing pair of distinct units, so its support is the complete
 treat-two randomization support rather than a smaller selected design. -/
theorem clique_pairs_complete :
    (∀ r, (cliquePairs r).1 < (cliquePairs r).2) ∧
    (∀ i j : Fin 12, i < j → ∃ r : Fin 66, cliquePairs r = (i,j)) := by
  constructor
  · intro r
    fin_cases r <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel

/-- T32 complete-design verification: an assignment treats exactly two units
 if and only if it is one of the explicitly enumerated 66 profiles. -/
theorem clique_complete_support (z : Assignment 12) :
    (Finset.univ.filter (fun i => z i)).card = 2 ↔ ∃ r, cliqueAssignments r = z := by
  constructor
  · intro hz
    obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp hz
    have hvec (r : Fin 66) (hr : cliquePairs r = (i,j) ∨ cliquePairs r = (j,i)) : cliqueAssignments r = z := by
      have hm (t : Fin 12) : z t = true ↔ t = i ∨ t = j := by
        calc
          z t = true ↔ t ∈ Finset.univ.filter (fun k => z k) := by simp
          _ ↔ t ∈ ({i,j} : Finset (Fin 12)) := by rw [hs]
          _ ↔ t = i ∨ t = j := by simp
      funext t
      unfold cliqueAssignments
      rcases hr with hr | hr <;> rw [hr]
      · cases ht : z t
        · have hn : ¬(t = i ∨ t = j) := by simpa [ht] using hm t
          simp [hn]
        · have hp := (hm t).mp ht
          simp [hp]
      · cases ht : z t
        · have hn : ¬(t = i ∨ t = j) := by simpa [ht] using hm t
          simp [hn, or_comm]
        · have hp := (hm t).mp ht
          simp [hp, or_comm]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · obtain ⟨r, hr⟩ := clique_pairs_complete.2 i j hlt
      exact ⟨r, hvec r (Or.inl hr)⟩
    · obtain ⟨r, hr⟩ := clique_pairs_complete.2 j i hgt
      exact ⟨r, hvec r (Or.inr hr)⟩
  · rintro ⟨r, rfl⟩
    exact clique_structure.2.1 r

/-- A two-point permutation used in T32's explicit symmetry witness: first
swap 0 to a, then send the resulting image of 1 to b. On the three- and
four-element sets used below, distinct a,b give the desired two images. -/
def twoImagePerm {n : ℕ} [NeZero n] (a b : Fin n) : Equiv.Perm (Fin n) :=
  let e := Equiv.swap 0 a
  e.trans (Equiv.swap (e 1) b)

/-- Permute the three clique labels, and independently permute the four
vertices of each source clique. This explicit product equivalence is used
only to verify the two representative-bank classes (T32(vi)). -/
def cliqueProductPerm (e : Equiv.Perm (Fin 3)) (u : Fin 3 → Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin 3 × Fin 4) where
  toFun x := (e x.1, u x.1 x.2)
  invFun x := (e.symm x.1, (u (e.symm x.1)).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- The explicit network-preserving relabeling that sends the representative
omitted pair (0,1) or (0,4) to the pair omitted by t in T32. -/
def cliqueRelabeling (t : Fin 66) : Equiv.Perm (Fin 12) :=
  let h := (finProdFinEquiv (m := 3) (n := 4)).symm
  let a := h (cliquePairs t).1
  let b := h (cliquePairs t).2
  let e := if a.1 = b.1 then Equiv.swap 0 a.1 else twoImagePerm a.1 b.1
  let u : Fin 3 → Equiv.Perm (Fin 4) := if a.1 = b.1 then fun _ => twoImagePerm a.2 b.2
    else fun r => if r = 0 then Equiv.swap 0 a.2 else if r = 1 then Equiv.swap 0 b.2 else Equiv.refl _
  h.trans ((cliqueProductPerm e u).trans h.symm)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- T32(vi): every omitted assignment becomes one of the two representative
omissions under an explicit permutation preserving the graph. All 18
same-block omissions use (0,1); all 48 other omissions use (0,4). -/
theorem clique_relabeling_verified :
    ∀ t : Fin 66,
      (∀ i j, cliqueAdj (cliqueRelabeling t i) (cliqueRelabeling t j) = cliqueAdj i j) ∧
      (∀ i, cliqueAssignments t (cliqueRelabeling t i) =
        cliqueAssignments (if (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4 then 0 else 3) i) ∧
      (∀ i, cliqueF t (cliqueRelabeling t i) =
        cliqueF (if (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4 then 0 else 3) i) := by
  intro t
  fin_cases t <;> decide +kernel

/-- Reindex both finite population sums by a single permutation,
without expanding any rational summand (T32's symmetry reduction). -/
theorem clique_pair_sum_relabel (e : Equiv.Perm (Fin 12)) (F : Fin 12 → Fin 12 → ℚ) :
    (∑ i, ∑ j, F i j) = ∑ i, ∑ j, F (e i) (e j) := by
  calc
    (∑ i, ∑ j, F i j) = ∑ i, ∑ j, F (e i) j := (Equiv.sum_comp e _).symm
    _ = ∑ i, ∑ j, F (e i) (e j) :=
      Finset.sum_congr rfl (fun i _ => (Equiv.sum_comp e (fun j => F (e i) j)).symm)

/-- T32: graph-preserving relabeling leaves each of the three conditional
moment formulas unchanged. It reduces all 66 banks to the two actual
representatives without assuming any moment or numerical equality. -/
theorem clique_conditional_relabel (t : Fin 66) (included : Bool) :
    let r : Fin 66 := if (cliquePairs t).1.val/4=(cliquePairs t).2.val/4 then 0 else 3
    cliqueConditionalMean t included=cliqueConditionalMean r included ∧
    cliqueConditionalSecond t included=cliqueConditionalSecond r included ∧
    cliqueConditionalV t included=cliqueConditionalV r included := by
  let r : Fin 66 := if (cliquePairs t).1.val/4=(cliquePairs t).2.val/4 then 0 else 3
  classical
  dsimp only
  let e := cliqueRelabeling t
  have hr := clique_relabeling_verified t
  have hF : ∀ i, cliqueF t (e i)=cliqueF r i := hr.2.2
  have heq : ∀ i j, e i=e j ↔ i=j := fun i j => e.injective.eq_iff
  have hsame : ∀ i j, (e i).val/4=(e j).val/4 ↔ i.val/4=j.val/4 := by
    intro i j
    by_cases hij : i=j
    · subst j
      simp
    · have hne : e i ≠ e j := e.injective.ne hij
      have hg0 : decide (e i ≠ e j ∧ (e i).val/4=(e j).val/4) =
          decide (i ≠ j ∧ i.val/4=j.val/4) := hr.1 i j
      have hg : decide ((e i).val/4=(e j).val/4) = decide (i.val/4=j.val/4) := by
        simpa [hij, hne] using hg0
      exact decide_eq_decide.mp hg
  have hc : ∀ i j a b, (a=Exposure.d01 ∨ a=.d00) → (b=Exposure.d01 ∨ b=.d00) →
      cliqueFullJoint (e i) (e j) a b=cliqueFullJoint i j a b := by
    intro i j a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals simp only [cliqueFullJoint, heq, hsame]
  have hw : ∀ i a, cliqueWeights t (e i) a=cliqueWeights r i a := by
    intro i a
    simp only [cliqueWeights, hF]
  have hm : ∀ i a, cliqueObservationMarginal t included (e i) a=
      cliqueObservationMarginal r included i a := by
    intro i a
    simp only [cliqueObservationMarginal, hF]
  have hJ : ∀ i j a b, (a=Exposure.d01 ∨ a=.d00) → (b=Exposure.d01 ∨ b=.d00) →
      cliqueObservationJoint t included (e i) (e j) a b=
        cliqueObservationJoint r included i j a b := by
    intro i j a b ha hb
    simp only [cliqueObservationJoint, hc i j a b ha hb, hF]
  have hq : ∀ i j a b, (a=Exposure.d01 ∨ a=.d00) → (b=Exposure.d01 ∨ b=.d00) →
      cliqueJoints t (e i) (e j) a b=cliqueJoints r i j a b := by
    intro i j a b ha hb
    simp only [cliqueJoints, hc i j a b ha hb, hF, heq]
  have hkk := fun i j => hJ i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
  have hll := fun i j => hJ i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
  have hkl := fun i j => hJ i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  have hlk := fun i j => hJ i j .d00 .d01 (Or.inr rfl) (Or.inl rfl)
  refine ⟨?_, ?_, ?_⟩
  · have hsum : ∀ a, (∑ i, cliqueObservationMarginal t included i a/cliqueWeights t i a) =
        ∑ i, cliqueObservationMarginal r included i a/cliqueWeights r i a := by
      intro a
      calc
        _ = ∑ i, cliqueObservationMarginal t included (e i) a/cliqueWeights t (e i) a :=
          (Equiv.sum_comp e _).symm
        _ = _ := by simp only [hm,hw]
    unfold cliqueConditionalMean
    rw [hsum,hsum]
  · unfold cliqueConditionalSecond
    rw [clique_pair_sum_relabel e]
    simp only [hkk,hll,hkl,hlk,hw]
    rfl
  · have hwithin : ∀ a, (a=Exposure.d01 ∨ a=.d00) →
        expectedTotalVariance (cliqueObservationMarginal t included)
          (cliqueObservationJoint t included) cliqueY (cliqueWeights t) (cliqueJoints t) a =
        expectedTotalVariance (cliqueObservationMarginal r included)
          (cliqueObservationJoint r included) cliqueY (cliqueWeights r) (cliqueJoints r) a := by
      intro a ha
      unfold expectedTotalVariance
      rw [clique_pair_sum_relabel e]
      simp only [hJ _ _ a a ha ha, hq _ _ a a ha ha, hm,hw,cliqueY, ne_eq,heq]
    have hcross : expectedTotalCovariance (cliqueObservationMarginal t included)
          (cliqueObservationJoint t included) cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00 =
        expectedTotalCovariance (cliqueObservationMarginal r included)
          (cliqueObservationJoint r included) cliqueY (cliqueWeights r) (cliqueJoints r) .d01 .d00 := by
      unfold expectedTotalCovariance
      rw [clique_pair_sum_relabel e]
      simp only [hkl, hq _ _ .d01 .d00 (Or.inl rfl) (Or.inr rfl),hm,hw,cliqueY]
    unfold cliqueConditionalV expectedVariance
    rw [hwithin .d01 (Or.inl rfl), hwithin .d00 (Or.inr rfl), hcross]

/-- T32: the uniform bank average of a statistic taking one value on the
18 same-clique omissions and another on the 48 different-clique omissions. -/
theorem clique_two_class_expect (F : Fin 66 → ℚ) (a b : ℚ)
    (hF : ∀ t, F t=if (cliquePairs t).1.val/4=(cliquePairs t).2.val/4 then a else b) :
    expect (fun _ : Fin 66 => (1/66 : ℚ)) F=(18*a+48*b)/66 := by
  simp only [expect]
  simp_rw [hF, mul_ite]
  rw [Finset.sum_ite]
  have hsame := clique_structure.2.2.2.2.2.2.1
  have hdiff := clique_structure.2.2.2.2.2.2.2
  simp only [Finset.sum_const, nsmul_eq_mul, hsame, hdiff]
  norm_num
  ring

set_option maxRecDepth 4096 in
/-- T32(iii)–(v): rational arithmetic on two representative conditional
moments, weighted 18/66 and 48/66, gives all six numerical values and
both strict underestimates. The preceding relabeling proves that these
are the actual full-bank averages. -/
theorem clique_two_representative_arithmetic :
    let M := fun included => (18*cliqueConditionalMean 0 included+48*cliqueConditionalMean 3 included)/66
    let S := fun included => (18*cliqueConditionalSecond 0 included+48*cliqueConditionalSecond 3 included)/66
    let V := fun included => (18*cliqueConditionalV 0 included+48*cliqueConditionalV 3 included)/66
    M false = -67/53592 ∧ S false-M false^2 = 113448938731/232640299584 ∧
    V false = 1040129476423/2326402995840 ∧
    M true = -67/52780 ∧ S true-M true^2 = 11375808887/23342482800 ∧
    V true = 4673362763/10414338480 ∧
    (∀ included, V included < S included-M included^2 ∧ V included < 6050/11907) := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- T32 arithmetic after exact finite-moment reduction: the conditional
moments averaged over all 66 omitted profiles give the two stated laws'
means, variances, expected variance estimates, and strict shortfalls. -/
theorem clique_reduced_arithmetic :
    let U := fun _ : Fin 66 => (1/66 : ℚ)
    let M := fun included => expect U (fun t => cliqueConditionalMean t included)
    let S := fun included => expect U (fun t => cliqueConditionalSecond t included)
    let V := fun included => expect U (fun t => cliqueConditionalV t included)
    M false = -67/53592 ∧ S false - M false ^ 2 = 113448938731/232640299584 ∧
    V false = 1040129476423/2326402995840 ∧
    M true = -67/52780 ∧ S true - M true ^ 2 = 11375808887/23342482800 ∧
    V true = 4673362763/10414338480 ∧
    (∀ included, V included < S included - M included ^ 2 ∧ V included < 6050/11907) := by
  dsimp only
  have hM : ∀ included, expect (fun _ : Fin 66 => (1/66 : ℚ))
      (fun t => cliqueConditionalMean t included) =
      (18*cliqueConditionalMean 0 included+48*cliqueConditionalMean 3 included)/66 := by
    intro included
    apply clique_two_class_expect
    intro t
    have h := (clique_conditional_relabel t included).1
    split_ifs with hs <;> simpa only [hs,ite_true,ite_false] using h
  have hS : ∀ included, expect (fun _ : Fin 66 => (1/66 : ℚ))
      (fun t => cliqueConditionalSecond t included) =
      (18*cliqueConditionalSecond 0 included+48*cliqueConditionalSecond 3 included)/66 := by
    intro included
    apply clique_two_class_expect
    intro t
    have h := (clique_conditional_relabel t included).2.1
    split_ifs with hs <;> simpa only [hs,ite_true,ite_false] using h
  have hV : ∀ included, expect (fun _ : Fin 66 => (1/66 : ℚ))
      (fun t => cliqueConditionalV t included) =
      (18*cliqueConditionalV 0 included+48*cliqueConditionalV 3 included)/66 := by
    intro included
    apply clique_two_class_expect
    intro t
    have h := (clique_conditional_relabel t included).2.2
    split_ifs with hs <;> simpa only [hs,ite_true,ite_false] using h
  simp_rw [hM,hS,hV]
  exact clique_two_representative_arithmetic

/-- T32(iii)–(v): exact rational computation on all 4356 independent or 4290
included (omitted,realized) pairs. Inputs are the omission formulas, whose
separate bridge to the enumerated package bank is clique_retained_weights. -/
theorem clique_joint_moments :
    expect (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = -67/53592 ∧
    designVariance (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = 113448938731/232640299584 ∧
    expect (cliqueJointMass false) (fun x => cliqueV x.1 x.2) = 1040129476423/2326402995840 ∧
    expect (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = -67/52780 ∧
    designVariance (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = 11375808887/23342482800 ∧
    expect (cliqueJointMass true) (fun x => cliqueV x.1 x.2) = 4673362763/10414338480 ∧
    (∀ included,
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) <
        designVariance (cliqueJointMass included) (fun x => cliqueT x.1 x.2) ∧
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) < 6050/11907) := by
  have hM (included : Bool) : expect (cliqueJointMass included) (fun x => cliqueT x.1 x.2) =
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (fun t => cliqueConditionalMean t included) := by
    rw [clique_joint_expectation included cliqueT]
    congr 1
    funext t
    exact (clique_conditional_moments t included).1
  have hS (included : Bool) : expect (cliqueJointMass included) (fun x => cliqueT x.1 x.2 ^ 2) =
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (fun t => cliqueConditionalSecond t included) := by
    rw [clique_joint_expectation included (fun t z => cliqueT t z ^ 2)]
    congr 1
    funext t
    exact (clique_conditional_moments t included).2.1
  have hV (included : Bool) : expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) =
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (fun t => cliqueConditionalV t included) := by
    rw [clique_joint_expectation included cliqueV]
    congr 1
    funext t
    exact (clique_conditional_moments t included).2.2
  unfold designVariance
  simp_rw [hM, hS, hV]
  exact clique_reduced_arithmetic

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- T32(vi): the exact conditional-moment formula verifies every fixed
bank, according to its same-clique or different-clique omitted pair.
This finite certificate uses only 66 sums of 144 ordered-pair terms,
rather than recomputing every variance functional on all observations. -/
theorem clique_all_fixed_reduced_arithmetic :
    ∀ t : Fin 66,
      let same := (cliquePairs t).1.val/4=(cliquePairs t).2.val/4
      cliqueConditionalSecond t false-(cliqueConditionalMean t false)^2 =
        (if same then 2810528137/5767941312 else 937589375/1922647104) ∧
      cliqueConditionalV t false =
        (if same then 267260522663/634473544320 else 4830430961/10574559072) ∧
      cliqueConditionalV t false-
        (cliqueConditionalSecond t false-(cliqueConditionalMean t false)^2) =
        (if same then -1551761941/23499020160 else -72513467/2349902016) ∧
      cliqueConditionalV t false <
        cliqueConditionalSecond t false-(cliqueConditionalMean t false)^2 := by
  intro t
  have h := clique_conditional_relabel t false
  dsimp only at h
  by_cases hs : (cliquePairs t).1.val/4=(cliquePairs t).2.val/4
  · simp only [hs,ite_true] at h ⊢
    rw [h.1,h.2.1,h.2.2]
    decide +kernel
  · simp only [hs,ite_false] at h ⊢
    rw [h.1,h.2.1,h.2.2]
    decide +kernel

/-- T32(vi): every fixed bank of 65 assignments underestimates the variance
over an independent complete-randomization observation. The exact variance,
expected variance estimate, and negative difference depend only on whether
the omitted pair shares a clique. This states the universal conclusion in
a counterexample to an exact finite-simulation extension of p. 298,
not to its contextual exact-probability guarantee. -/
theorem clique_all_fixed_table_counterexamples :
    ∀ t : Fin 66,
      let same := (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4
      designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT t) =
        (if same then 2810528137/5767941312 else 937589375/1922647104) ∧
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV t) =
        (if same then 267260522663/634473544320 else 4830430961/10574559072) ∧
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV t) -
        designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT t) =
        (if same then -1551761941/23499020160 else -72513467/2349902016) ∧
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV t) <
        designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT t) := by
  intro t
  have h := clique_conditional_moments t false
  simp only [clique_observation_independent_mass] at h
  unfold designVariance
  rw [h.1,h.2.1,h.2.2]
  exact clique_all_fixed_reduced_arithmetic t

/-- T32: every hypothesis of the explicit twelve-unit counterexample, and
its exact design and simulated-bank means, variances, expected variance
estimates, strict shortfalls in both sampling regimes, and the two fixed
representative tables. Counterexample to an exact finite-simulation extension
of p. 298; it concerns HT only. -/
theorem clique_variance_counterexample :
    cliqueF = (fun r => exposure cliqueAdj (cliqueAssignments r)) ∧
    (∀ z : Assignment 12, (Finset.univ.filter (fun i => z i)).card = 2 ↔ ∃ r, cliqueAssignments r = z) ∧
    (∀ i j, cliqueAdj i j = cliqueAdj j i) ∧
    Function.Injective cliqueAssignments ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueAssignments r i)).card = 2) ∧
    (∀ i, cliqueAdj i i = false ∧ ∃ j, cliqueAdj i j = true) ∧
    (∀ i, marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i .d01 = 9/22 ∧
      marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i .d00 = 14/33) ∧
    (∀ t, Function.Injective (retainedAssignments t) ∧
      (∀ r, retainedAssignments t r ≠ cliqueAssignments t)) ∧
    (∀ t i, 0 < (smoothedWeight (retainedF t) i .d01 : ℚ) ∧
      0 < (smoothedWeight (retainedF t) i .d00 : ℚ)) ∧
    tau cliqueY .d01 .d00 = 0 ∧
    (let w := marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF
     let q := joint (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF
     let T := htContrast cliqueF cliqueY w .d01 .d00
     expect (fun _ : Fin 66 => (1/66 : ℚ)) T = 0 ∧
     designVariance (fun _ : Fin 66 => (1/66 : ℚ)) T = 6050/11907 ∧
     expect (fun _ : Fin 66 => (1/66 : ℚ))
       (varianceEstimate cliqueF cliqueY w q .d01 .d00) = 6050/11907) ∧
    expect (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = -67/53592 ∧
    designVariance (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = 113448938731/232640299584 ∧
    expect (cliqueJointMass false) (fun x => cliqueV x.1 x.2) = 1040129476423/2326402995840 ∧
    expect (cliqueJointMass false) (fun x => cliqueV x.1 x.2) -
      designVariance (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = -953130413/23499020160 ∧
    expect (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = -67/52780 ∧
    designVariance (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = 11375808887/23342482800 ∧
    expect (cliqueJointMass true) (fun x => cliqueV x.1 x.2) = 4673362763/10414338480 ∧
    expect (cliqueJointMass true) (fun x => cliqueV x.1 x.2) -
      designVariance (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = -20161943/522324075 ∧
    (∀ included,
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) <
        designVariance (cliqueJointMass included) (fun x => cliqueT x.1 x.2) ∧
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) < 6050/11907) ∧
    designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 0) = 2810528137/5767941312 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 0) = 267260522663/634473544320 ∧
    designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 3) = 937589375/1922647104 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 3) = 4830430961/10574559072 := by
  have hs := clique_structure
  have hj := clique_joint_moments
  have hf := clique_fixed_table_counterexamples
  have hprob (i : Fin 12) :
      marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i .d01 = 9/22 ∧
      marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i .d00 = 14/33 := by
    have hk := clique_observation_marginal 0 false i .d01
    have hl := clique_observation_marginal 0 false i .d00
    rw [clique_observation_independent_mass] at hk hl
    norm_num [cliqueObservationMarginal, cliqueFullCount] at hk hl
    exact ⟨hk, hl⟩
  have hpos (t : Fin 66) (i : Fin 12) :
      0 < (smoothedWeight (retainedF t) i .d01 : ℚ) ∧ 0 < (smoothedWeight (retainedF t) i .d00 : ℚ) := by
    rw [← clique_retained_weights.1 t i .d01, ← clique_retained_weights.1 t i .d00]
    unfold cliqueWeights cliqueFullCount
    split_ifs <;> norm_num
  refine ⟨cliqueF_is_exposure, clique_complete_support, hs.2.2.1, hs.1, hs.2.1, hs.2.2.2.1, hprob, clique_retained_injective, hpos, ?_,
    clique_exact_moments, hj.1, hj.2.1, hj.2.2.1, ?_,
    hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, ?_, hj.2.2.2.2.2.2,
    hf.1, hf.2.1, hf.2.2.2.1, hf.2.2.2.2.1⟩
  · simp [tau, cliqueY]
  · rw [hj.2.2.1, hj.2.1]
    norm_num
  · rw [hj.2.2.2.2.2.1, hj.2.2.2.2.1]
    norm_num

/-- The exact rational randomization expectation agrees with the real
paper expectation after canonical embedding. This certifies the scalar
model used by the numerical counterexample in T32. -/
theorem ratCast_expect {Ω : Type*} [Fintype Ω] (p t : Ω → ℚ) :
    expect (fun ω => (p ω : ℝ)) (fun ω => (t ω : ℝ)) = ((expect p t : ℚ) : ℝ) := by
  simp only [expect, Rat.cast_sum, Rat.cast_mul]

/-- Rational randomization variance embeds as the identical real variance,
including the square of the unconditional randomization mean (T32). -/
theorem ratCast_designVariance {Ω : Type*} [Fintype Ω] (p t : Ω → ℚ) :
    designVariance (fun ω => (p ω : ℝ)) (fun ω => (t ω : ℝ)) = ((designVariance p t : ℚ) : ℝ) := by
  unfold designVariance
  simp only [Rat.cast_sub, Rat.cast_pow, ← ratCast_expect]


/-- HT unit contributions in rational witnesses are exactly the real
paper contributions after embedding (T32). -/
theorem ratCast_htTerm {Ω D : Type*} {N : ℕ} [DecidableEq D]
    (f : Ω → Fin N → D) (y w : Fin N → D → ℚ) (a : D) (ω : Ω) (i : Fin N) :
    htTerm f (fun i d => (y i d : ℝ)) (fun i d => (w i d : ℝ)) a ω i =
      ((htTerm f y w a ω i : ℚ) : ℝ) := by
  unfold htTerm
  split_ifs <;> simp only [Rat.cast_div, Rat.cast_zero]

/-- The HT exposure mean commutes with the rational-to-real embedding,
with the original population denominator N (P045-T32/T33). -/
theorem ratCast_htMean {Ω D : Type*} {N : ℕ} [DecidableEq D]
    (f : Ω → Fin N → D) (y w : Fin N → D → ℚ) (a : D) (ω : Ω) :
    htMean f (fun i d => (y i d : ℝ)) (fun i d => (w i d : ℝ)) a ω =
      ((htMean f y w a ω : ℚ) : ℝ) := by
  simp only [htMean, ratCast_htTerm, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]

/-- The HT effect contrast in rational witnesses is the real paper contrast
at canonically embedded outcomes and probability inputs (P045-T32/T33). -/
theorem ratCast_htContrast {Ω D : Type*} {N : ℕ} [DecidableEq D]
    (f : Ω → Fin N → D) (y w : Fin N → D → ℚ) (a b : D) (ω : Ω) :
    htContrast f (fun i d => (y i d : ℝ)) (fun i d => (w i d : ℝ)) a b ω =
      ((htContrast f y w a b ω : ℚ) : ℝ) := by
  simp only [htContrast, ratCast_htMean, Rat.cast_sub]

/-- The implemented variance functional commutes with rational-to-real
embedding, preserving the positive-joint and structural-zero guards and
all P045-T32/T33 denominators (T32). -/
theorem ratCast_varianceEstimate {Ω D : Type*} {N : ℕ} [DecidableEq D]
    (f : Ω → Fin N → D) (y w : Fin N → D → ℚ)
    (q : Fin N → Fin N → D → D → ℚ) (a b : D) (ω : Ω) :
    varianceEstimate f (fun i d => (y i d : ℝ)) (fun i d => (w i d : ℝ))
      (fun i j d e => (q i j d e : ℝ)) a b ω = ((varianceEstimate f y w q a b ω : ℚ) : ℝ) := by
  simp only [varianceEstimate, totalVarianceEstimate, totalCovarianceEstimate,
    Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_add,
    Rat.cast_sub, Rat.cast_mul, Rat.cast_one, Rat.cast_zero, Rat.cast_ofNat,
    apply_ite, Rat.cast_pos, Rat.cast_eq_zero]

/-- T32's strict counterexample in the paper's real scalar type. Both actual
joint randomization laws are nonnegative and normalized; using the same
point and variance functionals with real outcomes and real table inputs,
the expected variance estimate is below both the point estimator's actual
variance and the exact-probability variance 6050/11907. Counterexample to an
exact finite-simulation extension of p. 298. -/
theorem clique_real_variance_shortfall :
    ∀ included : Bool,
      (∀ x, 0 ≤ (cliqueJointMass included x : ℝ)) ∧
      (∑ x, (cliqueJointMass included x : ℝ)) = 1 ∧
      (let p := fun x => (cliqueJointMass included x : ℝ)
       let T := fun x : Fin 66 × Fin 66 =>
         htContrast cliqueF (fun i a => (cliqueY i a : ℝ))
           (fun i a => (cliqueWeights x.1 i a : ℝ)) .d01 .d00 x.2
       let V := fun x : Fin 66 × Fin 66 =>
         varianceEstimate cliqueF (fun i a => (cliqueY i a : ℝ))
           (fun i a => (cliqueWeights x.1 i a : ℝ))
           (fun i j a b => (cliqueJoints x.1 i j a b : ℝ)) .d01 .d00 x.2
       expect p V < designVariance p T ∧ expect p V < 6050/11907) := by
  intro included
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact_mod_cast clique_probability_laws.1 included x
  · exact_mod_cast clique_probability_laws.2.1 included
  · dsimp only
    have hT : (fun x : Fin 66 × Fin 66 =>
        htContrast cliqueF (fun i a => (cliqueY i a : ℝ))
          (fun i a => (cliqueWeights x.1 i a : ℝ)) .d01 .d00 x.2) =
        (fun x => (cliqueT x.1 x.2 : ℝ)) := by
      funext x
      exact ratCast_htContrast cliqueF cliqueY (cliqueWeights x.1) .d01 .d00 x.2
    have hV : (fun x : Fin 66 × Fin 66 =>
        varianceEstimate cliqueF (fun i a => (cliqueY i a : ℝ))
          (fun i a => (cliqueWeights x.1 i a : ℝ))
          (fun i j a b => (cliqueJoints x.1 i j a b : ℝ)) .d01 .d00 x.2) =
        (fun x => (cliqueV x.1 x.2 : ℝ)) := by
      funext x
      exact ratCast_varianceEstimate cliqueF cliqueY (cliqueWeights x.1)
        (cliqueJoints x.1) .d01 .d00 x.2
    rw [hT, hV, ratCast_expect, ratCast_designVariance]
    have h := clique_joint_moments.2.2.2.2.2.2 included
    constructor
    · exact Rat.cast_lt.mpr h.1
    · calc
        _ < ((6050/11907 : ℚ) : ℝ) := Rat.cast_lt.mpr h.2
        _ = 6050/11907 := by norm_num


end

end AronowAudit.P045.ExposureVariance
