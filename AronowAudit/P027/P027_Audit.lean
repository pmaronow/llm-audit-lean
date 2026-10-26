import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Formalization of claims in Aronow and Samii (2013), P027.
The sample distribution is finite, genuine and normalized; outcomes are fixed.
Ordered pairs are used throughout, including the diagonal in the HT estimator.
-/
namespace AronowAudit.P027
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

/-- A sampling design on a finite population: "a population U indexed by
1, ..., N ... a sampling design" (main pp. 232–233). `selected` is the sampled
subset at each atom; `weight` is its probability. Duplicate sample atoms and
zero-weight atoms are allowed and have no effect on expectations. -/
structure Design (U Ω : Type) [Fintype U] [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1
  selected : Ω → U → Bool

variable {U Ω : Type} [Fintype U] [Fintype Ω]

/-- "E" over the sampling design alone, the indicators being "the only
stochastic component" (main p. 233): a normalized weighted finite sum. -/
def expect (D : Design U Ω) (f : Ω → ℝ) : ℝ := ∑ ω, D.weight ω * f ω

/-- "I_k ∈ {0,1} is unit k's inclusion indicator" (main p. 233). -/
def indicator (D : Design U Ω) (ω : Ω) (k : U) : ℝ :=
  if D.selected ω k then 1 else 0

/-- "E(I_k) = π_k" (main p. 233). -/
def pi (D : Design U Ω) (k : U) : ℝ := expect D (fun ω => indicator D ω k)

/-- "Define E(I_k I_l) = π_kl" (main p. 233). -/
def joint (D : Design U Ω) (k l : U) : ℝ :=
  expect D (fun ω => indicator D ω k * indicator D ω l)

/-- "Condition 1 holds, as we assume throughout": π_k > 0 (main p. 233). -/
def Positive (D : Design U Ω) : Prop := ∀ k, 0 < pi D k

/-- Cov(I_k,I_l) = π_kl - π_k π_l (main pp. 233–234). -/
def inclusionCov (D : Design U Ω) (k l : U) : ℝ := joint D k l - pi D k * pi D l

/-- Design variance of a random variable, with its actual design mean; main
p. 233's Var(t-hat), not a freely chosen covariance expression. -/
def variance (D : Design U Ω) (f : Ω → ℝ) : ℝ :=
  expect D (fun ω => (f ω - expect D f)^2)

/-- "t-hat = ∑_{k∈U} I_k y_k/π_k" (main p. 233). -/
def htTotal (D : Design U Ω) (y : U → ℝ) (ω : Ω) : ℝ :=
  ∑ k, indicator D ω k * (y k / pi D k)

/-- "mu-hat_HT ≡ (1/N)t-hat" (supplement p. A1). -/
def htMean (D : Design U Ω) (y : U → ℝ) (ω : Ω) : ℝ :=
  htTotal D y ω / Fintype.card U

/-- The uncorrected HT variance estimator on s⁰: the proof of Proposition 1
uses ∑_k ∑_{l:π_kl>0} I_k I_l Cov(I_k,I_l)/π_kl · y_k/π_k · y_l/π_l
(main p. 234). Includes diagonal terms. -/
def htVarianceEstimator (D : Design U Ω) (y : U → ℝ) (ω : Ω) : ℝ :=
  ∑ k, ∑ l, if 0 < joint D k l then
    indicator D ω k * indicator D ω l * (inclusionCov D k l / joint D k l) *
      (y k / pi D k) * (y l / pi D l) else 0

/-- "A = ∑_k ∑_{l∈{U\k:π_kl=0}} y_k y_l" (main p. 234):
ordered DISTINCT pairs, with the minus sign outside the underbrace. -/
def biasA (D : Design U Ω) (y : U → ℝ) : ℝ :=
  ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then y k * y l else 0

/-- "A* = ∑ ... |y_k|^a_kl/a_kl + |y_l|^b_kl/b_kl" (main p. 236).
Both fractions are inside the ordered-pair sum; powers are real powers. -/
def youngA (D : Design U Ω) (y : U → ℝ) (a b : U → U → ℝ) : ℝ :=
  ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then
    |y k| ^ (a k l) / a k l + |y l| ^ (b k l) / b k l else 0

/-- "A-hat*" is the HT estimator of A* (main p. 236). -/
def youngCorrection (D : Design U Ω) (y : U → ℝ) (a b : U → U → ℝ)
    (ω : Ω) : ℝ :=
  ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then
    indicator D ω k * (|y k| ^ (a k l) / (a k l * pi D k)) +
    indicator D ω l * (|y l| ^ (b k l) / (b k l * pi D l)) else 0

/-- "Var-hat_C(t-hat)" is the HT part plus A-hat* (main p. 235). -/
def conservativeEstimator (D : Design U Ω) (y : U → ℝ) (a b : U → U → ℝ)
    (ω : Ω) : ℝ := htVarianceEstimator D y ω + youngCorrection D y a b ω

/-- "assigning all a_kl = b_kl = 2" gives Var-hat_C2 (main p. 237).
The polynomial spelling makes explicit the printed y_k² terms. -/
def quadraticCorrection (D : Design U Ω) (y : U → ℝ) (ω : Ω) : ℝ :=
  ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then
    indicator D ω k * (y k ^ 2 / (2 * pi D k)) +
    indicator D ω l * (y l ^ 2 / (2 * pi D l)) else 0

/-- Var-hat_C2 (main p. 237). -/
def c2Estimator (D : Design U Ω) (y : U → ℝ) (ω : Ω) : ℝ :=
  htVarianceEstimator D y ω + quadraticCorrection D y ω

/-- A* at exponents 2, used in the proof of Corollary 2 (main p. 237). -/
def quadraticA (D : Design U Ω) (y : U → ℝ) : ℝ :=
  ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then (y k ^ 2 + y l ^ 2) / 2 else 0

/-- The WR comparator: 1/(N²m(m−1)) ∑_{k∈s⁰}(y_k/p_k−t-hat)²,
p_k = π_k/m (supplement p. A3). -/
def wrEstimator (D : Design U Ω) (y : U → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  (∑ k, indicator D ω k * (y k / (pi D k / m) - htTotal D y ω)^2) /
    ((Fintype.card U : ℝ)^2 * m * (m - 1 : ℝ))

/-- Expectation is linear in a finite sum (the printed proofs of Props. 1–2). -/
theorem expect_sum {K : Type} [Fintype K] (D : Design U Ω) (f : K → Ω → ℝ) :
    expect D (fun ω => ∑ k, f k ω) = ∑ k, expect D (f k) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- Linearity in two summands (main p. 236). -/
theorem expect_add (D : Design U Ω) (f g : Ω → ℝ) :
    expect D (fun ω => f ω + g ω) = expect D f + expect D g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

/-- Constant multipliers can be moved through design expectation. -/
theorem expect_mul_const (D : Design U Ω) (f : Ω → ℝ) (c : ℝ) :
    expect D (fun ω => f ω * c) = expect D f * c := by
  unfold expect
  simp_rw [← mul_assoc]
  exact (Finset.sum_mul _ _ _).symm

/-- The normalized design expectation of a constant is the constant. -/
theorem expect_const (D : Design U Ω) (c : ℝ) : expect D (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, D.total]

/-- Inclusion indicators are nonnegative (main p. 233). -/
theorem indicator_nonneg (D : Design U Ω) (ω : Ω) (k : U) :
    0 ≤ indicator D ω k := by unfold indicator; split <;> norm_num

/-- First-order inclusion probabilities cannot exceed one (main p. 233). -/
theorem pi_le_one (D : Design U Ω) (k : U) : pi D k ≤ 1 := by
  rw [pi, expect, ← D.total]
  apply Finset.sum_le_sum
  intro ω _
  have h : indicator D ω k ≤ 1 := by unfold indicator; split <;> norm_num
  nlinarith [D.nonneg ω]

/-- Joint probabilities are nonnegative, since they are expectations of
products of Bernoulli indicators (main p. 233). -/
theorem joint_nonneg (D : Design U Ω) (k l : U) : 0 ≤ joint D k l := by
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (D.nonneg ω) (mul_nonneg (indicator_nonneg D ω k)
    (indicator_nonneg D ω l))

/-- "π_kk = π_k by construction" (main p. 233). -/
theorem joint_self (D : Design U Ω) (k : U) : joint D k k = pi D k := by
  unfold joint pi expect indicator
  congr 1; funext ω; dsimp; split <;> simp

/-- π_kl = π_lk, used by Corollary 3's ordered-pair symmetrisation. -/
theorem joint_symm (D : Design U Ω) (k l : U) : joint D k l = joint D l k := by
  unfold joint; simp only [mul_comm]

/-- The actual weighted variance equals the second moment minus mean². -/
theorem variance_second_moment (D : Design U Ω) (f : Ω → ℝ) :
    variance D f = expect D (fun ω => f ω ^ 2) - (expect D f)^2 := by
  have hp : (fun ω => (f ω - expect D f)^2) =
      (fun ω => f ω ^ 2 + (f ω * (-2 * expect D f) + (expect D f)^2)) := by
    funext ω; ring
  rw [variance, hp, expect_add, expect_add, expect_mul_const, expect_const]
  ring

/-- Unbiasedness of the HT total under condition 1 (main p. 233). -/
theorem ht_unbiased (D : Design U Ω) (h : Positive D) (y : U → ℝ) :
    expect D (htTotal D y) = ∑ k, y k := by
  unfold htTotal
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [expect_mul_const]
  change pi D k * (y k / pi D k) = y k
  field_simp [(h k).ne']

/-- The variance double-sum identity of Section 2.1 (main p. 233),
proved from the sampling distribution rather than assumed. -/
theorem ht_variance_identity (D : Design U Ω) (h : Positive D) (y : U → ℝ) :
    variance D (htTotal D y) =
      ∑ k, ∑ l, inclusionCov D k l * (y k / pi D k) * (y l / pi D l) := by
  rw [variance_second_moment]
  have hs : (fun ω => htTotal D y ω ^ 2) =
      (fun ω => ∑ k, ∑ l, (indicator D ω k * indicator D ω l) *
        ((y k / pi D k) * (y l / pi D l))) := by
    funext ω
    simp only [htTotal, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _; ring
  rw [hs, expect_sum]
  simp only [expect_sum, expect_mul_const]
  have hm : expect D (htTotal D y) = ∑ k, pi D k * (y k / pi D k) := by
    unfold htTotal
    rw [expect_sum]
    simp only [expect_mul_const, pi]
  rw [hm]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    inclusionCov, joint]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _; ring

/-- Expectation of the uncorrected estimator cancels each positive π_kl,
as in Proposition 1's proof (main p. 234). -/
theorem expected_ht_estimator (D : Design U Ω) (h : Positive D) (y : U → ℝ) :
    expect D (htVarianceEstimator D y) =
      ∑ k, ∑ l, if 0 < joint D k l then
        inclusionCov D k l * (y k / pi D k) * (y l / pi D l) else 0 := by
  unfold htVarianceEstimator
  rw [expect_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [expect_sum]
  apply Finset.sum_congr rfl; intro l _
  split_ifs with hkl
  · simp only [expect_mul_const]
    change joint D k l * (inclusionCov D k l / joint D k l) *
      (y k / pi D k) * (y l / pi D l) = _
    rw [mul_div_cancel₀ _ hkl.ne']
  · exact expect_const D 0

/-- Proposition 1: E[Var-hat(t-hat)] = Var(t-hat) + A (main p. 234).
Valid also when the zero-pair set is empty. -/
theorem proposition1 (D : Design U Ω) (h : Positive D) (y : U → ℝ) :
    expect D (htVarianceEstimator D y) = variance D (htTotal D y) + biasA D y := by
  rw [expected_ht_estimator D h, ht_variance_identity D h, biasA, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l _
  by_cases hkl : 0 < joint D k l
  · have hn : joint D k l ≠ 0 := hkl.ne'
    simp [hkl, hn]
  · have hz : joint D k l = 0 := le_antisymm (le_of_not_gt hkl) (joint_nonneg D k l)
    have hn : k ≠ l := by
      intro he; subst l; rw [joint_self] at hz; exact (h k).ne' hz
    simp only [inclusionCov, hz, hn, and_self, ite_true, zero_sub]
    norm_num [hn]
    field_simp [(h k).ne', (h l).ne']
    <;> ring

/-- Proposition 1's same-sign conclusion: A ≥ 0 if all fixed outcomes are
nonnegative or all are nonpositive (main p. 234). -/
theorem biasA_same_sign (D : Design U Ω) (h : Positive D) (y : U → ℝ)
    (hs : (∀ k, 0 ≤ y k) ∨ (∀ k, y k ≤ 0)) : 0 ≤ biasA D y := by
  apply Finset.sum_nonneg; intro k _
  apply Finset.sum_nonneg; intro l _
  split_ifs
  · rcases hs with hs | hs
    · exact mul_nonneg (hs k) (hs l)
    · exact mul_nonneg_of_nonpos_of_nonpos (hs k) (hs l)
  · exact le_rfl

/-- E[A-hat*] = A*, the unbiasedness step in Proposition 2 (main p. 236). -/
theorem expected_young_correction (D : Design U Ω) (h : Positive D) (y : U → ℝ)
    (a b : U → U → ℝ)
    (hab : ∀ k l, k ≠ l ∧ joint D k l = 0 → (a k l).HolderConjugate (b k l)) :
    expect D (youngCorrection D y a b) = youngA D y a b := by
  unfold youngCorrection youngA
  rw [expect_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [expect_sum]
  apply Finset.sum_congr rfl; intro l _
  split_ifs
  · rw [expect_add, expect_mul_const, expect_mul_const]
    change pi D k * _ + pi D l * _ = _
    by_cases ha : a k l = 0 <;> by_cases hb : b k l = 0 <;>
      (try simp [ha, hb]) <;> field_simp [(h k).ne', (h l).ne']
  · exact expect_const D 0

/-- A* ≥ A and A* ≥ −A, from Young's inequality, including arbitrary
signs and ordered, possibly asymmetric exponents (main p. 236). -/
theorem young_bounds (D : Design U Ω) (h : Positive D) (y : U → ℝ) (a b : U → U → ℝ)
    (hab : ∀ k l, k ≠ l ∧ joint D k l = 0 → (a k l).HolderConjugate (b k l)) :
    biasA D y ≤ youngA D y a b ∧ -biasA D y ≤ youngA D y a b := by
  constructor
  · apply Finset.sum_le_sum; intro k _
    apply Finset.sum_le_sum; intro l _
    split_ifs with hz
    · exact Real.young_inequality (y k) (y l) (hab k l hz)
    · exact le_rfl
  · unfold biasA youngA
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum; intro k _
    apply Finset.sum_le_sum; intro l _
    split_ifs with hz
    · have hy := Real.young_inequality (-(y k)) (y l) (hab k l hz)
      simpa using hy
    · norm_num

/-- Proposition 2's exact expectation identity, main p. 236. -/
theorem conservative_expectation (D : Design U Ω) (h : Positive D) (y : U → ℝ)
    (a b : U → U → ℝ)
    (hab : ∀ k l, k ≠ l ∧ joint D k l = 0 → (a k l).HolderConjugate (b k l)) :
    expect D (conservativeEstimator D y a b) =
      variance D (htTotal D y) + biasA D y + youngA D y a b := by
  unfold conservativeEstimator
  rw [expect_add, proposition1 D h, expected_young_correction D h y a b hab]

/-- Proposition 2: E[Var-hat_C(t-hat)] ≥ Var(t-hat) (main pp. 235–236),
with positive conjugate exponents at every ordered zero-inclusion pair. -/
theorem proposition2 (D : Design U Ω) (h : Positive D) (y : U → ℝ)
    (a b : U → U → ℝ)
    (hab : ∀ k l, k ≠ l ∧ joint D k l = 0 → (a k l).HolderConjugate (b k l)) :
    variance D (htTotal D y) ≤ expect D (conservativeEstimator D y a b) := by
  rw [conservative_expectation D h y a b hab]
  have hy := (young_bounds D h y a b hab).2
  linarith

/-- Corollary 1: the two printed equality conditions suffice for unbiasedness
of Var-hat_C (main pp. 236–237); no necessity is claimed. -/
theorem corollary1 (D : Design U Ω) (h : Positive D) (y : U → ℝ)
    (a b : U → U → ℝ)
    (hab : ∀ k l, k ≠ l ∧ joint D k l = 0 → (a k l).HolderConjugate (b k l))
    (heq : ∀ k l, k ≠ l ∧ joint D k l = 0 →
      |y k| ^ (a k l) = |y l| ^ (b k l))
    (hopp : ∀ k l, k ≠ l ∧ joint D k l = 0 → -y k * y l = |y k| * |y l|) :
    expect D (conservativeEstimator D y a b) = variance D (htTotal D y) := by
  have he : youngA D y a b = -biasA D y := by
    unfold youngA biasA
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    split_ifs with hz
    · have hy := (Real.young_inequality_eq_iff_of_nonneg (abs_nonneg (y k))
        (abs_nonneg (y l)) (hab k l hz)).mpr (heq k l hz)
      rw [← hy, ← hopp k l hz]; ring
    · norm_num
  rw [conservative_expectation D h y a b hab, he]
  ring

/-- Expected quadratic correction equals A* at a=b=2 (main p. 237). -/
theorem expected_quadratic_correction (D : Design U Ω) (h : Positive D) (y : U → ℝ) :
    expect D (quadraticCorrection D y) = quadraticA D y := by
  unfold quadraticCorrection quadraticA
  rw [expect_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [expect_sum]
  apply Finset.sum_congr rfl; intro l _
  split_ifs
  · rw [expect_add, expect_mul_const, expect_mul_const]
    change pi D k * _ + pi D l * _ = _
    field_simp [(h k).ne', (h l).ne']
    <;> ring
  · exact expect_const D 0

/-- The quadratic bias is half the ordered sum of (y_k+y_l)², the
identity underlying Corollary 2 (main p. 237). -/
theorem c2_bias_identity (D : Design U Ω) (h : Positive D) (y : U → ℝ) :
    expect D (c2Estimator D y) - variance D (htTotal D y) =
      ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then (y k + y l)^2 / 2 else 0 := by
  unfold c2Estimator
  rw [expect_add, proposition1 D h, expected_quadratic_correction D h]
  have he : biasA D y + quadraticA D y =
      ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then (y k + y l)^2 / 2 else 0 := by
    unfold biasA quadraticA
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _
    split_ifs <;> ring
  linarith

/-- Corollary 2: the quadratic estimator is conservative (main p. 237).
Its proof applies Proposition 2, despite the printed cross-reference to Prop. 1. -/
theorem corollary2 (D : Design U Ω) (h : Positive D) (y : U → ℝ) :
    variance D (htTotal D y) ≤ expect D (c2Estimator D y) := by
  have hn : 0 ≤ expect D (c2Estimator D y) - variance D (htTotal D y) := by
    rw [c2_bias_identity D h]
    apply Finset.sum_nonneg; intro k _
    apply Finset.sum_nonneg; intro l _
    split_ifs <;> positivity
  linarith

/-- Real powers at exponent 2 coincide with the printed squares. -/
theorem c2_is_young_two (D : Design U Ω) (y : U → ℝ) :
    c2Estimator D y = conservativeEstimator D y (fun _ _ => 2) (fun _ _ => 2) := by
  funext ω
  simp [c2Estimator, conservativeEstimator, quadraticCorrection, youngCorrection,
    Real.rpow_two, sq_abs]

/-- Swapping the two indices preserves the ordered zero-pair sum.
This is the symmetrisation step of Corollary 3 (main p. 238). -/
theorem zero_pair_sum_swap (D : Design U Ω) (f : U → U → ℝ) :
    (∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then f l k else 0) =
    ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then f k l else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  rw [joint_symm D l k]
  simp only [ne_comm]

/-- Corollary 3: for every sample, a=b=2 attains the minimum over
constant conjugate exponents (main p. 238). -/
theorem corollary3 (D : Design U Ω) (h : Positive D) (y : U → ℝ) (ω : Ω) :
    conservativeEstimator D y (fun _ _ => 2) (fun _ _ => 2) ω = c2Estimator D y ω ∧
    ∀ a b : ℝ, a.HolderConjugate b →
      c2Estimator D y ω ≤ conservativeEstimator D y (fun _ _ => a) (fun _ _ => b) ω := by
  constructor
  · rw [← c2_is_young_two]
  · intro a b hab
    have hs := zero_pair_sum_swap D (fun k l =>
      indicator D ω k * (|y k| ^ a / (a * pi D k)) +
      indicator D ω l * (|y l| ^ b / (b * pi D l)))
    have hsym : youngCorrection D y (fun _ _ => a) (fun _ _ => b) ω =
        ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then
          ((indicator D ω k / pi D k) * (|y k| ^ a / a + |y k| ^ b / b) +
           (indicator D ω l / pi D l) * (|y l| ^ a / a + |y l| ^ b / b)) / 2 else 0 := by
      unfold youngCorrection
      have havg : ∀ x z : ℝ, x = z → x = (x + z)/2 := by intros; linarith
      rw [havg _ _ hs.symm, ← Finset.sum_add_distrib]
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl; intro k _
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl; intro l _
      split_ifs <;> (try dsimp)
      · field_simp; ring
      · ring
    have hle : quadraticCorrection D y ω ≤
        youngCorrection D y (fun _ _ => a) (fun _ _ => b) ω := by
      rw [hsym]
      apply Finset.sum_le_sum; intro k _
      apply Finset.sum_le_sum; intro l _
      split_ifs
      · have hk := Real.young_inequality (y k) (y k) hab
        have hl := Real.young_inequality (y l) (y l) hab
        have hkn := div_nonneg (indicator_nonneg D ω k) (h k).le
        have hln := div_nonneg (indicator_nonneg D ω l) (h l).le
        have ek : indicator D ω k * (y k ^ 2 / (2 * pi D k)) =
            (indicator D ω k / pi D k) * y k ^ 2 / 2 := by ring
        have el : indicator D ω l * (y l ^ 2 / (2 * pi D l)) =
            (indicator D ω l / pi D l) * y l ^ 2 / 2 := by ring
        rw [ek, el]
        nlinarith [mul_le_mul_of_nonneg_left hk hkn, mul_le_mul_of_nonneg_left hl hln]
      · exact le_rfl
    unfold c2Estimator conservativeEstimator
    linarith

/-- The four-sample systematic PPS design common to the exact witnesses
T1 and T10: s_g={g,g+4}, with alternating low/high interval probabilities.
The coordinates are zero-based; supplement pp. A3–A4. -/
def fourPhase (low high : ℝ) (hl : 0 ≤ low) (hh : 0 ≤ high)
    (hn : 2*low + 2*high = 1) : Design (Fin 8) (Fin 4) where
  weight g := if g.val % 2 = 0 then low else high
  nonneg g := by split <;> assumption
  total := by norm_num [Fin.sum_univ_succ]; linarith
  selected g k := decide (k.val % 4 = g.val)

/-- The genuine positive design of T1, probabilities (1,5,1,5)/12. -/
def periodic8 : Design (Fin 8) (Fin 4) :=
  fourPhase (1/12) (5/12) (by norm_num) (by norm_num) (by norm_num)

/-- The genuine positive design of T10, probabilities (1,3,1,3)/8. -/
def random8 : Design (Fin 8) (Fin 4) :=
  fourPhase (1/8) (3/8) (by norm_num) (by norm_num) (by norm_num)

/-- The alternating demeaned population of T1, (-1,1,...). -/
def alternating8 (k : Fin 8) : ℝ := if k.val % 2 = 0 then -1 else 1

/-- Positive sizes in the periodic example, (2,10,...), supplement p. A4. -/
def periodicSize8 (k : Fin 8) : ℝ := if k.val % 2 = 0 then 2 else 10

/-- T10's positive size vector (1,3,...) in the offset-NB support. -/
def randomSize8 (k : Fin 8) : ℝ := if k.val % 2 = 0 then 1 else 3

/-- T10's mixed-sign outcomes (1,-1,...). -/
def randomOutcome8 (k : Fin 8) : ℝ := -alternating8 k

/-- Inclusion probabilities derived from all four atoms, not supplied as
unconstrained numbers; T1/T10 (C1). -/
theorem fourPhase_pi (low high : ℝ) (hl hh hn) (k : Fin 8) :
    pi (fourPhase low high hl hh hn) k = if k.val % 2 = 0 then low else high := by
  fin_cases k <;> norm_num [pi, expect, indicator, fourPhase, Fin.sum_univ_succ]

/-- All joint probabilities, including the diagonal, derived from the
four-sample law; T1/T10 (C1). -/
theorem fourPhase_joint (low high : ℝ) (hl hh hn) (k l : Fin 8) :
    joint (fourPhase low high hl hh hn) k l =
      if k.val % 4 = l.val % 4 then (if k.val % 2 = 0 then low else high) else 0 := by
  fin_cases k <;> fin_cases l <;>
    norm_num [joint, expect, indicator, fourPhase, Fin.sum_univ_succ]

/-- Every unit has strictly positive inclusion probability in T1. -/
theorem periodic8_positive : Positive periodic8 := by
  intro k; rw [periodic8, fourPhase_pi]; split <;> norm_num

/-- Every unit has strictly positive inclusion probability in T10. -/
theorem random8_positive : Positive random8 := by
  intro k; rw [random8, fourPhase_pi]; split <;> norm_num

/-- T1 (C2): centering does not cancel A: A=-16 for the explicit population. -/
theorem periodic8_bias : (∑ k, alternating8 k) = 0 ∧
    biasA periodic8 alternating8 = -16 ∧ quadraticA periodic8 alternating8 = 48 := by
  simp only [biasA, quadraticA, periodic8, Fin.sum_univ_succ, fourPhase_joint, alternating8]
  norm_num

/-- T1 (C3): the HT mean and both variance estimates on every sample. -/
theorem periodic8_sample_values (g : Fin 4) :
    htMean periodic8 alternating8 g = (if g.val % 2 = 0 then -3 else 3/5) ∧
    htVarianceEstimator periodic8 alternating8 g / 64 =
      (if g.val % 2 = 0 then 33/4 else 21/100) ∧
    c2Estimator periodic8 alternating8 g / 64 =
      (if g.val % 2 = 0 then 21/2 else 33/50) ∧
    wrEstimator periodic8 alternating8 2 g = 0 := by
  fin_cases g <;>
    simp only [htMean, htTotal, htVarianceEstimator, c2Estimator, quadraticCorrection,
      wrEstimator, inclusionCov, periodic8, fourPhase_pi, fourPhase_joint, Fin.sum_univ_succ] <;>
    norm_num [indicator, fourPhase, alternating8]

/-- T1 (C4–C5): expectation 31/20 below variance 9/5, bias −1/4;
the C2 expectation is 23/10 and WR is identically zero. -/
theorem periodic8_counterexample :
    expect periodic8 (htMean periodic8 alternating8) = 0 ∧
    variance periodic8 (htMean periodic8 alternating8) = 9/5 ∧
    expect periodic8 (fun g => htVarianceEstimator periodic8 alternating8 g / 64) = 31/20 ∧
    expect periodic8 (fun g => c2Estimator periodic8 alternating8 g / 64) = 23/10 ∧
    expect periodic8 (fun g => htVarianceEstimator periodic8 alternating8 g / 64) -
      variance periodic8 (htMean periodic8 alternating8) = -1/4 := by
  have hm := fun g => (periodic8_sample_values g).1
  have hv := fun g => (periodic8_sample_values g).2.1
  have hc := fun g => (periodic8_sample_values g).2.2.1
  simp only [variance, expect, hm, hv, hc, Fin.sum_univ_succ]
  norm_num [periodic8, fourPhase]

/-- Cluster witness law: {1,2} or {3}, each with probability 1/2;
units 1 and 2 are always co-included (main p. 237). -/
def cluster3 : Design (Fin 3) (Fin 2) where
  weight _ := 1/2
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_succ]
  selected g k := decide (if g.val = 0 then k.val < 2 else k.val = 2)

/-- The corresponding totalled law: one of two clusters with probability 1/2. -/
def cluster2 : Design (Fin 2) (Fin 2) where
  weight _ := 1/2
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_succ]
  selected g k := decide (g = k)

/-- T3's first original population: all three outcomes equal one. -/
def allOnes3 (_ : Fin 3) : ℝ := 1

/-- T3's first totalled population (2,1). -/
def totalledOnes (k : Fin 2) : ℝ := if k = 0 then 2 else 1

/-- T3's second original population (1,1,−1/4). -/
def mixed3 (k : Fin 3) : ℝ := if k = 2 then -1/4 else 1

/-- T3's second totalled population (2,−1/4). -/
def totalledMixed (k : Fin 2) : ℝ := if k = 0 then 2 else -1/4

/-- T3 (C1–C3): all-positive witness. Totalling preserves t-hat and its
uncorrected variance estimate but increases the C2 bias from 8 to 9. -/
theorem aggregation_counterexample_positive :
    Positive cluster3 ∧ Positive cluster2 ∧
    (∀ g, indicator cluster3 g 0 = indicator cluster3 g 1) ∧
    (∀ g, htTotal cluster3 allOnes3 g = htTotal cluster2 totalledOnes g) ∧
    variance cluster3 (htTotal cluster3 allOnes3) = 1 ∧
    biasA cluster3 allOnes3 = 4 ∧ quadraticA cluster3 allOnes3 = 4 ∧
    quadraticA cluster2 totalledOnes = 5 ∧
    expect cluster3 (c2Estimator cluster3 allOnes3) = 9 ∧
    expect cluster2 (c2Estimator cluster2 totalledOnes) = 10 := by
  simp only [Positive, pi, joint, expect, indicator, htTotal, variance, biasA,
    quadraticA, c2Estimator, htVarianceEstimator, quadraticCorrection, inclusionCov,
    cluster3, cluster2, allOnes3, totalledOnes, Fin.sum_univ_succ, Fin.forall_fin_succ]
  norm_num

/-- T3 (C4): mixed-sign witness, A=−1; C2 bias increases from 9/8 to
49/16 after totalling, while both estimates remain conservative. -/
theorem aggregation_counterexample_mixed :
    variance cluster3 (htTotal cluster3 mixed3) = 81/16 ∧
    variance cluster2 (htTotal cluster2 totalledMixed) = 81/16 ∧
    biasA cluster3 mixed3 = -1 ∧ biasA cluster2 totalledMixed = -1 ∧
    quadraticA cluster3 mixed3 = 17/8 ∧ quadraticA cluster2 totalledMixed = 65/16 ∧
    expect cluster3 (c2Estimator cluster3 mixed3) = 99/16 ∧
    expect cluster2 (c2Estimator cluster2 totalledMixed) = 65/8 := by
  norm_num [pi, joint, expect, indicator, htTotal, variance, biasA, quadraticA,
    c2Estimator, htVarianceEstimator, quadraticCorrection, inclusionCov,
    cluster3, cluster2, mixed3, totalledMixed, Fin.sum_univ_succ]

/-- T10 (C2): the explicit size-(1,3,...) systematic design has total
values 16 and −16/3 and HT variance estimates 224 and 160/9. -/
theorem random8_sample_values (g : Fin 4) :
    htTotal random8 randomOutcome8 g = (if g.val % 2 = 0 then 16 else -16/3) ∧
    htVarianceEstimator random8 randomOutcome8 g =
      (if g.val % 2 = 0 then 224 else 160/9) := by
  fin_cases g <;>
    simp only [htTotal, htVarianceEstimator, inclusionCov, random8, fourPhase_pi,
      fourPhase_joint, Fin.sum_univ_succ] <;>
    norm_num [indicator, fourPhase, randomOutcome8, alternating8]

/-- T10 (C3,C5): positive sizes do not imply conservative variance
estimation for every fixed population: A=−16, E[V-hat]=208/3 < Var=256/3;
C2's expectation is 352/3. -/
theorem random8_counterexample :
    (∀ k, 1 ≤ randomSize8 k) ∧
    biasA random8 randomOutcome8 = -16 ∧ quadraticA random8 randomOutcome8 = 48 ∧
    expect random8 (htTotal random8 randomOutcome8) = 0 ∧
    variance random8 (htTotal random8 randomOutcome8) = 256/3 ∧
    expect random8 (htVarianceEstimator random8 randomOutcome8) = 208/3 ∧
    expect random8 (c2Estimator random8 randomOutcome8) = 352/3 := by
  have hm := fun g => (random8_sample_values g).1
  have hv := fun g => (random8_sample_values g).2
  have hc : expect random8 (quadraticCorrection random8 randomOutcome8) = 48 := by
    rw [expected_quadratic_correction random8 random8_positive]
    simp only [quadraticA, random8, fourPhase_joint, Fin.sum_univ_succ]
    norm_num [randomOutcome8, alternating8]
  have ha : expect random8 (c2Estimator random8 randomOutcome8) = 352/3 := by
    unfold c2Estimator
    rw [expect_add, hc]
    simp only [expect, hv, Fin.sum_univ_succ]
    norm_num [random8, fourPhase]
  rw [ha]
  simp only [variance, expect, hm, hv, Fin.sum_univ_succ]
  simp only [biasA, quadraticA, random8, fourPhase_joint, Fin.sum_univ_succ,
    Fin.forall_fin_succ]
  norm_num [fourPhase, randomOutcome8, alternating8, randomSize8]

/-- Perfectly co-included clusters, main p. 237, are represented by the
disjoint nonempty fibres {g}×Fin(n_g). Any finite partition can be relabelled
this way. Null atoms may be removed, so almost-sure co-inclusion is represented
by an exact common indicator. -/
def liftDesign {G : Type} [Fintype G] (D : Design G Ω) (n : G → ℕ) :
    Design (Σ g, Fin (n g)) Ω where
  weight := D.weight
  nonneg := D.nonneg
  total := D.total
  selected ω k := D.selected ω k.1

/-- "Y_g = ∑_{k∈G_g} y_k", cluster totals (main p. 237). -/
def groupTotal {G : Type} (n : G → ℕ) (y : (Σ g, Fin (n g)) → ℝ) (g : G) : ℝ :=
  ∑ j, y ⟨g,j⟩

/-- "S_g = ∑_{k∈G_g} y_k²", within-cluster sums of squares. -/
def groupSquares {G : Type} (n : G → ℕ) (y : (Σ g, Fin (n g)) → ℝ) (g : G) : ℝ :=
  ∑ j, y ⟨g,j⟩ ^ 2

/-- Cluster membership preserves first-order probabilities, T4 (i). -/
theorem lift_pi {G : Type} [Fintype G] (D : Design G Ω) (n : G → ℕ)
    (k : Σ g, Fin (n g)) : pi (liftDesign D n) k = pi D k.1 := rfl

/-- Cluster membership preserves joint probabilities, T4 (i). -/
theorem lift_joint {G : Type} [Fintype G] (D : Design G Ω) (n : G → ℕ)
    (k l : Σ g, Fin (n g)) : joint (liftDesign D n) k l = joint D k.1 l.1 := rfl

/-- Finite Cauchy inequality: Y_g² ≤ n_g S_g, the finite lemma behind
the equal-cluster-size correction in T4 (vi). -/
theorem group_cauchy {G : Type} (n : G → ℕ)
    (y : (Σ g, Fin (n g)) → ℝ) (g : G) :
    groupTotal n y g ^ 2 ≤ (n g : ℝ) * groupSquares n y g := by
  simpa [groupTotal, groupSquares] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : Fin (n g) => y ⟨g,j⟩))


/-- A one-group draw with specified normalized probabilities; used for
periodic PPS phases and the population after totalling (supplement p. A4). -/
def oneDraw {G : Type} [Fintype G] (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (hs : ∑ g, p g = 1) : Design G G where
  weight := p
  nonneg := hp
  total := hs
  selected g k := decide (g = k)

/-- The q=2r phases have probabilities 1/(3q), 5/(3q); zero-based
second coordinate 0 is a low-size phase. T2 (i). -/
def phaseProb (r : ℕ) (g : Fin r × Fin 2) : ℝ :=
  if g.2 = 0 then 1/(6*r) else 5/(6*r)

/-- Normalization of the periodic random-start interval probabilities. -/
theorem phaseProb_total (r : ℕ) (hr : 0 < r) : ∑ g, phaseProb r g = 1 := by
  simp only [Fintype.sum_prod_type, phaseProb, Fin.sum_univ_two]
  have hrr : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  norm_num [Finset.sum_const]
  field_simp [hrr]
  <;> ring

/-- The totalled periodic design has q=2r units, one drawn with the exact
random-start interval probabilities; T2 (i) and T6 (i). -/
def phaseGrouped (r : ℕ) (hr : 0 < r) : Design (Fin r × Fin 2) (Fin r × Fin 2) :=
  oneDraw (phaseProb r) (fun g => by unfold phaseProb; split <;> positivity)
    (phaseProb_total r hr)

/-- Original periodic population: m co-selected units per phase,
N=mq, q=2r. The zero-based index is 2*g.1+g.2+q*j; T2 (i). -/
def phaseOriginal (r m : ℕ) (hr : 0 < r) := liftDesign (phaseGrouped r hr) (fun _ => m)

/-- Alternating sizes 2,10 on the periodic population (supplement p. A4). -/
def phaseSize {r m : ℕ} (k : Σ _ : Fin r × Fin 2, Fin m) : ℝ :=
  if k.1.2 = 0 then 2 else 10

/-- The square-sum identity for centered group totals, the deterministic
finite lemma supporting T2 and the rejection of cancellation in T7. -/
theorem centered_cross_products {G : Type} [Fintype G] (Y : G → ℝ)
    (h : ∑ g, Y g = 0) :
    (∑ g, ∑ h', if g ≠ h' then Y g * Y h' else 0) = -∑ g, Y g ^ 2 := by
  have hs : (∑ g, ∑ h', Y g * Y h') = (∑ g, Y g)^2 := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    simp only [mul_comm]
  have he : (∑ g, ∑ h', Y g * Y h') =
      (∑ g, ∑ h', if g ≠ h' then Y g * Y h' else 0) + ∑ g, Y g^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro g _
    have hd : (∑ h', if g = h' then Y g * Y h' else 0) = Y g^2 := by
      simp [pow_two]
    rw [← hd, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro h' _
    by_cases hh : g = h' <;> simp [hh, pow_two]
  rw [h] at hs
  linarith

/-- Cumulative-size interval left endpoint ∑_{a<k}x_a, the usual systematic
PPS rule (supplement pp. A3–A4). -/
def cumulativeLeft {N : ℕ} (x : Fin N → ℝ) (k : Fin N) : ℝ :=
  ∑ a, if a.val < k.val then x a else 0

/-- A unit is selected exactly when its half-open cumulative interval contains
one of u,u+I,...,u+(m−1)I, I=∑x/m. Supplement systematic PPS rule. -/
def systematicSelected {N : ℕ} (x : Fin N → ℝ) (m : ℕ) (u : ℝ) (k : Fin N) : Prop :=
  ∃ j : Fin m, cumulativeLeft x k ≤ u+(j:ℝ)*((∑ a, x a)/m) ∧
    u+(j:ℝ)*((∑ a, x a)/m) < cumulativeLeft x k+x k

/-- First-block intervals for four-phase certificates of T1/T10. -/
def fourLeft (a b : ℝ) (g : Fin 4) : ℝ :=
  if g = 0 then 0 else if g = 1 then a else if g = 2 then a+b else 2*a+b

/-- T1 (C1): the finite law is the exact coarsening of the uniform start
u∈[0,24), including boundary conventions of all half-open intervals. -/
theorem periodic8_systematic (g : Fin 4) (u : ℝ)
    (hu : fourLeft 2 10 g ≤ u ∧ u < fourLeft 2 10 g +
      (if g.val % 2 = 0 then 2 else 10)) :
    ∀ k, systematicSelected periodicSize8 2 u k ↔ periodic8.selected g k = true := by
  intro k
  fin_cases g <;> fin_cases k <;>
    norm_num [systematicSelected, cumulativeLeft, periodicSize8, fourLeft,
      periodic8, fourPhase, Fin.sum_univ_succ, Fin.exists_fin_succ] at * <;>
    aesop (add unsafe (by linarith))

/-- T10 (C1): the finite law is the exact uniform-start coarsening on [0,8). -/
theorem random8_systematic (g : Fin 4) (u : ℝ)
    (hu : fourLeft 1 3 g ≤ u ∧ u < fourLeft 1 3 g +
      (if g.val % 2 = 0 then 1 else 3)) :
    ∀ k, systematicSelected randomSize8 2 u k ↔ random8.selected g k = true := by
  intro k
  fin_cases g <;> fin_cases k <;>
    norm_num [systematicSelected, cumulativeLeft, randomSize8, fourLeft,
      random8, fourPhase, Fin.sum_univ_succ, Fin.exists_fin_succ] at * <;>
    aesop (add unsafe (by linarith))

/-- T5's four highlighted printed means, in row order 21,31,41,51
(supplement Table A3, p. A8). -/
def a3LowTrue : Fin 4 → ℝ := ![42.55,56.35,23.14,28.58]
/-- The C2 column of the same rows, Table A3 p. A8. -/
def a3LowC2 : Fin 4 → ℝ := ![653.92,891.43,622.28,861.11]
/-- q=N/m for those rows: 4,20,4,20. -/
def a3LowQ : Fin 4 → ℝ := ![4,20,4,20]

/-- T5 (C2): even allowing ±0.005 rounding in both means, each displayed
row violates the universal upper bound for totalled C2. A numerical witness
to the reporting interpretation, without asserting any false printed theorem. -/
theorem a3_grouped_table_refutation (row : Fin 4) (V G : ℝ)
    (hv : |V-a3LowTrue row| ≤ 0.005) (hg : |G-a3LowC2 row| ≤ 0.005) :
    0 < V ∧ ¬ G ≤ (1+5*(a3LowQ row-2)/(3*a3LowQ row))*V := by
  rw [abs_le] at hv hg
  fin_cases row <;> norm_num [a3LowTrue, a3LowC2, a3LowQ] at * <;>
    constructor <;> linarith


/-- The same explicit population in the fibre coordinates of the periodic
model: k=2*g.1+g.2+4*j, so the residual is 2*j−29. -/
def row21Fibre (k : Σ _ : Fin 2 × Fin 2, Fin 30) : ℝ :=
  (if k.1.2 = 0 then -4 else 4) + 2*(k.2 : ℝ) - 29

/- The source prose specifies no precise tendency probability, limit regime,
or exponent reassignment rule. Explicit mathematical readings are distinguished
from the paper's printed theorems. -/

/-- The printed PPS formula mx_k/∑x, supplement p. A3. -/
def printedPPS {N : ℕ} (m : ℕ) (x : Fin N → ℝ) (k : Fin N) : ℝ :=
  m*x k/(∑ a, x a)

/-- T12's size vector, (30,1,1,1,1,1,1,1). -/
def invalidSize8 (k : Fin 8) : ℝ := if k = 0 then 30 else 1

/-- T12 (C1–C2): the formula gives π₁=60/37>1; no genuine sampling
design can have those inclusion probabilities. -/
theorem invalid_pps_counterexample :
    (∑ k, invalidSize8 k) = 37 ∧ printedPPS 2 invalidSize8 0 = 60/37 ∧
    (∑ k, printedPPS 2 invalidSize8 k) = 2 ∧
    printedPPS 2 invalidSize8 0 - 1 = 23/37 ∧
    ∀ (Ω' : Type) [Fintype Ω'] (D : Design (Fin 8) Ω'),
      ¬ (∀ k, pi D k = printedPPS 2 invalidSize8 k) := by
  norm_num [printedPPS, invalidSize8, Fin.sum_univ_succ]
  intro Ω' _ D
  refine ⟨0, ?_⟩
  have hp := pi_le_one D 0
  norm_num at *
  linarith

/-- The real-shape NB mass in T12 (C3): (r)_j/j! p^r(1−p)^j,
r=18/5, p=3/8. -/
def nbMass (j : ℕ) : ℝ :=
  (∏ i ∈ Finset.range j, ((18/5 : ℝ)+(i:ℝ))) / (j.factorial : ℝ) *
    (3/8 : ℝ) ^ (18/5 : ℝ) * (5/8 : ℝ)^j

/-- Every NB count has positive mass; in particular the independent size
vector of T12 occurs with probability nbMass(29) nbMass(0)^7 > 0. -/
theorem nb_witness_positive : 0 < nbMass 29 * nbMass 0 ^ 7 := by
  have hp (j : ℕ) : 0 < nbMass j := by
    unfold nbMass
    apply mul_pos
    · apply mul_pos
      · apply div_pos
        · apply Finset.prod_pos; intro i _; positivity
        · exact_mod_cast Nat.factorial_pos j
      · exact Real.rpow_pos_of_pos (by norm_num) _
    · positivity
  exact mul_pos (hp 29) (pow_pos (hp 0) 7)

/-- T13 (i): feasibility of the printed formula requires mx_k≤∑x for
every k, equivalently m max_k x_k≤∑x. -/
theorem pps_feasibility_necessary {N : ℕ} (hN : 2 ≤ N) (m : ℕ)
    (hm : 0 < m) (hmN : m < N) (x : Fin N → ℝ) (hx : ∀ k, 0 < x k)
    (D : Design (Fin N) Ω) (hpi : ∀ k, pi D k = printedPPS m x k) :
    ∀ k, (m:ℝ)*x k ≤ ∑ a, x a := by
  have hs : 0 < ∑ k, x k := lt_of_lt_of_le (hx ⟨0, by omega⟩)
    (Finset.single_le_sum (fun k _ => (hx k).le) (Finset.mem_univ _))
  intro k
  have hp := pi_le_one D k
  rw [hpi, printedPPS, div_le_iff₀ hs] at hp
  simpa using hp

/-- T13 (ii): redistributed probabilities exist for every positive size
vector and 0<m<N; when feasible, c=m/∑x retains the printed formula. -/
theorem capped_pps_exists {N : ℕ} (hN : 2 ≤ N) (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (x : Fin N → ℝ) (hx : ∀ k, 0 < x k) :
    (∃ c : ℝ, 0 < c ∧ (∑ k, min 1 (c*x k)) = m) ∧
    ((∀ k, (m:ℝ)*x k ≤ ∑ a, x a) →
      (∑ k, min 1 ((m:ℝ)/(∑ a, x a)*x k)) = m ∧
      ∀ k, min 1 ((m:ℝ)/(∑ a, x a)*x k) = printedPPS m x k) := by
  let k0 : Fin N := ⟨0, by omega⟩
  let S : ℝ := ∑ k, x k
  have hS : 0 < S := lt_of_lt_of_le (hx k0)
    (Finset.single_le_sum (fun k _ => (hx k).le) (Finset.mem_univ k0))
  let upper : ℝ := ∑ k, 1/x k
  have hupper : 0 < upper := lt_of_lt_of_le (one_div_pos.mpr (hx k0))
    (Finset.single_le_sum (fun k _ => (one_div_pos.mpr (hx k)).le) (Finset.mem_univ k0))
  let f : ℝ → ℝ := fun c => ∑ k, min 1 (c*x k)
  have h0 : f 0 = 0 := by simp [f]
  have hu : f upper = N := by
    have hu1 (k : Fin N) : 1 ≤ upper*x k := by
      apply (div_le_iff₀ (hx k)).mp
      exact Finset.single_le_sum (fun l _ => (one_div_pos.mpr (hx l)).le) (Finset.mem_univ k)
    simp [f, fun k => min_eq_left (hu1 k)]
  have hf : Continuous f := by unfold f; fun_prop
  have hi : (m:ℝ) ∈ Set.Icc (f 0) (f upper) := by
    rw [h0, hu]
    exact ⟨(Nat.cast_nonneg m), by exact_mod_cast hmN.le⟩
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hupper.le hf.continuousOn hi
  have hcpos : 0 < c := by
    by_contra hh
    have he : c = 0 := le_antisymm (le_of_not_gt hh) hc.1
    rw [he, h0] at hfc
    exact (Nat.cast_pos.mpr hm).ne' hfc.symm
  refine ⟨⟨c, hcpos, hfc⟩, ?_⟩
  intro hfeas
  have hcap (k : Fin N) : min 1 ((m:ℝ)/S*x k) = (m:ℝ)*x k/S := by
    have hk : (m:ℝ)*x k/S ≤ 1 := by
      rw [div_le_iff₀ hS]; simpa using hfeas k
    have he : (m:ℝ)/S*x k = (m:ℝ)*x k/S := by ring
    rw [he, min_eq_right hk]
  constructor
  · change (∑ k, min 1 ((m:ℝ)/S*x k)) = m
    simp_rw [hcap]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    change (m:ℝ)*S/S = m
    exact mul_div_cancel_right₀ _ hS.ne'
  · intro k
    change min 1 ((m:ℝ)/S*x k) = (m:ℝ)*x k/S
    exact hcap k

/-- T13 (iv): redistribution repairs the witness with c=1/7;
naive capping instead sums to 51/37, not 2. -/
theorem redistributed_witness :
    (∑ k, min 1 ((1/7 : ℝ)*invalidSize8 k)) = 2 ∧
    (∑ k, min 1 (printedPPS 2 invalidSize8 k)) = 51/37 ∧
    (∀ k, min 1 ((1/7 : ℝ)*invalidSize8 k) = if k = 0 then 1 else 1/7) := by
  simp only [printedPPS, invalidSize8, Fin.sum_univ_succ, Fin.forall_fin_succ]
  norm_num


open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- E_y is expectation over generated outcomes, separate from design E_s;
supplement pp. A1–A4, corrections T2, T11, T15, T17, T19. -/
def outcomeE {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) (f : Ξ → ℝ) : ℝ :=
  ∫ ξ, f ξ ∂μ

/-- Mean-zero, common-variance, zero-covariance noise with finite second
moments. Independent Gaussian errors in supplement pp. A2–A3 satisfy these
conditions. Products are integrable; diagonal moment is σ², others zero. -/
def NoiseMoments {Ξ K : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (ε : K → Ξ → ℝ) (σ2 : ℝ) : Prop :=
  (∀ k, Integrable (ε k) μ ∧ outcomeE μ (ε k) = 0) ∧
  ∀ k l, Integrable (fun ξ => ε k ξ * ε l ξ) μ ∧
    outcomeE μ (fun ξ => ε k ξ * ε l ξ) = if k = l then σ2 else 0

/-- T11 correction: "mean-zero errors" with
finite variances and zero distinct-coordinate cross moments. Diagonal products
are integrable, but their integrals need not agree across population units. -/
def UncorrelatedNoise {Ξ K : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (ε : K → Ξ → ℝ) : Prop :=
  (∀ k, Integrable (ε k) μ ∧ outcomeE μ (ε k) = 0) ∧
  ∀ k l, Integrable (fun ξ => ε k ξ * ε l ξ) μ ∧
    (k ≠ l → outcomeE μ (fun ξ => ε k ξ * ε l ξ) = 0)

/-- "y_k = β x_k + ε_k" (supplement p. A3). -/
def rawOutcomes {Ξ K : Type} (x : K → ℝ) (β : ℝ) (ε : K → Ξ → ℝ)
    (ξ : Ξ) (k : K) : ℝ := β*x k+ε k ξ

/-- "y-tilde_k ≡ y_k−y-bar" (supplement p. A4). -/
def centeredOutcomes {Ξ K : Type} [Fintype K] (x : K → ℝ) (β : ℝ)
    (ε : K → Ξ → ℝ) (ξ : Ξ) (k : K) : ℝ :=
  rawOutcomes x β ε ξ k - (∑ l, rawOutcomes x β ε ξ l)/(Fintype.card K : ℝ)


/-- T11 (iv): the outcome-average coefficient is 176 in T10's design,
despite the negative A of its explicit fixed population. -/
theorem random8_outcome_coefficient : biasA random8 randomSize8 = 176 ∧
    (3/2:ℝ)^2 * biasA random8 randomSize8 = 396 := by
  simp only [biasA, random8, fourPhase_joint, Fin.sum_univ_succ]
  norm_num [randomSize8]


/-- T2 (vi): the exact calibrated model bias on the mean scale, using
the divisor-(N−1) size variance as stated by the correction. -/
def calibratedMeanBias (q : ℝ) (ρ : ℝ) (N : ℝ) : ℝ :=
  -900*ρ^2*(N-1)/(q*N)-900*(1-ρ^2)*(q-1)/(q*N)

/-- T2 (vi), fixed sampling fraction: the corrected bias formula tends
to −900ρ²/q as N=mq grows. The original vanishing-bias assertion is not
substituted for this statement. -/
theorem fixed_fraction_bias_limit (r : ℕ) (hr : 0 < r) (ρ : ℝ) :
    Tendsto (fun m : ℕ => calibratedMeanBias (2*r) ρ ((m:ℝ)*(2*r))) atTop
      (𝓝 (-900*ρ^2/(2*r))) := by
  let q : ℝ := 2*r
  have hq : q ≠ 0 := by dsimp [q]; positivity
  have hi : Tendsto (fun m : ℕ => (1:ℝ)/((m:ℝ)*q)) atTop (𝓝 0) := by
    have h := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [div_mul_eq_div_div, zero_div] using h.div_const q
  have hh : Tendsto (fun m : ℕ => -900*ρ^2/q +
      (900*ρ^2/q-900*(1-ρ^2)*(q-1)/q)*(1/((m:ℝ)*q))) atTop
      (𝓝 (-900*ρ^2/q)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul hi)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmr : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  unfold calibratedMeanBias
  dsimp [q] at *
  have hqr : (2*(r:ℝ)) ≠ 0 := by positivity
  field_simp [hqr, hmr]
  <;> ring

/-- "two strata each of size M ... from each stratum a single unit is
randomly sampled" (supplement p. A1), with independent uniform draws.
Unit=(within-stratum index,stratum), atom=(draw in stratum 0,draw in stratum 1). -/
def strataDesign (M : ℕ) (hM : 0 < M) : Design (Fin M × Fin 2) (Fin M × Fin M) where
  weight _ := 1/(M:ℝ)^2
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    have hMr : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
    <;> ring
  selected ω k := if k.2 = 0 then decide (k.1 = ω.1) else decide (k.1 = ω.2)

/-- "α_1=α, α_2=-α" (supplement Section B, p. A2): the two
fixed stratum means, with stratum 0 corresponding to printed stratum 1. -/
def stratumMeans (α : ℝ) (s : Fin 2) : ℝ := if s = 0 then α else -α

/-- S_α²=∑_s(α_s-α_bar)²/(2-1), the divisor-1 variance of
stratum means in T17 (ii). -/
def stratumMeansVariance (α : ℝ) : ℝ :=
  (∑ s : Fin 2, (stratumMeans α s-(∑ t : Fin 2, stratumMeans α t)/2)^2)/(2-1)

/-- "y_ks=α_s+ε_ks" (supplement pp. A1–A2), with α_1=α=−α_2.
This corrects the unintroduced noise index i in the printed display (T18 d). -/
def stratumOutcomes {M : ℕ} {Ξ : Type} (α : ℝ)
    (ε : (Fin M × Fin 2) → Ξ → ℝ) (ξ : Ξ) (k : Fin M × Fin 2) : ℝ :=
  stratumMeans α k.2+ε k ξ

/-- "V-hat_CS = (y_k1−y_l2)²/4" (supplement p. A2). -/
def collapsedEstimator {M : ℕ} (y : (Fin M × Fin 2) → ℝ) (ω : Fin M × Fin M) : ℝ :=
  (y (ω.1,0)-y (ω.2,1))^2/4

/-- Divisor-M within-stratum population variance v_s of T15 (ii). -/
def stratumVariance {M : ℕ} (y : (Fin M × Fin 2) → ℝ) (s : Fin 2) : ℝ :=
  (∑ k, y (k,s)^2)/(M:ℝ) - ((∑ k, y (k,s))/(M:ℝ))^2


/-- Closed bias expression B_C2 in the correction T15 (iii); this is a
FORMULA, whose identification with the actual averaged bias is a separate theorem. -/
def strataC2BiasFormula (M α : ℝ) : ℝ := (M-1)/(2*M)*(1+2*α^2)
/-- Closed bias expression B_CS in T15 (iii). -/
def strataCSBiasFormula (M α : ℝ) : ℝ := α^2+1/(2*M)

/-- T15 (iv), the exact finite comparison: C2 bias is smaller exactly when
M<2(1+α²), ties at equality, reverses above it. This is a bias, not MSE ranking. -/
theorem strata_bias_ranking (M : ℕ) (hM : 2 ≤ M) (α : ℝ) :
    strataC2BiasFormula M α-strataCSBiasFormula M α = (M-2-2*α^2)/(2*M) ∧
    (strataC2BiasFormula M α < strataCSBiasFormula M α ↔ M < 2*(1+α^2)) ∧
    (strataC2BiasFormula M α = strataCSBiasFormula M α ↔ M = 2*(1+α^2)) ∧
    (strataCSBiasFormula M α < strataC2BiasFormula M α ↔ 2*(1+α^2) < M) := by
  have hMr : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have he : strataC2BiasFormula M α-strataCSBiasFormula M α =
      (M-2-2*α^2)/(2*M) := by
    unfold strataC2BiasFormula strataCSBiasFormula
    field_simp; ring
  refine ⟨he, ?_, ?_, ?_⟩
  · rw [← sub_lt_zero, he, div_lt_iff₀ (by linarith : (0:ℝ) < 2*M)]
    constructor <;> intro hh <;> nlinarith
  · rw [← sub_eq_zero, he, div_eq_zero_iff]
    constructor
    · intro hh; rcases hh with hh | hh <;> nlinarith
    · intro hh; exact Or.inl (by nlinarith)
  · rw [← sub_pos, he, lt_div_iff₀ (by linarith : (0:ℝ) < 2*M)]
    constructor <;> intro hh <;> nlinarith

/-- The printed variance-ratio parameter ρ_ICC=α²/(α²+1/2)
(supplement p. A2), called q in the corrected statement T17. -/
def heterogeneity (α : ℝ) : ℝ := α^2/(α^2+1/2)

/-- The ordinary same-stratum pair correlation formula of T17 (i). -/
def pairCorrelationFormula (α : ℝ) : ℝ := α^2/(α^2+1)

/-- T15 (v): the exact ratio of expected estimates at finite M is
(1−1/M)(2−q); this is the finite algebra underlying the large-M claim. -/
theorem strata_ratio_formula (M : ℕ) (hM : 2 ≤ M) (α : ℝ) :
    ((M-1)/M*(1+α^2))/(α^2+1/2) = (1-1/M)*(2-heterogeneity α) := by
  have hMr : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  unfold heterogeneity
  have hd : α^2+1/2 ≠ 0 := by positivity
  field_simp; ring

/-- T15 (v): with α fixed, the expected-estimate ratio tends to 2−q,
the expectation difference to 1/2, and the true variance to 1/2. -/
theorem strata_large_size_limits (α : ℝ) :
    Tendsto (fun M : ℕ => (1-1/(M:ℝ))*(2-heterogeneity α)) atTop
      (𝓝 (2-heterogeneity α)) ∧
    Tendsto (fun M : ℕ => (1/2:ℝ)-(1+α^2)/(M:ℝ)) atTop (𝓝 (1/2)) ∧
    Tendsto (fun M : ℕ => ((M:ℝ)-1)/(2*M)) atTop (𝓝 (1/2)) := by
  have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  constructor
  · simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hi).mul_const (2-heterogeneity α)
  constructor
  · simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := (1/2:ℝ))).sub
      (hi.const_mul (1+α^2))
  · have hh : Tendsto (fun M : ℕ => (1/2:ℝ)-(1/2)*(1/(M:ℝ))) atTop (𝓝 (1/2)) := by
      simpa using (tendsto_const_nhds (x := (1/2:ℝ))).sub (hi.const_mul (1/2:ℝ))
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hMr : (M:ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    field_simp <;> ring

/-- T14's deviations, (3/2,−3/2,1/2,−1/2,0). -/
def deviations5 : Fin 5 → ℝ := ![3/2,-3/2,1/2,-1/2,0]
/-- Two explicit five-unit strata with means α,−α and deviations above. -/
def fixedStrata5 (α : ℝ) (k : Fin 5 × Fin 2) : ℝ :=
  stratumMeans α k.2+deviations5 k.1


/-- T14 (C2–C3): the model bias formulas reverse at M=5, and at
M=500,α=0 large strata leave C2 relative bias 1 versus CS relative bias 1/499. -/
theorem strata_model_numeric_witnesses :
    strataC2BiasFormula 5 0 = 2/5 ∧ strataCSBiasFormula 5 0 = 1/10 ∧
    strataC2BiasFormula 5 2 = 18/5 ∧ strataCSBiasFormula 5 2 = 41/10 ∧
    (499/500:ℝ)/(499/1000)-1 = 1 ∧ (1/2:ℝ)/(499/1000)-1 = 1/499 := by
  norm_num [strataC2BiasFormula, strataCSBiasFormula]

/-- Covariance of real outcome variables under the finite outcome law;
used for the pair-correlation witness T16. -/
def outcomeCov (D : Design U Ω) (f g : Ω → ℝ) : ℝ :=
  expect D (fun ω => f ω*g ω)-expect D f*expect D g

/-- Ordinary correlation Cov(Y,Y')/sqrt(Var(Y)Var(Y')), T16/T17. -/
def outcomeCorr (D : Design U Ω) (f g : Ω → ℝ) : ℝ :=
  outcomeCov D f g/Real.sqrt (variance D f*variance D g)

/-- A symmetric ±1 variable, mean zero and variance one. -/
def sign2 (s : Fin 2) : ℝ := if s = 0 then -1 else 1

/-- Three independent symmetric signs: common stratum S, ε, ε', each
of variance one. These moments do not require Gaussianity (T16). -/
def pairLaw : Design Unit (Fin 2 × Fin 2 × Fin 2) where
  weight _ := 1/8
  nonneg _ := by norm_num
  total := by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]
  selected _ _ := false

/-- S in the T16 moment witness. -/
def pairS (ω : Fin 2 × Fin 2 × Fin 2) := sign2 ω.1
/-- The first independent error in T16. -/
def pairE (ω : Fin 2 × Fin 2 × Fin 2) := sign2 ω.2.1
/-- The second independent error in T16. -/
def pairE' (ω : Fin 2 × Fin 2 × Fin 2) := sign2 ω.2.2

/-- T16: an explicit normalized moment-model witness at α=1/2. The
ordinary correlation is 1/5 while the printed ratio is 1/3 (difference 2/15). -/
theorem icc_counterexample :
    let Y := fun ω => (1/2:ℝ)*pairS ω+pairE ω
    let Y' := fun ω => (1/2:ℝ)*pairS ω+pairE' ω
    expect pairLaw pairS = 0 ∧ expect pairLaw pairE = 0 ∧ expect pairLaw pairE' = 0 ∧
    variance pairLaw pairS = 1 ∧ variance pairLaw pairE = 1 ∧ variance pairLaw pairE' = 1 ∧
    expect pairLaw (fun ω => pairS ω*pairE ω) = 0 ∧
    expect pairLaw (fun ω => pairS ω*pairE' ω) = 0 ∧
    expect pairLaw (fun ω => pairE ω*pairE' ω) = 0 ∧
    expect pairLaw Y = 0 ∧ expect pairLaw Y' = 0 ∧
    variance pairLaw Y = 5/4 ∧ variance pairLaw Y' = 5/4 ∧ outcomeCov pairLaw Y Y' = 1/4 ∧
    outcomeCorr pairLaw Y Y' = 1/5 ∧ heterogeneity (1/2) = 1/3 ∧
    heterogeneity (1/2)-outcomeCorr pairLaw Y Y' = 2/15 := by
  norm_num [expect, variance, outcomeCov, outcomeCorr, pairLaw, pairS, pairE, pairE',
    sign2, Fintype.sum_prod_type, Fin.sum_univ_two, heterogeneity]

/-- T17 (ii–iv): the printed parameter uses divisor-1 variance 2α²,
exceeds ordinary pair correlation except at α=0, and converts by r=q/(2−q). -/
theorem heterogeneity_conversion (α : ℝ) :
    heterogeneity α = (2*α^2)/(2*α^2+1) ∧
    heterogeneity α-pairCorrelationFormula α = α^2/((α^2+1)*(2*α^2+1)) ∧
    0 ≤ heterogeneity α-pairCorrelationFormula α ∧
    (heterogeneity α = pairCorrelationFormula α ↔ α = 0) ∧
    pairCorrelationFormula α = heterogeneity α/(2-heterogeneity α) ∧
    α^2 = heterogeneity α/(2*(1-heterogeneity α)) := by
  have h1 : α^2+1/2 ≠ 0 := by positivity
  have h2 : α^2+1 ≠ 0 := by positivity
  have h3 : 2*α^2+1 ≠ 0 := by positivity
  have hd : heterogeneity α-pairCorrelationFormula α = α^2/((α^2+1)*(2*α^2+1)) := by
    unfold heterogeneity pairCorrelationFormula
    field_simp; ring
  refine ⟨?_, hd, ?_, ?_, ?_, ?_⟩
  · unfold heterogeneity; field_simp <;> ring
  · rw [hd]; positivity
  · rw [← sub_eq_zero, hd, div_eq_zero_iff]
    constructor
    · intro h; rcases h with h | h
      · nlinarith [sq_nonneg α]
      · exact False.elim ((mul_ne_zero h2 h3) h)
    · intro h; subst α; norm_num
  · have h4 : 2-heterogeneity α ≠ 0 := by
      unfold heterogeneity
      intro h4
      have := (div_eq_iff h1).mp (show α^2/(α^2+1/2) = 2 by linarith)
      nlinarith [sq_nonneg α]
    unfold heterogeneity pairCorrelationFormula at *
    field_simp [h1, h2, h3, h4] <;> ring
    all_goals
      have hz : (1+α^2:ℝ) ≠ 0 := by positivity
      have hinv := mul_inv_cancel₀ hz
      nlinarith [hinv]
  · have h4 : 1-heterogeneity α ≠ 0 := by
      unfold heterogeneity
      intro h4
      have := (div_eq_iff h1).mp (show α^2/(α^2+1/2) = 1 by linarith)
      linarith
    unfold heterogeneity at *
    field_simp [h1, h4] <;> ring

/-- T17 (iv): q↦q/(2−q) is strictly increasing on [0,1). -/
theorem heterogeneity_conversion_monotone :
    StrictMonoOn (fun q : ℝ => q/(2-q)) (Set.Ico 0 1) := by
  intro a ha b hb hab
  apply (div_lt_div_iff₀ (by linarith [ha.2]) (by linarith [hb.2])).mpr
  nlinarith

/-- T17 (iv): all six tabulated parameter labels convert as recorded. -/
theorem printed_icc_labels :
    (0.33:ℝ)/(2-0.33) = 33/167 ∧ (0.50:ℝ)/(2-0.50) = 1/3 ∧
    (0.67:ℝ)/(2-0.67) = 67/133 ∧ (0.82:ℝ)/(2-0.82) = 41/59 ∧
    (0.90:ℝ)/(2-0.90) = 9/11 ∧ (0.99:ℝ)/(2-0.99) = 99/101 := by norm_num

/-- Mean-scale design quantities V,H,C,W for T19, with C explicitly the
ORIGINAL-unit C2 expectation. N² is never replaced by q². -/
def periodicMeanV {r m : ℕ} (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) : ℝ :=
  variance (phaseOriginal r m hr) (htMean (phaseOriginal r m hr) z)
/-- Mean-scale H of T19, supplement Table A3. -/
def periodicMeanH {r m : ℕ} (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) : ℝ :=
  expect (phaseOriginal r m hr) (fun ω => htVarianceEstimator (phaseOriginal r m hr) z ω /
    ((m:ℝ)*(2*r))^2)
/-- Mean-scale original-unit C of T19. -/
def periodicMeanC {r m : ℕ} (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) : ℝ :=
  expect (phaseOriginal r m hr) (fun ω => c2Estimator (phaseOriginal r m hr) z ω /
    ((m:ℝ)*(2*r))^2)
/-- Mean-scale WR expectation W of T19. -/
def periodicMeanW {r m : ℕ} (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) : ℝ :=
  expect (phaseOriginal r m hr) (wrEstimator (phaseOriginal r m hr) z m)

/-- R=5(q−1)/(9q−5) in T19's signal-canceling contrast. -/
def contrastR (q : ℝ) : ℝ := 5*(q-1)/(9*q-5)
/-- c=6q/(9q−5) in T19's diagonalization and tail bound. -/
def contrastCoefficient (q : ℝ) : ℝ := 6*q/(9*q-5)
/-- T(z)=C−(1+R)H, T19 (iii). -/
def periodicContrast {r m : ℕ} (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) : ℝ :=
  periodicMeanC hr z-(1+contrastR (2*r))*periodicMeanH hr z

/-- Squared Euclidean norm of a finite population vector, T19 (iii). -/
def populationSquareNorm {K : Type} [Fintype K] (z : K → ℝ) : ℝ := ∑ k, z k^2

/-- The W,P,L,G components of the centered periodic-population space:
within-phase zero sums, alternating signal, and low/high
phase constants whose totals separately sum to zero. -/
structure PhaseDecomposition (r m : ℕ)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) where
  within : (Σ _ : Fin r × Fin 2, Fin m) → ℝ
  signal : (Σ _ : Fin r × Fin 2, Fin m) → ℝ
  low : (Σ _ : Fin r × Fin 2, Fin m) → ℝ
  high : (Σ _ : Fin r × Fin 2, Fin m) → ℝ
  within_zero : ∀ g, groupTotal (fun _ : Fin r × Fin 2 => m) within g = 0
  signal_multiple : ∃ b : ℝ, ∀ k, signal k = b*(phaseSize k-6)
  low_constant : ∃ v : (Fin r × Fin 2) → ℝ, (∑ g, v g) = 0 ∧
    (∀ g, g.2 ≠ 0 → v g = 0) ∧ ∀ k, low k = v k.1
  high_constant : ∃ v : (Fin r × Fin 2) → ℝ, (∑ g, v g) = 0 ∧
    (∀ g, g.2 = 0 → v g = 0) ∧ ∀ k, high k = v k.1
  reconstruct : ∀ k, z k = within k+signal k+low k+high k

/-- The space of demeaned vectors, "sum_i z_i = 0" (T19 iii),
with its usual real vector-space operations. -/
def phaseCenteredSpace (r m : ℕ) :
    Submodule ℝ ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) where
  carrier := {v | ∑ k, v k = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change (∑ k, v k) = 0 at hv
    change (∑ k, w k) = 0 at hw
    simpa [Finset.sum_add_distrib, hv, hw]
  smul_mem' := by
    intro c v hv
    change (∑ k, v k) = 0 at hv
    simpa [← Finset.mul_sum, hv]

/-- W: "vectors that sum to zero within every G_g" (T19 iii).
Its dimension is asserted separately, not assumed. -/
def phaseWithinSpace (r m : ℕ) :
    Submodule ℝ ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) where
  carrier := {v | ∀ g, ∑ j : Fin m, v ⟨g,j⟩ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw g
    simpa [Finset.sum_add_distrib, hv g, hw g]
  smul_mem' := by intro c v hv g; simpa [← Finset.mul_sum, hv g]

/-- P: "the multiples of x - 6" (T19 iii). -/
def phaseSignalSpace (r m : ℕ) :
    Submodule ℝ ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) :=
  Submodule.span ℝ {fun k => phaseSize k - 6}

/-- L or G: "constant on each G_g", supported on one parity and
"sum to zero" (T19 iii). `false` selects the low-size
phases; `true` selects the high-size phases. -/
def phaseParitySpace (r m : ℕ) (high : Bool) :
    Submodule ℝ ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) where
  carrier := {v | (∀ (g : Fin r × Fin 2) (i j : Fin m), v ⟨g,i⟩ = v ⟨g,j⟩) ∧
    (∀ k, (if high then k.1.2 = 0 else k.1.2 ≠ 0) → v k = 0) ∧
    ∑ k, v k = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    refine ⟨?_, ?_, ?_⟩
    · intro g i j; change v ⟨g,i⟩ + w ⟨g,i⟩ = v ⟨g,j⟩ + w ⟨g,j⟩
      rw [hv.1 g i j, hw.1 g i j]
    · intro k hk; change v k + w k = 0; rw [hv.2.1 k hk, hw.2.1 k hk]; ring
    · simpa [Finset.sum_add_distrib, hv.2.2, hw.2.2]
  smul_mem' := by
    intro c v hv
    refine ⟨?_, ?_, ?_⟩
    · intro g i j; change c * v ⟨g,i⟩ = c * v ⟨g,j⟩; rw [hv.1 g i j]
    · intro k hk; change c * v k = 0; rw [hv.2.1 k hk]; ring
    · simpa [← Finset.mul_sum, hv.2.2]

/-- The four subspaces W,P,L,G of the orthogonal direct sum in T19 iii,
in that order. -/
def phaseComponentSpace (r m : ℕ) (i : Fin 4) :
    Submodule ℝ ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) :=
  if i = 0 then phaseWithinSpace r m else if i = 1 then phaseSignalSpace r m
  else if i = 2 then phaseParitySpace r m false else phaseParitySpace r m true


/-- Independent Gaussian noise in one generated population, as used in
the simulation's ordinary reading: measurable coordinates, marginal law
N(0,σ²), and joint independence. No independence BETWEEN populations is added. -/
def GaussianNoise {Ξ K : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (ε : K → Ξ → ℝ) (σ2 : ℝ) : Prop :=
  (∀ k, AEMeasurable (ε k) μ ∧ μ.map (ε k) = gaussianReal 0 σ2.toNNReal) ∧
    iIndepFun ε μ

/-- Chi-square_d, defined as the pushforward of d independent standard
Gaussians by their squared norm (T19 iv); d=0 is the point mass at zero. -/
def chiSquaredLaw (d : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map
    (fun v : Fin d → ℝ => ∑ j, v j^2)


/-- High-ρ rows 30,40,50,60: printed H means (Table A3 p. A8). -/
def a3HighH : Fin 4 → ℝ := ![1412.15,1564.34,1430.59,1562.38]
/-- Printed original-unit C2 means of those rows. -/
def a3HighC : Fin 4 → ℝ := ![2029.28,2396.58,2032.07,2395.86]
/-- Half the number q of phases: 2,10,2,10 for those rows. -/
def a3HighR : Fin 4 → ℕ := ![2,10,2,10]
/-- Sample sizes m=30,30,60,60. -/
def a3HighM : Fin 4 → ℕ := ![30,30,60,60]
/-- The four exact contrast values. -/
def a3HighContrast : Fin 4 → ℝ := ![-102561/1550,-29703/1750,-281297/3100,-25671/1750]
/-- Lower bound exponents J−h: 189,213,522,371. -/
def a3HighExponent : Fin 4 → ℕ := ![189,213,522,371]

/-- T19 (vi), deterministic part: exact contrasts computed from printed
means; rounding bounds are 77/6200 for q=4, 89/7000 for q=20. -/
theorem a3_high_contrast_arithmetic (row : Fin 4) :
    a3HighC row-(1+contrastR (2*a3HighR row))*a3HighH row = a3HighContrast row ∧
    (0.005:ℝ)*(2+contrastR (2*a3HighR row)) =
      (if a3HighR row = 2 then 77/6200 else 89/7000) ∧
    ((2:ℝ)^(a3HighExponent row))⁻¹ ≤
      (if row = 0 then (10:ℝ)^(-56:ℤ) else if row = 1 then (10:ℝ)^(-64:ℤ)
       else if row = 2 then (10:ℝ)^(-157:ℤ) else (10:ℝ)^(-111:ℤ)) := by
  have h522 : (2:ℝ)^522 = ((2:ℝ)^174)^3 := by rw [← pow_mul]
  have h371 : (2:ℝ)^371 = ((2:ℝ)^185)^2*2 := by rw [← pow_mul, ← pow_succ]
  fin_cases row <;>
    norm_num [a3HighC, a3HighH, contrastR, a3HighR, a3HighContrast, a3HighExponent, h522, h371]


/-- All 48 ordered distinct zero-inclusion pairs in the T1/T10 examples.
The small finite certificate counts the actual derived joint probabilities. -/
theorem four_phase_zero_pair_count :
    (Finset.univ.filter (fun kl : Fin 8 × Fin 8 =>
      kl.1 ≠ kl.2 ∧ joint periodic8 kl.1 kl.2 = 0)).card = 48 ∧
    (Finset.univ.filter (fun kl : Fin 8 × Fin 8 =>
      kl.1 ≠ kl.2 ∧ joint random8 kl.1 kl.2 = 0)).card = 48 := by
  have hp (k l : Fin 8) : joint periodic8 k l = 0 ↔ k.val%4 ≠ l.val%4 := by
    rw [periodic8, fourPhase_joint]
    split_ifs <;> norm_num <;> assumption
  have hr (k l : Fin 8) : joint random8 k l = 0 ↔ k.val%4 ≠ l.val%4 := by
    rw [random8, fourPhase_joint]
    split_ifs <;> norm_num <;> assumption
  simp only [hp, hr]
  decide

/-- The six (N,m) configurations of Table A2 (supplement p. A7),
for the invalid-probability witnesses in T12 C4. -/
def ppsConfigurationN : Fin 6 → ℕ := ![8,40,120,600,240,1200]
/-- The sample sizes of the six configurations, Table A2 p. A7. -/
def ppsConfigurationM : Fin 6 → ℕ := ![2,2,30,30,60,60]
/-- "L = floor((N-1)/(m-1))+1" (T12 C4).
The values are 8,40,5,21,5,21. -/
def ppsConfigurationL : Fin 6 → ℕ := ![8,40,5,21,5,21]
/-- The six exact first-unit printed probabilities in T12 C4. -/
def ppsConfigurationPi : Fin 6 → ℝ := ![16/15,80/79,150/124,630/620,300/244,1260/1220]

/-- Product measure built from the real-shape negative-binomial masses
specified in T12 C3. Normalization is not assumed by this definition. -/
def nbProductLawN (N : ℕ) : Measure (Fin N → ℕ) :=
  Measure.sum (fun v : Fin N → ℕ =>
    ENNReal.ofReal (∏ k, nbMass (v k)) • Measure.dirac v)


/-- The numerical model expectations in T19 (ii) are closed second-moment
predictions, not proposed replacements for unavailable realized table means. -/
def periodicModelPredictions (N m ρ : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  let q := N/m
  let σ2 := 900*(1-ρ^2)
  let β2 := 900*ρ^2*(N-1)/(16*N)
  let B := 16*β2/q+σ2*(N-m)/N^2
  let V := (9*q/5)*B
  let H := V-B
  let C := H+(N-m)/N^2*(16*N*β2+(N-1)*σ2)
  let W := (9/5)*σ2/m
  (V,H,C,W)

/-- T19 (ii): exact calibrated model means at ρ=.99 for all four rows.
This is only an arithmetic certificate for the moment formulas. -/
theorem periodic_model_prediction_values :
    periodicModelPredictions 120 30 0.99 = (1575.3366,1356.53985,2025.91485,1.0746) ∧
    periodicModelPredictions 600 30 0.99 = (1586.1366,1542.07725,2395.65225,1.0746) ∧
    periodicModelPredictions 240 60 0.99 = (1581.5493,1361.889675,2034.077175,0.5373) ∧
    periodicModelPredictions 1200 60 0.99 = (1586.9493,1542.867375,2397.154875,0.5373) := by
  norm_num [periodicModelPredictions]

/-- T17 (iv): conversion approaches 1 as the heterogeneity parameter
approaches 1 from below. -/
theorem heterogeneity_conversion_limit :
    Tendsto (fun q : ℝ => q/(2-q)) (𝓝[<] 1) (𝓝 1) := by
  have hc : ContinuousAt (fun q : ℝ => q/(2-q)) 1 := by fun_prop (disch := norm_num)
  convert hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1)) using 1 <;> norm_num

/-- Design expectations scale by a constant divisor (mean-scale corrections). -/
theorem expect_div_const (D : Design U Ω) (f : Ω → ℝ) (c : ℝ) :
    expect D (fun ω => f ω/c) = expect D f/c := by
  simpa only [div_eq_mul_inv] using expect_mul_const D f c⁻¹

/-- Design variance scales by the square of the divisor (supplement p. A1). -/
theorem variance_div_const (D : Design U Ω) (f : Ω → ℝ) (c : ℝ) :
    variance D (fun ω => f ω/c) = variance D f/c^2 := by
  unfold variance
  rw [expect_div_const]
  simp only [← sub_div, div_pow]
  exact expect_div_const D _ _

/-- Proposition 1 on the mean scale, keeping the original N² divisor. -/
theorem mean_bias_identity (D : Design U Ω) (hD : Positive D) (y : U → ℝ) :
    expect D (fun ω => htVarianceEstimator D y ω/(Fintype.card U : ℝ)^2) -
      variance D (htMean D y) = biasA D y/(Fintype.card U : ℝ)^2 := by
  unfold htMean
  rw [expect_div_const, variance_div_const, proposition1 D hD]
  ring

/-- Expectation of the actual raw-model cross product, T11 (i), proved
without Gaussianity from the stated integrability and zero-cross-moment assumptions. -/
theorem raw_model_cross_moment {Ξ K : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (x : K → ℝ) (β : ℝ)
    (ε : K → Ξ → ℝ) (hε : UncorrelatedNoise μ ε) (k l : K) (hkl : k ≠ l) :
    Integrable (fun ξ => rawOutcomes x β ε ξ k * rawOutcomes x β ε ξ l) μ ∧
    outcomeE μ (fun ξ => rawOutcomes x β ε ξ k * rawOutcomes x β ε ξ l) = β^2*x k*x l := by
  have he : (fun ξ => rawOutcomes x β ε ξ k * rawOutcomes x β ε ξ l) =
      (fun ξ => β^2*x k*x l + ((β*x k)*ε l ξ + (β*x l)*ε k ξ + ε k ξ*ε l ξ)) := by
    funext ξ; unfold rawOutcomes; ring
  have h1 := (hε.1 l).1.const_mul (β*x k)
  have h2 := (hε.1 k).1.const_mul (β*x l)
  have h3 := (hε.2 k l).1
  have h12 : Integrable (fun ξ => (β*x k)*ε l ξ+(β*x l)*ε k ξ) μ := h1.add h2
  have h123 : Integrable (fun ξ => (β*x k)*ε l ξ+(β*x l)*ε k ξ+ε k ξ*ε l ξ) μ := h12.add h3
  have hc : Integrable (fun _ : Ξ => β^2*x k*x l) μ := integrable_const _
  rw [he]
  constructor
  · exact hc.add ((h1.add h2).add h3)
  · unfold outcomeE
    dsimp only
    rw [integral_add hc h123, integral_add h12 h3,
      integral_add h1 h2, integral_const,
      integral_const_mul (β*x k) (ε l), integral_const_mul (β*x l) (ε k)]
    have hk := (hε.1 k).2
    have hl := (hε.1 l).2
    have hz := (hε.2 k l).2 hkl
    simp only [outcomeE] at hk hl hz
    rw [hk, hl, hz]
    simp [hkl]

/-- Integrating the finite ordered sum A under the outcome law, T11 (ii).
The zero-pair set is fixed by the size-dependent design before averaging. -/
theorem outcome_average_A {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (D : Design U Ω)
    (x : U → ℝ) (β : ℝ) (ε : U → Ξ → ℝ) (hε : UncorrelatedNoise μ ε) :
    outcomeE μ (fun ξ => biasA D (rawOutcomes x β ε ξ)) = β^2*biasA D x := by
  have hi (k l : U) : Integrable (fun ξ => if k ≠ l ∧ joint D k l = 0 then
      rawOutcomes x β ε ξ k * rawOutcomes x β ε ξ l else 0) μ := by
    split_ifs with hh
    · exact (raw_model_cross_moment μ x β ε hε k l hh.1).1
    · exact integrable_const 0
  have hsum (k : U) : Integrable (fun ξ => ∑ l, if k ≠ l ∧ joint D k l = 0 then
      rawOutcomes x β ε ξ k * rawOutcomes x β ε ξ l else 0) μ := by
    exact integrable_finsetSum _ (fun l _ => hi k l)
  unfold outcomeE biasA
  rw [integral_finsetSum _ (fun k _ => hsum k)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [integral_finsetSum _ (fun l _ => hi k l)]
  apply Finset.sum_congr rfl; intro l _
  split_ifs with hh
  · simpa only [outcomeE, mul_assoc] using (raw_model_cross_moment μ x β ε hε k l hh.1).2
  · simp

/-- T4 (i): totalling the fibres preserves the estimated total on every
sample, with the original positive probabilities inherited from the groups. -/
theorem aggregation_total_preserved {G : Type} [Fintype G]
    (D : Design G Ω) (hD : Positive D) (n : G → ℕ) (y : (Σ g, Fin (n g)) → ℝ) (ω : Ω) :
    htTotal (liftDesign D n) y ω = htTotal D (groupTotal n y) ω := by
  unfold htTotal
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl; intro g _
  change (∑ j, indicator D ω g * (y ⟨g,j⟩/pi D g)) =
    indicator D ω g * ((∑ j, y ⟨g,j⟩)/pi D g)
  simp only [Finset.sum_div, Finset.mul_sum]

/-- Positivity is inherited by original units from their cluster law. -/
theorem lift_positive {G : Type} [Fintype G] (D : Design G Ω) (h : Positive D)
    (n : G → ℕ) : Positive (liftDesign D n) := fun k => h k.1

/-- First-order inclusion probability of a one-group draw is its given
normalized weight; used to connect the periodic definitions to the paper. -/
theorem oneDraw_pi {G : Type} [Fintype G] (p : G → ℝ) (hp hs) (k : G) :
    pi (oneDraw p hp hs) k = p k := by
  simp [pi, expect, indicator, oneDraw]

/-- One-group draws have π_kl=0 for distinct groups, π_kk=p_k. -/
theorem oneDraw_joint {G : Type} [Fintype G] (p : G → ℝ) (hp hs) (k l : G) :
    joint (oneDraw p hp hs) k l = if k = l then p k else 0 := by
  by_cases hh : k = l
  · subst l; rw [joint_self, oneDraw_pi]; simp
  · simp [joint, expect, indicator, oneDraw, hh, Ne.symm hh]

/-- The grouped periodic design meets condition 1 with no extra assumption. -/
theorem phaseGrouped_positive (r : ℕ) (hr : 0 < r) : Positive (phaseGrouped r hr) := by
  intro g
  rw [phaseGrouped, oneDraw_pi]
  unfold phaseProb
  split <;> positivity

/-- The original periodic design meets condition 1 for every m. -/
theorem phaseOriginal_positive (r m : ℕ) (hr : 0 < r) : Positive (phaseOriginal r m hr) :=
  lift_positive _ (phaseGrouped_positive r hr) _

/-- A one-group draw estimates the HT total by Y_g/p_g, sample by sample;
T2 (iii), T6 (ii). -/
theorem oneDraw_total {G : Type} [Fintype G] (p : G → ℝ) (hp hs) (Y : G → ℝ) (g : G) :
    htTotal (oneDraw p hp hs) Y g = Y g/p g := by
  simp only [htTotal, oneDraw_pi]
  simp [indicator, oneDraw]

/-- The centered one-group design variance is ∑Y_g²/p_g, T2 (iii). -/
theorem oneDraw_centered_variance {G : Type} [Fintype G]
    (p : G → ℝ) (hp hs) (hpos : ∀ g, 0 < p g) (Y : G → ℝ) (hY : ∑ g, Y g = 0) :
    variance (oneDraw p hp hs) (htTotal (oneDraw p hp hs) Y) = ∑ g, Y g^2/p g := by
  have hD : Positive (oneDraw p hp hs) := by intro g; rw [oneDraw_pi]; exact hpos g
  have he := ht_unbiased (oneDraw p hp hs) hD Y
  rw [hY] at he
  unfold variance
  rw [he]
  simp only [sub_zero, expect, oneDraw_total]
  simp only [oneDraw]
  apply Finset.sum_congr rfl; intro g _
  field_simp [(hpos g).ne']

/-- Re-index A over the finite set of ordered distinct zero-inclusion pairs.
This does not change the paper's factor-of-two convention. -/
theorem biasA_pair_sum (D : Design U Ω) (y : U → ℝ) :
    biasA D y = (Finset.univ.filter (fun kl : U × U =>
      kl.1 ≠ kl.2 ∧ joint D kl.1 kl.2 = 0)).sum (fun kl => y kl.1*y kl.2) := by
  simp only [Finset.sum_filter, Fintype.sum_prod_type, biasA]

/-- Quadratic perturbation certificate for the open neighborhood in T10:
within 1/8 of each ±1 outcome, each cross product increases by at most 17/64. -/
theorem witness_product_perturbation (y : Fin 8 → ℝ)
    (hy : ∀ k, |y k-randomOutcome8 k| < 1/8) (k l : Fin 8) :
    y k*y l ≤ randomOutcome8 k*randomOutcome8 l+17/64 := by
  let a := randomOutcome8 k
  let b := randomOutcome8 l
  let h := y k-a
  let t := y l-b
  have ha : |a| = 1 := by unfold a randomOutcome8 alternating8; split <;> norm_num
  have hb : |b| = 1 := by unfold b randomOutcome8 alternating8; split <;> norm_num
  have hh : |h| ≤ 1/8 := (hy k).le
  have ht : |t| ≤ 1/8 := (hy l).le
  have hht : |h*t| ≤ (1/8:ℝ)*(1/8) := by
    rw [abs_mul]
    exact mul_le_mul hh ht (abs_nonneg t) (by norm_num)
  have had : |a*t| ≤ 1/8 := by rw [abs_mul, ha, one_mul]; exact ht
  have hbd : |b*h| ≤ 1/8 := by rw [abs_mul, hb, one_mul]; exact hh
  have hd : y k*y l-a*b = a*t+b*h+h*t := by dsimp [a,b,h,t]; ring
  have hbound : |a*t+b*h+h*t| ≤ |a*t|+|b*h|+|h*t| := by
    have hfirst := abs_add_le (a*t+b*h) (h*t)
    have hsecond := abs_add_le (a*t) (b*h)
    linarith
  have hlower := le_abs_self (y k*y l-a*b)
  rw [hd] at hlower
  dsimp [a,b] at *
  linarith

/-- T11 (i–iii): after averaging over the error law with sizes and design
fixed, the uncorrected mean-variance estimator is conservative. It asserts
no pointwise same-sign condition on realized outcomes. -/
theorem outcome_averaged_conservativity {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (D : Design U Ω) (hD : Positive D)
    (hU : 0 < Fintype.card U) (x : U → ℝ) (hx : ∀ k, 1 ≤ x k) (β : ℝ)
    (ε : U → Ξ → ℝ) (hε : UncorrelatedNoise μ ε) :
    (∀ k l, k ≠ l → outcomeE μ (fun ξ =>
      rawOutcomes x β ε ξ k * rawOutcomes x β ε ξ l) = β^2*x k*x l) ∧
    outcomeE μ (fun ξ => biasA D (rawOutcomes x β ε ξ)) = β^2*biasA D x ∧
    0 ≤ outcomeE μ (fun ξ => biasA D (rawOutcomes x β ε ξ)) ∧
    outcomeE μ (fun ξ => expect D (fun ω =>
      htVarianceEstimator D (rawOutcomes x β ε ξ) ω/(Fintype.card U : ℝ)^2) -
      variance D (htMean D (rawOutcomes x β ε ξ))) =
      β^2*biasA D x/(Fintype.card U : ℝ)^2 ∧
    0 ≤ outcomeE μ (fun ξ => expect D (fun ω =>
      htVarianceEstimator D (rawOutcomes x β ε ξ) ω/(Fintype.card U : ℝ)^2) -
      variance D (htMean D (rawOutcomes x β ε ξ))) := by
  have hp := fun k l hk => (raw_model_cross_moment μ x β ε hε k l hk).2
  have ha := outcome_average_A μ D x β ε hε
  have hnon : 0 ≤ β^2*biasA D x := by
    apply mul_nonneg (sq_nonneg β)
    apply biasA_same_sign D hD
    exact Or.inl (fun k => le_trans (by norm_num) (hx k))
  have hb : (fun ξ => expect D (fun ω => htVarianceEstimator D (rawOutcomes x β ε ξ) ω/
      (Fintype.card U : ℝ)^2) - variance D (htMean D (rawOutcomes x β ε ξ))) =
      (fun ξ => biasA D (rawOutcomes x β ε ξ)/(Fintype.card U : ℝ)^2) := by
    funext ξ; exact mean_bias_identity D hD _
  have he : outcomeE μ (fun ξ => expect D (fun ω =>
      htVarianceEstimator D (rawOutcomes x β ε ξ) ω/(Fintype.card U : ℝ)^2) -
      variance D (htMean D (rawOutcomes x β ε ξ))) = β^2*biasA D x/(Fintype.card U : ℝ)^2 := by
    rw [hb]
    unfold outcomeE
    simp only [div_eq_mul_inv, integral_mul_const]
    change outcomeE μ (fun ξ => biasA D (rawOutcomes x β ε ξ)) * _ = _
    rw [ha]
  refine ⟨hp, ha, ?_, he, ?_⟩
  · rw [ha]; exact hnon
  · rw [he]; positivity

/-- T10 (C4): a whole open box around the witness has negative bias;
under independent nondegenerate Gaussian errors this is a positive-probability
failure, not merely a point of zero probability. -/
theorem negative_bias_neighborhood (y : Fin 8 → ℝ)
    (hy : ∀ k, |y k-randomOutcome8 k| < 1/8) : biasA random8 y ≤ -13/4 := by
  let Z := Finset.univ.filter (fun kl : Fin 8 × Fin 8 =>
    kl.1 ≠ kl.2 ∧ joint random8 kl.1 kl.2 = 0)
  have hZ : Z.card = 48 := four_phase_zero_pair_count.2
  have hb := (random8_counterexample).2.1
  have he (v : Fin 8 → ℝ) : biasA random8 v = Z.sum (fun kl => v kl.1*v kl.2) := by
    simp only [biasA, Z, Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    split_ifs <;> rfl
  have hs : biasA random8 y ≤ biasA random8 randomOutcome8 + 48*(17/64:ℝ) := by
    rw [he, he]
    calc
      Z.sum (fun kl => y kl.1*y kl.2) ≤ Z.sum (fun kl => randomOutcome8 kl.1*randomOutcome8 kl.2+17/64) := by
        apply Finset.sum_le_sum; intro kl _
        exact witness_product_perturbation y hy kl.1 kl.2
      _ = Z.sum (fun kl => randomOutcome8 kl.1*randomOutcome8 kl.2)+48*(17/64:ℝ) := by
        simp [Finset.sum_add_distrib, hZ]
  linarith

/-- Exact first-order probabilities of independent uniform stratum draws,
derived from the normalized product design, T18 (i). -/
theorem strata_pi_value (M : ℕ) (hM : 0 < M) (k : Fin M × Fin 2) :
    pi (strataDesign M hM) k = 1/(M:ℝ) := by
  rcases k with ⟨i,s⟩
  have hMr : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  fin_cases s <;> simp [pi, expect, indicator, strataDesign, Fintype.sum_prod_type] <;>
    (try rw [Finset.sum_comm]) <;> (try simp [hMr]) <;> field_simp <;> ring

/-- Joint probabilities of independent uniform stratum draws, including
the diagonal corrected by T18 (ii–iii). -/
theorem strata_joint_value (M : ℕ) (hM : 0 < M) (k l : Fin M × Fin 2) :
    joint (strataDesign M hM) k l = if k = l then 1/(M:ℝ) else
      if k.2 = l.2 then 0 else 1/(M:ℝ)^2 := by
  by_cases hkl : k = l
  · subst l; rw [joint_self, strata_pi_value]; simp
  · rcases k with ⟨i,s⟩
    rcases l with ⟨j,t⟩
    fin_cases s <;> fin_cases t <;>
      simp [joint, expect, indicator, strataDesign, Fintype.sum_prod_type, hkl,
        Prod.ext_iff, Ne.symm] at * <;> simp_all

/-- T18 (c), corrected inclusion formula: diagonal 1/M, distinct same-
stratum joint 0, cross-stratum joint 1/M². Also all printed covariance cases. -/
theorem strata_inclusion_correction (M : ℕ) (hM : 0 < M) :
    let D := strataDesign M hM
    (∀ k, pi D k = 1/(M:ℝ)) ∧
    (∀ k l, joint D k l = if k = l then 1/(M:ℝ) else
      if k.2 = l.2 then 0 else 1/(M:ℝ)^2) ∧
    (∀ k l, inclusionCov D k l = if k = l then
      (1/(M:ℝ))*(1-1/(M:ℝ)) else if k.2 = l.2 then -1/(M:ℝ)^2 else 0) := by
  dsimp only
  refine ⟨strata_pi_value M hM, strata_joint_value M hM, ?_⟩
  intro k l
  unfold inclusionCov
  rw [strata_joint_value, strata_pi_value, strata_pi_value]
  have hMr : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  split_ifs <;> field_simp <;> ring

/-- Factoring a finite ordered pair sum, used in the cluster correction. -/
theorem pair_sum_factor {A B : Type} [Fintype A] [Fintype B]
    (f : A → ℝ) (g : B → ℝ) (c : ℝ) :
    (∑ i, ∑ j, c*f i*g j) = c*(∑ i, f i)*(∑ j, g j) := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  all_goals
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _; ring

/-- T4 (ii): totalling preserves the uncorrected estimator sample by sample. -/
theorem aggregation_ht_estimator_preserved {G : Type} [Fintype G]
    (D : Design G Ω) (hD : Positive D) (n : G → ℕ) (y : (Σ g, Fin (n g)) → ℝ) (ω : Ω) :
    htVarianceEstimator (liftDesign D n) y ω = htVarianceEstimator D (groupTotal n y) ω := by
  unfold htVarianceEstimator
  simp only [Fintype.sum_sigma, lift_joint, lift_pi]
  apply Finset.sum_congr rfl; intro g _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro h _
  by_cases hgh : 0 < joint D g h
  · simp only [hgh, ite_true]
    let c := indicator D ω g*indicator D ω h*(inclusionCov D g h/joint D g h)/
      pi D g/pi D h
    have he (i : Fin (n g)) (j : Fin (n h)) :
        indicator (liftDesign D n) ω ⟨g,i⟩ * indicator (liftDesign D n) ω ⟨h,j⟩ *
          (inclusionCov (liftDesign D n) ⟨g,i⟩ ⟨h,j⟩/joint D g h)*
          (y ⟨g,i⟩/pi D g)*(y ⟨h,j⟩/pi D h) = c*y ⟨g,i⟩*y ⟨h,j⟩ := by
      change indicator D ω g*indicator D ω h*(inclusionCov D g h/joint D g h)*
        (y ⟨g,i⟩/pi D g)*(y ⟨h,j⟩/pi D h) = _
      dsimp [c]; ring
    simp_rw [he]
    rw [pair_sum_factor]
    dsimp [c, groupTotal]
    ring
  · simp [hgh]

/-- T4 (iii): A is preserved by totalling, because positive diagonal
probabilities exclude same-cluster zero pairs. -/
theorem aggregation_A_preserved {G : Type} [Fintype G]
    (D : Design G Ω) (hD : Positive D) (n : G → ℕ)
    (y : (Σ g, Fin (n g)) → ℝ) : biasA (liftDesign D n) y = biasA D (groupTotal n y) := by
  have hh (g h : G) (i : Fin (n g)) (j : Fin (n h)) :
      ((⟨g,i⟩ : Σ g, Fin (n g)) ≠ ⟨h,j⟩ ∧ joint D g h = 0) ↔
        g ≠ h ∧ joint D g h = 0 := by
    constructor
    · intro hz
      refine ⟨?_, hz.2⟩
      intro he; subst h
      rw [joint_self] at hz
      exact (hD g).ne' hz.2
    · intro hz
      refine ⟨?_, hz.2⟩
      intro he; exact hz.1 (congrArg Sigma.fst he)
  unfold biasA
  simp only [Fintype.sum_sigma, lift_joint, hh]
  apply Finset.sum_congr rfl; intro g _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro h _
  by_cases hgh : g ≠ h ∧ joint D g h = 0
  · simp [hgh.1, hgh.2]
    simpa only [one_mul, groupTotal] using
      pair_sum_factor (fun i => y ⟨g,i⟩) (fun j => y ⟨h,j⟩) 1
  · simp [hgh]

/-- T4 (i–iii), corrected p. 237: totalling perfectly co-selected units
preserves the HT total, its actual design variance, the HT variance estimator
sample by sample, and A. -/
theorem aggregation_preservation {G : Type} [Fintype G]
    (D : Design G Ω) (h : Positive D) (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (y : (Σ g, Fin (n g)) → ℝ) :
    (∀ ω, htTotal (liftDesign D n) y ω = htTotal D (groupTotal n y) ω) ∧
    variance (liftDesign D n) (htTotal (liftDesign D n) y) =
      variance D (htTotal D (groupTotal n y)) ∧
    (∀ ω, htVarianceEstimator (liftDesign D n) y ω =
      htVarianceEstimator D (groupTotal n y) ω) ∧
    biasA (liftDesign D n) y = biasA D (groupTotal n y) := by
  have ht := aggregation_total_preserved D h n y
  have hv : variance (liftDesign D n) (htTotal (liftDesign D n) y) =
      variance D (htTotal D (groupTotal n y)) := by
    have hf : htTotal (liftDesign D n) y = htTotal D (groupTotal n y) := funext ht
    rw [hf]
    rfl
  exact ⟨ht, hv, aggregation_ht_estimator_preserved D h n y, aggregation_A_preserved D h n y⟩

/-- Zero-based one-dimensional indexing of periodic population fibres;
g+qj in one-based notation (T2 i, supplement pp. A3–A4). -/
def phaseIndex {r m : ℕ} (k : Σ _ : Fin r × Fin 2, Fin m) : ℕ :=
  2*k.1.1.val+k.1.2.val+2*r*k.2.val

/-- First-block phase interval left endpoint: low at 12i, high at 12i+2. -/
def phaseStartLeft {r : ℕ} (g : Fin r × Fin 2) : ℝ :=
  12*(g.1:ℝ)+(if g.2 = 0 then 0 else 2)


/-- The periodic sizes have mean 6 and divisor-(N−1) variance 16N/(N−1),
T2 (vi), T19 calibration, with original N=2rm. -/
theorem periodic_size_moments (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    let N : ℝ := (m:ℝ)*(2*r)
    (∑ k : Σ _ : Fin r × Fin 2, Fin m, phaseSize k) = 6*N ∧
    (∑ k : Σ _ : Fin r × Fin 2, Fin m, (phaseSize k-6)^2) = 16*N ∧
    (∑ k : Σ _ : Fin r × Fin 2, Fin m, (phaseSize k-6)^2)/(N-1) = 16*N/(N-1) := by
  dsimp only
  have hsum : (∑ k : Σ _ : Fin r × Fin 2, Fin m, phaseSize k) = 6*((m:ℝ)*(2*r)) := by
    simp [Fintype.sum_sigma, Fintype.sum_prod_type, phaseSize, Fin.sum_univ_two,
      Finset.sum_const, nsmul_eq_mul] <;> ring
  have hsq : (∑ k : Σ _ : Fin r × Fin 2, Fin m, (phaseSize k-6)^2) =
      16*((m:ℝ)*(2*r)) := by
    simp [Fintype.sum_sigma, Fintype.sum_prod_type, phaseSize, Fin.sum_univ_two,
      Finset.sum_const, nsmul_eq_mul] <;> ring
  exact ⟨hsum, hsq, by rw [hsq]⟩

/-- Explicit totalled q=4 law for T6's population-specific ratio example. -/
def groupedPeriodic4 : Design (Fin 4) (Fin 4) :=
  oneDraw periodic8.weight periodic8.nonneg periodic8.total

/-- Group totals (1,0,−1,0) in T6 (vii), corresponding to the original
8-unit population (1,0,−1,0,0,0,0,0). -/
def ratioExampleTotals : Fin 4 → ℝ := ![1,0,-1,0]

/-- T6 (vii): the ratio 5/18 is NOT universal for individual populations:
an exact totalled population has S=2,V=24,G=28, relative bias 1/6. -/
theorem realized_ratio_example :
    (∑ g, ratioExampleTotals g^2) = 2 ∧
    variance groupedPeriodic4 (htTotal groupedPeriodic4 ratioExampleTotals) = 24 ∧
    expect groupedPeriodic4 (c2Estimator groupedPeriodic4 ratioExampleTotals) = 28 ∧
    (28-24:ℝ)/24 = 1/6 := by
  have hpi (k : Fin 4) : pi groupedPeriodic4 k = periodic8.weight k := oneDraw_pi _ _ _ k
  have hj (k l : Fin 4) : joint groupedPeriodic4 k l =
      if k = l then periodic8.weight k else 0 := by
    by_cases hkl : k = l <;> simp [groupedPeriodic4, oneDraw_joint, hkl]
  have ht (ω : Fin 4) : htTotal groupedPeriodic4 ratioExampleTotals ω =
      (![12,0,-12,0] : Fin 4 → ℝ) ω := by
    unfold groupedPeriodic4
    rw [oneDraw_total]
    fin_cases ω <;> norm_num [ratioExampleTotals, periodic8, fourPhase]
  have hc (ω : Fin 4) : c2Estimator groupedPeriodic4 ratioExampleTotals ω =
      (![168,0,168,0] : Fin 4 → ℝ) ω := by
    simp only [c2Estimator, htVarianceEstimator, quadraticCorrection, inclusionCov, hpi, hj]
    fin_cases ω <;> norm_num [indicator, groupedPeriodic4, oneDraw, ratioExampleTotals,
      periodic8, fourPhase, Fin.sum_univ_succ]
  have htf : htTotal groupedPeriodic4 ratioExampleTotals = ![12,0,-12,0] := funext ht
  have hcf : c2Estimator groupedPeriodic4 ratioExampleTotals = ![168,0,168,0] := funext hc
  rw [htf, hcf]
  norm_num [variance, expect, groupedPeriodic4, oneDraw, periodic8, fourPhase,
    ratioExampleTotals, Fin.sum_univ_succ]

/-- The corrected witness of T13 draws {1,j}, j=2,...,8, with probability
1/7, after redistributing certainty-unit inclusion probability. -/
def certainty8 : Design (Fin 8) (Fin 7) where
  weight _ := 1/7
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_succ]
  selected ω k := decide (k = 0 ∨ k.val = ω.val+1)

/-- T13 (iv): the corrected positive finite design has π=(1,1/7,...),
certainty-to-other joints 1/7 and all distinct noncertainty joints zero. -/
theorem certainty8_probabilities : Positive certainty8 ∧
    (∀ k, pi certainty8 k = min 1 ((1/7:ℝ)*invalidSize8 k)) ∧
    (∀ k l, joint certainty8 k l = if k = l then pi certainty8 k else
      if k = 0 ∨ l = 0 then 1/7 else 0) := by
  simp only [Positive, pi, joint, expect, indicator, certainty8, invalidSize8,
    Fin.sum_univ_succ, Fin.forall_fin_succ]
  norm_num

/-- T2 (i), T6 (i): actual inclusion probabilities and maximal co-selected
classes in the periodic design, derived from its selected subsets. -/
theorem phase_inclusions (r m : ℕ) (hr : 0 < r) :
    (∀ k : Σ _ : Fin r × Fin 2, Fin m,
      pi (phaseOriginal r m hr) k = phaseProb r k.1) ∧
    (∀ k l : Σ _ : Fin r × Fin 2, Fin m,
      joint (phaseOriginal r m hr) k l =
        if k.1 = l.1 then phaseProb r k.1 else 0) ∧
    (∀ (g : Fin r × Fin 2) (k : Σ _ : Fin r × Fin 2, Fin m),
      (phaseOriginal r m hr).selected g k = decide (g = k.1)) ∧
    (∀ k l : Σ _ : Fin r × Fin 2, Fin m,
      (∀ g, (phaseOriginal r m hr).selected g k =
        (phaseOriginal r m hr).selected g l) ↔ k.1 = l.1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    simp [phaseOriginal, lift_pi, phaseGrouped, oneDraw_pi]
  · intro k l
    by_cases hkl : k.1 = l.1 <;>
      simp [phaseOriginal, lift_joint, phaseGrouped, oneDraw_joint, hkl]
  · intro g k
    by_cases hgk : g = k.1 <;> simp [phaseOriginal, liftDesign, phaseGrouped, oneDraw, hgk]
  · intro k l
    constructor
    · intro h
      have hh := h k.1
      simpa [phaseOriginal, liftDesign, phaseGrouped, oneDraw] using hh
    · intro h g
      simp [phaseOriginal, liftDesign, phaseGrouped, oneDraw, h]

/-- T2 (ii): centering gives A=-∑Y_g², never positive, with equality
exactly when every phase total vanishes. This is an actual design bias,
not a replacement definition of A. -/
theorem periodic_negative_square (r m : ℕ) (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (hz : ∑ k, z k = 0) :
    let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
    (∑ g, Y g) = 0 ∧
    biasA (phaseOriginal r m hr) z = -∑ g, Y g^2 ∧
    0 ≤ ∑ g, Y g^2 ∧
    ((∑ g, Y g^2) = 0 ↔ ∀ g, Y g = 0) := by
  dsimp only
  let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
  have hY : ∑ g, Y g = 0 := by
    simpa only [Y, groupTotal, Fintype.sum_sigma] using hz
  have hD := phaseGrouped_positive r hr
  have hA : biasA (phaseOriginal r m hr) z = -∑ g, Y g^2 := by
    unfold phaseOriginal
    rw [aggregation_A_preserved (phaseGrouped r hr) hD (fun _ => m) z]
    unfold biasA
    have hj (g h : Fin r × Fin 2) :
        (g ≠ h ∧ joint (phaseGrouped r hr) g h = 0) ↔ g ≠ h := by
      by_cases hgh : g = h
      · simp [hgh]
      · simp [phaseGrouped, oneDraw_joint, hgh]
    simp only [hj]
    convert centered_cross_products Y hY using 1
    apply Finset.sum_congr rfl; intro g _
    apply Finset.sum_congr rfl; intro h _
    by_cases hh : g = h <;> simp [hh, Y]
  have hS : 0 ≤ ∑ g, Y g^2 := Finset.sum_nonneg (fun g _ => sq_nonneg (Y g))
  refine ⟨hY, hA, hS, ?_⟩
  constructor
  · intro hs g
    have hl := Finset.single_le_sum (fun h _ => sq_nonneg (Y h)) (Finset.mem_univ g)
    rw [hs] at hl
    nlinarith [sq_nonneg (Y g)]
  · intro hy; simp [hy]

/-- T2 (iii), T6 (ii): exact HT total variance and expected uncorrected
estimator for every centered periodic population. -/
theorem periodic_ht_expectations (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (hz : ∑ k, z k = 0) :
    let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
    let D := phaseOriginal r m hr
    expect D (htTotal D z) = 0 ∧
    variance D (htTotal D z) = ∑ g, Y g^2/phaseProb r g ∧
    expect D (htVarianceEstimator D z) =
      variance D (htTotal D z)-(∑ g, Y g^2) := by
  dsimp only
  have hneg := periodic_negative_square r m hr z hz
  have hg := phaseGrouped_positive r hr
  have hp := phaseOriginal_positive r m hr
  have hpr (g : Fin r × Fin 2) : 0 < phaseProb r g := by
    simpa only [phaseGrouped, oneDraw_pi] using hg g
  have hv := (aggregation_preservation (phaseGrouped r hr) hg (fun _ => m)
    (fun _ => hm) z).2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [ht_unbiased _ hp, hz]
  · unfold phaseOriginal
    rw [hv]
    exact oneDraw_centered_variance _ _ _ hpr _ hneg.1
  · rw [proposition1 _ hp, hneg.2.1]
    ring

/-- T4 (iv): the constituent quadratic correction in group coordinates,
on ordered cluster zero-pairs with the original sizes retained. -/
theorem quadraticA_lift {G : Type} [Fintype G]
    (D : Design G Ω) (hD : Positive D) (n : G → ℕ)
    (y : (Σ g, Fin (n g)) → ℝ) :
    quadraticA (liftDesign D n) y =
      (∑ g, ∑ h, if g ≠ h ∧ joint D g h = 0 then
        (n h : ℝ)*groupSquares n y g+(n g : ℝ)*groupSquares n y h else 0)/2 := by
  have hh (g h : G) (i : Fin (n g)) (j : Fin (n h)) :
      ((⟨g,i⟩ : Σ g, Fin (n g)) ≠ ⟨h,j⟩ ∧ joint D g h = 0) ↔
        g ≠ h ∧ joint D g h = 0 := by
    constructor
    · intro hz
      refine ⟨?_, hz.2⟩
      intro he; subst h
      rw [joint_self] at hz
      exact (hD g).ne' hz.2
    · intro hz
      refine ⟨?_, hz.2⟩
      intro he; exact hz.1 (congrArg Sigma.fst he)
  unfold quadraticA
  simp only [Fintype.sum_sigma, lift_joint, hh, Finset.sum_div]
  apply Finset.sum_congr rfl; intro g _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro h _
  by_cases hgh : g ≠ h ∧ joint D g h = 0
  · simp only [hgh.2, and_true]
    simp only [if_pos hgh.1]
    simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      groupSquares]
    (try simp only [← Finset.mul_sum, ← Finset.sum_mul])
    all_goals ring
  · simp [hgh]

/-- The HT mean from independent uniform strata is the average of the
two drawn outcomes (supplement Section B, p. A1; T15 finite lemma). -/
theorem strata_sample_mean (M : ℕ) (hM : 0 < M)
    (y : (Fin M × Fin 2) → ℝ) (ω : Fin M × Fin M) :
    htMean (strataDesign M hM) y ω = (y (ω.1,0)+y (ω.2,1))/2 := by
  unfold htMean htTotal
  simp only [strata_pi_value, Fintype.card_prod, Fintype.card_fin]
  have hMr : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp [indicator, strataDesign, Fintype.sum_prod_type, Fin.sum_univ_two,
    Finset.sum_add_distrib, div_eq_mul_inv]
  field_simp <;> ring

/-- T14 (C1): actual 25-sample fixed-population witnesses at M=5 have
true variance 1/2 in both cases and reverse the C2/CS bias ranking with α. -/
theorem strata5_counterexample :
    let D := strataDesign 5 (by norm_num)
    variance D (htMean D (fixedStrata5 0)) = 1/2 ∧
    variance D (htMean D (fixedStrata5 2)) = 1/2 ∧
    expect D (fun ω => htVarianceEstimator D (fixedStrata5 0) ω/100) = 2/5 ∧
    expect D (fun ω => c2Estimator D (fixedStrata5 0) ω/100) = 4/5 ∧
    expect D (collapsedEstimator (fixedStrata5 0)) = 1/2 ∧
    expect D (fun ω => htVarianceEstimator D (fixedStrata5 2) ω/100) = 2 ∧
    expect D (fun ω => c2Estimator D (fixedStrata5 2) ω/100) = 4 ∧
    expect D (collapsedEstimator (fixedStrata5 2)) = 9/2 := by
  dsimp only
  let D := strataDesign 5 (by norm_num)
  have hp : Positive D := by intro k; rw [strata_pi_value]; norm_num
  have hj (k l : Fin 5 × Fin 2) : joint D k l =
      if k = l then 1/5 else if k.2 = l.2 then 0 else 1/25 := by
    by_cases hkl : k = l <;> by_cases hst : k.2 = l.2
    all_goals
      have h := strata_joint_value 5 (by norm_num) k l
      norm_num [hkl, hst] at h
      simpa [D, hkl, hst] using h
  have hn : biasA D (fixedStrata5 0) = -10 ∧ quadraticA D (fixedStrata5 0) = 40 ∧
      biasA D (fixedStrata5 2) = 150 ∧ quadraticA D (fixedStrata5 2) = 200 := by
    simp only [biasA, quadraticA, hj]
    norm_num [fixedStrata5, stratumMeans, deviations5, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have ht (α : ℝ) : htMean D (fixedStrata5 α) =
      (fun ω => (deviations5 ω.1+deviations5 ω.2)/2) := by
    funext ω
    rw [strata_sample_mean]
    simp [fixedStrata5, stratumMeans]
    ring
  have hv (α : ℝ) : variance D (htMean D (fixedStrata5 α)) = 1/2 := by
    rw [ht]
    norm_num [variance_second_moment, expect, D, strataDesign, deviations5,
      Fintype.sum_prod_type, Fin.sum_univ_succ]
  have hh (α : ℝ) := mean_bias_identity D hp (fixedStrata5 α)
  have he (α : ℝ) : expect D (fun ω => c2Estimator D (fixedStrata5 α) ω/100) =
      expect D (fun ω => htVarianceEstimator D (fixedStrata5 α) ω/100)+
        quadraticA D (fixedStrata5 α)/100 := by
    rw [expect_div_const]
    unfold c2Estimator
    rw [expect_add, expected_quadratic_correction D hp, expect_div_const]
    ring
  have hh0 := hh 0
  have hh2 := hh 2
  simp only [Fintype.card_prod, Fintype.card_fin] at hh0 hh2
  rw [hv, hn.1] at hh0
  rw [hv, hn.2.2.1] at hh2
  norm_num at hh0 hh2
  have hc0 := he 0
  have hc2 := he 2
  rw [hn.2.1] at hc0
  rw [hn.2.2.2] at hc2
  refine ⟨hv 0, hv 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · norm_num [expect, D, strataDesign, collapsedEstimator, fixedStrata5, stratumMeans,
      deviations5, Fintype.sum_prod_type, Fin.sum_univ_succ]
  · linarith
  · linarith
  · norm_num [expect, D, strataDesign, collapsedEstimator, fixedStrata5, stratumMeans,
      deviations5, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- T17 (ii): the actual divisor-1 variance of the fixed stratum means
is 2α², and its variance ratio is precisely the printed parameter. -/
theorem stratum_means_variance (α : ℝ) :
    (∑ s, stratumMeans α s)/2 = 0 ∧
    stratumMeansVariance α = 2*α^2 ∧
    heterogeneity α = stratumMeansVariance α/(stratumMeansVariance α+1) := by
  have hm : (∑ s, stratumMeans α s)/2 = 0 := by
    simp [stratumMeans, Fin.sum_univ_two]
  have hv : stratumMeansVariance α = 2*α^2 := by
    simp [stratumMeansVariance, stratumMeans, Fin.sum_univ_two]
    <;> ring
  refine ⟨hm, hv, ?_⟩
  rw [hv]
  exact (heterogeneity_conversion α).1

/-- The exact C2 expectation Var(t-hat)+A+A*, combining Propositions
1 and 2 at a=b=2 (main pp. 234–237). -/
theorem c2_expectation (D : Design U Ω) (hD : Positive D) (y : U → ℝ) :
    expect D (c2Estimator D y) = variance D (htTotal D y)+biasA D y+quadraticA D y := by
  unfold c2Estimator
  rw [expect_add, proposition1 D hD, expected_quadratic_correction D hD]

/-- T4 (iv–vii), corrected p. 237: exact bias change on ORDERED cluster
zero pairs, hence the factor 1/2. Equal sizes suffice for no increase, and
constant outcomes can increase bias at unequal linked sizes. -/
theorem aggregation_bias_change {G : Type} [Fintype G]
    (D : Design G Ω) (h : Positive D) (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (y : (Σ g, Fin (n g)) → ℝ) :
    let Y := groupTotal n y
    let S := groupSquares n y
    let Δ := (expect (liftDesign D n) (c2Estimator (liftDesign D n) y) -
      variance (liftDesign D n) (htTotal (liftDesign D n) y)) -
      (expect D (c2Estimator D Y) - variance D (htTotal D Y))
    Δ = (∑ g, ∑ h', if g ≠ h' ∧ joint D g h' = 0 then
      (n h' : ℝ)*S g + (n g : ℝ)*S h' - Y g^2 - Y h'^2 else 0)/2 ∧
    ((∀ g h', g ≠ h' ∧ joint D g h' = 0 → n g = n h') → 0 ≤ Δ) ∧
    (∀ v : ℝ, (∀ k, y k = v) →
      Δ = -v^2 * (∑ g, ∑ h', if g ≠ h' ∧ joint D g h' = 0 then
        ((n g : ℝ) - n h')^2 else 0)/2) ∧
    0 ≤ expect D (c2Estimator D Y) - variance D (htTotal D Y) ∧
    0 ≤ expect (liftDesign D n) (c2Estimator (liftDesign D n) y) -
      variance (liftDesign D n) (htTotal (liftDesign D n) y) := by
  dsimp only
  let Y := groupTotal n y
  let S := groupSquares n y
  let Δ := (expect (liftDesign D n) (c2Estimator (liftDesign D n) y) -
    variance (liftDesign D n) (htTotal (liftDesign D n) y)) -
      (expect D (c2Estimator D Y) - variance D (htTotal D Y))
  have hp := lift_positive D h n
  have hΔ : Δ = quadraticA (liftDesign D n) y-quadraticA D Y := by
    dsimp [Δ]
    rw [c2_expectation D h, c2_expectation (liftDesign D n) hp,
      aggregation_A_preserved D h n y]
    ring
  have hex : Δ = (∑ g, ∑ h', if g ≠ h' ∧ joint D g h' = 0 then
      (n h' : ℝ)*S g+(n g : ℝ)*S h'-Y g^2-Y h'^2 else 0)/2 := by
    rw [hΔ, quadraticA_lift D h]
    unfold quadraticA
    simp only [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro g _
    apply Finset.sum_congr rfl; intro h' _
    split_ifs <;> ring
  refine ⟨hex, ?_, ?_, ?_, ?_⟩
  · intro hsizes
    change 0 ≤ Δ
    rw [hex]
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg; intro g _
    apply Finset.sum_nonneg; intro h' _
    by_cases he : g ≠ h' ∧ joint D g h' = 0
    · rw [if_pos he]
      have hg : Y g^2 ≤ (n g : ℝ)*S g := group_cauchy n y g
      have hh : Y h'^2 ≤ (n h' : ℝ)*S h' := group_cauchy n y h'
      have hncast : (n g : ℝ) = (n h' : ℝ) := congrArg (fun a : ℕ => (a:ℝ)) (hsizes g h' he)
      rw [hncast] at hg
      rw [← hncast] at hh
      linarith
    · simp [he]
  · intro v hy
    have hY (g : G) : Y g = (n g : ℝ)*v := by
      simp [Y, groupTotal, hy]
    have hS (g : G) : S g = (n g : ℝ)*v^2 := by
      simp [S, groupSquares, hy]
    change Δ = _
    rw [hex]
    simp only [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro g _
    apply Finset.sum_congr rfl; intro h' _
    split_ifs <;> (try simp only [hY, hS]) <;> ring
  · have hc := corollary2 D h Y
    linarith
  · have hc := corollary2 (liftDesign D n) hp y
    linarith


/-- The count vector (29,0,...,0) corresponding to the size witness
(30,1,...,1), T12 (C3). -/
def nbWitness (k : Fin 8) : ℕ := if k = 0 then 29 else 0

/-- Independent eight-coordinate NB counts with the printed mean 6 and
standard deviation 4 (supplement Section C, p. A3), shape 18/5 and p=3/8.
This is the actual atomic product-weight measure, not a stipulated expectation. -/
def nbProductLaw : Measure (Fin 8 → ℕ) :=
  Measure.sum (fun v : Fin 8 → ℕ =>
    ENNReal.ofReal (∏ k, nbMass (v k)) • Measure.dirac v)


/-- m_g in T4 (vi): the number of groups with zero joint inclusion
with g, excluding g itself. -/
def zeroNeighborCount {G : Type} [Fintype G] (D : Design G Ω) (g : G) : ℕ :=
  (Finset.univ.filter (fun h => g ≠ h ∧ joint D g h = 0)).card

/-- M_g in T4 (vi): the sum of sizes of g's zero-inclusion neighbors. -/
def zeroNeighborSize {G : Type} [Fintype G] (D : Design G Ω) (n : G → ℕ) (g : G) : ℝ :=
  ∑ h, if g ≠ h ∧ joint D g h = 0 then (n h:ℝ) else 0

/-- T4 (vi), the more general lower bound when linked cluster sizes
may differ. It retains the paper's original-unit bias and group totals. -/
theorem aggregation_degree_bound {G : Type} [Fintype G]
    (D : Design G Ω) (hD : Positive D) (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (y : (Σ g, Fin (n g)) → ℝ) :
    (∑ g, (zeroNeighborSize D n g-(zeroNeighborCount D g:ℝ)*(n g:ℝ))*groupSquares n y g) ≤
      (expect (liftDesign D n) (c2Estimator (liftDesign D n) y)-
        variance (liftDesign D n) (htTotal (liftDesign D n) y)) -
      (expect D (c2Estimator D (groupTotal n y))-
        variance D (htTotal D (groupTotal n y))) := by
  let Y := groupTotal n y
  let S := groupSquares n y
  let f : G → G → ℝ := fun g h => ((n h:ℝ)-(n g:ℝ))*S g
  have hcard (g : G) : (zeroNeighborCount D g:ℝ) =
      ∑ h, if g ≠ h ∧ joint D g h = 0 then (1:ℝ) else 0 := by
    simp only [zeroNeighborCount, ← Finset.sum_filter]
    simp
  have hB : (∑ g, (zeroNeighborSize D n g-(zeroNeighborCount D g:ℝ)*(n g:ℝ))*S g) =
      ∑ g, ∑ h, if g ≠ h ∧ joint D g h = 0 then f g h else 0 := by
    apply Finset.sum_congr rfl; intro g _
    rw [hcard]
    unfold zeroNeighborSize
    simp only [sub_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro h _
    split_ifs <;> (try dsimp [f]) <;> ring
  have hswap := zero_pair_sum_swap D f
  have hbound :
      (∑ g, ∑ h, if g ≠ h ∧ joint D g h = 0 then f g h else 0)+
      (∑ g, ∑ h, if g ≠ h ∧ joint D g h = 0 then f h g else 0) ≤
      ∑ g, ∑ h, if g ≠ h ∧ joint D g h = 0 then
        (n h:ℝ)*S g+(n g:ℝ)*S h-Y g^2-Y h^2 else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro g _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro h _
    by_cases he : g ≠ h ∧ joint D g h = 0
    · rw [if_pos he, if_pos he, if_pos he]
      have hg : Y g^2 ≤ (n g:ℝ)*S g := group_cauchy n y g
      have hh : Y h^2 ≤ (n h:ℝ)*S h := group_cauchy n y h
      dsimp [f]
      nlinarith
    · simp [he]
  rw [hswap] at hbound
  have hex := (aggregation_bias_change D hD n hn y).1
  (try dsimp only at hex)
  change (∑ g, (zeroNeighborSize D n g-(zeroNeighborCount D g:ℝ)*(n g:ℝ))*S g) ≤ _
  rw [hB, hex]
  (try dsimp [f, Y, S] at hbound ⊢)
  linarith

/-- T4 (v): constant nonzero outcomes strictly increase C2 bias on
aggregation whenever a zero-inclusion edge joins unequal nonempty groups. -/
theorem constant_aggregation_strict {G : Type} [Fintype G]
    (D : Design G Ω) (hD : Positive D) (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (v : ℝ) (hv : v ≠ 0)
    (hedge : ∃ g h, g ≠ h ∧ joint D g h = 0 ∧ n g ≠ n h) :
    expect (liftDesign D n) (c2Estimator (liftDesign D n) (fun _ => v))-
      variance (liftDesign D n) (htTotal (liftDesign D n) (fun _ => v)) <
    expect D (c2Estimator D (groupTotal n (fun _ => v)))-
      variance D (htTotal D (groupTotal n (fun _ => v))) := by
  have hf := (aggregation_bias_change D hD n hn (fun _ => v)).2.2.1 v (fun _ => rfl)
  let f : G → G → ℝ := fun g h => if g ≠ h ∧ joint D g h = 0 then
    ((n g:ℝ)-n h)^2 else 0
  have hn0 (g h : G) : 0 ≤ f g h := by dsimp [f]; split_ifs <;> positivity
  rcases hedge with ⟨g,h,hgh,hj,hng⟩
  have hneq : (n g:ℝ) ≠ (n h:ℝ) := by exact_mod_cast hng
  have hterm : 0 < f g h := by
    rw [show f g h = ((n g:ℝ)-n h)^2 by simp [f,hgh,hj]]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hneq)
  have hinner := Finset.single_le_sum (fun h' _ => hn0 g h') (Finset.mem_univ h)
  have houter : (∑ h', f g h') ≤ ∑ g', ∑ h', f g' h' := Finset.single_le_sum
    (fun g' _ => Finset.sum_nonneg (fun h' _ => hn0 g' h')) (Finset.mem_univ g)
  have hsum : 0 < ∑ g', ∑ h', f g' h' := lt_of_lt_of_le hterm (le_trans hinner houter)
  have hneg : -v^2*(∑ g', ∑ h', f g' h')/2 < 0 := by
    have hp := mul_pos (sq_pos_of_ne_zero hv) hsum
    linarith
  change _ = -v^2*(∑ g', ∑ h', f g' h')/2 at hf
  linarith

/-- T10 (C1,C3): the exact printed PPS probabilities and all mean-scale
values of the negative-bias witness, with the ORIGINAL divisor 8². -/
theorem random8_mean_counterexample :
    (∑ k, randomSize8 k) = 16 ∧
    (∀ k, pi random8 k = printedPPS 2 randomSize8 k) ∧
    variance random8 (htMean random8 randomOutcome8) = 4/3 ∧
    expect random8 (fun ω => htVarianceEstimator random8 randomOutcome8 ω/64) = 13/12 ∧
    expect random8 (fun ω => htVarianceEstimator random8 randomOutcome8 ω/64)-
      variance random8 (htMean random8 randomOutcome8) = -1/4 ∧
    expect random8 (fun ω => htVarianceEstimator random8 randomOutcome8 ω/64) <
      variance random8 (htMean random8 randomOutcome8) := by
  rcases random8_counterexample with ⟨hx, ha, hstar, he, hv, hh, hc⟩
  have hs : (∑ k, randomSize8 k) = 16 := by
    norm_num [randomSize8, Fin.sum_univ_succ]
  have hp (k : Fin 8) : pi random8 k = printedPPS 2 randomSize8 k := by
    simp only [random8, fourPhase_pi, printedPPS, hs]
    fin_cases k <;> norm_num [randomSize8]
  refine ⟨hs, hp, ?_⟩
  unfold htMean
  simp only [Fintype.card_fin, variance_div_const, expect_div_const, hv, hh]
  norm_num

/-- T17 (i): ordinary pair covariance, variance, and correlation under
the stated common-stratum model, using exactly its second-moment assumptions. -/
theorem same_stratum_correlation {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (α : ℝ) (S ε ε' : Ξ → ℝ)
    (hS : ∀ᵐ ξ ∂μ, S ξ = 1 ∨ S ξ = -1)
    (hSmean : outcomeE μ S = 0) (hint : Integrable S μ)
    (hε : Integrable ε μ) (hε' : Integrable ε' μ)
    (hmeans : outcomeE μ ε = 0 ∧ outcomeE μ ε' = 0)
    (hsecond : Integrable (fun ξ => ε ξ^2) μ ∧ Integrable (fun ξ => ε' ξ^2) μ ∧
      outcomeE μ (fun ξ => ε ξ^2) = 1 ∧ outcomeE μ (fun ξ => ε' ξ^2) = 1)
    (hcross : Integrable (fun ξ => S ξ*ε ξ) μ ∧ Integrable (fun ξ => S ξ*ε' ξ) μ ∧
      Integrable (fun ξ => ε ξ*ε' ξ) μ ∧ outcomeE μ (fun ξ => S ξ*ε ξ) = 0 ∧
      outcomeE μ (fun ξ => S ξ*ε' ξ) = 0 ∧ outcomeE μ (fun ξ => ε ξ*ε' ξ) = 0) :
    let Y := fun ξ => α*S ξ+ε ξ
    let Y' := fun ξ => α*S ξ+ε' ξ
    outcomeE μ Y = 0 ∧ outcomeE μ Y' = 0 ∧
    outcomeE μ (fun ξ => Y ξ^2) = α^2+1 ∧
    outcomeE μ (fun ξ => Y' ξ^2) = α^2+1 ∧
    outcomeE μ (fun ξ => Y ξ*Y' ξ) = α^2 ∧
    outcomeE μ (fun ξ => Y ξ*Y' ξ)/
      Real.sqrt (outcomeE μ (fun ξ => Y ξ^2)*outcomeE μ (fun ξ => Y' ξ^2)) =
      pairCorrelationFormula α := by
  dsimp only
  have hsqae : (fun ξ => S ξ^2) =ᵐ[μ] (fun _ => (1:ℝ)) := by
    filter_upwards [hS] with ξ hξ
    rcases hξ with hξ | hξ <;> simp [hξ]
  have hsqint : Integrable (fun ξ => S ξ^2) μ := (integrable_const (1:ℝ)).congr hsqae.symm
  have hsq : outcomeE μ (fun ξ => S ξ^2) = 1 := by
    unfold outcomeE
    rw [integral_congr_ae hsqae]
    simp
  have hmean (e : Ξ → ℝ) (hintE : Integrable e μ) (he : outcomeE μ e = 0) :
      outcomeE μ (fun ξ => α*S ξ+e ξ) = 0 := by
    unfold outcomeE
    rw [integral_add (hint.const_mul α) hintE, integral_const_mul α S]
    change α*outcomeE μ S+outcomeE μ e = 0
    rw [hSmean, he]; ring
  have hsecondE (e : Ξ → ℝ) (hi2 : Integrable (fun ξ => e ξ^2) μ)
      (hiSE : Integrable (fun ξ => S ξ*e ξ) μ)
      (he2 : outcomeE μ (fun ξ => e ξ^2) = 1)
      (heSE : outcomeE μ (fun ξ => S ξ*e ξ) = 0) :
      outcomeE μ (fun ξ => (α*S ξ+e ξ)^2) = α^2+1 := by
    have hex : (fun ξ => (α*S ξ+e ξ)^2) =
        (fun ξ => (α^2*S ξ^2+(2*α)*(S ξ*e ξ))+e ξ^2) := by funext ξ; ring
    have hsum : Integrable (fun ξ => α^2*S ξ^2+(2*α)*(S ξ*e ξ)) μ :=
      (hsqint.const_mul _).add (hiSE.const_mul _)
    rw [hex]
    unfold outcomeE
    rw [integral_add hsum hi2,
      integral_add (hsqint.const_mul _) (hiSE.const_mul _),
      integral_const_mul (α^2) (fun ξ => S ξ^2),
      integral_const_mul (2*α) (fun ξ => S ξ*e ξ)]
    change α^2*outcomeE μ (fun ξ => S ξ^2)+
      (2*α)*outcomeE μ (fun ξ => S ξ*e ξ)+outcomeE μ (fun ξ => e ξ^2) = _
    rw [hsq, heSE, he2]; ring
  have hm := hmean ε hε hmeans.1
  have hm' := hmean ε' hε' hmeans.2
  have hs := hsecondE ε hsecond.1 hcross.1 hsecond.2.2.1 hcross.2.2.2.1
  have hs' := hsecondE ε' hsecond.2.1 hcross.2.1 hsecond.2.2.2 hcross.2.2.2.2.1
  have hc : outcomeE μ (fun ξ => (α*S ξ+ε ξ)*(α*S ξ+ε' ξ)) = α^2 := by
    have hex : (fun ξ => (α*S ξ+ε ξ)*(α*S ξ+ε' ξ)) =
        (fun ξ => ((α^2*S ξ^2+α*(S ξ*ε ξ))+α*(S ξ*ε' ξ))+ε ξ*ε' ξ) := by
      funext ξ; ring
    have h1 : Integrable (fun ξ => α^2*S ξ^2+α*(S ξ*ε ξ)) μ :=
      (hsqint.const_mul _).add (hcross.1.const_mul _)
    have h2 : Integrable (fun ξ => (α^2*S ξ^2+α*(S ξ*ε ξ))+α*(S ξ*ε' ξ)) μ :=
      h1.add (hcross.2.1.const_mul _)
    rw [hex]
    unfold outcomeE
    rw [integral_add h2 hcross.2.2.1, integral_add h1 (hcross.2.1.const_mul _),
      integral_add (hsqint.const_mul _) (hcross.1.const_mul _),
      integral_const_mul (α^2) (fun ξ => S ξ^2),
      integral_const_mul α (fun ξ => S ξ*ε ξ),
      integral_const_mul α (fun ξ => S ξ*ε' ξ)]
    change α^2*outcomeE μ (fun ξ => S ξ^2)+
      α*outcomeE μ (fun ξ => S ξ*ε ξ)+α*outcomeE μ (fun ξ => S ξ*ε' ξ)+
      outcomeE μ (fun ξ => ε ξ*ε' ξ) = _
    rw [hsq, hcross.2.2.2.1, hcross.2.2.2.2.1, hcross.2.2.2.2.2]
    ring
  refine ⟨hm, hm', hs, hs', hc, ?_⟩
  rw [hc, hs, hs']
  have hroot : Real.sqrt ((α^2+1)*(α^2+1)) = α^2+1 := by
    rw [← pow_two, Real.sqrt_sq (by positivity : 0 ≤ α^2+1)]
  rw [hroot]
  rfl


/-- T1 C6: the explicit alternating population at every periodic population
size; the proof uses group totals rather than expanding an entire population. -/
theorem alternating_family_witness (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    let D := phaseOriginal r m hr
    let z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ := fun k => if k.1.2 = 0 then -1 else 1
    let q : ℝ := 2*r
    let N : ℝ := m*q
    (∑ k, z k) = 0 ∧ biasA D z = -q*(m:ℝ)^2 ∧
    variance D (htMean D z) = 9/5 ∧
    expect D (fun ω => htVarianceEstimator D z ω / N^2) - variance D (htMean D z) = -1/q ∧
    (2 ≤ m → ∀ ω, wrEstimator D z m ω = 0) := by
  dsimp only
  let D := phaseOriginal r m hr
  let z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ := fun k => if k.1.2 = 0 then -1 else 1
  have hmr : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hrr : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hq : (2*(r:ℝ)) ≠ 0 := by positivity
  have hp := phaseOriginal_positive r m hr
  have hY (g : Fin r × Fin 2) : groupTotal (fun _ => m) z g =
      if g.2 = 0 then -(m:ℝ) else m := by
    by_cases hg : g.2 = 0 <;> simp [groupTotal, z, hg]
  have hz : ∑ k, z k = 0 := by
    simp [z, Fintype.sum_sigma, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hS : (∑ g, (groupTotal (fun _ : Fin r × Fin 2 => m) z g)^2) =
      (2*(r:ℝ))*(m:ℝ)^2 := by
    simp_rw [hY]
    have he (g : Fin r × Fin 2) : (if g.2 = 0 then -(m:ℝ) else m)^2 = (m:ℝ)^2 := by
      split_ifs <;> ring
    simp_rw [he]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hA : biasA D z = -(2*(r:ℝ))*(m:ℝ)^2 := by
    rw [(periodic_negative_square r m hr z hz).2.1, hS]
    ring
  have hv : variance D (htTotal D z) = (9/5)*(2*(r:ℝ))^2*(m:ℝ)^2 := by
    rw [(periodic_ht_expectations r m hr hm z hz).2.1]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, hY, phaseProb]
    norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp <;> ring
  have hcard : (Fintype.card (Σ _ : Fin r × Fin 2, Fin m) : ℝ) =
      (m:ℝ)*(2*r) := by
    simp [Fintype.card_sigma, Fintype.card_prod]
    ring
  have ht (g : Fin r × Fin 2) : htTotal D z g =
      (if g.2 = 0 then -(m:ℝ) else m)/phaseProb r g := by
    unfold D phaseOriginal
    rw [aggregation_total_preserved _ (phaseGrouped_positive r hr)]
    change htTotal (oneDraw _ _ _) _ g = _
    rw [oneDraw_total, hY]
  refine ⟨hz, hA, ?_, ?_, ?_⟩
  · change variance D (fun ω => htTotal D z ω / Fintype.card _) = _
    rw [variance_div_const, hv, hcard]
    field_simp <;> ring
  · change expect D (fun ω => htVarianceEstimator D z ω / ((m:ℝ)*(2*r))^2) -
        variance D (fun ω => htTotal D z ω / Fintype.card _) = _
    rw [expect_div_const, variance_div_const, hcard, ← sub_div, proposition1 D hp, hA]
    field_simp
    ring
  · intro _ ω
    unfold wrEstimator
    change (∑ k, indicator D ω k * (z k / (pi D k / (m:ℝ)) - htTotal D z ω)^2) /
      ((Fintype.card (Σ _ : Fin r × Fin 2, Fin m) : ℝ)^2 * m * (m-1:ℝ)) = 0
    have he (k : Σ _ : Fin r × Fin 2, Fin m) :
        indicator D ω k * (z k / (pi D k / (m:ℝ)) - htTotal D z ω)^2 = 0 := by
      by_cases hkg : k.1 = ω
      · have hpk : pi D k = phaseProb r k.1 := (phase_inclusions r m hr).1 k
        have hzkg : z k = if ω.2 = 0 then -1 else 1 := by simp [z, hkg]
        have hpg : phaseProb r ω ≠ 0 := by
          have h := (phaseGrouped_positive r hr) ω
          simpa only [phaseGrouped, oneDraw_pi] using h.ne'
        rw [hpk, hkg, ht, hzkg]
        have hzero : (if ω.2 = 0 then (-1:ℝ) else 1) / (phaseProb r ω / (m:ℝ)) -
            (if ω.2 = 0 then -(m:ℝ) else m) / phaseProb r ω = 0 := by
          split_ifs <;> field_simp <;> ring
        rw [hzero]
        simp
      · have hi : indicator D ω k = 0 := by
          simp [D, phaseOriginal, liftDesign, phaseGrouped, oneDraw, indicator, Ne.symm hkg]
        rw [hi]; ring
    simp_rw [he]
    simp

/-- A unit's C2 correction counts its distinct zero-probability partners;
the two half-terms in the ordered pair sum combine by symmetry (p. 237). -/
theorem quadratic_correction_degree (D : Design U Ω) (hD : Positive D)
    (y : U → ℝ) (ω : Ω) :
    quadraticCorrection D y ω = ∑ k, (zeroNeighborCount D k : ℝ) *
      indicator D ω k * (y k^2 / pi D k) := by
  let f : U → ℝ := fun k => indicator D ω k * (y k^2/(2*pi D k))
  have hs := zero_pair_sum_swap D (fun k _ => f k)
  have hc (k : U) : (∑ l, if k ≠ l ∧ joint D k l = 0 then f k else 0) =
      (zeroNeighborCount D k : ℝ) * f k := by
    rw [← Finset.sum_filter]
    simp [zeroNeighborCount, nsmul_eq_mul]
  have he : quadraticCorrection D y ω =
      (∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then f k else 0) +
      (∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then f l else 0) := by
    unfold quadraticCorrection
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _
    split_ifs <;> simp [f]
  rw [he, hs]
  simp_rw [hc]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  dsimp [f]
  field_simp [(hD k).ne']
  ring

/-- Summing a constant over all other finite-population units excludes
exactly one diagonal term; used to count missing partners (T2 iv). -/
theorem sum_ne_const {G : Type} [Fintype G] [DecidableEq G] (g : G) (c : ℝ) :
    (∑ h, if g ≠ h then c else 0) = ((Fintype.card G : ℝ)-1)*c := by
  have he : (∑ h, if g = h then c else 0) = c := by simp
  have hs : (∑ h, if g ≠ h then c else 0) +
      (∑ h, if g = h then c else 0) = ∑ _ : G, c := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro h _
    by_cases hh : g = h <;> simp [hh]
  rw [he] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  linarith

/-- In the periodic design each original unit has N-m zero-inclusion
partners (T2 iv and T19 i); this counts actual joint probabilities. -/
theorem phase_zero_degree (r m : ℕ) (hr : 0 < r)
    (k : Σ _ : Fin r × Fin 2, Fin m) :
    (zeroNeighborCount (phaseOriginal r m hr) k : ℝ) = (m:ℝ)*(2*r)-m := by
  have hpg (g : Fin r × Fin 2) : phaseProb r g ≠ 0 := by
    have h := phaseGrouped_positive r hr g
    simpa only [phaseGrouped, oneDraw_pi] using h.ne'
  have hz (l : Σ _ : Fin r × Fin 2, Fin m) :
      (k ≠ l ∧ joint (phaseOriginal r m hr) k l = 0) ↔ k.1 ≠ l.1 := by
    rw [(phase_inclusions r m hr).2.1 k l]
    by_cases hh : k.1 = l.1
    · simp [hh, hpg]
    · have hne : k ≠ l := by intro he; exact hh (congrArg Sigma.fst he)
      simp [hh, hne]
  have hc : (zeroNeighborCount (phaseOriginal r m hr) k : ℝ) =
      ∑ l, if k ≠ l ∧ joint (phaseOriginal r m hr) k l = 0 then (1:ℝ) else 0 := by
    simp [zeroNeighborCount, ← Finset.sum_filter]
  rw [hc]
  simp_rw [hz]
  rw [Fintype.sum_sigma]
  have he (g : Fin r × Fin 2) :
      (∑ _ : Fin m, if k.1 ≠ g then (1:ℝ) else 0) = if k.1 ≠ g then (m:ℝ) else 0 := by
    by_cases hh : k.1 = g <;> simp [hh]
  simp_rw [he]
  calc
    (∑ h : Fin r × Fin 2, if k.1 ≠ h then (m:ℝ) else 0) =
      ((Fintype.card (Fin r × Fin 2):ℝ)-1)*(m:ℝ) := sum_ne_const k.1 (m:ℝ)
    _ = _ := by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- A totalled periodic phase has q-1 zero-inclusion partners, T6 iii. -/
theorem phase_grouped_zero_degree (r : ℕ) (hr : 0 < r) (g : Fin r × Fin 2) :
    (zeroNeighborCount (phaseGrouped r hr) g : ℝ) = 2*r-1 := by
  have hz (h : Fin r × Fin 2) :
      (g ≠ h ∧ joint (phaseGrouped r hr) g h = 0) ↔ g ≠ h := by
    by_cases hh : g = h
    · simp [hh]
    · simp [phaseGrouped, oneDraw_joint, hh]
  have hc : (zeroNeighborCount (phaseGrouped r hr) g : ℝ) =
      ∑ h, if g ≠ h ∧ joint (phaseGrouped r hr) g h = 0 then (1:ℝ) else 0 := by
    simp [zeroNeighborCount, ← Finset.sum_filter]
  rw [hc]
  simp_rw [hz]
  calc
    (∑ h : Fin r × Fin 2, if g ≠ h then (1:ℝ) else 0) =
      ((Fintype.card (Fin r × Fin 2):ℝ)-1)*1 := sum_ne_const g (1:ℝ)
    _ = _ := by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- Samplewise C2 corrections in the periodic design, distinguishing
original units from totalled phases (T2 iv and T6 iii-v). -/
theorem phase_correction_values (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (g : Fin r × Fin 2) :
    quadraticCorrection (phaseOriginal r m hr) z g =
      ((m:ℝ)*(2*r)-m)*groupSquares (fun _ => m) z g/phaseProb r g ∧
    quadraticCorrection (phaseGrouped r hr) (groupTotal (fun _ => m) z) g =
      (2*r-1)*(groupTotal (fun _ => m) z g)^2/phaseProb r g := by
  have hi (k : Σ _ : Fin r × Fin 2, Fin m) :
      indicator (phaseOriginal r m hr) g k = if g = k.1 then 1 else 0 := by
    simp [indicator, phaseOriginal, liftDesign, phaseGrouped, oneDraw]
  constructor
  · rw [quadratic_correction_degree _ (phaseOriginal_positive r m hr)]
    simp_rw [phase_zero_degree, (phase_inclusions r m hr).1, hi]
    rw [Fintype.sum_sigma]
    have he (h : Fin r × Fin 2) :
        (∑ j : Fin m, ((m:ℝ)*(2*r)-m)*(if g = h then 1 else 0)*
          (z ⟨h,j⟩^2/phaseProb r h)) =
        if g = h then ((m:ℝ)*(2*r)-m)*groupSquares (fun _ => m) z h/phaseProb r h else 0 := by
      by_cases hh : g = h
      · simp [hh, groupSquares, ← Finset.mul_sum, ← Finset.sum_div, mul_div_assoc]
      · simp [hh]
    simp_rw [he]
    simp
  · rw [quadratic_correction_degree _ (phaseGrouped_positive r hr)]
    have hip (h : Fin r × Fin 2) : pi (phaseGrouped r hr) h = phaseProb r h :=
      oneDraw_pi _ _ _ h
    have hig (h : Fin r × Fin 2) : indicator (phaseGrouped r hr) g h = if g = h then 1 else 0 := by
      simp [indicator, phaseGrouped, oneDraw]
    simp_rw [phase_grouped_zero_degree, hip, hig]
    simp only [ite_mul, mul_ite, zero_mul, mul_zero, mul_one]
    simp
    ring

/-- For a one-phase draw the uncorrected variance estimator is
(1-p_g)Y_g^2/p_g^2 (T2 iii). -/
theorem oneDraw_ht_estimator {G : Type} [Fintype G] (p : G → ℝ)
    (hp : ∀ g, 0 ≤ p g) (hs : ∑ g, p g = 1) (hpos : ∀ g, 0 < p g)
    (Y : G → ℝ) (g : G) :
    htVarianceEstimator (oneDraw p hp hs) Y g = (1-p g)*Y g^2/(p g)^2  := by
  have hi (k : G) : indicator (oneDraw p hp hs) g k = if g = k then 1 else 0 := by
    simp [indicator, oneDraw]
  have he (k l : G) : (if 0 < joint (oneDraw p hp hs) k l then
      indicator (oneDraw p hp hs) g k * indicator (oneDraw p hp hs) g l *
        (inclusionCov (oneDraw p hp hs) k l / joint (oneDraw p hp hs) k l) *
        (Y k / pi (oneDraw p hp hs) k) * (Y l / pi (oneDraw p hp hs) l) else 0) =
      if k = g then (if l = g then (1-p g)*Y g^2/(p g)^2 else 0) else 0 := by
    by_cases hk : k = g
    · subst k
      by_cases hl : l = g
      · subst l
        simp only [joint_self, oneDraw_pi, inclusionCov, hi]
        simp [hpos g, oneDraw_joint, oneDraw_pi]
        field_simp [(hpos g).ne'] <;> ring
      · have hl0 : indicator (oneDraw p hp hs) g l = 0 := by rw [hi]; simp [Ne.symm hl]
        simp [hl0, hl]
    · have hk0 : indicator (oneDraw p hp hs) g k = 0 := by rw [hi]; simp [Ne.symm hk]
      simp [hk0, hk]
  unfold htVarianceEstimator
  simp_rw [he]
  simp

/-- Within a nonempty group, n S_g-Y_g^2 equals n times the sum of
squared deviations from its mean (T6 v). -/
theorem group_deviation_identity {G : Type} (n : G → ℕ)
    (hn : ∀ g, 0 < n g) (z : (Σ g, Fin (n g)) → ℝ) (g : G) :
    (n g : ℝ)*groupSquares n z g-(groupTotal n z g)^2 =
      (n g : ℝ)*(∑ j : Fin (n g), (z ⟨g,j⟩-groupTotal n z g/(n g : ℝ))^2) := by
  have he (j : Fin (n g)) : (z ⟨g,j⟩-groupTotal n z g/(n g : ℝ))^2 =
      z ⟨g,j⟩^2-2*(groupTotal n z g/(n g : ℝ))*z ⟨g,j⟩+
        (groupTotal n z g/(n g : ℝ))^2 := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (n g : ℝ)*groupSquares n z g-(groupTotal n z g)^2 =
    (n g : ℝ)*(groupSquares n z g-2*(groupTotal n z g/(n g : ℝ))*groupTotal n z g+
      (n g : ℝ)*(groupTotal n z g/(n g : ℝ))^2)
  field_simp [(Nat.cast_pos.mpr (hn g) : (0:ℝ) < n g).ne']
  ring

/-- Finite T2 (ii–iv) and T6 (ii–vi), corrected periodic-design statements.
Includes the negative-square identity, both C2 expectations, pointwise
comparison and relative-bias bounds, for EVERY centered population. -/
theorem periodic_finite_correction (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (hz : ∑ k, z k = 0) :
    let D := phaseOriginal r m hr
    let Dc := phaseGrouped r hr
    let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
    let Qg := groupSquares (fun _ : Fin r × Fin 2 => m) z
    let S := ∑ g, Y g^2
    let Q := ∑ g, Qg g
    let q : ℝ := 2*r
    let N : ℝ := m*q
    let V := variance D (htTotal D z)
    let H := expect D (htVarianceEstimator D z)
    let Uc := expect D (c2Estimator D z)
    let Gc := expect Dc (c2Estimator Dc Y)
    (∑ g, Y g) = 0 ∧
    biasA D z = -S ∧ 0 ≤ S ∧ (S = 0 ↔ ∀ g, Y g = 0) ∧
    expect D (htTotal D z) = 0 ∧ V = ∑ g, Y g^2 / phaseProb r g ∧
    H = V-S ∧ Uc = V-S+(N-m)*Q ∧ Gc = V+(q-2)*S ∧
    (∀ g, htTotal D z g = Y g / phaseProb r g ∧
      htVarianceEstimator D z g = (1-phaseProb r g)*Y g^2/(phaseProb r g)^2 ∧
      quadraticCorrection D z g = (N-m)*Qg g / phaseProb r g ∧
      quadraticCorrection Dc Y g = (q-1)*Y g^2 / phaseProb r g ∧
      c2Estimator D z g - c2Estimator Dc Y g =
        (q-1)/phaseProb r g * ((m:ℝ)*Qg g - Y g^2) ∧
      c2Estimator D z g - c2Estimator Dc Y g =
        (m:ℝ)*(q-1)/phaseProb r g *
          (∑ j : Fin m, (z ⟨g,j⟩-Y g/(m:ℝ))^2) ∧
      0 ≤ c2Estimator D z g - c2Estimator Dc Y g) ∧
    Uc - Gc = (q-1)*((m:ℝ)*Q-S) ∧ V ≤ Gc ∧ Gc ≤ Uc ∧
    (3*q/5)*S ≤ V ∧ V ≤ 3*q*S ∧
    (0 < V → -5/(3*q) ≤ biasA D z/V ∧ biasA D z/V ≤ -1/(3*q) ∧
      (q-2)/(3*q) ≤ (Gc-V)/V ∧ (Gc-V)/V ≤ 5*(q-2)/(3*q)) := by
  dsimp only
  let D := phaseOriginal r m hr
  let Dc := phaseGrouped r hr
  let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
  let Qg := groupSquares (fun _ : Fin r × Fin 2 => m) z
  let S := ∑ g, Y g^2
  let Q := ∑ g, Qg g
  let q : ℝ := 2*r
  let N : ℝ := m*q
  let V := variance D (htTotal D z)
  let Uc := expect D (c2Estimator D z)
  let Gc := expect Dc (c2Estimator Dc Y)
  have hD := phaseOriginal_positive r m hr
  have hDc := phaseGrouped_positive r hr
  have hpg (g : Fin r × Fin 2) : 0 < phaseProb r g := by
    simpa only [phaseGrouped, oneDraw_pi] using hDc g
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq2 : 0 ≤ q-2 := by dsimp [q]; linarith
  have hq1 : 0 ≤ q-1 := by linarith
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hneg := periodic_negative_square r m hr z hz
  have hht := periodic_ht_expectations r m hr hm z hz
  have hY : (∑ g, Y g) = 0 := hneg.1
  have hA : biasA D z = -S := hneg.2.1
  have hS : 0 ≤ S := hneg.2.2.1
  have hSzero : S = 0 ↔ ∀ g, Y g = 0 := hneg.2.2.2
  have hV : V = ∑ g, Y g^2/phaseProb r g := hht.2.1
  have hH : expect D (htVarianceEstimator D z) = V-S := hht.2.2
  have hpres := aggregation_preservation Dc hDc (fun _ => m) (fun _ => hm) z
  have hvg : variance Dc (htTotal Dc Y) = V := hpres.2.1.symm
  have hag : biasA Dc Y = -S := hpres.2.2.2.symm.trans hA
  have hQg : ∀ g, quadraticCorrection D z g = (N-m)*Qg g/phaseProb r g := by
    intro g; exact (phase_correction_values r m hr hm z g).1
  have hQY : ∀ g, quadraticCorrection Dc Y g = (q-1)*Y g^2/phaseProb r g := by
    intro g; exact (phase_correction_values r m hr hm z g).2
  have hEQ : expect D (quadraticCorrection D z) = (N-m)*Q := by
    change (∑ g, phaseProb r g * quadraticCorrection D z g) = _
    simp_rw [hQg]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro g _
    field_simp [(hpg g).ne'] <;> ring
  have hEG : expect Dc (quadraticCorrection Dc Y) = (q-1)*S := by
    change (∑ g, phaseProb r g * quadraticCorrection Dc Y g) = _
    simp_rw [hQY]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro g _
    field_simp [(hpg g).ne'] <;> ring
  have hUc : Uc = V-S+(N-m)*Q := by
    unfold Uc c2Estimator
    rw [expect_add, hH, hEQ]
  have hGc : Gc = V+(q-2)*S := by
    unfold Gc c2Estimator
    rw [expect_add, proposition1 Dc hDc, hvg, hag, hEG]
    ring
  have htot (g : Fin r × Fin 2) : htTotal D z g = Y g/phaseProb r g := by
    calc
      htTotal D z g = htTotal Dc Y g := hpres.1 g
      _ = _ := oneDraw_total _ _ _ Y g
  have hhat (g : Fin r × Fin 2) :
      htVarianceEstimator D z g = (1-phaseProb r g)*Y g^2/(phaseProb r g)^2 := by
    calc
      htVarianceEstimator D z g = htVarianceEstimator Dc Y g := hpres.2.2.1 g
      _ = _ := oneDraw_ht_estimator _ _ _ hpg Y g
  have hdiff (g : Fin r × Fin 2) :
      c2Estimator D z g-c2Estimator Dc Y g =
        (q-1)/phaseProb r g*((m:ℝ)*Qg g-Y g^2) := by
    unfold c2Estimator
    have hEp : htVarianceEstimator D z g = htVarianceEstimator Dc Y g := hpres.2.2.1 g
    rw [hEp, hQg, hQY]
    dsimp [N]
    ring
  have hdeviation (g : Fin r × Fin 2) :
      c2Estimator D z g-c2Estimator Dc Y g =
        (m:ℝ)*(q-1)/phaseProb r g*(∑ j : Fin m, (z ⟨g,j⟩-Y g/(m:ℝ))^2) := by
    rw [hdiff, group_deviation_identity (fun _ => m) (fun _ => hm)]
    ring
  have hnon (g : Fin r × Fin 2) : 0 ≤ c2Estimator D z g-c2Estimator Dc Y g := by
    rw [hdiff]
    exact mul_nonneg (div_nonneg hq1 (hpg g).le)
      (sub_nonneg.mpr (group_cauchy (fun _ => m) z g))
  have hdelta : Uc-Gc = (q-1)*((m:ℝ)*Q-S) := by
    rw [hUc, hGc]
    dsimp [N]
    ring
  have hCS : S ≤ (m:ℝ)*Q := by
    dsimp [S,Q]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro g _
    exact group_cauchy (fun _ => m) z g
  have hVG : V ≤ Gc := by rw [hGc]; nlinarith [mul_nonneg hq2 hS]
  have hGU : Gc ≤ Uc := by
    have he : 0 ≤ Uc-Gc := by
      rw [hdelta]; exact mul_nonneg hq1 (sub_nonneg.mpr hCS)
    linarith
  have hprob (g : Fin r × Fin 2) :
      3*q/5 ≤ (phaseProb r g)⁻¹ ∧ (phaseProb r g)⁻¹ ≤ 3*q := by
    unfold phaseProb
    by_cases hg : g.2 = 0
    · rw [if_pos hg]; simp only [one_div, inv_inv]
      dsimp [q]; constructor <;> linarith
    · rw [if_neg hg]; rw [inv_div]
      dsimp [q]; constructor <;> linarith
  have hVl : (3*q/5)*S ≤ V := by
    rw [hV]
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro g _
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right (hprob g).1 (sq_nonneg (Y g))
  have hVu : V ≤ 3*q*S := by
    rw [hV]
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro g _
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right (hprob g).2 (sq_nonneg (Y g))
  refine ⟨hY, hA, hS, hSzero, hht.1, hV, hH, hUc, hGc, ?_,
    hdelta, hVG, hGU, hVl, hVu, ?_⟩
  · intro g
    exact ⟨htot g, hhat g, hQg g, hQY g, hdiff g, hdeviation g, hnon g⟩
  · intro hVpos
    have h3q : 0 < 3*q := by positivity
    have hSl : 1/(3*q) ≤ S/V := by
      apply (div_le_div_iff₀ h3q hVpos).mpr
      nlinarith [hVu]
    have hSu : S/V ≤ 5/(3*q) := by
      apply (div_le_div_iff₀ hVpos h3q).mpr
      nlinarith [hVl]
    have hl : -5/(3*q) ≤ biasA D z/V := by
      rw [hA]; simpa only [neg_div] using neg_le_neg hSu
    have hu : biasA D z/V ≤ -1/(3*q) := by
      rw [hA]; simpa only [neg_div] using neg_le_neg hSl
    have hgl : (q-2)/(3*q) ≤ (Gc-V)/V := by
      have hh := mul_le_mul_of_nonneg_left hSl hq2
      rw [hGc]
      convert hh using 1 <;> ring
    have hgu : (Gc-V)/V ≤ 5*(q-2)/(3*q) := by
      have hh := mul_le_mul_of_nonneg_left hSu hq2
      rw [hGc]
      convert hh using 1 <;> ring
    exact ⟨hl, hu, hgl, hgu⟩

/-- T5 (C3): all exact original-unit and totalled values of the explicit
120-unit population; mean-scale normalization remains the ORIGINAL N². -/
theorem row21_exact_witness :
    let D := phaseOriginal 2 30 (by norm_num)
    let Dc := phaseGrouped 2 (by norm_num)
    let Y := groupTotal (fun _ : Fin 2 × Fin 2 => 30) row21Fibre
    (∑ k, row21Fibre k) = 0 ∧ (∑ g, Y g^2) = 57600 ∧
    (∑ k, row21Fibre k^2) = 37880 ∧
    variance D (htTotal D row21Fibre) = 414720 ∧
    expect D (htVarianceEstimator D row21Fibre) = 357120 ∧
    expect D (c2Estimator D row21Fibre) = 3766320 ∧
    expect Dc (c2Estimator Dc Y) = 529920 := by
  dsimp only
  let D := phaseOriginal 2 30 (by norm_num)
  let Dc := phaseGrouped 2 (by norm_num)
  let Y := groupTotal (fun _ : Fin 2 × Fin 2 => 30) row21Fibre
  let Qg := groupSquares (fun _ : Fin 2 × Fin 2 => 30) row21Fibre
  let e : Fin 30 → ℝ := fun j => 2*(j:ℝ)-29
  have he0 : (∑ j, e j) = 0 := by norm_num [e, Fin.sum_univ_succ]
  have he2 : (∑ j, e j^2) = 8990 := by norm_num [e, Fin.sum_univ_succ]
  have hY (g : Fin 2 × Fin 2) : Y g = if g.2 = 0 then -120 else 120 := by
    have he (j : Fin 30) : row21Fibre ⟨g,j⟩ = (if g.2 = 0 then -4 else 4)+e j := by
      dsimp [row21Fibre,e]; ring
    change (∑ j, row21Fibre ⟨g,j⟩) = _
    simp_rw [he]
    rw [Finset.sum_add_distrib, he0]
    split_ifs <;> norm_num
  have hQg (g : Fin 2 × Fin 2) : Qg g = 9470 := by
    have he (j : Fin 30) : row21Fibre ⟨g,j⟩^2 =
        (if g.2 = 0 then -4 else 4)^2+2*(if g.2 = 0 then -4 else 4)*e j+e j^2 := by
      dsimp [row21Fibre,e]; ring
    change (∑ j, row21Fibre ⟨g,j⟩^2) = _
    simp_rw [he]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [he0,he2]
    split_ifs <;> norm_num
  have hz : (∑ k, row21Fibre k) = 0 := by
    rw [Fintype.sum_sigma]
    change (∑ g, Y g) = 0
    simp_rw [hY]
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]
  have hS : (∑ g, Y g^2) = 57600 := by
    simp_rw [hY]
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]
  have hQ : (∑ g, Qg g) = 37880 := by simp_rw [hQg]; norm_num
  have hQfull : (∑ k, row21Fibre k^2) = 37880 := by
    rw [Fintype.sum_sigma]
    exact hQ
  have hf := periodic_finite_correction 2 30 (by norm_num) (by norm_num) row21Fibre hz
  dsimp only at hf
  rcases hf with ⟨_,_,_,_,_,hvar,hht,huc,hgc,_⟩
  have hv : variance D (htTotal D row21Fibre) = 414720 := by
    calc
      _ = ∑ g, Y g^2/phaseProb 2 g := hvar
      _ = _ := by
        simp_rw [hY]
        norm_num [phaseProb,Fintype.sum_prod_type,Fin.sum_univ_two]
  have hH : expect D (htVarianceEstimator D row21Fibre) = 357120 := by
    calc
      _ = variance D (htTotal D row21Fibre) - (∑ g, Y g^2) := hht
      _ = _ := by rw [hv,hS]; norm_num
  have hU : expect D (c2Estimator D row21Fibre) = 3766320 := by
    calc
      _ = variance D (htTotal D row21Fibre) - (∑ g, Y g^2) +
        ((30:ℝ)*(2*2)-30)*(∑ g, Qg g) := huc
      _ = _ := by rw [hv,hS,hQ]; norm_num
  have hG : expect Dc (c2Estimator Dc Y) = 529920 := by
    calc
      _ = variance D (htTotal D row21Fibre)+(2*2-2)*(∑ g, Y g^2) := hgc
      _ = _ := by rw [hv,hS]; norm_num
  exact ⟨hz,hS,hQfull,hv,hH,hU,hG⟩


/-- On a selected periodic phase, the with-replacement estimator has the
within-phase sum-of-squares value used in T19 i.
It keeps the original population-mean divisor N². -/
theorem phase_wr_value (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (g : Fin r × Fin 2) :
    let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
    let Qg := groupSquares (fun _ : Fin r × Fin 2 => m) z
    let N : ℝ := (m:ℝ)*(2*r)
    wrEstimator (phaseOriginal r m hr) z m g =
      ((m:ℝ)*Qg g-Y g^2)/(N^2*((m:ℝ)-1)*(phaseProb r g)^2) := by
  dsimp only
  let D := phaseOriginal r m hr
  let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
  let Qg := groupSquares (fun _ : Fin r × Fin 2 => m) z
  let N : ℝ := (m:ℝ)*(2*r)
  have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (m:ℝ)-1 ≠ 0 := by
    have h : (2:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hN : N ≠ 0 := by dsimp [N]; positivity
  have hpg : phaseProb r g ≠ 0 := by
    have h := phaseGrouped_positive r hr g
    simpa only [phaseGrouped, oneDraw_pi] using h.ne'
  have hcard : (Fintype.card (Σ _ : Fin r × Fin 2, Fin m) : ℝ) = N := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [N]
    ring
  have ht : htTotal D z g = Y g/phaseProb r g := by
    calc
      _ = htTotal (phaseGrouped r hr) Y g :=
        aggregation_total_preserved _ (phaseGrouped_positive r hr) _ z g
      _ = _ := oneDraw_total _ _ _ Y g
  have hpi (k : Σ _ : Fin r × Fin 2, Fin m) : pi D k = phaseProb r k.1 :=
    (phase_inclusions r m hr).1 k
  have hi (k : Σ _ : Fin r × Fin 2, Fin m) :
      indicator D g k = if g = k.1 then 1 else 0 := by
    simp [D,indicator,phaseOriginal,liftDesign,phaseGrouped,oneDraw]
  have hquad : (∑ j : Fin m, (z ⟨g,j⟩/(phaseProb r g/(m:ℝ))-Y g/phaseProb r g)^2) =
      ((m:ℝ)^2*Qg g-(m:ℝ)*Y g^2)/(phaseProb r g)^2 := by
    have hp (j : Fin m) : (z ⟨g,j⟩/(phaseProb r g/(m:ℝ))-Y g/phaseProb r g)^2 =
        ((m:ℝ)^2*z ⟨g,j⟩^2-2*(m:ℝ)*Y g*z ⟨g,j⟩+Y g^2)/(phaseProb r g)^2 := by
      field_simp [hpg,hmR.ne'] <;> ring
    simp_rw [hp]
    simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change ((m:ℝ)^2*Qg g-2*(m:ℝ)*Y g*Y g+(m:ℝ)*Y g^2)/(phaseProb r g)^2 = _
    ring
  have hsum : (∑ k, indicator D g k*(z k/(pi D k/(m:ℝ))-htTotal D z g)^2) =
      ((m:ℝ)^2*Qg g-(m:ℝ)*Y g^2)/(phaseProb r g)^2 := by
    simp_rw [hpi,hi,ht]
    rw [Fintype.sum_sigma]
    have he (h : Fin r × Fin 2) :
        (∑ j : Fin m, (if g = h then (1:ℝ) else 0)*
          (z ⟨h,j⟩/(phaseProb r h/(m:ℝ))-Y g/phaseProb r g)^2) =
        if g = h then (∑ j : Fin m,
          (z ⟨g,j⟩/(phaseProb r g/(m:ℝ))-Y g/phaseProb r g)^2) else 0 := by
      by_cases hh : g = h
      · subst h; simp
      · simp [hh]
    simp_rw [he]
    simpa using hquad
  change (∑ k, indicator D g k*(z k/(pi D k/(m:ℝ))-htTotal D z g)^2) /
    ((Fintype.card (Σ _ : Fin r × Fin 2, Fin m):ℝ)^2*m*(m-1:ℝ)) = _
  rw [hsum,hcard]
  field_simp [hpg,hmR.ne',hm1,hN] <;> ring

/-- T19 (i): deterministic design expectations, valid for EVERY centered
population. The WR identity needs m≥2; nothing probabilistic about outcomes
is used in this statement. -/
theorem periodic_mean_identities (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (hz : ∑ k, z k = 0) :
    let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
    let Qg := groupSquares (fun _ : Fin r × Fin 2 => m) z
    let Q := ∑ k, z k^2
    let N : ℝ := m*(2*r)
    let V := periodicMeanV hr z
    let H := periodicMeanH hr z
    let C := periodicMeanC hr z
    let W := periodicMeanW hr z
    V = (∑ g, Y g^2/phaseProb r g)/N^2 ∧
    H = V-(∑ g, Y g^2)/N^2 ∧ 0 ≤ (∑ g, Y g^2)/N^2 ∧
    C-H = (N-m)*Q/N^2 ∧
    W = ((m:ℝ)*(∑ g, Qg g/phaseProb r g)-N^2*V)/(N^2*((m:ℝ)-1)) := by
  dsimp only
  let D := phaseOriginal r m hr
  let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
  let Qg := groupSquares (fun _ : Fin r × Fin 2 => m) z
  let S := ∑ g, Y g^2
  let Q := ∑ k, z k^2
  let N : ℝ := (m:ℝ)*(2*r)
  let Vt := variance D (htTotal D z)
  have hN : N ≠ 0 := by dsimp [N]; positivity
  have hpg (g : Fin r × Fin 2) : phaseProb r g ≠ 0 := by
    have h := phaseGrouped_positive r hr g
    simpa only [phaseGrouped,oneDraw_pi] using h.ne'
  have hcard : (Fintype.card (Σ _ : Fin r × Fin 2, Fin m):ℝ) = N := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [N]; ring
  have hf := periodic_finite_correction r m hr (by omega) z hz
  dsimp only at hf
  rcases hf with ⟨_,_,hS,_,_,hvar,hht,huc,_,_⟩
  have hVT : Vt = ∑ g, Y g^2/phaseProb r g := hvar
  have hHT : expect D (htVarianceEstimator D z) = Vt-S := hht
  have hQ : (∑ g, Qg g) = Q := by dsimp [Q,Qg]; rw [Fintype.sum_sigma]; rfl
  have hUC : expect D (c2Estimator D z) = Vt-S+(N-m)*Q := by
    calc
      _ = Vt-S+(N-m)*(∑ g, Qg g) := huc
      _ = _ := by rw [hQ]
  have hVM : periodicMeanV hr z = Vt/N^2 := by
    unfold periodicMeanV htMean
    rw [variance_div_const,hcard]
  have hHM : periodicMeanH hr z = (Vt-S)/N^2 := by
    unfold periodicMeanH
    rw [expect_div_const]
    exact congrArg (fun v => v/N^2) hHT
  have hCM : periodicMeanC hr z = (Vt-S+(N-m)*Q)/N^2 := by
    unfold periodicMeanC
    rw [expect_div_const]
    exact congrArg (fun v => v/N^2) hUC
  have hWM : periodicMeanW hr z =
      ((m:ℝ)*(∑ g, Qg g/phaseProb r g)-Vt)/(N^2*((m:ℝ)-1)) := by
    change (∑ g, phaseProb r g*wrEstimator D z m g) = _
    have he (g : Fin r × Fin 2) : phaseProb r g*wrEstimator D z m g =
        ((m:ℝ)*(Qg g/phaseProb r g)-Y g^2/phaseProb r g)/(N^2*((m:ℝ)-1)) := by
      have hw : wrEstimator D z m g =
          ((m:ℝ)*Qg g-Y g^2)/(N^2*((m:ℝ)-1)*(phaseProb r g)^2) := phase_wr_value r m hr hm z g
      rw [hw]
      field_simp [hpg g] <;> ring
    simp_rw [he]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hVT]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hVM,hVT]
  · rw [hHM,hVM]; dsimp [S]; ring
  · exact div_nonneg hS (sq_nonneg N)
  · rw [hCM,hHM]; ring
  · rw [hWM,hVM]
    field_simp [hN] <;> ring


/-- In the one-unit-per-stratum design, the uncorrected total-variance
estimate and its quadratic correction both equal M(M-1) times the sum
of squares of the two selected outcomes (T15 i). -/
theorem strata_quadratic_values (M : ℕ) (hM : 2 ≤ M)
    (y : (Fin M × Fin 2) → ℝ) (ω : Fin M × Fin M) :
    let D := strataDesign M (by omega)
    htVarianceEstimator D y ω = (M:ℝ)*((M:ℝ)-1)*(y (ω.1,0)^2+y (ω.2,1)^2) ∧
    quadraticCorrection D y ω = (M:ℝ)*((M:ℝ)-1)*(y (ω.1,0)^2+y (ω.2,1)^2) := by
  dsimp only
  let D := strataDesign M (by omega)
  let c : ℝ := (M:ℝ)*((M:ℝ)-1)
  have hmR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hpi (k : Fin M × Fin 2) : pi D k = 1/(M:ℝ) := strata_pi_value M (by omega) k
  have hD : Positive D := by intro k; rw [strata_pi_value]; positivity
  have hz (k l : Fin M × Fin 2) : (k ≠ l ∧ joint D k l = 0) ↔
      k.1 ≠ l.1 ∧ k.2 = l.2 := by
    change (k ≠ l ∧ joint (strataDesign M _) k l = 0) ↔ _
    rw [strata_joint_value]
    by_cases he : k = l
    · subst l; simp
    · by_cases hs : k.2 = l.2
      · have hf : k.1 ≠ l.1 := by intro hh; exact he (Prod.ext hh hs)
        simp [he,hs,hf]
      · simp [he,hs,hmR.ne']
  have hd (k : Fin M × Fin 2) : (zeroNeighborCount D k:ℝ) = (M:ℝ)-1 := by
    have hc : (zeroNeighborCount D k:ℝ) =
        ∑ l, if k ≠ l ∧ joint D k l = 0 then (1:ℝ) else 0 := by
      simp [zeroNeighborCount,← Finset.sum_filter]
    rw [hc]
    simp_rw [hz]
    have he : (∑ l : Fin M × Fin 2, if k.1 ≠ l.1 ∧ k.2 = l.2 then (1:ℝ) else 0) =
        ∑ j : Fin M, if k.1 ≠ j then (1:ℝ) else 0 := by
      rcases k with ⟨i,s⟩
      rw [Fintype.sum_prod_type]
      fin_cases s <;> apply Finset.sum_congr rfl <;> intro j _ <;>
        by_cases hij : i = j <;> simp [hij,Fin.sum_univ_two]
    rw [he]
    simpa using sum_ne_const k.1 (1:ℝ)
  have hsamp : (∑ k, indicator D ω k * y k^2) = y (ω.1,0)^2+y (ω.2,1)^2 := by
    simp [D,indicator,strataDesign,Fintype.sum_prod_type,Fin.sum_univ_two,Finset.sum_add_distrib]
  have hterm (k l : Fin M × Fin 2) : (if 0 < joint D k l then
      indicator D ω k*indicator D ω l*(inclusionCov D k l/joint D k l)*
        (y k/pi D k)*(y l/pi D l) else 0) =
      if k = l then indicator D ω k*c*y k^2 else 0 := by
    by_cases he : k = l
    · subst l
      have hi : indicator D ω k * indicator D ω k = indicator D ω k := by
        unfold indicator; split <;> norm_num
      simp only [inclusionCov,joint_self,hpi,hi]
      simp only [ite_true,if_pos (one_div_pos.mpr hmR)]
      dsimp [c]
      field_simp [hmR.ne'] <;> ring
    · by_cases hs : k.2 = l.2
      · have hj : joint D k l = 0 := by
          change joint (strataDesign M _) k l = _
          simp [strata_joint_value,he,hs]
        simp [hj,he]
      · have hc : inclusionCov D k l = 0 := by
          unfold inclusionCov
          change joint (strataDesign M _) k l-pi (strataDesign M _) k*pi (strataDesign M _) l = _
          rw [strata_joint_value,strata_pi_value,strata_pi_value]
          simp only [he,hs,ite_false]
          field_simp [hmR.ne'] <;> ring
        simp [hc,he]
  constructor
  · calc
      htVarianceEstimator D y ω = ∑ k, indicator D ω k*c*y k^2 := by
        unfold htVarianceEstimator; simp_rw [hterm]; simp
      _ = c*(∑ k, indicator D ω k*y k^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring
      _ = _ := by rw [hsamp]
  · rw [quadratic_correction_degree D hD]
    have he (k : Fin M × Fin 2) : (zeroNeighborCount D k:ℝ)*indicator D ω k*(y k^2/pi D k) =
        c*(indicator D ω k*y k^2) := by
      rw [hd,hpi]
      dsimp [c]
      field_simp [hmR.ne'] <;> ring
    simp_rw [he]
    rw [← Finset.mul_sum,hsamp]

/-- T15 (i–ii): all three estimators and the actual design variance for
every fixed two-stratum population, on the ORIGINAL mean scale N=2M. -/
theorem strata_finite_formulas (M : ℕ) (hM : 2 ≤ M) (y : (Fin M × Fin 2) → ℝ) :
    let D := strataDesign M (by omega)
    let N : ℝ := 2*M
    (∀ ω, htMean D y ω = (y (ω.1,0)+y (ω.2,1))/2 ∧
      htVarianceEstimator D y ω/N^2 = ((M:ℝ)-1)/(4*M)*
        (y (ω.1,0)^2+y (ω.2,1)^2) ∧
      c2Estimator D y ω/N^2 = ((M:ℝ)-1)/(2*M)*
        (y (ω.1,0)^2+y (ω.2,1)^2)) ∧
    variance D (htMean D y) = (stratumVariance y 0+stratumVariance y 1)/4 := by
  dsimp only
  let D := strataDesign M (by omega)
  let a : Fin M → ℝ := fun i => y (i,0)
  let b : Fin M → ℝ := fun i => y (i,1)
  have hmR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hfirst (f : Fin M → ℝ) : expect D (fun ω => f ω.1) = (∑ i, f i)/(M:ℝ) := by
    change (∑ ω : Fin M × Fin M, (1/(M:ℝ)^2)*f ω.1) = _
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    calc
      _ = ((M:ℝ)/(M:ℝ)^2)*(∑ i, f i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      _ = _ := by field_simp [hmR.ne'] <;> ring
  have hsecond (f : Fin M → ℝ) : expect D (fun ω => f ω.2) = (∑ i, f i)/(M:ℝ) := by
    change (∑ ω : Fin M × Fin M, (1/(M:ℝ)^2)*f ω.2) = _
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [hmR.ne'] <;> ring
  have hcross (f g : Fin M → ℝ) : expect D (fun ω => f ω.1*g ω.2) =
      (∑ i, f i)*(∑ j, g j)/(M:ℝ)^2 := by
    change (∑ ω : Fin M × Fin M, (1/(M:ℝ)^2)*(f ω.1*g ω.2)) = _
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_assoc]
    rw [pair_sum_factor]
    ring
  have hmean : expect D (htMean D y) = ((∑ i, a i)+(∑ j, b j))/(2*M) := by
    have hf : htMean D y = (fun ω => a ω.1*(1/2)+b ω.2*(1/2)) := by
      funext ω
      rw [strata_sample_mean]
      dsimp [a,b]; ring
    rw [hf,expect_add,expect_mul_const,expect_mul_const,hfirst,hsecond]
    ring
  have hsquare : expect D (fun ω => (htMean D y ω)^2) =
      ((∑ i, a i^2)/(M:ℝ)+(∑ j, b j^2)/(M:ℝ))/4+
        ((∑ i, a i)*(∑ j, b j)/(M:ℝ)^2)/2 := by
    have hf : (fun ω => (htMean D y ω)^2) = (fun ω =>
        (a ω.1)^2*(1/4)+((b ω.2)^2*(1/4)+(a ω.1*b ω.2)*(1/2))) := by
      funext ω
      rw [strata_sample_mean]
      dsimp [a,b]; ring
    rw [hf,expect_add,expect_add,expect_mul_const,expect_mul_const,expect_mul_const,
      hfirst (fun i => a i^2),hsecond (fun i => b i^2),hcross a b]
    ring
  constructor
  · intro ω
    have hvals := strata_quadratic_values M hM y ω
    dsimp only at hvals
    have hh : htVarianceEstimator D y ω =
        (M:ℝ)*((M:ℝ)-1)*(y (ω.1,0)^2+y (ω.2,1)^2) := hvals.1
    have hq : quadraticCorrection D y ω =
        (M:ℝ)*((M:ℝ)-1)*(y (ω.1,0)^2+y (ω.2,1)^2) := hvals.2
    refine ⟨strata_sample_mean M (by omega) y ω, ?_, ?_⟩
    · rw [hh]; field_simp [hmR.ne'] <;> ring
    · unfold c2Estimator
      rw [hh,hq]; field_simp [hmR.ne'] <;> ring
  · rw [variance_second_moment,hmean,hsquare]
    unfold stratumVariance
    dsimp [a,b]
    field_simp [hmR.ne'] <;> ring


/-- Finite linear combinations of mean-zero uncorrelated errors have
second moment σ² sum_k c_k². Adding a fixed signal s adds s², with no
signal-noise cross term. These are the finite moment facts behind the
periodic and stratified corrections (T2 v, T15 iii, T19 ii). -/
theorem noise_linear_moments {Ξ K : Type} [MeasurableSpace Ξ] [Fintype K]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (ε : K → Ξ → ℝ)
    (σ2 : ℝ) (hε : NoiseMoments μ ε σ2) (c : K → ℝ) (s : ℝ) :
    let Z := fun ξ => ∑ k, c k*ε k ξ
    Integrable Z μ ∧ outcomeE μ Z = 0 ∧
    Integrable (fun ξ => Z ξ^2) μ ∧
    outcomeE μ (fun ξ => Z ξ^2) = σ2*(∑ k, c k^2) ∧
    Integrable (fun ξ => (s+Z ξ)^2) μ ∧
    outcomeE μ (fun ξ => (s+Z ξ)^2) = s^2+σ2*(∑ k, c k^2) := by
  dsimp only
  let Z := fun ξ => ∑ k, c k*ε k ξ
  have hi (k : K) : Integrable (fun ξ => c k*ε k ξ) μ := (hε.1 k).1.const_mul (c k)
  have hZ : Integrable Z μ := integrable_finsetSum _ (fun k _ => hi k)
  have hmean : outcomeE μ Z = 0 := by
    unfold outcomeE Z
    rw [integral_finsetSum _ (fun k _ => hi k)]
    simp only [integral_const_mul]
    change (∑ k, c k*outcomeE μ (ε k)) = 0
    simp [fun k => (hε.1 k).2]
  have hprod (k l : K) : Integrable (fun ξ => (c k*c l)*(ε k ξ*ε l ξ)) μ :=
    (hε.2 k l).1.const_mul (c k*c l)
  have hsum (k : K) : Integrable (fun ξ => ∑ l, (c k*c l)*(ε k ξ*ε l ξ)) μ :=
    integrable_finsetSum _ (fun l _ => hprod k l)
  have he : (fun ξ => Z ξ^2) = (fun ξ => ∑ k, ∑ l, (c k*c l)*(ε k ξ*ε l ξ)) := by
    funext ξ
    simp only [Z,pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _; ring
  have hsqint : Integrable (fun ξ => Z ξ^2) μ := by
    rw [he]
    exact integrable_finsetSum _ (fun k _ => hsum k)
  have hsquare : outcomeE μ (fun ξ => Z ξ^2) = σ2*(∑ k, c k^2) := by
    rw [he]
    unfold outcomeE
    rw [integral_finsetSum _ (fun k _ => hsum k)]
    have hinner (k : K) : (∫ ξ, (∑ l, (c k*c l)*(ε k ξ*ε l ξ)) ∂μ) = c k^2*σ2 := by
      rw [integral_finsetSum _ (fun l _ => hprod k l)]
      simp only [integral_const_mul]
      change (∑ l, (c k*c l)*outcomeE μ (fun ξ => ε k ξ*ε l ξ)) = _
      simp_rw [fun l => (hε.2 k l).2]
      simp [mul_ite,pow_two]
    simp_rw [hinner]
    rw [← Finset.sum_mul]
    ring
  have hshift : (fun ξ => (s+Z ξ)^2) = (fun ξ => s^2+((2*s)*Z ξ+Z ξ^2)) := by
    funext ξ; ring
  have hc : Integrable (fun _ : Ξ => s^2) μ := integrable_const _
  have hlin : Integrable (fun ξ => (2*s)*Z ξ) μ := hZ.const_mul _
  have hshiftint : Integrable (fun ξ => (s+Z ξ)^2) μ := by
    rw [hshift]; exact hc.add (hlin.add hsqint)
  have hshiftmean : outcomeE μ (fun ξ => (s+Z ξ)^2) = s^2+σ2*(∑ k, c k^2) := by
    rw [hshift]
    unfold outcomeE
    dsimp only
    have hlinSq : Integrable (fun ξ => (2*s)*Z ξ+Z ξ^2) μ := hlin.add hsqint
    rw [integral_add hc hlinSq,integral_add hlin hsqint,
      integral_const_mul (2*s) Z]
    change (∫ _ : Ξ, s^2 ∂μ)+((2*s)*outcomeE μ Z+outcomeE μ (fun ξ => Z ξ^2)) = _
    rw [hmean,hsquare]
    simp
  exact ⟨hZ,hmean,hsqint,hsquare,hshiftint,hshiftmean⟩

/-- The coefficients of "ε_i - ε-bar" under population demeaning
(supplement A4; corrected T2 v). -/
def centeringCoeff {K : Type} [Fintype K] (i k : K) : ℝ :=
  (if i = k then 1 else 0)-1/(Fintype.card K : ℝ)

/-- The squared coefficients of a demeaned noise coordinate sum to
1-1/N; this is the finite covariance fact used by the corrected model. -/
theorem centering_coeff_square_sum {K : Type} [Fintype K]
    (hK : 0 < Fintype.card K) (i : K) :
    (∑ k, centeringCoeff i k^2) = 1-1/(Fintype.card K : ℝ) := by
  let N : ℝ := Fintype.card K
  have hN : N ≠ 0 := by dsimp [N]; exact_mod_cast hK.ne'
  have he (k : K) : centeringCoeff i k^2 =
      (if i = k then 1-2/N else 0)+(1/N)^2 := by
    unfold centeringCoeff
    by_cases hk : i = k <;> simp only [hk,ite_true,ite_false] <;> dsimp [N] <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hd : (∑ k : K, if i = k then 1-2/N else 0) = 1-2/N := by simp
  rw [hd]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change (1-2/N)+N*(1/N)^2 = 1-1/N
  field_simp [hN] <;> ring

/-- Demeaning gives exactly zero population total (supplement A4),
for every generated outcome vector, not just in expectation. -/
theorem centered_outcomes_zero {K Ξ : Type} [Fintype K]
    (hK : 0 < Fintype.card K) (x : K → ℝ) (β : ℝ)
    (ε : K → Ξ → ℝ) (ξ : Ξ) : ∑ k, centeredOutcomes x β ε ξ k = 0 := by
  have hN : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold centeredOutcomes
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp [hN] <;> ring

/-- The demeaned model is its fixed centered signal plus the finite
linear combination representing ε_i-ε-bar (T2 v; supplement A4). -/
theorem centered_outcomes_linear {K Ξ : Type} [Fintype K]
    (x : K → ℝ) (β : ℝ) (ε : K → Ξ → ℝ) (ξ : Ξ) (i : K) :
    centeredOutcomes x β ε ξ i =
      β*(x i-(∑ k, x k)/(Fintype.card K : ℝ))+
        ∑ k, centeringCoeff i k*ε k ξ := by
  have he : (∑ k, centeringCoeff i k*ε k ξ) =
      ε i ξ-(∑ k, ε k ξ)/(Fintype.card K : ℝ) := by
    unfold centeringCoeff
    simp only [sub_mul,ite_mul,one_mul,zero_mul]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum]
    have hd : (∑ k : K, if i = k then ε k ξ else 0) = ε i ξ := by simp
    rw [hd]
    ring
  rw [he]
  simp only [centeredOutcomes,rawOutcomes,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

/-- Each demeaned outcome's actual second moment is the squared
centered signal plus σ²(1-1/N), under the finite second-moment model
(T2 v, T19 ii). -/
theorem centered_unit_second_moment {Ξ K : Type} [MeasurableSpace Ξ] [Fintype K]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (hK : 0 < Fintype.card K)
    (x : K → ℝ) (β σ2 : ℝ) (ε : K → Ξ → ℝ) (hε : NoiseMoments μ ε σ2) (i : K) :
    Integrable (fun ξ => centeredOutcomes x β ε ξ i^2) μ ∧
    outcomeE μ (fun ξ => centeredOutcomes x β ε ξ i^2) =
      β^2*(x i-(∑ k, x k)/(Fintype.card K : ℝ))^2+
        σ2*(1-1/(Fintype.card K : ℝ)) := by
  have hf : (fun ξ => centeredOutcomes x β ε ξ i^2) = (fun ξ =>
      (β*(x i-(∑ k, x k)/(Fintype.card K : ℝ))+
        ∑ k, centeringCoeff i k*ε k ξ)^2) := by
    funext ξ; rw [centered_outcomes_linear]
  have h := noise_linear_moments μ ε σ2 hε (centeringCoeff i)
    (β*(x i-(∑ k, x k)/(Fintype.card K : ℝ)))
  dsimp only at h
  rcases h with ⟨_,_,_,_,hint,hmoment⟩
  rw [hf]
  refine ⟨hint, ?_⟩
  rw [hmoment,centering_coeff_square_sum hK]
  ring

/-- Coefficients of R_g=sum_{i∈G_g} ε_i-m ε-bar in the corrected
periodic model (T2 v); m/N=1/q. -/
def phaseNoiseCoeff {r m : ℕ} (g : Fin r × Fin 2)
    (k : Σ _ : Fin r × Fin 2, Fin m) : ℝ :=
  (if g = k.1 then 1 else 0)-1/(2*r)

/-- The phase-centered noise has coefficient squared sum m(1-1/q),
the finite covariance calculation in T2 v. -/
theorem phase_noise_coeff_square_sum (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (g : Fin r × Fin 2) :
    (∑ k : Σ _ : Fin r × Fin 2, Fin m, phaseNoiseCoeff g k^2) =
      (m:ℝ)*(1-1/(2*r)) := by
  let q : ℝ := 2*r
  have hq : q ≠ 0 := by dsimp [q]; positivity
  have hc : (Fintype.card (Fin r × Fin 2):ℝ) = q := by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    dsimp [q]; ring
  have hs : (∑ k : Σ _ : Fin r × Fin 2, Fin m, phaseNoiseCoeff g k^2) =
      (m:ℝ)*(∑ h : Fin r × Fin 2, ((if g = h then (1:ℝ) else 0)-1/q)^2) := by
    rw [Fintype.sum_sigma]
    change (∑ h : Fin r × Fin 2, ∑ _j : Fin m,
      ((if g = h then (1:ℝ) else 0)-1/q)^2) = _
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have he (h : Fin r × Fin 2) : ((if g = h then (1:ℝ) else 0)-1/q)^2 =
      (if g = h then 1-2/q else 0)+(1/q)^2 := by
    by_cases hh : g = h <;> simp [hh] <;> ring
  have hd : (∑ h : Fin r × Fin 2, if g = h then 1-2/q else 0) = 1-2/q := by simp
  rw [hs]
  simp_rw [he]
  rw [Finset.sum_add_distrib,hd]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [hc]
  change (m:ℝ)*((1-2/q)+q*(1/q)^2) = (m:ℝ)*(1-1/q)
  field_simp [hq] <;> ring

/-- Each demeaned phase total is its fixed alternating signal plus
R_g=sum_{i∈G_g} ε_i-m ε-bar, exactly as in corrected T2 v. -/
theorem phase_centered_total_formula {Ξ : Type} (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (β : ℝ) (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ)
    (ξ : Ξ) (g : Fin r × Fin 2) :
    groupTotal (fun _ => m) (centeredOutcomes phaseSize β ε ξ) g =
      (m:ℝ)*β*(if g.2 = 0 then -4 else 4)+
        ∑ k : Σ _ : Fin r × Fin 2, Fin m, phaseNoiseCoeff g k*ε k ξ := by
  let q : ℝ := 2*r
  let N : ℝ := (m:ℝ)*q
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hq : q ≠ 0 := by dsimp [q]; positivity
  have hN : N ≠ 0 := by dsimp [N]; exact mul_ne_zero hmR hq
  have hcard : (Fintype.card (Σ _ : Fin r × Fin 2, Fin m):ℝ) = N := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Finset.sum_const,Finset.card_univ,
      Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
    dsimp [N,q]; ring
  have hx : (∑ k : Σ _ : Fin r × Fin 2, Fin m, phaseSize k) = 6*N :=
    (periodic_size_moments r m hr hm).1
  have hraw : (∑ k : Σ _ : Fin r × Fin 2, Fin m, rawOutcomes phaseSize β ε ξ k) =
      6*β*N+(∑ k : Σ _ : Fin r × Fin 2, Fin m, ε k ξ) := by
    simp only [rawOutcomes,Finset.sum_add_distrib,← Finset.mul_sum]
    rw [hx]; ring
  have hgroup : (∑ j : Fin m, rawOutcomes phaseSize β ε ξ ⟨g,j⟩) =
      (m:ℝ)*β*(if g.2 = 0 then 2 else 10)+(∑ j : Fin m, ε ⟨g,j⟩ ξ) := by
    simp only [rawOutcomes,Finset.sum_add_distrib,phaseSize]
    change (∑ _j : Fin m, β*(if g.2 = 0 then (2:ℝ) else 10))+
      (∑ j : Fin m, ε ⟨g,j⟩ ξ) = _
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hind (f : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) :
      (∑ k, (if g = k.1 then (1:ℝ) else 0)*f k) = ∑ j : Fin m, f ⟨g,j⟩ := by
    rw [Fintype.sum_sigma]
    have he (h : Fin r × Fin 2) : (∑ j : Fin m, (if g = h then (1:ℝ) else 0)*f ⟨h,j⟩) =
        if g = h then (∑ j : Fin m, f ⟨g,j⟩) else 0 := by
      by_cases hh : g = h
      · subst h; simp
      · simp [hh]
    simp_rw [he]; simp
  have hnoise : (∑ k : Σ _ : Fin r × Fin 2, Fin m, phaseNoiseCoeff g k*ε k ξ) =
      (∑ j : Fin m, ε ⟨g,j⟩ ξ)-(1/q)*(∑ k : Σ _ : Fin r × Fin 2, Fin m, ε k ξ) := by
    simp only [phaseNoiseCoeff,sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum]
    rw [hind]
  unfold groupTotal centeredOutcomes
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [hcard,hgroup,hraw,hnoise]
  by_cases hg : g.2 = 0 <;> simp only [hg,ite_true,ite_false] <;>
    dsimp [N] <;> field_simp [hq,hmR] <;> ring

/-- The actual second moment of every phase total is
16m²β²+mσ²(1-1/q), requiring only the stated finite error moments
(T2 v, T19 ii). -/
theorem phase_centered_second_moment {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (β σ2 : ℝ) (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ)
    (hε : NoiseMoments μ ε σ2) (g : Fin r × Fin 2) :
    Integrable (fun ξ => (groupTotal (fun _ => m) (centeredOutcomes phaseSize β ε ξ) g)^2) μ ∧
    outcomeE μ (fun ξ => (groupTotal (fun _ => m) (centeredOutcomes phaseSize β ε ξ) g)^2) =
      16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/(2*r)) := by
  have hf : (fun ξ => (groupTotal (fun _ => m) (centeredOutcomes phaseSize β ε ξ) g)^2) =
      (fun ξ => ((m:ℝ)*β*(if g.2 = 0 then -4 else 4)+
        ∑ k : Σ _ : Fin r × Fin 2, Fin m, phaseNoiseCoeff g k*ε k ξ)^2) := by
    funext ξ; rw [phase_centered_total_formula r m hr hm]
  have h := noise_linear_moments μ ε σ2 hε (phaseNoiseCoeff g)
    ((m:ℝ)*β*(if g.2 = 0 then -4 else 4))
  dsimp only at h
  rcases h with ⟨_,_,_,_,hint,he⟩
  rw [hf]
  refine ⟨hint, ?_⟩
  rw [he,phase_noise_coeff_square_sum r m hr hm]
  have hs : (if g.2 = 0 then (-4:ℝ) else 4)^2 = 16 := by split_ifs <;> norm_num
  simp only [mul_pow,hs]
  ring

/-- The reciprocal phase probabilities sum to (9/5)q². This is the
finite design coefficient in T2 v and T19 ii. -/
theorem phase_inverse_sum (r : ℕ) (hr : 0 < r) :
    (∑ g : Fin r × Fin 2, 1/phaseProb r g) = (9/5)*(2*(r:ℝ))^2 := by
  have hrR : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [Fintype.sum_prod_type,phaseProb,Fin.sum_univ_two]
  norm_num only [Fin.reduceEq,ite_true,ite_false]
  change (∑ _i : Fin r, (1/(1/(6*(r:ℝ)))+1/(5/(6*(r:ℝ))))) = _
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp [hrR] <;> ring

/-- T2 v and T19 ii: the actual outcome expectation of A and A/N²
under the stated centered periodic second-moment model. The group-square
sum is integrable and equals qL in expectation; no expected value is
introduced as a definition. -/
theorem periodic_model_bias {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (β σ2 : ℝ) (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ)
    (hε : NoiseMoments μ ε σ2) :
    let D := phaseOriginal r m hr
    let z := centeredOutcomes phaseSize β ε
    let S := fun ξ => ∑ g, (groupTotal (fun _ => m) (z ξ) g)^2
    let q : ℝ := 2*r
    let N : ℝ := (m:ℝ)*q
    let L := 16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/q)
    Integrable S μ ∧ outcomeE μ S = q*L ∧
    outcomeE μ (fun ξ => biasA D (z ξ)) = -q*L ∧
    outcomeE μ (fun ξ => biasA D (z ξ)/N^2) =
      -16*β^2/q-σ2*(1-1/q)/N := by
  dsimp only
  let D := phaseOriginal r m hr
  let z := centeredOutcomes phaseSize β ε
  let Y := fun ξ => groupTotal (fun _ : Fin r × Fin 2 => m) (z ξ)
  let S := fun ξ => ∑ g, Y ξ g^2
  let q : ℝ := 2*r
  let N : ℝ := (m:ℝ)*q
  let L := 16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/q)
  have hq : q ≠ 0 := by dsimp [q]; positivity
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN : N ≠ 0 := by dsimp [N]; exact mul_ne_zero hmR hq
  have hK : 0 < Fintype.card (Σ _ : Fin r × Fin 2, Fin m) := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Finset.sum_const,
      Finset.card_univ,Fintype.card_prod,nsmul_eq_mul]
    positivity
  have hYS (g : Fin r × Fin 2) : Integrable (fun ξ => Y ξ g^2) μ ∧
      outcomeE μ (fun ξ => Y ξ g^2) = L :=
    phase_centered_second_moment μ r m hr hm β σ2 ε hε g
  have hS : Integrable S μ := integrable_finsetSum _ (fun g _ => (hYS g).1)
  have hES : outcomeE μ S = q*L := by
    unfold outcomeE S
    rw [integral_finsetSum _ (fun g _ => (hYS g).1)]
    change (∑ g : Fin r × Fin 2, outcomeE μ (fun ξ => Y ξ g^2)) = _
    simp_rw [fun g => (hYS g).2]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
    dsimp [q]; ring
  have hA : (fun ξ => biasA D (z ξ)) = (fun ξ => -S ξ) := by
    funext ξ
    exact (periodic_negative_square r m hr (z ξ)
      (centered_outcomes_zero hK phaseSize β ε ξ)).2.1
  have hEA : outcomeE μ (fun ξ => biasA D (z ξ)) = -q*L := by
    rw [hA]
    unfold outcomeE
    rw [integral_neg]
    change -outcomeE μ S = _
    rw [hES]; ring
  refine ⟨hS,hES,hEA,?_⟩
  have hd : outcomeE μ (fun ξ => biasA D (z ξ)/N^2) =
      outcomeE μ (fun ξ => biasA D (z ξ))/N^2 := by
    unfold outcomeE; rw [integral_div]
  rw [hd,hEA]
  dsimp [L,N]
  field_simp [hq,hmR] <;> ring

/-- T2 (vi): identifying the calibrated finite formula with ACTUAL
outcome-averaged design bias, rather than defining the expectation to equal it. -/
theorem periodic_calibrated_bias {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (ρ β : ℝ) (hρ : |ρ| ≤ 1)
    (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ)
    (hε : NoiseMoments μ ε (900*(1-ρ^2)))
    (hβ : β^2 = 900*ρ^2*((m:ℝ)*(2*r)-1)/(16*((m:ℝ)*(2*r)))) :
    outcomeE μ (fun ξ => biasA (phaseOriginal r m hr)
      (centeredOutcomes phaseSize β ε ξ)/((m:ℝ)*(2*r))^2) =
        calibratedMeanBias (2*r) ρ ((m:ℝ)*(2*r)) := by
  have h := (periodic_model_bias μ r m hr hm β (900*(1-ρ^2)) ε hε).2.2.2
  rw [h]
  unfold calibratedMeanBias
  rw [hβ]
  have hq : (2*(r:ℝ)) ≠ 0 := by positivity
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp [hq,hmR] <;> ring


/-- T2 (v–vi), T6 (vii), T19 (ii): exact periodic-design model moments,
using only mean-zero uncorrelated errors. Ratios are ratios of model means,
NOT averages of individual population ratios. q=2r and original N=mq. -/
theorem periodic_model_moments {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (β σ2 : ℝ) (hσ : 0 ≤ σ2)
    (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ) (hε : NoiseMoments μ ε σ2) :
    let D := phaseOriginal r m hr
    let Dc := phaseGrouped r hr
    let z := centeredOutcomes phaseSize β ε
    let Y := fun ξ => groupTotal (fun _ : Fin r × Fin 2 => m) (z ξ)
    let q : ℝ := 2*r
    let N : ℝ := m*q
    let L := 16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/q)
    let V := fun ξ => variance D (htTotal D (z ξ))
    let H := fun ξ => expect D (htVarianceEstimator D (z ξ))
    let Uc := fun ξ => expect D (c2Estimator D (z ξ))
    let Gc := fun ξ => expect Dc (c2Estimator Dc (Y ξ))
    let Q := fun ξ => ∑ k, z ξ k^2
    (∀ g, outcomeE μ (fun ξ => Y ξ g ^ 2) = L) ∧
    outcomeE μ (fun ξ => biasA D (z ξ)) = -q*L ∧
    outcomeE μ V = (9/5)*q^2*L ∧
    outcomeE μ H = outcomeE μ V-q*L ∧
    outcomeE μ Q = 16*N*β^2+(N-1)*σ2 ∧
    outcomeE μ Uc = outcomeE μ H+(N-m)*outcomeE μ Q ∧
    outcomeE μ Gc = outcomeE μ V+(q-2)*q*L ∧
    (0 < L → (outcomeE μ H-outcomeE μ V)/outcomeE μ V = -5/(9*q) ∧
      (outcomeE μ Gc-outcomeE μ V)/outcomeE μ V = (5/9)*(1-2/q)) ∧
    outcomeE μ (fun ξ => biasA D (z ξ)/N^2) =
      -16*β^2/q-σ2*(1-1/q)/N ∧
    (2 ≤ m → outcomeE μ (fun ξ => expect D (wrEstimator D (z ξ) m)) =
      (9/5)*σ2/m) := by
  dsimp only
  let D := phaseOriginal r m hr
  let Dc := phaseGrouped r hr
  let z := centeredOutcomes phaseSize β ε
  let Y := fun ξ => groupTotal (fun _ : Fin r × Fin 2 => m) (z ξ)
  let Qg := fun ξ => groupSquares (fun _ : Fin r × Fin 2 => m) (z ξ)
  let S := fun ξ => ∑ g, Y ξ g^2
  let Q := fun ξ => ∑ k, z ξ k^2
  let q : ℝ := 2*r
  let N : ℝ := (m:ℝ)*q
  let L := 16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/q)
  let V := fun ξ => variance D (htTotal D (z ξ))
  let H := fun ξ => expect D (htVarianceEstimator D (z ξ))
  let Uc := fun ξ => expect D (c2Estimator D (z ξ))
  let Gc := fun ξ => expect Dc (c2Estimator Dc (Y ξ))
  let K : ℝ := 16*β^2+σ2*(1-1/N)
  have hq : 0 < q := by dsimp [q]; positivity
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hN : N ≠ 0 := by dsimp [N]; positivity
  have hcard : (Fintype.card (Σ _ : Fin r × Fin 2, Fin m):ℝ) = N := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Finset.sum_const,Finset.card_univ,
      Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
    dsimp [N,q]; ring
  have hK : 0 < Fintype.card (Σ _ : Fin r × Fin 2, Fin m) := by
    have hn : (0:ℝ) < Fintype.card (Σ _ : Fin r × Fin 2, Fin m) := by
      rw [hcard]; dsimp [N]; positivity
    exact_mod_cast hn
  have hz (ξ : Ξ) : ∑ k, z ξ k = 0 := centered_outcomes_zero hK phaseSize β ε ξ
  have hYS (g : Fin r × Fin 2) : Integrable (fun ξ => Y ξ g^2) μ ∧
      outcomeE μ (fun ξ => Y ξ g^2) = L :=
    phase_centered_second_moment μ r m hr hm β σ2 ε hε g
  have hb := periodic_model_bias μ r m hr hm β σ2 ε hε
  dsimp only at hb
  have hS : Integrable S μ := hb.1
  have hES : outcomeE μ S = q*L := hb.2.1
  have hEA : outcomeE μ (fun ξ => biasA D (z ξ)) = -q*L := hb.2.2.1
  have hfinite (ξ : Ξ) := periodic_finite_correction r m hr hm (z ξ) (hz ξ)
  have hVfun : V = (fun ξ => ∑ g, Y ξ g^2/phaseProb r g) := by
    funext ξ; exact (hfinite ξ).2.2.2.2.2.1
  have hHfun : H = (fun ξ => V ξ-S ξ) := by
    funext ξ; exact (hfinite ξ).2.2.2.2.2.2.1
  have hQsum (ξ : Ξ) : (∑ g, Qg ξ g) = Q ξ := by
    dsimp [Qg,Q]; rw [Fintype.sum_sigma]; rfl
  have hUfun : Uc = (fun ξ => (V ξ-S ξ)+(N-m)*Q ξ) := by
    funext ξ
    calc
      _ = V ξ-S ξ+(N-m)*(∑ g, Qg ξ g) := (hfinite ξ).2.2.2.2.2.2.2.1
      _ = _ := by rw [hQsum]
  have hGfun : Gc = (fun ξ => V ξ+(q-2)*S ξ) := by
    funext ξ; exact (hfinite ξ).2.2.2.2.2.2.2.2.1
  have hVi (g : Fin r × Fin 2) : Integrable (fun ξ => Y ξ g^2/phaseProb r g) μ :=
    (hYS g).1.div_const _
  have hV : Integrable V μ := by rw [hVfun]; exact integrable_finsetSum _ (fun g _ => hVi g)
  have hEV : outcomeE μ V = (9/5)*q^2*L := by
    rw [hVfun]
    unfold outcomeE
    rw [integral_finsetSum _ (fun g _ => hVi g)]
    simp only [integral_div]
    change (∑ g : Fin r × Fin 2, outcomeE μ (fun ξ => Y ξ g^2)/phaseProb r g) = _
    simp_rw [fun g => (hYS g).2]
    have he (g : Fin r × Fin 2) : L/phaseProb r g = (1/phaseProb r g)*L := by ring
    simp_rw [he]
    rw [← Finset.sum_mul,phase_inverse_sum r hr]
  have hH : Integrable H μ := by rw [hHfun]; exact hV.sub hS
  have hEH : outcomeE μ H = outcomeE μ V-q*L := by
    rw [hHfun]
    unfold outcomeE
    rw [integral_sub hV hS]
    change outcomeE μ V-outcomeE μ S = _
    rw [hES]; rfl
  have hmeanx : (∑ k : Σ _ : Fin r × Fin 2, Fin m, phaseSize k)/
      (Fintype.card (Σ _ : Fin r × Fin 2, Fin m):ℝ) = 6 := by
    rw [hcard,(periodic_size_moments r m hr hm).1]
    change 6*N/N = 6
    field_simp [hN]
  have hunit (k : Σ _ : Fin r × Fin 2, Fin m) : Integrable (fun ξ => z ξ k^2) μ ∧
      outcomeE μ (fun ξ => z ξ k^2) = K := by
    have h := centered_unit_second_moment μ hK phaseSize β σ2 ε hε k
    rw [hmeanx,hcard] at h
    have hs : (phaseSize k-6)^2 = (16:ℝ) := by
      unfold phaseSize; split_ifs <;> norm_num
    rw [hs] at h
    refine ⟨h.1,?_⟩
    dsimp [K]
    convert h.2 using 1 <;> ring
  have hQ : Integrable Q μ := integrable_finsetSum _ (fun k _ => (hunit k).1)
  have hEQ : outcomeE μ Q = 16*N*β^2+(N-1)*σ2 := by
    unfold outcomeE Q
    rw [integral_finsetSum _ (fun k _ => (hunit k).1)]
    change (∑ k, outcomeE μ (fun ξ => z ξ k^2)) = _
    simp_rw [fun k => (hunit k).2]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [hcard]
    dsimp [K]
    field_simp [hN] <;> ring
  have hEU : outcomeE μ Uc = outcomeE μ H+(N-m)*outcomeE μ Q := by
    have he : Uc = (fun ξ => H ξ+(N-m)*Q ξ) := by rw [hUfun,hHfun]
    rw [he]
    unfold outcomeE
    rw [integral_add hH (hQ.const_mul (N-m)),integral_const_mul]
  have hEG : outcomeE μ Gc = outcomeE μ V+(q-2)*q*L := by
    rw [hGfun]
    unfold outcomeE
    rw [integral_add hV (hS.const_mul (q-2)),integral_const_mul]
    change outcomeE μ V+(q-2)*outcomeE μ S = _
    rw [hES]
    simp only [outcomeE]
    ring
  refine ⟨fun g => (hYS g).2,hEA,hEV,hEH,hEQ,hEU,hEG,?_,hb.2.2.2,?_⟩
  · intro hL
    rw [hEH,hEG,hEV]
    have hl : L ≠ 0 := hL.ne'
    constructor <;> field_simp [hq.ne',hl] <;> ring
  · intro hm2
    have hm1 : (m:ℝ)-1 ≠ 0 := by
      have ht : (2:ℝ) ≤ m := by exact_mod_cast hm2
      linarith
    let B := fun ξ => ∑ g, Qg ξ g/phaseProb r g
    have hQg (g : Fin r × Fin 2) : Integrable (fun ξ => Qg ξ g) μ :=
      integrable_finsetSum _ (fun j _ => (hunit ⟨g,j⟩).1)
    have hEQg (g : Fin r × Fin 2) : outcomeE μ (fun ξ => Qg ξ g) = (m:ℝ)*K := by
      unfold outcomeE Qg groupSquares
      rw [integral_finsetSum _ (fun j _ => (hunit ⟨g,j⟩).1)]
      change (∑ j : Fin m, outcomeE μ (fun ξ => z ξ ⟨g,j⟩^2)) = _
      simp_rw [fun j => (hunit ⟨g,j⟩).2]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hBi (g : Fin r × Fin 2) : Integrable (fun ξ => Qg ξ g/phaseProb r g) μ :=
      (hQg g).div_const _
    have hB : Integrable B μ := integrable_finsetSum _ (fun g _ => hBi g)
    have hEB : outcomeE μ B = (9/5)*q^2*((m:ℝ)*K) := by
      unfold outcomeE B
      rw [integral_finsetSum _ (fun g _ => hBi g)]
      simp only [integral_div]
      change (∑ g : Fin r × Fin 2, outcomeE μ (fun ξ => Qg ξ g)/phaseProb r g) = _
      simp_rw [hEQg]
      have he (g : Fin r × Fin 2) : (m:ℝ)*K/phaseProb r g =
          (1/phaseProb r g)*((m:ℝ)*K) := by ring
      simp_rw [he]
      rw [← Finset.sum_mul,phase_inverse_sum r hr]
    have hWfun : (fun ξ => expect D (wrEstimator D (z ξ) m)) =
        (fun ξ => ((m:ℝ)*B ξ-V ξ)/(N^2*((m:ℝ)-1))) := by
      funext ξ
      change (∑ g, phaseProb r g*wrEstimator D (z ξ) m g) = _
      have hp (g : Fin r × Fin 2) : phaseProb r g ≠ 0 := by
        have h := phaseGrouped_positive r hr g
        simpa only [phaseGrouped,oneDraw_pi] using h.ne'
      have he (g : Fin r × Fin 2) : phaseProb r g*wrEstimator D (z ξ) m g =
          ((m:ℝ)*(Qg ξ g/phaseProb r g)-Y ξ g^2/phaseProb r g)/
            (N^2*((m:ℝ)-1)) := by
        rw [phase_wr_value r m hr hm2]
        field_simp [hp g,hN,hm1] <;> ring
      simp_rw [he]
      rw [← Finset.sum_div,Finset.sum_sub_distrib,← Finset.mul_sum]
      have hv : V ξ = ∑ g, Y ξ g^2/phaseProb r g := congrFun hVfun ξ
      rw [← hv]
    rw [hWfun]
    unfold outcomeE
    rw [integral_div,integral_sub (hB.const_mul (m:ℝ)) hV,integral_const_mul]
    change ((m:ℝ)*outcomeE μ B-outcomeE μ V)/(N^2*((m:ℝ)-1)) = _
    rw [hEB,hEV]
    dsimp [K,L,N]
    field_simp [hq.ne',hmR.ne',hm1] <;> ring


/-- Independent homoscedastic noise in the supplement is a special case
of the unequal-variance, uncorrelated second-moment model in T11. -/
theorem noiseMoments_uncorrelated {Ξ K : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (ε : K → Ξ → ℝ) (σ2 : ℝ) (h : NoiseMoments μ ε σ2) :
    UncorrelatedNoise μ ε := by
  refine ⟨h.1, ?_⟩
  intro k l
  refine ⟨(h.2 k l).1, ?_⟩
  intro hkl
  simpa [hkl] using (h.2 k l).2


/-- A shifted noise coordinate has second moment s²+σ² under the
finite moment conditions. This specializes the supplement's normal
outcome models without assuming a Gaussian distribution (T15 iii). -/
theorem shifted_noise_second_moment {Ξ K : Type} [MeasurableSpace Ξ] [Fintype K]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (ε : K → Ξ → ℝ)
    (σ2 : ℝ) (hε : NoiseMoments μ ε σ2) (k : K) (s : ℝ) :
    Integrable (fun ξ => (s+ε k ξ)^2) μ ∧
    outcomeE μ (fun ξ => (s+ε k ξ)^2) = s^2+σ2 := by
  let c := fun l : K => if k = l then (1:ℝ) else 0
  have hZ (ξ : Ξ) : (∑ l, c l*ε l ξ) = ε k ξ := by simp [c]
  have hc : (∑ l, c l^2) = (1:ℝ) := by simp [c]
  have h := noise_linear_moments μ ε σ2 hε c s
  dsimp only at h
  rcases h with ⟨_,_,_,_,hint,he⟩
  simp_rw [hZ] at hint he
  rw [hc] at he
  exact ⟨hint,by simpa using he⟩

/-- Outcome expectation commutes with a finite design expectation when
each sampled quantity is integrable. The weights remain the actual
design distribution, separate from the generated-outcome law (T15 iii). -/
theorem outcomeE_expect {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (D : Design U Ω) (f : Ξ → Ω → ℝ)
    (hf : ∀ ω, Integrable (fun ξ => f ξ ω) μ) :
    Integrable (fun ξ => expect D (f ξ)) μ ∧
    outcomeE μ (fun ξ => expect D (f ξ)) =
      expect D (fun ω => outcomeE μ (fun ξ => f ξ ω)) := by
  have hi (ω : Ω) : Integrable (fun ξ => D.weight ω*f ξ ω) μ :=
    (hf ω).const_mul _
  constructor
  · exact integrable_finsetSum _ (fun ω _ => hi ω)
  · unfold outcomeE expect
    rw [integral_finsetSum _ (fun ω _ => hi ω)]
    simp only [integral_const_mul]

/-- T15 (iii): second moments of the actual outcome-and-design model give
the displayed true variance, estimator expectations, and biases. -/
theorem strata_model_moments {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (M : ℕ) (hM : 2 ≤ M) (α : ℝ)
    (ε : (Fin M × Fin 2) → Ξ → ℝ) (hε : NoiseMoments μ ε 1) :
    let D := strataDesign M (by omega)
    let y := stratumOutcomes α ε
    let N : ℝ := 2*M
    outcomeE μ (fun ξ => variance D (htMean D (y ξ))) = ((M:ℝ)-1)/(2*M) ∧
    outcomeE μ (fun ξ => expect D (fun ω => htVarianceEstimator D (y ξ) ω/N^2)) =
      ((M:ℝ)-1)/(2*M)*(1+α^2) ∧
    outcomeE μ (fun ξ => expect D (fun ω => c2Estimator D (y ξ) ω/N^2)) =
      ((M:ℝ)-1)/M*(1+α^2) ∧
    outcomeE μ (fun ξ => expect D (collapsedEstimator (y ξ))) = α^2+1/2 ∧
    outcomeE μ (fun ξ => expect D (fun ω => c2Estimator D (y ξ) ω/N^2) -
      variance D (htMean D (y ξ))) = strataC2BiasFormula M α ∧
    outcomeE μ (fun ξ => expect D (collapsedEstimator (y ξ)) -
      variance D (htMean D (y ξ))) = strataCSBiasFormula M α := by
  dsimp only
  let D := strataDesign M (by omega)
  let y := stratumOutcomes α ε
  let N : ℝ := 2*M
  let V := fun ξ => variance D (htMean D (y ξ))
  let H := fun ξ => expect D (fun ω => htVarianceEstimator D (y ξ) ω/N^2)
  let C := fun ξ => expect D (fun ω => c2Estimator D (y ξ) ω/N^2)
  let CS := fun ξ => expect D (collapsedEstimator (y ξ))
  have hmR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hunit (k : Fin M × Fin 2) : Integrable (fun ξ => y ξ k^2) μ ∧
      outcomeE μ (fun ξ => y ξ k^2) = α^2+1 := by
    have h := shifted_noise_second_moment μ ε 1 hε k (stratumMeans α k.2)
    have hs : (stratumMeans α k.2)^2 = α^2 := by
      unfold stratumMeans; split_ifs <;> ring
    rw [hs] at h
    exact h
  have hssq (s : Fin 2) : Integrable (fun ξ => ∑ i : Fin M, y ξ (i,s)^2) μ ∧
      outcomeE μ (fun ξ => ∑ i : Fin M, y ξ (i,s)^2) = (M:ℝ)*(α^2+1) := by
    refine ⟨integrable_finsetSum _ (fun i _ => (hunit (i,s)).1),?_⟩
    unfold outcomeE
    rw [integral_finsetSum _ (fun i _ => (hunit (i,s)).1)]
    change (∑ i : Fin M, outcomeE μ (fun ξ => y ξ (i,s)^2)) = _
    simp_rw [fun i => (hunit (i,s)).2]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have havg (s : Fin 2) : Integrable (fun ξ => ((∑ i : Fin M, y ξ (i,s))/(M:ℝ))^2) μ ∧
      outcomeE μ (fun ξ => ((∑ i : Fin M, y ξ (i,s))/(M:ℝ))^2) = α^2+1/(M:ℝ) := by
    let es := fun i : Fin M => ε (i,s)
    have heps : NoiseMoments μ es 1 := by
      constructor
      · intro i; exact hε.1 (i,s)
      · intro i j
        have h := hε.2 (i,s) (j,s)
        by_cases hij : i = j
        · subst j; simpa [es] using h
        · simpa [es,hij] using h
    let c := fun _ : Fin M => 1/(M:ℝ)
    have hc : (∑ i : Fin M, c i^2) = 1/(M:ℝ) := by
      simp only [c,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp [hmR.ne'] <;> ring
    have hf : (fun ξ => ((∑ i : Fin M, y ξ (i,s))/(M:ℝ))^2) =
        (fun ξ => (stratumMeans α s+∑ i, c i*es i ξ)^2) := by
      funext ξ
      congr 1
      dsimp [y,stratumOutcomes,c,es]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← Finset.mul_sum]
      field_simp [hmR.ne'] <;> ring
    have h := noise_linear_moments μ es 1 heps c (stratumMeans α s)
    dsimp only at h
    rcases h with ⟨_,_,_,_,hint,he⟩
    have hs : (stratumMeans α s)^2 = α^2 := by
      unfold stratumMeans; split_ifs <;> ring
    rw [hc,hs] at he
    rw [hf]
    exact ⟨hint,by simpa using he⟩
  have hstr (s : Fin 2) : Integrable (fun ξ => stratumVariance (y ξ) s) μ ∧
      outcomeE μ (fun ξ => stratumVariance (y ξ) s) = ((M:ℝ)-1)/M := by
    have hi := (hssq s).1.div_const (M:ℝ)
    refine ⟨hi.sub (havg s).1,?_⟩
    unfold outcomeE stratumVariance
    rw [integral_sub hi (havg s).1,integral_div]
    change outcomeE μ (fun ξ => ∑ i : Fin M, y ξ (i,s)^2)/(M:ℝ)-
      outcomeE μ (fun ξ => ((∑ i : Fin M, y ξ (i,s))/(M:ℝ))^2) = _
    rw [(hssq s).2,(havg s).2]
    field_simp [hmR.ne'] <;> ring
  have hVfun : V = (fun ξ => (stratumVariance (y ξ) 0+stratumVariance (y ξ) 1)/4) := by
    funext ξ; exact (strata_finite_formulas M hM (y ξ)).2
  have hV : Integrable V μ := by
    rw [hVfun]; exact ((hstr 0).1.add (hstr 1).1).div_const 4
  have hEV : outcomeE μ V = ((M:ℝ)-1)/(2*M) := by
    rw [hVfun]
    unfold outcomeE
    rw [integral_div,integral_add (hstr 0).1 (hstr 1).1]
    change (outcomeE μ (fun ξ => stratumVariance (y ξ) 0)+
      outcomeE μ (fun ξ => stratumVariance (y ξ) 1))/4 = _
    rw [(hstr 0).2,(hstr 1).2]; ring
  have hweighted (ω : Fin M × Fin M) (c : ℝ) :
      Integrable (fun ξ => c*(y ξ (ω.1,0)^2+y ξ (ω.2,1)^2)) μ ∧
      outcomeE μ (fun ξ => c*(y ξ (ω.1,0)^2+y ξ (ω.2,1)^2)) = c*(2*(α^2+1)) := by
    refine ⟨((hunit (ω.1,0)).1.add (hunit (ω.2,1)).1).const_mul c,?_⟩
    unfold outcomeE
    rw [integral_const_mul,integral_add (hunit (ω.1,0)).1 (hunit (ω.2,1)).1]
    change c*(outcomeE μ (fun ξ => y ξ (ω.1,0)^2)+
      outcomeE μ (fun ξ => y ξ (ω.2,1)^2)) = _
    rw [(hunit (ω.1,0)).2,(hunit (ω.2,1)).2]; ring
  have hHpoint (ω : Fin M × Fin M) : Integrable (fun ξ => htVarianceEstimator D (y ξ) ω/N^2) μ ∧
      outcomeE μ (fun ξ => htVarianceEstimator D (y ξ) ω/N^2) =
        ((M:ℝ)-1)/(2*M)*(1+α^2) := by
    have hf : (fun ξ => htVarianceEstimator D (y ξ) ω/N^2) =
        (fun ξ => ((M:ℝ)-1)/(4*M)*(y ξ (ω.1,0)^2+y ξ (ω.2,1)^2)) := by
      funext ξ; exact ((strata_finite_formulas M hM (y ξ)).1 ω).2.1
    rw [hf]
    refine ⟨(hweighted ω _).1,?_⟩
    rw [(hweighted ω _).2]; ring
  have hCpoint (ω : Fin M × Fin M) : Integrable (fun ξ => c2Estimator D (y ξ) ω/N^2) μ ∧
      outcomeE μ (fun ξ => c2Estimator D (y ξ) ω/N^2) =
        ((M:ℝ)-1)/M*(1+α^2) := by
    have hf : (fun ξ => c2Estimator D (y ξ) ω/N^2) =
        (fun ξ => ((M:ℝ)-1)/(2*M)*(y ξ (ω.1,0)^2+y ξ (ω.2,1)^2)) := by
      funext ξ; exact ((strata_finite_formulas M hM (y ξ)).1 ω).2.2
    rw [hf]
    refine ⟨(hweighted ω _).1,?_⟩
    rw [(hweighted ω _).2]; ring
  have hH := outcomeE_expect μ D (fun ξ ω => htVarianceEstimator D (y ξ) ω/N^2)
    (fun ω => (hHpoint ω).1)
  have hC := outcomeE_expect μ D (fun ξ ω => c2Estimator D (y ξ) ω/N^2)
    (fun ω => (hCpoint ω).1)
  have hEH : outcomeE μ H = ((M:ℝ)-1)/(2*M)*(1+α^2) := by
    rw [hH.2]
    simp_rw [fun ω => (hHpoint ω).2]
    exact expect_const D _
  have hEC : outcomeE μ C = ((M:ℝ)-1)/M*(1+α^2) := by
    rw [hC.2]
    simp_rw [fun ω => (hCpoint ω).2]
    exact expect_const D _
  have hCSpoint (ω : Fin M × Fin M) : Integrable (fun ξ => collapsedEstimator (y ξ) ω) μ ∧
      outcomeE μ (fun ξ => collapsedEstimator (y ξ) ω) = α^2+1/2 := by
    have hne : (ω.1,(0:Fin 2)) ≠ (ω.2,(1:Fin 2)) := by
      intro h; have hs := congrArg Prod.snd h; exact (by decide : (0:Fin 2) ≠ 1) hs
    have hprod := raw_model_cross_moment μ (fun k : Fin M × Fin 2 => stratumMeans α k.2)
      1 ε (noiseMoments_uncorrelated μ ε 1 hε) (ω.1,0) (ω.2,1) hne
    have hp : Integrable (fun ξ => y ξ (ω.1,0)*y ξ (ω.2,1)) μ ∧
        outcomeE μ (fun ξ => y ξ (ω.1,0)*y ξ (ω.2,1)) = -α^2 := by
      simpa [rawOutcomes,stratumOutcomes,y,stratumMeans,pow_two] using hprod
    have hf : (fun ξ => collapsedEstimator (y ξ) ω) = (fun ξ =>
        (y ξ (ω.1,0)^2+y ξ (ω.2,1)^2)/4-(y ξ (ω.1,0)*y ξ (ω.2,1))/2) := by
      funext ξ; unfold collapsedEstimator; ring
    have hi : Integrable (fun ξ => (y ξ (ω.1,0)^2+y ξ (ω.2,1)^2)/4) μ :=
      ((hunit (ω.1,0)).1.add (hunit (ω.2,1)).1).div_const 4
    have hj : Integrable (fun ξ => (y ξ (ω.1,0)*y ξ (ω.2,1))/2) μ :=
      hp.1.div_const 2
    rw [hf]
    refine ⟨hi.sub hj,?_⟩
    unfold outcomeE
    rw [integral_sub hi hj,integral_div,integral_div,
      integral_add (hunit (ω.1,0)).1 (hunit (ω.2,1)).1]
    change (outcomeE μ (fun ξ => y ξ (ω.1,0)^2)+
      outcomeE μ (fun ξ => y ξ (ω.2,1)^2))/4-
      outcomeE μ (fun ξ => y ξ (ω.1,0)*y ξ (ω.2,1))/2 = _
    rw [(hunit (ω.1,0)).2,(hunit (ω.2,1)).2,hp.2]; ring
  have hCS := outcomeE_expect μ D (fun ξ ω => collapsedEstimator (y ξ) ω)
    (fun ω => (hCSpoint ω).1)
  have hECS : outcomeE μ CS = α^2+1/2 := by
    rw [hCS.2]
    simp_rw [fun ω => (hCSpoint ω).2]
    exact expect_const D _
  refine ⟨hEV,hEH,hEC,hECS,?_,?_⟩
  · unfold outcomeE
    rw [integral_sub hC.1 hV]
    change outcomeE μ C-outcomeE μ V = _
    rw [hEC,hEV]
    unfold strataC2BiasFormula
    field_simp [hmR.ne'] <;> ring
  · unfold outcomeE
    rw [integral_sub hCS.1 hV]
    change outcomeE μ CS-outcomeE μ V = _
    rw [hECS,hEV]
    unfold strataCSBiasFormula
    field_simp [hmR.ne'] <;> ring


end
end AronowAudit.P027

