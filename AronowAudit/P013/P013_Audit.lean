import Mathlib

/-!
P013: Aronow and Samii (2017), Annals of Applied Statistics 11, 1912--1947.
The design-based objects below use real weighted finite sums. No probabilities
are estimated except in the explicitly labelled Monte Carlo statements.
-/

namespace AronowAudit.P013

open scoped BigOperators Topology NNReal ENNReal
open Filter Finset

noncomputable section

/-- "Pr(Z = z) = p_z", with support "Ω = {z : p_z > 0}" (pp. 1914--1915).
Ω labels the supported assignment vectors; its finite type carries their exact
design weights. Fixed traits are absorbed into the exposure map below. -/
structure Design (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  positive : ∀ z, 0 < weight z
  total : ∑ z, weight z = 1

variable {Ω : Type*} [Fintype Ω]

/-- Expectation over the known randomization distribution, "E" (Sections 4--8). -/
def expectation (P : Design Ω) (X : Ω → ℝ) : ℝ := ∑ z, P.weight z * X z

/-- Randomization covariance "Cov", over the fixed finite design (p. 1921). -/
def covariance (P : Design Ω) (X Y : Ω → ℝ) : ℝ :=
  expectation P (fun z => X z * Y z) - expectation P X * expectation P Y

/-- Randomization variance "Var" (p. 1919); equal to E[(X-E[X])²]. -/
def variance (P : Design Ω) (X : Ω → ℝ) : ℝ := covariance P X X

/-- Probability of an event under the randomization plan (p. 1915). -/
def probability (P : Design Ω) (A : Ω → Prop) : ℝ :=
  by classical exact ∑ z, if A z then P.weight z else 0

/-- "I(D_i = d_k)" (p. 1916), a real 0--1 indicator. -/
def indicator {N K : ℕ} (D : Ω → Fin N → Fin K) (i : Fin N) (d : Fin K)
    (z : Ω) : ℝ := if D z i = d then 1 else 0

/-- "D_i = f(Z, θ_i)" and fixed "y_i(d_k)" (pp. 1916, 1918).
Defining the randomization potential outcome as y_i(D_i(z)) implements Condition 1;
the observed outcome below implements Condition 2. -/
structure Population (P : Design Ω) (N K : ℕ) where
  exposure : Ω → Fin N → Fin K
  outcome : Fin N → Fin K → ℝ

/-- "π_i(d_k) = Σ_z p_z I(f(z,θ_i)=d_k)" (p. 1916). -/
def pi {N K : ℕ} {P : Design Ω} (F : Population P N K) (i : Fin N) (d : Fin K) :=
  expectation P (indicator F.exposure i d)

/-- "π_ij(d_k,d_l)" and "π_ij(d_k)" (pp. 1916--1917);
the latter is obtained by putting the two exposures equal. -/
def jointPi {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (i j : Fin N) (d e : Fin K) :=
  expectation P (fun z => indicator F.exposure i d z * indicator F.exposure j e z)

/-- "Y_i = Σ_k I(D_i=d_k)y_i(d_k)" (Condition 2, p. 1918).
Since each unit receives exactly one exposure this is y_i(D_i). -/
def observed {N K : ℕ} {P : Design Ω} (F : Population P N K) (z : Ω) (i : Fin N) :=
  F.outcome i (F.exposure z i)

/-- "0 < π_i(d_k) < 1" (p. 1918), for the exposure being estimated. -/
def Positivity {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) : Prop :=
  ∀ i, 0 < pi F i d ∧ pi F i d < 1

/-- "y^T(d_k)" and "μ(d_k) = (1/N)Σ_i y_i(d_k)" (p. 1919). -/
def potentialTotal {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) :=
  ∑ i, F.outcome i d

/-- Population mean "μ(d_k)" (p. 1919). -/
def potentialMean {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) :=
  potentialTotal F d / (N : ℝ)

/-- "τ(d_k,d_l) = μ(d_k)-μ(d_l)" (p. 1919). -/
def causalEffect {N K : ℕ} {P : Design Ω} (F : Population P N K) (d e : Fin K) :=
  potentialMean F d - potentialMean F e

/-- Expression (1), "Σ_i I(D_i=d_k)Y_i/π_i(d_k)" (p. 1919).
Here the masked outcome is replaced by the fixed y_i(d_k), as Conditions 1--2 allow. -/
def htTotal {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  ∑ i, indicator F.exposure i d z * (F.outcome i d / pi F i d)

/-- "μ̂_HT(d_k) = ŷ^T_HT(d_k)/N" (p. 1920). -/
def htMean {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  htTotal F d z / (N : ℝ)

/-- Expression (3), "τ̂_HT(d_k,d_l)" (p. 1920). -/
def htEffect {N K : ℕ} {P : Design Ω} (F : Population P N K) (d e : Fin K) (z : Ω) :=
  (htTotal F d z - htTotal F e z) / (N : ℝ)

/-- The design expectation of a constant equals that constant.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem expectation_const (P : Design Ω) (c : ℝ) :
    expectation P (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul, P.total]

/-- Design expectation distributes over addition.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem expectation_add (P : Design Ω) (X Y : Ω → ℝ) :
    expectation P (fun z => X z + Y z) = expectation P X + expectation P Y := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

/-- Design expectation distributes over subtraction.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem expectation_sub (P : Design Ω) (X Y : Ω → ℝ) :
    expectation P (fun z => X z - Y z) = expectation P X - expectation P Y := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

/-- A constant right factor can be taken outside design expectation.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem expectation_mul_const (P : Design Ω) (X : Ω → ℝ) (c : ℝ) :
    expectation P (fun z => X z * c) = expectation P X * c := by
  simp [expectation, ← mul_assoc, Finset.sum_mul]

/-- A constant left factor can be taken outside design expectation.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem expectation_const_mul (P : Design Ω) (X : Ω → ℝ) (c : ℝ) :
    expectation P (fun z => c * X z) = c * expectation P X := by
  simp only [mul_comm c, expectation_mul_const]

/-- The design expectation of a finite sum is the sum of its expectations.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem expectation_sum {ι : Type*} [Fintype ι] (P : Design Ω) (X : ι → Ω → ℝ) :
    expectation P (fun z => ∑ i, X i z) = ∑ i, expectation P (X i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- A nonnegative outcome at every supported assignment has nonnegative expectation.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem expectation_nonneg (P : Design Ω) {X : Ω → ℝ} (h : ∀ z, 0 ≤ X z) :
    0 ≤ expectation P X := Finset.sum_nonneg fun z _ => mul_nonneg (P.positive z).le (h z)

/-- Pointwise ordered randomization outcomes have ordered design expectations.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem expectation_mono (P : Design Ω) {X Y : Ω → ℝ} (h : ∀ z, X z ≤ Y z) :
    expectation P X ≤ expectation P Y :=
  Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (h z) (P.positive z).le

/-- The randomization variance equals the weighted mean squared deviation from design expectation.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem variance_centered (P : Design Ω) (X : Ω → ℝ) :
    variance P X = expectation P (fun z => (X z - expectation P X)^2) := by
  unfold variance covariance
  have hp : (fun z => (X z - expectation P X)^2) =
      (fun z => X z * X z - 2 * expectation P X * X z + (expectation P X)^2) := by
    funext z; ring
  rw [hp, expectation_add, expectation_sub, expectation_const_mul, expectation_const]
  ring

/-- The randomization variance is nonnegative.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem variance_nonneg (P : Design Ω) (X : Ω → ℝ) : 0 ≤ variance P X := by
  rw [variance_centered]
  exact expectation_nonneg P fun z => sq_nonneg _

/-- Randomization covariance is symmetric in the two random variables.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem covariance_symm (P : Design Ω) (X Y : Ω → ℝ) :
    covariance P X Y = covariance P Y X := by
  simp [covariance, mul_comm]

/-- The covariance of two finite sums equals the double sum of pairwise covariances.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem covariance_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Design Ω) (X : ι → Ω → ℝ) (Y : κ → Ω → ℝ) :
    covariance P (fun z => ∑ i, X i z) (fun z => ∑ j, Y j z) =
      ∑ i, ∑ j, covariance P (X i) (Y j) := by
  simp only [covariance, Finset.sum_mul_sum, expectation_sum,
    Finset.sum_sub_distrib]

/-- Multiplying two random variables by constants multiplies their covariance by the product of those constants.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem covariance_mul_const (P : Design Ω) (X Y : Ω → ℝ) (a b : ℝ) :
    covariance P (fun z => X z * a) (fun z => Y z * b) = covariance P X Y * a * b := by
  have hp : (fun z => X z * a * (Y z * b)) = (fun z => (X z * Y z) * (a * b)) := by
    funext z; ring
  simp only [covariance, hp, expectation_mul_const]
  ring

/-- The variance of a scaled difference equals the sum of the two variances minus twice the covariance, divided by the square of the scale.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem variance_sub_div (P : Design Ω) (X Y : Ω → ℝ) (n : ℝ) :
    variance P (fun z => (X z - Y z) / n) =
      (variance P X + variance P Y - 2 * covariance P X Y) / n^2 := by
  have hp : (fun z => (X z - Y z) * (X z - Y z)) =
      (fun z => X z * X z + Y z * Y z - 2 * (X z * Y z)) := by
    funext z; ring
  simp only [div_eq_mul_inv, variance, covariance_mul_const]
  unfold covariance
  rw [hp, expectation_sub, expectation_add, expectation_const_mul, expectation_sub]
  ring

/-- Conditions 1--2 identify the masked observed outcome in (1) with y_i(d_k)
(p. 1918; Appendix A.2, p. 1938). -/
theorem htTotal_observed {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (z : Ω) :
    htTotal F d z = ∑ i, indicator F.exposure i d z * observed F z i / pi F i d := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : F.exposure z i = d
  · simp [indicator, observed, h]
  · simp [indicator, h]

/-- Lemma 4.1, expectation: E[ŷ^T_HT(d_k)] = Σ_i y_i(d_k) (p. 1919). -/
theorem ht_unbiased {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hpos : Positivity F d) :
    expectation P (htTotal F d) = potentialTotal F d := by
  change expectation P (fun z => ∑ i, indicator F.exposure i d z *
    (F.outcome i d / pi F i d)) = ∑ i, F.outcome i d
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [expectation_mul_const]
  change pi F i d * (F.outcome i d / pi F i d) = F.outcome i d
  field_simp [ne_of_gt (hpos i).1]

/-- The mean form of Lemma 4.1, also used in Appendix A.6 (pp. 1920, 1942). -/
theorem htMean_unbiased {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hpos : Positivity F d) :
    expectation P (htMean F d) = potentialMean F d := by
  change expectation P (fun z => htTotal F d z / (N : ℝ)) = potentialTotal F d / (N : ℝ)
  simp only [div_eq_mul_inv, expectation_mul_const, ht_unbiased F d hpos]

/-- Proposition 4.2, expression (4): the HT exposure contrast is unbiased (p. 1920). -/
theorem htEffect_unbiased {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hposd : Positivity F d) (hpose : Positivity F e) :
    expectation P (htEffect F d e) = causalEffect F d e := by
  change expectation P (fun z => (htTotal F d z - htTotal F e z) / (N : ℝ)) = _
  simp only [causalEffect, potentialMean, div_eq_mul_inv,
    expectation_mul_const, expectation_sub, ht_unbiased F d hposd, ht_unbiased F e hpose]
  ring

/-- Proposition 4.2, expression (5): variance of the difference of totals (p. 1920). -/
theorem htEffect_variance {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) :
    variance P (htEffect F d e) =
      (variance P (htTotal F d) + variance P (htTotal F e) -
        2 * covariance P (htTotal F d) (htTotal F e)) / (N : ℝ)^2 :=
  variance_sub_div P _ _ _

/-- The full double-sum covariance identity of Appendix A.4 (p. 1938). -/
theorem ht_covariance_full {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) :
    covariance P (htTotal F d) (htTotal F e) =
      ∑ i, ∑ j, (jointPi F i j d e - pi F i d * pi F j e) *
        (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e) := by
  change covariance P (fun z => ∑ i, indicator F.exposure i d z *
    (F.outcome i d / pi F i d)) (fun z => ∑ j, indicator F.exposure j e z *
    (F.outcome j e / pi F j e)) = _
  rw [covariance_sum_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact covariance_mul_const P _ _ _ _

/-- A same-exposure joint probability for a unit with itself equals its marginal exposure probability.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem jointPi_self {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (i : Fin N) (d : Fin K) : jointPi F i i d d = pi F i d := by
  unfold jointPi pi
  congr 1
  funext z
  unfold indicator
  split <;> norm_num

/-- A unit cannot receive two distinct exposures, so its cross-exposure joint probability with itself is zero.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem jointPi_cross_self {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (i : Fin N) (d e : Fin K) (hne : d ≠ e) : jointPi F i i d e = 0 := by
  have hp : (fun z => indicator F.exposure i d z * indicator F.exposure i e z) =
      (fun _ => (0 : ℝ)) := by
    funext z
    by_cases hd : F.exposure z i = d
    · have he : F.exposure z i ≠ e := fun h => hne (hd.symm.trans h)
      simp [indicator, hd, he, hne]
    · simp [indicator, hd]
  unfold jointPi
  rw [hp, expectation_const]

/-- A double population sum splits into its diagonal and off-diagonal sums.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem sum_diag_off {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ι → ℝ) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) + ∑ i, ∑ j ∈ univ.erase i, f i j := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have h := sum_erase_add univ (f i) (mem_univ i)
  linarith

/-- Lemma 4.1, expression (2), including its diagonal and ordered off-diagonal
terms exactly as printed (p. 1919). -/
theorem ht_variance_formula {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) :
    variance P (htTotal F d) =
      (∑ i, pi F i d * (1 - pi F i d) * (F.outcome i d / pi F i d)^2) +
      ∑ i, ∑ j ∈ univ.erase i, (jointPi F i j d d - pi F i d * pi F j d) *
        (F.outcome i d / pi F i d) * (F.outcome j d / pi F j d) := by
  rw [variance, ht_covariance_full, sum_diag_off]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [jointPi_self]
  ring

/-- Proposition 4.2, expression (6), with the unobservable within-unit
cross-exposure products subtracted (p. 1921). -/
theorem ht_covariance_formula {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e) :
    covariance P (htTotal F d) (htTotal F e) =
      (∑ i, ∑ j ∈ univ.erase i, (jointPi F i j d e - pi F i d * pi F j e) *
        (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e)) -
      ∑ i, F.outcome i d * F.outcome i e := by
  rw [ht_covariance_full, sum_diag_off]
  have hdiag : (∑ i, (jointPi F i i d e - pi F i d * pi F i e) *
      (F.outcome i d / pi F i d) * (F.outcome i e / pi F i e)) =
      -∑ i, F.outcome i d * F.outcome i e := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    rw [jointPi_cross_self F i d e hne]
    field_simp [ne_of_gt (hd i).1, ne_of_gt (he i).1]
    ring
  rw [hdiag]
  ring

/-- Observable ordered-pair term in (7), (8) and (10), pp. 1921--1924.
Division by zero is Lean's real-field convention, 0/0=0 (p. 1922).
Masked y_i(d) equals masked Y_i by Conditions 1--2. -/
def pairTerm {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (i j : Fin N) (d e : Fin K) (z : Ω) : ℝ :=
  (indicator F.exposure i d z * indicator F.exposure j e z) *
    ((jointPi F i j d e - pi F i d * pi F j e) / jointPi F i j d e) *
    (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e)

/-- Expression (7), p. 1921; its diagonal is written separately as printed. -/
def varianceHT {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  (∑ i, indicator F.exposure i d z * (1 - pi F i d) * (F.outcome i d / pi F i d)^2) +
  ∑ i, ∑ j ∈ univ.erase i, pairTerm F i j d d z

/-- "Â_2(d_k)" from Young's inequality, p. 1922: sum over ordered
distinct-unit pairs with zero same-exposure joint probability. -/
def correctionA2 {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  ∑ i, ∑ j ∈ univ.erase i, if jointPi F i j d d = 0 then
    indicator F.exposure i d z * F.outcome i d ^ 2 / (2 * pi F i d) +
    indicator F.exposure j d z * F.outcome j d ^ 2 / (2 * pi F j d) else 0

/-- "A = Σ_i Σ_{j≠i:π_ij(d)=0} y_i(d)y_j(d)" (Proposition 5.1, p. 1922). -/
def missingA {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) :=
  ∑ i, ∑ j ∈ univ.erase i, if jointPi F i j d d = 0 then
    F.outcome i d * F.outcome j d else 0

/-- Expression (8), p. 1923, covariance estimator for positive off-diagonal joints. -/
def covarianceHT {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (z : Ω) :=
  (∑ i, ∑ j ∈ univ.erase i, pairTerm F i j d e z) -
  ∑ i, (indicator F.exposure i d z * F.outcome i d ^ 2 / (2 * pi F i d) +
    indicator F.exposure i e z * F.outcome i e ^ 2 / (2 * pi F i e))

/-- Expression (10), p. 1924: observable positive joints minus squared-outcome
corrections for every zero joint, including i=j. -/
def covarianceA {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (z : Ω) :=
  (∑ i, ∑ j ∈ univ.erase i, if 0 < jointPi F i j d e then pairTerm F i j d e z else 0) -
  ∑ i, ∑ j, if jointPi F i j d e = 0 then
    indicator F.exposure i d z * F.outcome i d ^ 2 / (2 * pi F i d) +
    indicator F.exposure j e z * F.outcome j e ^ 2 / (2 * pi F j e) else 0

/-- Expression (11), p. 1924, the printed conservative HT-effect variance estimator. -/
def effectVariance {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (z : Ω) :=
  (varianceHT F d z + correctionA2 F d z + varianceHT F e z + correctionA2 F e z -
    2 * covarianceA F d e z) / (N : ℝ)^2

/-- The design expectation of a sum over a fixed finite set equals the sum of its expectations.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem expectation_finset_sum {ι : Type*} (s : Finset ι) (P : Design Ω) (X : ι → Ω → ℝ) :
    expectation P (fun z => ∑ i ∈ s, X i z) = ∑ i ∈ s, expectation P (X i) := by
  simp only [expectation, mul_sum]
  exact sum_comm

/-- Every joint exposure probability is nonnegative.
Supporting weighted-sum identity for Lemma 4.1 and Proposition 4.2, pp. 1919--1921 (P013-T13). -/
theorem jointPi_nonneg {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (i j : Fin N) (d e : Fin K) : 0 ≤ jointPi F i j d e := by
  apply expectation_nonneg
  intro z
  unfold indicator
  split <;> split <;> norm_num

/-- The pair sampling term has expectation equal to its population covariance contribution when its joint probability is nonzero, and zero when that probability is zero.
Supporting finite lemma for Section 5, pp. 1921--1924 (P013-T14,T15). -/
theorem pairTerm_expectation {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (i j : Fin N) (d e : Fin K) :
    expectation P (pairTerm F i j d e) =
      if jointPi F i j d e = 0 then 0 else
        (jointPi F i j d e - pi F i d * pi F j e) *
          (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e) := by
  change expectation P (fun z => _) = _
  simp only [pairTerm, expectation_mul_const]
  change jointPi F i j d e *
      ((jointPi F i j d e - pi F i d * pi F j e) / jointPi F i j d e) *
      (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e) = _
  by_cases h : jointPi F i j d e = 0
  · simp [h]
  · simp only [h, if_false]
    field_simp

/-- Lemma 5.1: (7) is unbiased when every same-exposure joint is positive
(p. 1922). -/
theorem varianceHT_unbiased {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hpos : ∀ i j, 0 < jointPi F i j d d) :
    expectation P (varianceHT F d) = variance P (htTotal F d) := by
  change expectation P (fun z => _ + _) = _
  rw [expectation_add, expectation_sum, expectation_sum, ht_variance_formula]
  congr 1
  · apply sum_congr rfl
    intro i _
    simp only [expectation_mul_const]
    rfl
  · apply sum_congr rfl
    intro i _
    rw [expectation_finset_sum]
    apply sum_congr rfl
    intro j _
    rw [pairTerm_expectation, if_neg (ne_of_gt (hpos i j))]

/-- Proposition 5.1 and Appendix A.5 Proposition A.1: omitted zero joints
give exactly the additive bias A (pp. 1922, 1940). The identity also covers A=0. -/
theorem varianceHT_bias {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hd : Positivity F d) :
    expectation P (varianceHT F d) = variance P (htTotal F d) + missingA F d := by
  change expectation P (fun z => _ + _) = _
  rw [expectation_add, expectation_sum, expectation_sum, ht_variance_formula]
  have hdiag : (∑ i, expectation P (fun z => indicator F.exposure i d z *
      (1 - pi F i d) * (F.outcome i d / pi F i d)^2)) =
      ∑ i, pi F i d * (1 - pi F i d) * (F.outcome i d / pi F i d)^2 := by
    apply sum_congr rfl
    intro i _
    simp only [expectation_mul_const]
    rfl
  rw [hdiag, add_assoc]
  congr 1
  unfold missingA
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [expectation_finset_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [pairTerm_expectation]
  by_cases hz : jointPi F i j d d = 0
  · simp only [hz, if_true]
    field_simp [ne_of_gt (hd i).1, ne_of_gt (hd j).1]
    ring
  · simp [hz]

/-- The expected inverse-probability squared-outcome correction for one unit equals one half of its squared potential outcome.
Supporting finite lemma for Section 5, pp. 1921--1924 (P013-T14,T15). -/
theorem squareTerm_expectation {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (i : Fin N) (d : Fin K) (hp : 0 < pi F i d) :
    expectation P (fun z => indicator F.exposure i d z * F.outcome i d ^ 2 /
      (2 * pi F i d)) = F.outcome i d ^ 2 / 2 := by
  simp only [div_eq_mul_inv, expectation_mul_const]
  change pi F i d * F.outcome i d ^ 2 * (2 * pi F i d)⁻¹ = _
  field_simp [ne_of_gt hp]

/-- The expected zero-joint correction A2 equals the sum of half the paired squared potential outcomes over zero-joint ordered pairs.
Supporting finite lemma for Section 5, pp. 1921--1924 (P013-T14,T15). -/
theorem correctionA2_expectation {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hd : Positivity F d) :
    expectation P (correctionA2 F d) = ∑ i, ∑ j ∈ univ.erase i,
      if jointPi F i j d d = 0 then (F.outcome i d ^ 2 + F.outcome j d ^ 2) / 2 else 0 := by
  change expectation P (fun z => ∑ i, ∑ j ∈ univ.erase i, _) = _
  rw [expectation_sum]
  apply sum_congr rfl
  intro i _
  rw [expectation_finset_sum]
  apply sum_congr rfl
  intro j _
  by_cases hz : jointPi F i j d d = 0
  · simp only [hz, if_true, expectation_add,
      squareTerm_expectation F i d (hd i).1, squareTerm_expectation F j d (hd j).1]
    ring
  · simp only [hz, if_false, expectation_const]

/-- Proposition 5.2 / Appendix A.5 Corollary A.2: (7)+Â₂ is conservative
in expectation for arbitrary signed outcomes and zero joints (pp. 1922, 1942). -/
theorem varianceHT_conservative {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hd : Positivity F d) :
    variance P (htTotal F d) ≤ expectation P (fun z => varianceHT F d z + correctionA2 F d z) := by
  rw [expectation_add, varianceHT_bias F d hd]
  have hnonneg : 0 ≤ missingA F d + expectation P (correctionA2 F d) := by
    rw [missingA, correctionA2_expectation F d hd, ← sum_add_distrib]
    apply sum_nonneg
    intro i _
    rw [← sum_add_distrib]
    apply sum_nonneg
    intro j _
    by_cases hz : jointPi F i j d d = 0
    · simp only [hz, if_true]
      nlinarith [sq_nonneg (F.outcome i d + F.outcome j d)]
    · simp [hz]
  linarith

/-- The expectation of covariance estimator (8) is its full off-diagonal covariance sum minus the sum of half the two squared potential outcomes.
Supporting finite lemma for Section 5, pp. 1921--1924 (P013-T14,T15). -/
theorem covarianceHT_expectation {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hd : Positivity F d) (he : Positivity F e)
    (hj : ∀ i j, i ≠ j → 0 < jointPi F i j d e) :
    expectation P (covarianceHT F d e) =
      (∑ i, ∑ j ∈ univ.erase i, (jointPi F i j d e - pi F i d * pi F j e) *
        (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e)) -
      ∑ i, (F.outcome i d ^ 2 + F.outcome i e ^ 2) / 2 := by
  change expectation P (fun z => _ - _) = _
  rw [expectation_sub, expectation_sum, expectation_sum]
  congr 1
  · apply sum_congr rfl
    intro i _
    rw [expectation_finset_sum]
    apply sum_congr rfl
    intro j hjmem
    rw [pairTerm_expectation, if_neg (ne_of_gt (hj i j (ne_of_mem_erase hjmem).symm))]
  · apply sum_congr rfl
    intro i _
    rw [expectation_add, squareTerm_expectation F i d (hd i).1,
      squareTerm_expectation F i e (he i).1]
    ring

/-- Proposition 5.3: (8) has expectation at most the true covariance when
every distinct-unit cross joint is positive (p. 1923). -/
theorem covarianceHT_conservative {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e)
    (hj : ∀ i j, i ≠ j → 0 < jointPi F i j d e) :
    expectation P (covarianceHT F d e) ≤ covariance P (htTotal F d) (htTotal F e) := by
  rw [covarianceHT_expectation F d e hd he hj, ht_covariance_formula F d e hne hd he]
  have hy : (∑ i, F.outcome i d * F.outcome i e) ≤
      ∑ i, (F.outcome i d ^ 2 + F.outcome i e ^ 2) / 2 := by
    apply sum_le_sum
    intro i _
    nlinarith [sq_nonneg (F.outcome i d - F.outcome i e)]
  linarith

/-- Proposition 5.4: (8) is unbiased when the two exposure-specific outcomes
coincide for every unit and all distinct-unit cross joints are positive (p. 1923). -/
theorem covarianceHT_unbiased_no_effect {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e)
    (hj : ∀ i j, i ≠ j → 0 < jointPi F i j d e) (hy : ∀ i, F.outcome i d = F.outcome i e) :
    expectation P (covarianceHT F d e) = covariance P (htTotal F d) (htTotal F e) := by
  rw [covarianceHT_expectation F d e hd he hj, ht_covariance_formula F d e hne hd he]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [hy i]
  ring

/-- The true covariance splits into contributions with positive joint exposure probability and the missing products from zero-joint pairs, including the diagonal.
Supporting finite lemma for Section 5, pp. 1921--1924 (P013-T14,T15). -/
theorem covariance_split_zeros {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e) :
    covariance P (htTotal F d) (htTotal F e) =
      (∑ i, ∑ j ∈ univ.erase i, if 0 < jointPi F i j d e then
        (jointPi F i j d e - pi F i d * pi F j e) *
          (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e) else 0) -
      ∑ i, ∑ j, if jointPi F i j d e = 0 then F.outcome i d * F.outcome j e else 0 := by
  have hfull : (∑ i, ∑ j ∈ univ.erase i, if 0 < jointPi F i j d e then
      (jointPi F i j d e - pi F i d * pi F j e) *
        (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e) else 0) =
      ∑ i, ∑ j, if 0 < jointPi F i j d e then
        (jointPi F i j d e - pi F i d * pi F j e) *
          (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e) else 0 := by
    rw [sum_diag_off]
    simp [jointPi_cross_self F _ d e hne]
  rw [hfull, ht_covariance_full, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  by_cases hz : jointPi F i j d e = 0
  · simp only [hz, lt_self_iff_false, if_false, if_true, zero_sub]
    field_simp [ne_of_gt (hd i).1, ne_of_gt (he j).1]
  · have hjp : 0 < jointPi F i j d e := lt_of_le_of_ne (jointPi_nonneg F i j d e) (Ne.symm hz)
    simp [hz, hjp]

/-- The expectation of covariance estimator (10) is its positive-joint covariance sum minus half the paired squared outcomes over all zero-joint pairs.
Supporting finite lemma for Section 5, pp. 1921--1924 (P013-T14,T15). -/
theorem covarianceA_expectation {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hd : Positivity F d) (he : Positivity F e) :
    expectation P (covarianceA F d e) =
      (∑ i, ∑ j ∈ univ.erase i, if 0 < jointPi F i j d e then
        (jointPi F i j d e - pi F i d * pi F j e) *
          (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e) else 0) -
      ∑ i, ∑ j, if jointPi F i j d e = 0 then
        (F.outcome i d ^ 2 + F.outcome j e ^ 2) / 2 else 0 := by
  change expectation P (fun z => _ - _) = _
  rw [expectation_sub, expectation_sum, expectation_sum]
  congr 1
  · apply sum_congr rfl
    intro i _
    rw [expectation_finset_sum]
    apply sum_congr rfl
    intro j _
    by_cases hp : 0 < jointPi F i j d e
    · simp only [hp, if_true, pairTerm_expectation, if_neg (ne_of_gt hp)]
    · simp only [hp, if_false, expectation_const]
  · apply sum_congr rfl
    intro i _
    rw [expectation_sum]
    apply sum_congr rfl
    intro j _
    by_cases hz : jointPi F i j d e = 0
    · simp only [hz, if_true, expectation_add,
        squareTerm_expectation F i d (hd i).1, squareTerm_expectation F j e (he j).1]
      ring
    · simp only [hz, if_false, expectation_const]

/-- Proposition 5.5: (10) has expectation at most true covariance, with no
restriction on zero cross-exposure joints (p. 1924). -/
theorem covarianceA_conservative {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e) :
    expectation P (covarianceA F d e) ≤ covariance P (htTotal F d) (htTotal F e) := by
  rw [covarianceA_expectation F d e hd he, covariance_split_zeros F d e hne hd he]
  have hy : (∑ i, ∑ j, if jointPi F i j d e = 0 then F.outcome i d * F.outcome j e else 0) ≤
      ∑ i, ∑ j, if jointPi F i j d e = 0 then
        (F.outcome i d ^ 2 + F.outcome j e ^ 2) / 2 else 0 := by
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    by_cases hz : jointPi F i j d e = 0
    · simp only [hz, if_true]
      nlinarith [sq_nonneg (F.outcome i d - F.outcome j e)]
    · simp [hz]
  linarith

/-- Proposition 5.6: the variance estimator (11) is conservative in
expectation, including zero joints and mixed-sign outcomes (p. 1924). -/
theorem effectVariance_conservative {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e) :
    variance P (htEffect F d e) ≤ expectation P (effectVariance F d e) := by
  have hvd := varianceHT_conservative F d hd
  have hve := varianceHT_conservative F e he
  have hcov := covarianceA_conservative F d e hne hd he
  rw [expectation_add] at hvd hve
  rw [htEffect_variance]
  change _ ≤ expectation P (fun z => _ / (N : ℝ)^2)
  simp only [div_eq_mul_inv, expectation_mul_const, expectation_sub, expectation_add,
    expectation_const_mul]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sq_nonneg (N : ℝ)))
  linarith

/-- Independence of two finite exposure vectors means factorization of every
pair of vector point events (p. 1925). For empty sets the vector is constant. -/
def VectorIndependent {N K : ℕ} (P : Design Ω) (D : Ω → Fin N → Fin K)
    (A B : Finset (Fin N)) : Prop :=
  ∀ a b : Fin N → Fin K,
    probability P (fun z => (∀ i ∈ A, D z i = a i) ∧ (∀ j ∈ B, D z j = b j)) =
      probability P (fun z => ∀ i ∈ A, D z i = a i) *
      probability P (fun z => ∀ j ∈ B, D z j = b j)

/-- The four clauses of the dependency antecedent *as printed*, p. 1925.
All four clauses use nonmembership. -/
def PrintedNoEdge {N : ℕ} (h : Fin N → Fin N → Bool) (A B : Finset (Fin N)) : Prop :=
  ¬ ∃ i j, h i j = true ∧
    ((i ∈ A ∧ j ∉ B) ∨ (j ∈ A ∧ i ∉ B) ∨
      (i ∉ A ∧ j ∈ B) ∨ (j ∉ A ∧ i ∈ B))

/-- The printed requirement on h before Condition 5, p. 1925. -/
def PrintedDependency {N K : ℕ} (P : Design Ω) (D : Ω → Fin N → Fin K)
    (h : Fin N → Fin N → Bool) : Prop :=
  ∀ A B, Disjoint A B → PrintedNoEdge h A B → VectorIndependent P D A B

/-- Corrected four membership clauses (P013-E002; P013-T6(a), p. 1925). -/
def CorrectedNoEdge {N : ℕ} (h : Fin N → Fin N → Bool) (A B : Finset (Fin N)) : Prop :=
  ¬ ∃ i j, h i j = true ∧
    ((i ∈ A ∧ j ∈ B) ∨ (j ∈ A ∧ i ∈ B) ∨
      (i ∈ A ∧ j ∈ B) ∨ (j ∈ A ∧ i ∈ B))

/-- Independence of full disjoint exposure vectors when no h-edge connects
the two sets: corrected dependency definition (P013-T6, pp. 1925--1926). -/
def GenuineDependency {N K : ℕ} (P : Design Ω) (D : Ω → Fin N → Fin K)
    (h : Fin N → Fin N → Bool) : Prop :=
  ∀ A B, Disjoint A B → CorrectedNoEdge h A B → VectorIndependent P D A B

/-- "Σ_j h_ij ≤ m" (Condition 5, p. 1925); h is binary. -/
def RowBound {N : ℕ} (h : Fin N → Fin N → Bool) (m : ℕ) : Prop :=
  ∀ i, ∑ j, (if h i j = true then 1 else 0 : ℕ) ≤ m

/-- Pairwise independence of D_i and D_j, equivalent to factorization of
all exposure joint probabilities (Condition 4 context, p. 1925). -/
def PairIndependent {N K : ℕ} {P : Design Ω} (F : Population P N K) (i j : Fin N) : Prop :=
  ∀ d e, jointPi F i j d e = pi F i d * pi F j e

/-- "g_ij := 1" on the diagonal or either orientation of an h-edge,
and zero otherwise (corrected Condition 5 subsumes Condition 4, P013-T6). -/
def graphPairIndicator {N : ℕ} (h : Fin N → Fin N → Bool) (i j : Fin N) : ℕ :=
  if i = j ∨ h i j = true ∨ h j i = true then 1 else 0

/-- With the identity indicator, the printed antecedent holds exactly for
two empty sets, hence imposes no dependence restriction (P013-T5(a), p. 1925). -/
theorem printed_identity_vacuous {N : ℕ} (A B : Finset (Fin N)) (hd : Disjoint A B) :
    PrintedNoEdge (fun i j => decide (i = j)) A B ↔ A = ∅ ∧ B = ∅ := by
  classical
  constructor
  · intro h
    have hA : ∀ i, i ∉ A := by
      intro i hi
      have hnot : i ∉ B := (disjoint_left.mp hd) hi
      exact h ⟨i, i, by simp, Or.inl ⟨hi, hnot⟩⟩
    have hB : ∀ i, i ∉ B := by
      intro i hi
      have hnot : i ∉ A := (disjoint_right.mp hd) hi
      exact h ⟨i, i, by simp, Or.inr (Or.inr (Or.inl ⟨hnot, hi⟩))⟩
    exact ⟨eq_empty_iff_forall_notMem.mpr hA, eq_empty_iff_forall_notMem.mpr hB⟩
  · rintro ⟨rfl, rfl⟩
    simp [PrintedNoEdge]

/-- The identity h satisfies the printed definition and row bound m=1
for every joint exposure law (P013-T5(a)). -/
theorem printed_identity_dependency {N K : ℕ} (P : Design Ω) (D : Ω → Fin N → Fin K) :
    PrintedDependency P D (fun i j => decide (i = j)) ∧
    RowBound (fun i j : Fin N => decide (i = j)) 1 := by
  classical
  constructor
  · intro A B hd h
    obtain ⟨rfl, rfl⟩ := (printed_identity_vacuous A B hd).mp h
    intro a b
    simp [probability, P.total]
  · intro i
    simp

/-- The repaired four clauses mean absence of an edge in either direction
(P013-T6(a), p. 1925). This does not assume symmetry. -/
theorem corrected_edge_equivalence {N : ℕ} (h : Fin N → Fin N → Bool)
    (A B : Finset (Fin N)) :
    CorrectedNoEdge h A B ↔ ∀ i ∈ A, ∀ j ∈ B, h i j = false ∧ h j i = false := by
  classical
  unfold CorrectedNoEdge
  constructor
  · intro hno i hi j hj
    constructor
    · cases hx : h i j
      · rfl
      · exact False.elim (hno ⟨i,j,hx,Or.inl ⟨hi,hj⟩⟩)
    · cases hx : h j i
      · rfl
      · exact False.elim (hno ⟨j,i,hx,Or.inr (Or.inl ⟨hi,hj⟩)⟩)
  · intro hn ⟨i,j,hij,hor⟩
    rcases hor with h | h | h | h
    · have := (hn i h.1 j h.2).1; simp_all
    · have := (hn j h.1 i h.2).2; simp_all
    · have := (hn i h.1 j h.2).1; simp_all
    · have := (hn j h.1 i h.2).2; simp_all

/-- For symmetric h the repaired definition is exactly the standard
no-cross-edge antecedent (P013-T6(a)). -/
theorem corrected_symmetric_equivalence {N : ℕ} (h : Fin N → Fin N → Bool)
    (hs : ∀ i j, h i j = h j i) (A B : Finset (Fin N)) :
    CorrectedNoEdge h A B ↔ ∀ i ∈ A, ∀ j ∈ B, h i j = false := by
  rw [corrected_edge_equivalence]
  constructor
  · intro ha i hi j hj; exact (ha i hi j hj).1
  · intro ha i hi j hj; exact ⟨ha i hi j hj, by rw [← hs]; exact ha i hi j hj⟩

/-- Genuine graph independence applied to two nonadjacent singletons gives
pairwise independence (P013-T6(b)). -/
theorem genuine_implies_pair_independent {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (h : Fin N → Fin N → Bool)
    (hg : GenuineDependency P F.exposure h) (i j : Fin N)
    (hne : i ≠ j) (hij : h i j = false) (hji : h j i = false) :
    PairIndependent F i j := by
  have hd : Disjoint ({i} : Finset (Fin N)) {j} := by simpa using hne
  have hn : CorrectedNoEdge h {i} {j} := by
    rw [corrected_edge_equivalence]
    simpa using And.intro hij hji
  have hv := hg {i} {j} hd hn
  intro d e
  have hx := hv (fun _ => d) (fun _ => e)
  simp only [mem_singleton, forall_eq] at hx
  have hpa : probability P (fun z => F.exposure z i = d) = pi F i d := by
    unfold probability pi expectation
    apply sum_congr rfl
    intro z _
    by_cases hi : F.exposure z i = d <;> simp [indicator, hi]
  have hpb : probability P (fun z => F.exposure z j = e) = pi F j e := by
    unfold probability pi expectation
    apply sum_congr rfl
    intro z _
    by_cases hi : F.exposure z j = e <;> simp [indicator, hi]
  have hpab : probability P (fun z => F.exposure z i = d ∧ F.exposure z j = e) =
      jointPi F i j d e := by
    unfold probability jointPi expectation
    apply sum_congr rfl
    intro z _
    by_cases hi : F.exposure z i = d <;> by_cases hj : F.exposure z j = e <;>
      simp [indicator, hi, hj]
  rw [hpab, hpa, hpb] at hx
  exact hx

/-- Bounded row sums imply at most N(2m+1) potentially dependent ordered
pairs (P013-T6(c), p. 1926). -/
theorem graph_pair_count {N : ℕ} (h : Fin N → Fin N → Bool) (m : ℕ) (hb : RowBound h m) :
    (∑ i, ∑ j, graphPairIndicator h i j) ≤ N * (2*m + 1) := by
  have hp : ∀ i j, graphPairIndicator h i j ≤
      (if i = j then 1 else 0 : ℕ) + (if h i j = true then 1 else 0) +
        (if h j i = true then 1 else 0) := by
    intro i j
    by_cases heq : i = j <;> by_cases hij : h i j = true <;> by_cases hji : h j i = true <;>
      simp [graphPairIndicator, heq, hij, hji] <;> omega
  calc
    _ ≤ ∑ i, ∑ j, ((if i = j then 1 else 0 : ℕ) +
        (if h i j = true then 1 else 0) + (if h j i = true then 1 else 0)) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => hp i j
    _ = N + (∑ i, ∑ j, (if h i j = true then 1 else 0 : ℕ)) +
        ∑ j, ∑ i, (if h j i = true then 1 else 0 : ℕ) := by
      simp only [sum_add_distrib]
      rw [sum_comm (f := fun i j => if h j i = true then 1 else 0)]
      simp
    _ ≤ N + N*m + N*m := by
      gcongr
      · exact (sum_le_sum fun i _ => hb i).trans_eq (by simp)
      · exact (sum_le_sum fun j _ => hb j).trans_eq (by simp)
    _ = N * (2*m+1) := by ring

/-- For symmetric h the sharper pair count is N(m+1), accommodating either
self-loop convention (P013-T6(c), p. 1926). -/
theorem graph_pair_count_symmetric {N : ℕ} (h : Fin N → Fin N → Bool) (m : ℕ)
    (hs : ∀ i j, h i j = h j i) (hb : RowBound h m) :
    (∑ i, ∑ j, graphPairIndicator h i j) ≤ N * (m+1) := by
  have hp : ∀ i j, graphPairIndicator h i j ≤
      (if i = j then 1 else 0 : ℕ) + (if h i j = true then 1 else 0) := by
    intro i j
    unfold graphPairIndicator
    rw [← hs i j]
    by_cases heq : i = j <;> by_cases hij : h i j = true <;> simp [heq,hij]
  calc
    _ ≤ ∑ i, ∑ j, ((if i = j then 1 else 0 : ℕ) + (if h i j = true then 1 else 0)) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => hp i j
    _ = N + ∑ i, ∑ j, (if h i j = true then 1 else 0 : ℕ) := by
      simp [sum_add_distrib]
    _ ≤ N + N*m := by
      gcongr
      exact (sum_le_sum fun i _ => hb i).trans_eq (by simp)
    _ = N*(m+1) := by ring

/-- The shared Bernoulli assignment design (P013-T5(c)) has
exactly the two assignments all-zero and all-one, each with probability 1/2. -/
def sharedDesign : Design (Fin 2) where
  weight := fun _ => 1/2
  positive := by intro z; norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- Own-assignment exposure D_i=X for every unit in the shared assignment
design (P013-T5(c)); zero potential outcomes satisfy Conditions 1--2. -/
def sharedPopulation (N : ℕ) : Population sharedDesign N 2 where
  exposure := fun z _ => z
  outcome := fun _ _ => 0

/-- Concrete design witness: printed Condition 5 holds with m=1, every
unit/exposure has marginal probability 1/2, all pairs have joint probability
1/2 for exposure 1, and no two exposures are independent (P013-T5(a,c)). -/
theorem shared_exposure_counterexample (N : ℕ) :
    PrintedDependency sharedDesign (sharedPopulation N).exposure (fun i j => decide (i=j)) ∧
    RowBound (fun i j : Fin N => decide (i=j)) 1 ∧
    (∀ i d, pi (sharedPopulation N) i d = 1/2) ∧
    (∀ i j, jointPi (sharedPopulation N) i j 1 1 = 1/2 ∧
      ¬ PairIndependent (sharedPopulation N) i j) := by
  obtain ⟨hdep,hrow⟩ := printed_identity_dependency sharedDesign (sharedPopulation N).exposure
  refine ⟨hdep,hrow,?_,?_⟩
  · intro i d
    fin_cases d <;> norm_num [pi, expectation, indicator, sharedPopulation,
      sharedDesign, Fin.sum_univ_succ]
  · intro i j
    have hj : jointPi (sharedPopulation N) i j 1 1 = 1/2 := by
      norm_num [jointPi, expectation, indicator, sharedPopulation, sharedDesign, Fin.sum_univ_succ]
    refine ⟨hj,?_⟩
    intro hh
    have hx := hh 1 1
    rw [hj] at hx
    norm_num [pi, expectation, indicator, sharedPopulation, sharedDesign, Fin.sum_univ_succ] at hx

/-- Any pairwise dependency indicator g for the shared-exposure witness must
be all ones, and its count is exactly N² (P013-T5(c), Condition 4 failure). -/
theorem shared_pair_count (N : ℕ) (g : Fin N → Fin N → Bool)
    (hg : ∀ i j, g i j = false → PairIndependent (sharedPopulation N) i j) :
    (∑ i, ∑ j, (if g i j = true then 1 else 0 : ℕ)) = N^2 := by
  have hall : ∀ i j, g i j = true := by
    intro i j
    cases hx : g i j
    · exact False.elim ((shared_exposure_counterexample N).2.2.2 i j |>.2 (hg i j hx))
    · rfl
  simp [hall, pow_two]

/-- With zero self-loops, disjoint triangles also make the printed antecedent
vacuous and have row sum 2 (P013-T5(b)). -/
theorem printed_triangles_vacuous (q : ℕ) (A B : Finset (Fin (3*q))) (hd : Disjoint A B) :
    let h := fun i j : Fin (3*q) => decide (i ≠ j ∧ i.val/3 = j.val/3)
    (PrintedNoEdge h A B ↔ A = ∅ ∧ B = ∅) ∧
      (∀ i, ∑ j, (if h i j = true then 1 else 0 : ℕ) = 2) := by
  classical
  dsimp only
  let h : Fin (3*q) → Fin (3*q) → Bool :=
    fun i j => decide (i ≠ j ∧ i.val/3 = j.val/3)
  have hnbr : ∀ i : Fin (3*q), ∃ j k : Fin (3*q),
      h i j = true ∧ h i k = true ∧ h j k = true ∧ j ≠ k ∧
      (∀ l, h i l = true ↔ l = j ∨ l = k) := by
    intro i
    let j : Fin (3*q) := ⟨3*(i.val/3) + (if i.val%3=0 then 1 else 0), by
      have hi := i.isLt
      split_ifs <;> omega⟩
    let k : Fin (3*q) := ⟨3*(i.val/3) + (if i.val%3=2 then 1 else 2), by
      have hi := i.isLt
      split_ifs <;> omega⟩
    refine ⟨j,k,?_,?_,?_,?_,?_⟩
    · simp only [h,decide_eq_true_eq,ne_eq,Fin.ext_iff]
      dsimp only [j]
      split_ifs <;> omega
    · simp only [h,decide_eq_true_eq,ne_eq,Fin.ext_iff]
      dsimp only [k]
      split_ifs <;> omega
    · simp only [h,decide_eq_true_eq,ne_eq,Fin.ext_iff]
      dsimp only [j,k]
      split_ifs <;> omega
    · simp only [ne_eq,Fin.ext_iff]
      dsimp only [j,k]
      split_ifs <;> omega
    · intro l
      simp only [h,decide_eq_true_eq,ne_eq,Fin.ext_iff]
      dsimp only [j,k]
      split_ifs <;> omega
  have hs : ∀ i j, h i j = h j i := by
    intro i j
    simp only [h,ne_comm,eq_comm]
  change (PrintedNoEdge h A B ↔ A = ∅ ∧ B = ∅) ∧
    (∀ i, ∑ j, (if h i j = true then 1 else 0 : ℕ) = 2)
  constructor
  · constructor
    · intro hn
      have ha : ∀ i ∈ A, ∀ j, h i j = true → j ∈ B := by
        intro i hi j hij
        by_contra hj
        exact hn ⟨i,j,hij,Or.inl ⟨hi,hj⟩⟩
      have hb : ∀ i ∈ B, ∀ j, h i j = true → j ∈ A := by
        intro i hi j hij
        by_contra hj
        exact hn ⟨i,j,hij,Or.inr (Or.inr (Or.inr ⟨hj,hi⟩))⟩
      constructor
      · apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨j,k,hij,hik,hjk,_,_⟩ := hnbr i
        exact (disjoint_left.mp hd) (hb j (ha i hi j hij) k hjk) (ha i hi k hik)
      · apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨j,k,hij,hik,hjk,_,_⟩ := hnbr i
        exact (disjoint_left.mp hd) (hb i hi k hik) (ha j (hb i hi j hij) k hjk)
    · rintro ⟨rfl,rfl⟩
      simp [PrintedNoEdge]
  · intro i
    obtain ⟨j,k,_,_,_,hjk,hn⟩ := hnbr i
    have hf : univ.filter (fun l => h i l = true) = {j,k} := by
      ext l
      simp [hn l]
    rw [sum_boole, hf]
    simp [hjk]


/-- The "predefined" and "fixed" predictions g_i of Section 7.1 (p. 1927)
are real numbers independent of the randomized assignment. Expression (12). -/
def differenceTotal {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (g : Fin N → ℝ) (z : Ω) :=
  htTotal F d z - (∑ i, indicator F.exposure i d z * (g i / pi F i d)) + ∑ i, g i

/-- The HT total of fixed auxiliary predictions has expectation equal to their population total.
Supporting finite lemma for Section 7, pp. 1927--1929 (P013-T16). -/
theorem auxiliary_unbiased {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (g : Fin N → ℝ) (hd : Positivity F d) :
    expectation P (fun z => ∑ i, indicator F.exposure i d z * (g i / pi F i d)) = ∑ i, g i := by
  rw [expectation_sum]
  apply sum_congr rfl
  intro i _
  rw [expectation_mul_const]
  change pi F i d * (g i / pi F i d) = g i
  field_simp [ne_of_gt (hd i).1]

/-- Section 7.1, expression (12): fixed predictions give an unbiased
difference estimator of the population total (p. 1927; P013-T16(a1)). -/
theorem differenceTotal_unbiased {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (g : Fin N → ℝ) (hd : Positivity F d) :
    expectation P (differenceTotal F d g) = potentialTotal F d := by
  change expectation P (fun z => _ - _ + _) = _
  rw [expectation_add, expectation_sub, ht_unbiased F d hd,
    auxiliary_unbiased F d g hd, expectation_const]
  ring

/-- Expressions (12) and (13) agree assignment by assignment, with residual
ε_i = Y_i-g_i for the observed exposure (p. 1927; P013-T16(a1)). -/
theorem differenceTotal_residual {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (g : Fin N → ℝ) (z : Ω) :
    differenceTotal F d g z =
      (∑ i, indicator F.exposure i d z * ((observed F z i - g i) / pi F i d)) + ∑ i, g i := by
  rw [differenceTotal, htTotal_observed]
  congr 1
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  ring

/-- The denominator of the Hajek estimator (15), Σ_i I(D_i=d_k)/π_i(d_k),
is the HT estimate of population size (p. 1928). -/
def htCount {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  ∑ i, indicator F.exposure i d z / pi F i d

/-- Section 7.2: the Hajek denominator has expectation N (p. 1928;
P013-T16(b1)). -/
theorem htCount_unbiased {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hd : Positivity F d) : expectation P (htCount F d) = (N : ℝ) := by
  have h := auxiliary_unbiased F d (fun _ => 1) hd
  change expectation P (fun z => ∑ i, indicator F.exposure i d z / pi F i d) = (N : ℝ)
  simpa [div_eq_mul_inv] using h

/-- Expression (15), p. 1928: Hajek ratio; real division sets it to zero
on the empty-exposure event, applying the paper's 0/0=0 convention (p. 1922). -/
def hajek {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  htTotal F d z / htCount F d z

/-- The exposure indicator is nonnegative at every assignment.
Supporting finite lemma for Section 7, pp. 1927--1929 (P013-T16). -/
theorem indicator_nonneg {N K : ℕ} (D : Ω → Fin N → Fin K) (i : Fin N) (d : Fin K) (z : Ω) :
    0 ≤ indicator D i d z := by unfold indicator; split <;> norm_num

/-- Under positivity, a zero inverse-probability exposure count implies a zero HT outcome total.
Supporting finite lemma for Section 7, pp. 1927--1929 (P013-T16). -/
theorem htTotal_zero_of_count_zero {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hd : Positivity F d) (z : Ω) (hz : htCount F d z = 0) :
    htTotal F d z = 0 := by
  have hnonneg : ∀ i ∈ (univ : Finset (Fin N)), 0 ≤ indicator F.exposure i d z / pi F i d := by
    intro i _
    exact div_nonneg (indicator_nonneg _ _ _ _) (hd i).1.le
  have hterms := (sum_eq_zero_iff_of_nonneg hnonneg).mp hz
  apply sum_eq_zero
  intro i hi
  have hdiv := hterms i hi
  have hind : indicator F.exposure i d z = 0 := by
    have hx := (div_eq_iff (ne_of_gt (hd i).1)).mp hdiv
    simpa using hx
  rw [hind, zero_mul]

/-- The Hajek mean times the normalized HT count equals the HT mean,
including the event of no exposed units (P013-T16 finite lemma, p. 1929). -/
theorem hajek_product_identity {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hd : Positivity F d) (z : Ω) :
    hajek F d z * (htCount F d z / (N : ℝ)) = htMean F d z := by
  by_cases hz : htCount F d z = 0
  · have ht := htTotal_zero_of_count_zero F d hd z hz
    simp [hajek, htMean, hz, ht]
  · unfold hajek htMean
    rw [← mul_div_assoc, div_mul_cancel₀ _ hz]

/-- Randomization covariance equals the expectation of the product of the two centered random variables.
Supporting finite lemma for Section 7, pp. 1927--1929 (P013-T16). -/
theorem covariance_centered (P : Design Ω) (X Y : Ω → ℝ) :
    covariance P X Y = expectation P (fun z => (X z-expectation P X)*(Y z-expectation P Y)) := by
  have hx : (fun z => (X z-expectation P X)*(Y z-expectation P Y)) =
      (fun z => X z*Y z - X z*expectation P Y - expectation P X*Y z +
        expectation P X*expectation P Y) := by funext z; ring
  rw [hx, expectation_add, expectation_sub, expectation_sub,
    expectation_mul_const, expectation_const_mul, expectation_const]
  unfold covariance
  ring

/-- Weighted finite Cauchy--Schwarz for randomization covariance, the
inequality used for the Hartley--Ross bias bound (p. 1929). -/
theorem covariance_abs_bound (P : Design Ω) (X Y : Ω → ℝ) :
    |covariance P X Y| ≤ Real.sqrt (variance P X * variance P Y) := by
  have hsq : covariance P X Y ^ 2 ≤ variance P X * variance P Y := by
    rw [covariance_centered, variance_centered, variance_centered]
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    · intro z _; exact mul_nonneg (P.positive z).le (sq_nonneg _)
    · intro z _; exact mul_nonneg (P.positive z).le (sq_nonneg _)
    · intro z _; dsimp; nlinarith [sq_nonneg (P.weight z *
        (X z - expectation P X) * (Y z - expectation P Y))]
  have hn : 0 ≤ variance P X * variance P Y :=
    mul_nonneg (variance_nonneg P X) (variance_nonneg P Y)
  have hs := Real.sq_sqrt hn
  nlinarith [sq_abs (covariance P X Y), abs_nonneg (covariance P X Y),
    Real.sqrt_nonneg (variance P X * variance P Y)]

/-- The Hajek bias is minus its covariance with the normalized HT count
(P013-T16 finite lemma, Section 7.2, p. 1929). -/
theorem hajek_bias_covariance {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (hN : 0 < N) (d : Fin K) (hd : Positivity F d) :
    expectation P (hajek F d) - potentialMean F d =
      -covariance P (hajek F d) (fun z => htCount F d z / (N : ℝ)) := by
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hc : expectation P (fun z => htCount F d z / (N : ℝ)) = 1 := by
    simp only [div_eq_mul_inv, expectation_mul_const, htCount_unbiased F d hd]
    exact mul_inv_cancel₀ hn0
  have hp : (fun z => hajek F d z * (htCount F d z / (N : ℝ))) = htMean F d := by
    funext z; exact hajek_product_identity F d hd z
  unfold covariance
  rw [hp, htMean_unbiased F d hd, hc]
  ring

/-- The exact Hartley--Ross Hajek bias bound displayed in Section 7.2,
valid with the zero-empty-sample convention (p. 1929; P013-T16(b2)). -/
theorem hajek_bias_bound {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (hN : 0 < N) (d : Fin K) (hd : Positivity F d) :
    |expectation P (hajek F d) - potentialMean F d| ≤
      Real.sqrt (variance P (fun z => htCount F d z / (N : ℝ)) * variance P (hajek F d)) := by
  rw [hajek_bias_covariance F hN d hd, abs_neg, mul_comm]
  exact covariance_abs_bound P _ _

/-- "There exists ... f(z,θ_i)=f(z',θ_i) and y_i^r(z)≠y_i^r(z')"
(Condition 7, p. 1929). Randomization outcomes are fixed functions of z. -/
def Misspecified {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (yr : Fin N → Ω → ℝ) : Prop :=
  ∃ i z z', F.exposure z i = F.exposure z' i ∧ yr i z ≠ yr i z'

/-- Under Condition 7 the actual observed outcome is y_i^r(Z), and (1)
uses this outcome, without Conditions 1--2 (Proposition 8.1, p. 1929). -/
def htRandomizationTotal {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (yr : Fin N → Ω → ℝ) (d : Fin K) (z : Ω) :=
  ∑ i, indicator F.exposure i d z * yr i z / pi F i d

/-- "w_{i,z}=p_z/π_i(f(z,θ_i))" (Proposition 8.1 and Corollary 8.1,
pp. 1929--1930), using the denominator for the exposure of the summand. -/
def randomizationWeight {N K : ℕ} {P : Design Ω} (F : Population P N K) (i : Fin N) (z : Ω) :=
  P.weight z / pi F i (F.exposure z i)

/-- The right side of (16): sum of individual conditional randomization
potential outcomes under the exposure d (pp. 1929--1930). -/
def conditionalPotentialTotal {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (yr : Fin N → Ω → ℝ) (d : Fin K) :=
  ∑ i, ∑ z, if F.exposure z i = d then randomizationWeight F i z * yr i z else 0

/-- Proposition 8.1, expression (16), under Condition 7 in place of
Conditions 1--2 (p. 1929). The identity actually does not need the existence
clause of misspecification. -/
theorem misspecified_expectation {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (yr : Fin N → Ω → ℝ) (d : Fin K) (_hm : Misspecified F yr) (_hd : Positivity F d) :
    expectation P (htRandomizationTotal F yr d) = conditionalPotentialTotal F yr d := by
  change expectation P (fun z => ∑ i, _) = _
  rw [expectation_sum]
  apply sum_congr rfl
  intro i _
  unfold expectation
  apply sum_congr rfl
  intro z _
  by_cases h : F.exposure z i = d
  · simp only [indicator, h, if_true, one_mul, randomizationWeight]
    ring
  · simp [indicator, h]

/-- Corollary 8.1: the expected misspecified HT contrast is the difference
of conditional randomization-outcome totals divided by N (p. 1930). -/
theorem misspecified_contrast {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (yr : Fin N → Ω → ℝ) (d e : Fin K) (_hne : d ≠ e) (hm : Misspecified F yr)
    (hd : Positivity F d) (he : Positivity F e) :
    expectation P (fun z => (htRandomizationTotal F yr d z - htRandomizationTotal F yr e z) /
      (N : ℝ)) = (conditionalPotentialTotal F yr d - conditionalPotentialTotal F yr e) / (N : ℝ) := by
  simp only [div_eq_mul_inv, expectation_mul_const, expectation_sub,
    misspecified_expectation F yr d hm hd, misspecified_expectation F yr e hm he]


variable {Ξ : Type*} [Fintype Ξ]

/-- Independent designs multiply their assignment probabilities. Used for
the independent experiment and simulated replicates (pp. 1917, 1920; A.3). -/
def independentProduct (P : Design Ω) (Q : Design Ξ) : Design (Ω × Ξ) where
  weight z := P.weight z.1 * Q.weight z.2
  positive z := mul_pos (P.positive z.1) (Q.positive z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← mul_sum, Q.total, mul_one, P.total]

/-- R independent draws "based on the randomization plan" (p. 1917),
the interpretation used by the Binomial(R,π_i) computation in Appendix A.3. -/
def replicateDesign (P : Design Ω) (R : ℕ) : Design (Fin R → Ω) where
  weight z := ∏ r, P.weight (z r)
  positive z := prod_pos fun r _ => P.positive (z r)
  total := by
    classical
    simpa [Fintype.piFinset_univ, P.total] using
      (sum_prod_piFinset (univ : Finset Ω) (fun _ : Fin R => P.weight))

/-- Marginalization of an independent finite product design: any one draw
has the original design expectation (Monte Carlo setup, pp. 1917, 1920). -/
theorem replicate_marginal (P : Design Ω) (R : ℕ) (r : Fin R) (g : Ω → ℝ) :
    expectation (replicateDesign P R) (fun zs => g (zs r)) = expectation P g := by
  classical
  change (∑ zs : Fin R → Ω, (∏ t, P.weight (zs t)) * g (zs r)) = _
  calc
    _ = ∑ zs : Fin R → Ω, ∏ t, P.weight (zs t) * (if t=r then g (zs t) else 1) := by
      apply sum_congr rfl
      intro zs _
      rw [prod_mul_distrib]
      simp
    _ = ∏ t : Fin R, ∑ z, P.weight z * (if t=r then g z else 1) := by
      simpa [Fintype.piFinset_univ] using
        (sum_prod_piFinset (univ : Finset Ω)
          (fun t : Fin R => fun z => P.weight z * (if t=r then g z else 1)))
    _ = expectation P g := by
      have hs : ∀ t : Fin R, (∑ z, P.weight z*(if t=r then g z else 1)) =
          if t=r then expectation P g else 1 := by
        intro t
        by_cases ht : t=r
        · simp [ht, expectation]
        · simp [ht, P.total]
      simp_rw [hs]
      simp

/-- Distinct independent replicate coordinates factorize expectations of
products, without requiring identical functions at the two coordinates
(Proposition 3.1 setup and the independent-assignment witnesses P013-T1,T7). -/
theorem replicate_pair_marginal (P : Design Ω) (R : ℕ) (i j : Fin R) (hne : i ≠ j)
    (g k : Ω → ℝ) :
    expectation (replicateDesign P R) (fun zs => g (zs i)*k (zs j)) =
      expectation P g*expectation P k := by
  classical
  change (∑ zs : Fin R → Ω, (∏ r, P.weight (zs r)) * (g (zs i)*k (zs j))) = _
  calc
    _ = ∑ zs : Fin R → Ω, ∏ r, P.weight (zs r) *
        (if r=i then g (zs r) else 1) * (if r=j then k (zs r) else 1) := by
      apply sum_congr rfl
      intro zs _
      simp only [prod_mul_distrib]
      simp [mul_assoc]
    _ = ∏ r : Fin R, ∑ z, P.weight z * (if r=i then g z else 1) *
        (if r=j then k z else 1) := by
      simpa [Fintype.piFinset_univ] using
        (sum_prod_piFinset (univ : Finset Ω) (fun r : Fin R => fun z =>
          P.weight z * (if r=i then g z else 1) * (if r=j then k z else 1)))
    _ = _ := by
      have hs : ∀ r : Fin R, (∑ z, P.weight z*(if r=i then g z else 1)*
          (if r=j then k z else 1)) =
          (if r=i then expectation P g else 1)*(if r=j then expectation P k else 1) := by
        intro r
        by_cases hr : r=i <;> by_cases ht : r=j
        · exact False.elim (hne (hr.symm.trans ht))
        · simp [hr,ht,hne,hne.symm,expectation]
        · simp [hr,ht,hne,hne.symm,expectation]
        · simp [hr,ht,P.total]
      simp_rw [hs]
      rw [prod_mul_distrib]
      simp

/-- Coordinate permutation preserves the iid finite product law (A.3 setup).  Supporting finite lemma for corrected Proposition 4.1 (T4), Appendix A.3, p. 1938. -/
theorem replicate_reindex (P : Design Ω) (R : ℕ) (σ : Equiv.Perm (Fin R))
    (g : (Fin R → Ω) → ℝ) :
    expectation (replicateDesign P R) (fun zs => g (zs ∘ σ)) =
      expectation (replicateDesign P R) g := by
  classical
  let e : (Fin R → Ω) ≃ (Fin R → Ω) :=
    { toFun := fun zs => zs ∘ σ
      invFun := fun zs => zs ∘ σ.symm
      left_inv := by intro zs; funext r; simp
      right_inv := by intro zs; funext r; simp }
  unfold expectation
  apply Fintype.sum_equiv e
  intro zs
  change (∏ r, P.weight (zs r)) * g (zs ∘ σ) =
    (∏ r, P.weight (zs (σ r))) * g (zs ∘ σ)
  rw [Equiv.prod_comp σ (fun t => P.weight (zs t))]

/-- Splitting the first coordinate in a product design is an exact finite Fubini identity.  Supporting finite lemma for corrected Proposition 4.1 (T4), Appendix A.3, p. 1938. -/
theorem replicate_cons_expectation (P : Design Ω) (R : ℕ)
    (g : (Fin (R+1) → Ω) → ℝ) :
    expectation (replicateDesign P (R+1)) g =
      expectation P (fun z => expectation (replicateDesign P R) (fun zs => g (Fin.cons z zs))) := by
  classical
  unfold expectation
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (R+1) => Ω))
    (fun x : Ω × (Fin R → Ω) =>
      (replicateDesign P (R+1)).weight (Fin.cons x.1 x.2) * g (Fin.cons x.1 x.2))
    (fun zs => (replicateDesign P (R+1)).weight zs * g zs) (by intro x; rfl)]
  simp only [Fintype.sum_prod_type, replicateDesign, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.mul_sum, mul_assoc]

/-- Symmetrization of R+1 success indicators yields the exact inverse-count
moment without regrouping assignments into binomial fibers (corrected A.3).  Supporting finite lemma for corrected Proposition 4.1 (T4), Appendix A.3, p. 1938. -/
theorem smoothed_inverse_success (P : Design Ω) (A : Ω → Prop) [DecidablePred A] (R : ℕ) :
    let b := fun z => if A z then (1 : ℝ) else 0
    let p := expectation P b
    p * expectation (replicateDesign P R)
      (fun zs => (R+1 : ℝ) / ((∑ r, b (zs r)) + 1)) = 1-(1-p)^(R+1) := by
  classical
  let b : Ω → ℝ := fun z => if A z then 1 else 0
  let count : (Fin (R+1) → Ω) → ℝ := fun zs => ∑ r, b (zs r)
  let H : Fin (R+1) → ℝ := fun r => expectation (replicateDesign P (R+1))
    (fun zs => b (zs r) / count zs)
  have hsym : ∀ r, H r = H 0 := by
    intro r
    let σ : Equiv.Perm (Fin (R+1)) := Equiv.swap 0 r
    have h := replicate_reindex P (R+1) σ (fun zs => b (zs 0) / count zs)
    have hc : ∀ zs : Fin (R+1) → Ω, count (zs ∘ σ) = count zs := by
      intro zs
      exact Equiv.sum_comp σ (fun t => b (zs t))
    simpa only [Function.comp_apply, hc, σ, Equiv.swap_apply_left] using h
  have hz : ∀ zs : Fin (R+1) → Ω,
      (∑ r, b (zs r)/count zs) = if ∀ r, ¬ A (zs r) then 0 else 1 := by
    intro zs
    rw [← sum_div]
    change count zs / count zs = _
    by_cases h : ∀ r, ¬ A (zs r)
    · have hc : count zs = 0 := by simp [count,b,h]
      simp [h,hc]
    · obtain ⟨r,hr⟩ : ∃ r, A (zs r) := by simpa using h
      have hc : 0 < count zs := by
        have ht : b (zs r) ≤ count zs :=
          single_le_sum (f := fun t => b (zs t))
            (fun t _ => by simp only [b]; split_ifs <;> norm_num) (mem_univ r)
        have hb : b (zs r) = 1 := by simp [b,hr]
        linarith
      simp [h,div_self (ne_of_gt hc)]
  have htot : (R+1 : ℝ) * H 0 = 1-(1-expectation P b)^(R+1) := by
    calc
      _ = ∑ r : Fin (R+1), H r := by simp [hsym, mul_comm]
      _ = expectation (replicateDesign P (R+1))
          (fun zs => ∑ r, b (zs r)/count zs) := (expectation_sum _ _).symm
      _ = expectation (replicateDesign P (R+1))
          (fun zs => if ∀ r, ¬ A (zs r) then 0 else 1) := by simp_rw [hz]
      _ = 1-expectation (replicateDesign P (R+1))
          (fun zs => ∏ r, (1-b (zs r))) := by
        have hf : (fun zs : Fin (R+1) → Ω => if ∀ r, ¬ A (zs r) then (0:ℝ) else 1) =
            (fun zs => 1-∏ r, (1-b (zs r))) := by
          funext zs
          by_cases h : ∀ r, ¬ A (zs r)
          · simp [h,b]
          · obtain ⟨r,hr⟩ : ∃ r, A (zs r) := by simpa using h
            have hp : (∏ r, (1-b (zs r))) = 0 := by
              apply prod_eq_zero (mem_univ r)
              simp [b,hr]
            simp [h,hp]
        rw [hf,expectation_sub,expectation_const]
      _ = _ := by
        have hp : expectation (replicateDesign P (R+1))
            (fun zs => ∏ r, (1-b (zs r))) = (1-expectation P b)^(R+1) := by
          change (∑ zs : Fin (R+1) → Ω, (∏ r, P.weight (zs r)) *
            (∏ r, (1-b (zs r)))) = _
          simp_rw [← prod_mul_distrib]
          rw [show (∑ zs : Fin (R+1) → Ω, ∏ r, P.weight (zs r) * (1-b (zs r))) =
            ∏ r : Fin (R+1), ∑ z, P.weight z * (1-b z) by
            simpa [Fintype.piFinset_univ] using
              (sum_prod_piFinset (univ : Finset Ω)
                (fun _ : Fin (R+1) => fun z => P.weight z * (1-b z)))]
          simp [mul_sub, sum_sub_distrib, P.total, expectation]
        rw [hp]
  have hfirst : H 0 = expectation P b * expectation (replicateDesign P R)
      (fun zs => 1 / ((∑ r, b (zs r)) + 1)) := by
    dsimp [H]
    rw [replicate_cons_expectation P R]
    simp only [Fin.cons_zero]
    have hg : (fun z : Ω => expectation (replicateDesign P R)
        (fun zs : Fin R → Ω => b z / count (Fin.cons z zs))) =
        (fun z => b z * expectation (replicateDesign P R)
          (fun zs => 1 / ((∑ r, b (zs r)) + 1))) := by
      funext z
      by_cases h : A z
      · have hbz : b z = 1 := by simp [b,h]
        have hc : ∀ zs : Fin R → Ω, count (Fin.cons z zs) = (∑ r, b (zs r)) + 1 := by
          intro zs
          dsimp only [count]
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero,Fin.cons_succ,hbz]
          ring
        simp only [hbz,hc,one_mul]
      · simp [b,h,expectation]
    rw [hg, expectation_mul_const]
  dsimp only
  change expectation P b * expectation (replicateDesign P R)
    (fun zs => (R+1 : ℝ) / ((∑ r, b (zs r)) + 1)) = _
  rw [show (fun zs : Fin R → Ω => (R+1 : ℝ)/((∑ r, b (zs r))+1)) =
    (fun zs => (R+1 : ℝ)*(1/((∑ r, b (zs r))+1))) by funext zs; ring,
    expectation_const_mul]
  rw [hfirst] at htot
  nlinarith [htot]

/-- Probability of coordinatewise events factors in the product assignment law.  Supporting product-law lemma for Conditions 5 and the T1 paired witness, p. 1925. -/
theorem replicate_probability_product (P : Design Ω) (R : ℕ)
    (A : Fin R → Ω → Prop) :
    probability (replicateDesign P R) (fun zs => ∀ r, A r (zs r)) =
      ∏ r, probability P (A r) := by
  classical
  unfold probability
  calc
    _ = ∑ zs : Fin R → Ω, ∏ r, if A r (zs r) then P.weight (zs r) else 0 := by
      apply sum_congr rfl
      intro zs _
      by_cases h : ∀ r, A r (zs r)
      · simp [h,replicateDesign]
      · obtain ⟨r,hr⟩ : ∃ r, ¬ A r (zs r) := by simpa using h
        simp only [h,if_false]
        symm
        exact prod_eq_zero (mem_univ r) (by simp [hr])
    _ = _ := by
      simpa [Fintype.piFinset_univ] using
        (sum_prod_piFinset (univ : Finset Ω)
          (fun r : Fin R => fun z => if A r z then P.weight z else 0))

/-- A unit exposure depending on one product coordinate admits a product
formula for every vector event, including multiple units on one coordinate.  Supporting vector-event lemma for genuine Condition 5 and the T1 paired witness, p. 1925. -/
theorem replicate_probability_by_units {N K : ℕ} (P : Design Ω) (R : ℕ)
    (index : Fin N → Fin R) (φ : Fin N → Ω → Fin K)
    (A : Finset (Fin N)) (a : Fin N → Fin K) :
    probability (replicateDesign P R) (fun zs => ∀ i ∈ A, φ i (zs (index i)) = a i) =
      ∏ r, probability P (fun x => ∀ i ∈ A, index i = r → φ i x = a i) := by
  classical
  have h : (fun zs : Fin R → Ω => ∀ i ∈ A, φ i (zs (index i)) = a i) =
      (fun zs => ∀ r, ∀ i ∈ A, index i = r → φ i (zs r) = a i) := by
    funext zs
    apply propext
    constructor
    · intro h r i hi hir
      subst r
      exact h i hi
    · intro h i hi
      exact h (index i) i hi rfl
  rw [h]
  exact replicate_probability_product P R (fun r x => ∀ i ∈ A, index i = r → φ i x = a i)

/-- Units using disjoint independent product coordinates have independent
full exposure vectors. It certifies the genuine pair graph for T1 and T7.  Supporting finite lemma for corrected Condition 5 (T6), p. 1925, used in T1 and T7. -/
theorem coordinate_population_genuine_dependency {N K : ℕ} (P : Design Ω) (R : ℕ)
    (index : Fin N → Fin R) (φ : Fin N → Ω → Fin K) :
    GenuineDependency (replicateDesign P R) (fun zs i => φ i (zs (index i)))
      (fun i j => decide (index i = index j)) := by
  classical
  intro A B _hdis hno a b
  let C : Fin R → Ω → Prop := fun r x => ∀ i ∈ A, index i = r → φ i x = a i
  let D : Fin R → Ω → Prop := fun r x => ∀ i ∈ B, index i = r → φ i x = b i
  have hj : (fun zs : Fin R → Ω =>
      (∀ i ∈ A, φ i (zs (index i)) = a i) ∧ (∀ i ∈ B, φ i (zs (index i)) = b i)) =
      (fun zs => ∀ r, C r (zs r) ∧ D r (zs r)) := by
    funext zs
    apply propext
    constructor
    · rintro ⟨ha,hb⟩ r
      constructor
      · intro i hi hir; subst r; exact ha i hi
      · intro i hi hir; subst r; exact hb i hi
    · intro h
      exact ⟨fun i hi => (h (index i)).1 i hi rfl,
        fun i hi => (h (index i)).2 i hi rfl⟩
  change probability (replicateDesign P R) _ = _
  rw [hj,replicate_probability_product P R (fun r x => C r x ∧ D r x),
    replicate_probability_by_units P R index φ A a,
    replicate_probability_by_units P R index φ B b,← prod_mul_distrib]
  apply prod_congr rfl
  intro r _
  change probability P (fun x => C r x ∧ D r x) = probability P (C r) * probability P (D r)
  by_cases ha : ∃ i ∈ A, index i = r
  · obtain ⟨i,hi,hir⟩ := ha
    have hd : ∀ x, D r x := by
      intro x j hj hjr
      have he : index i = index j := hir.trans hjr.symm
      exact False.elim (hno ⟨i,j,by simp [he],Or.inl ⟨hi,hj⟩⟩)
    simp [probability,hd,P.total]
    apply sum_congr rfl
    intro x _
    split_ifs <;> rfl
  · have hc : ∀ x, C r x := by
      intro x i hi hir
      exact False.elim (ha ⟨i,hi,hir⟩)
    simp [probability,hc,P.total]
    apply sum_congr rfl
    intro x _
    split_ifs <;> rfl

/-- "X_i = Σ_{r=1}^R I_r(f(z_r,θ_i)=d_k)" (p. 1920).
The count is real-valued but is a finite sum of binary indicators. -/
def replicateCount {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (R : ℕ) (zs : Fin R → Ω) (i : Fin N) :=
  ∑ r, indicator F.exposure i d (zs r)

/-- "π̂_i(d_k) = (X_i+1)/(R+1)" (pp. 1919--1920), additive smoothing. -/
def simulatedPi {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (R : ℕ) (zs : Fin R → Ω) (i : Fin N) :=
  (replicateCount F d R zs i + 1) / (R+1 : ℕ)

/-- "ŷ^T_HT,R(d_k) = Σ_i I(D_i=d_k)Y_i/π̂_i(d_k)" (p. 1920),
on the joint probability space of experiment and independent replicates. -/
def simulatedHTTotal {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (R : ℕ) (z : Ω × (Fin R → Ω)) :=
  ∑ i, indicator F.exposure i d z.1 * observed F z.1 i / simulatedPi F d R z.2 i

/-- "π_0(d_k) = min_i {π_i(d_k)}" (Proposition 4.1, p. 1920), represented
by its minimum specification. Nonempty finite populations attain this minimum. -/
def IsMinimumPi {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (p0 : ℝ) : Prop :=
  (∃ i, pi F i d = p0) ∧ ∀ i, p0 ≤ pi F i d

/-- The signed-outcome correction factor κ = Σ_i |y_i(d)| / |y^T(d)|
(P013-T4(c), correction to Proposition 4.1). -/
def cancellationFactor {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) :=
  (∑ i, |F.outcome i d|) / |potentialTotal F d|


/-- Exact triangle-inequality lemma behind the repaired bound: if
0 ≤ q_i ≤ q_0 then |Σ_i y_i q_i| ≤ q_0 Σ_i |y_i| (P013-T4 finite lemma). -/
theorem signed_bias_absolute_bound {ι : Type*} [Fintype ι] (y q : ι → ℝ)
    (q0 : ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ q0) :
    |∑ i, y i * q i| ≤ q0 * ∑ i, |y i| := by
  calc
    _ ≤ ∑ i, |y i * q i| := abs_sum_le_sum_abs _ _
    _ = ∑ i, |y i| * q i := by
      apply sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hq i).1]
    _ ≤ ∑ i, |y i| * q0 := sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hq i).2 (abs_nonneg _)
    _ = q0 * ∑ i, |y i| := by rw [← sum_mul]; ring

/-- The power weights q_i=(1-π_i)^(R+1) satisfy 0 ≤ q_i ≤ (1-π_0)^(R+1)
when π_0 is the minimum exposure probability (P013-T4 finite lemma). -/
theorem simulated_power_bound {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hd : Positivity F d) (R : ℕ) (p0 : ℝ) (hmin : IsMinimumPi F d p0) :
    ∀ i, 0 ≤ (1-pi F i d)^(R+1) ∧ (1-pi F i d)^(R+1) ≤ (1-p0)^(R+1) := by
  intro i
  constructor
  · exact pow_nonneg (by linarith [(hd i).2]) _
  · exact pow_le_pow_left₀ (by linarith [(hd i).2]) (by linarith [hmin.2 i]) _







set_option exponentiation.threshold 11000 in
set_option maxHeartbeats 4000000 in
/-- In the numerical example, 10,593 replicates pass the printed
power criterion and 10,592 fail (p. 1920; P013-T4(f), P013-T12). -/
theorem replicate_rule_numerical :
    ((1999/2000 : ℚ) ^ (10593+1)) ≤ 1/200 ∧
    1/200 < ((1999/2000 : ℚ) ^ (10592+1)) := by
  norm_num

/-- Two independent Bernoulli treatments with probabilities 1/3 and 2/3;
the supported vectors (00),(01),(10),(11) have weights 2/9,4/9,1/9,2/9
(P013-T3, correction P013-E003). Fin 2 relabels paper treatments 1,2 as 0,1. -/
def signedReplicationDesign : Design (Fin 4) where
  weight := ![2/9, 4/9, 1/9, 2/9]
  positive := by intro z; fin_cases z <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- The two-unit experiment for T3: exposure is own assignment;
unexposed outcomes are zero, exposed outcomes are (a,-1), with a=2 or a=1. -/
def signedReplicationPopulation (a : ℝ) : Population signedReplicationDesign 2 2 where
  exposure z i := if i = 0 then (if z.val < 2 then 0 else 1) else
    (if z.val % 2 = 0 then 0 else 1)
  outcome i d := if d = 0 then 0 else if i = 0 then a else -1

/-- The R=1 smoothed estimator on the 16 equally indexed pairs (Z,Z'),
using their unequal product design weights (P013-T3). -/
def signedOneReplicate (a : ℝ) (z : Fin 4 × Fin 4) : ℝ :=
  ∑ i, indicator (signedReplicationPopulation a).exposure i 1 z.1 *
    observed (signedReplicationPopulation a) z.1 i /
    ((indicator (signedReplicationPopulation a).exposure i 1 z.2 + 1)/2)

/-- Concrete counterexample to Proposition 4.1 and the R-rule: all exposure
probabilities are strictly between 0 and 1, the total is 1, the independently
replicated estimator has expectation 2/9, and its relative bias 7/9 exceeds
both the printed 4/9 bound and b=1/2 although R=1 passes (P013-T3(a,b)). -/
theorem signed_replication_counterexample :
    (∀ i d, 0 < pi (signedReplicationPopulation 2) i d ∧
      pi (signedReplicationPopulation 2) i d < 1) ∧
    pi (signedReplicationPopulation 2) 0 1 = 1/3 ∧
    pi (signedReplicationPopulation 2) 1 1 = 2/3 ∧
    potentialTotal (signedReplicationPopulation 2) 1 = 1 ∧
    expectation (independentProduct signedReplicationDesign signedReplicationDesign)
      (signedOneReplicate 2) = 2/9 ∧
    |(expectation (independentProduct signedReplicationDesign signedReplicationDesign)
      (signedOneReplicate 2) - 1)/1| = 7/9 ∧
    (4/9 : ℝ) < 7/9 ∧ (1/2 : ℝ) < 7/9 ∧
    ((1-1/3 : ℝ)^(1+1)) ≤ 1/2 ∧ (1/2 : ℝ) < (1-1/3)^1 := by
  constructor
  · intro i d
    fin_cases i <;> fin_cases d <;> norm_num [pi, expectation, indicator,
      signedReplicationPopulation, signedReplicationDesign, Fin.sum_univ_succ]
  · norm_num [pi, potentialTotal, expectation, independentProduct, signedOneReplicate,
      indicator, observed, signedReplicationPopulation, signedReplicationDesign,
      Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- With the same fully specified design and exposed outcomes (1,-1),
the total is zero but the simulated estimator has expectation -1/3; the
last absolute-bias inequality of Appendix A.3 fails (P013-T3(c), p. 1938). -/
theorem zero_total_replication_counterexample :
    potentialTotal (signedReplicationPopulation 1) 1 = 0 ∧
    expectation (independentProduct signedReplicationDesign signedReplicationDesign)
      (signedOneReplicate 1) = -1/3 ∧
    |expectation (independentProduct signedReplicationDesign signedReplicationDesign)
      (signedOneReplicate 1) - potentialTotal (signedReplicationPopulation 1) 1| >
      |potentialTotal (signedReplicationPopulation 1) 1| * (1-1/3)^(1+1) := by
  norm_num [pi, potentialTotal, expectation, independentProduct, signedOneReplicate,
    indicator, observed, signedReplicationPopulation, signedReplicationDesign,
    Fintype.sum_prod_type, Fin.sum_univ_succ]


/-- Convergence in probability for changing finite randomization designs:
for every ε>0, Pr(|X_N-a|>ε)→0 (Section 6, pp. 1924--1926). -/
def ConvergesInProbability {L : ℕ → Type*} [∀ n : ℕ, Fintype (L n)]
    (P : ∀ n : ℕ, Design (L n)) (X : ∀ n : ℕ, L n → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => probability (P n) (fun z => ε < |X n z-a|)) atTop (𝓝 0)

/-- The standard normal distribution function Φ, used by Proposition 6.2
and the coverage statements (pp. 1926, 1943). -/
def normalCDF (x : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x

/-- z_(1-α/2), the (1-α/2)-quantile of N(0,1), as the least x whose
CDF is at least 1-α/2 (Proposition 6.2, p. 1926; only used for 0<α<1). -/
def normalCritical (α : ℝ) : ℝ := sInf {x : ℝ | 1-α/2 ≤ normalCDF x}

/-- Normal convergence in distribution through CDFs, which characterizes
weak convergence because the limiting positive-variance normal CDF is continuous. -/
def TendsNormal {L : ℕ → Type*} [∀ n : ℕ, Fintype (L n)]
    (P : ∀ n : ℕ, Design (L n)) (X : ∀ n : ℕ, L n → ℝ) (μ : ℝ) (v : ℝ≥0) : Prop :=
  ∀ x : ℝ, Tendsto (fun n : ℕ => probability (P n) (fun z => X n z ≤ x)) atTop
    (𝓝 (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal μ v) x))

/-- A population-size-N experiment, with finite supported assignment vectors,
exact probabilities, an exposure mapping and fixed exposure-specific outcomes
(Sections 3--6, pp. 1914--1926). Fin supportSize merely relabels Ω. -/
structure Experiment (N : ℕ) where
  supportSize : ℕ
  exposureSize : ℕ
  design : Design (Fin supportSize)
  population : Population design N exposureSize

/-- A size-indexed experiment array with two distinct comparison exposures.
Index n means N=n+1. `NestedPopulationSetup` supplies the paper's nested
population and fixed-label/outcome setup when a target requires it (p. 1924). -/
structure ExperimentSequence where
  experiment : ∀ n : ℕ, Experiment (n+1)
  treated : ∀ n : ℕ, Fin (experiment n).exposureSize
  control : ∀ n : ℕ, Fin (experiment n).exposureSize
  distinct : ∀ n : ℕ, treated n ≠ control n
  positiveTreated : ∀ n : ℕ, Positivity (experiment n).population (treated n)
  positiveControl : ∀ n : ℕ, Positivity (experiment n).population (control n)

/-- "A sequence of nested populations indexed by size N" (Section 6,
p. 1924), with the same fixed y_i(d) for existing units (p. 1918).
Fin(n+1) are the nested unit prefixes. Injective exposure names and one
global potential-outcome table identify all populations' outcomes, and the
two comparison exposure names stay fixed. The number of other exposure
labels and each size's randomization law can vary. -/
def NestedPopulationSetup (S : ExperimentSequence) : Prop :=
  ∃ labels : ∀ n, Fin (S.experiment n).exposureSize ↪ ℕ,
    ∃ d e : ℕ, ∃ outcomes : ℕ → ℕ → ℝ, d ≠ e ∧
      (∀ n, labels n (S.treated n) = d ∧ labels n (S.control n) = e) ∧
      (∀ n (i : Fin (n+1)) a,
        (S.experiment n).population.outcome i a = outcomes i.val (labels n a))

/-- The exact randomization law at population size N=n+1 (Section 6, p. 1924). -/
abbrev seqLaw (S : ExperimentSequence) (n : ℕ) := (S.experiment n).design
/-- The exposure mapping and fixed outcomes in U_N (Section 6, p. 1924). -/
abbrev seqPopulation (S : ExperimentSequence) (n : ℕ) := (S.experiment n).population
/-- "τ̂_HT(d_k,d_l)" along the population sequence (expression (3), p. 1920). -/
abbrev seqEstimate (S : ExperimentSequence) (n : ℕ) :=
  htEffect (seqPopulation S n) (S.treated n) (S.control n)
/-- "τ(d_k,d_l)" along the population sequence (p. 1919). -/
abbrev seqTarget (S : ExperimentSequence) (n : ℕ) :=
  causalEffect (seqPopulation S n) (S.treated n) (S.control n)
/-- "Var[τ̂_HT(d_k,d_l)]" along the sequence (Condition 6, p. 1926). -/
abbrev seqTrueVariance (S : ExperimentSequence) (n : ℕ) := variance (seqLaw S n) (seqEstimate S n)
/-- "Var̂[τ̂_HT(d_k,d_l)]" along the sequence (expression (11), p. 1924). -/
abbrev seqVarianceEstimate (S : ExperimentSequence) (n : ℕ) :=
  effectVariance (seqPopulation S n) (S.treated n) (S.control n)

/-- "0 < π_i(d_k) < 1 for all i and k" along the sequence
(p. 1918). Printed headline results use this standing positivity premise;
the corrected Proposition 6.2 only requires the two comparison exposures. -/
def StandingPositivity (S : ExperimentSequence) : Prop :=
  ∀ n d, Positivity (seqPopulation S n) d

/-- The repaired C3 bounds only |y_i(d)| and 1/π_i(d) for the two
exposures under comparison, uniformly in N (P013-T2(C3)). -/
def ComparisonBounded (S : ExperimentSequence) : Prop :=
  ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ 0 < c2 ∧ ∀ n i,
    |(seqPopulation S n).outcome i (S.treated n)| ≤ c1 ∧
    |(seqPopulation S n).outcome i (S.control n)| ≤ c1 ∧
    |1 / pi (seqPopulation S n) i (S.treated n)| ≤ c2 ∧
    |1 / pi (seqPopulation S n) i (S.control n)| ≤ c2

/-- "For all values i and d_k, |y_i(d_k)| ≤ c1 and |1/π_i(d_k)| ≤ c2",
with constants independent of N (Condition 3, p. 1925). -/
def Condition3 (S : ExperimentSequence) : Prop :=
  ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ 0 < c2 ∧ ∀ n i d,
    |(seqPopulation S n).outcome i d| ≤ c1 ∧
    |1 / pi (seqPopulation S n) i d| ≤ c2

/-- Printed Condition 3 implies the comparison-specific corrected C3
(P013-T2; Condition 3, p. 1925). -/
theorem condition3_implies_comparison (S : ExperimentSequence) (hc : Condition3 S) :
    ComparisonBounded S := by
  obtain ⟨c1,c2,h1,h2,hb⟩ := hc
  exact ⟨c1,c2,h1,h2,fun n i =>
    ⟨(hb n i (S.treated n)).1,(hb n i (S.control n)).1,
      (hb n i (S.treated n)).2,(hb n i (S.control n)).2⟩⟩

/-- Pairwise dependence count o(N²), with g_ij=0 implying independence
(Condition 4, p. 1925). The ratio tending to zero is precisely little-o. -/
def Condition4 (S : ExperimentSequence) : Prop :=
  ∃ g : ∀ n : ℕ, Fin (n+1) → Fin (n+1) → Bool,
    (∀ n i j, g n i j = false → PairIndependent (seqPopulation S n) i j) ∧
    Tendsto (fun n : ℕ => (∑ i, ∑ j, (if g n i j = true then 1 else 0 : ℝ)) / (n+1 : ℝ)^2)
      atTop (𝓝 0)

/-- Condition 5 with the literal four nonmembership clauses (pp. 1925--1926).
No symmetry or diagonal convention was printed, so none is added here. -/
def Condition5Printed (S : ExperimentSequence) : Prop :=
  ∃ m : ℕ, ∃ h : ∀ n : ℕ, Fin (n+1) → Fin (n+1) → Bool, ∀ n : ℕ,
    PrintedDependency (seqLaw S n) (seqPopulation S n).exposure (h n) ∧ RowBound (h n) m

/-- Repaired Condition 5: a symmetric genuine dependency graph and one
finite degree bound m uniform in N (P013-T2(C5), P013-T6). -/
def Condition5Genuine (S : ExperimentSequence) : Prop :=
  ∃ m : ℕ, ∃ h : ∀ n : ℕ, Fin (n+1) → Fin (n+1) → Bool, ∀ n : ℕ,
    (∀ i j, h n i j = h n j i) ∧
    GenuineDependency (seqLaw S n) (seqPopulation S n).exposure (h n) ∧ RowBound (h n) m

/-- "N Var(τ̂_HT) → c, c>0" (Condition 6, p. 1926). The sequence is
deterministic, so the printed probability arrow is ordinary convergence. -/
def Condition6 (S : ExperimentSequence) : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (n+1 : ℝ)*seqTrueVariance S n) atTop (𝓝 c)

/-- The lower-tail condition (L) added to repair Proposition 6.2 (P013-T2).
It requires concentration at or above true variance, not convergence of a ratio. -/
def LowerTailCondition (S : ExperimentSequence) : Prop :=
  ∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => probability (seqLaw S n)
    (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z < (n+1 : ℝ)*seqTrueVariance S n-δ))
      atTop (𝓝 0)

/-- Wald coverage of τ_N using exactly expression (11). Negative estimated
variance counts as noncoverage; under (L) together with Condition 6 its
probability vanishes. Proposition 6.2, p. 1926; corrected P013-T2 and T8. -/
def seqCoverage (S : ExperimentSequence) (α : ℝ) (n : ℕ) :=
  probability (seqLaw S n) (fun z => 0 ≤ seqVarianceEstimate S n z ∧
    |seqEstimate S n z-seqTarget S n| ≤ normalCritical α * Real.sqrt (seqVarianceEstimate S n z))


/-- Corrected algebraic display of Appendix A.7, centered at the population
effect τ, valid when true and estimated variances are positive
(P013-T9(iii), P013-T8 finite lemma, p. 1943). -/
theorem studentized_identity (estimate target V Vhat : ℝ) (hV : 0 < V) (hVhat : 0 < Vhat) :
    (estimate-target) / Real.sqrt Vhat =
      ((estimate-target) / Real.sqrt V) * Real.sqrt (V/Vhat) := by
  rw [Real.sqrt_div hV.le Vhat]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hV), ne_of_gt (Real.sqrt_pos.2 hVhat)]

/-- Finite-design Chebyshev inequality (Appendix A.6--A.7, pp. 1942--1943):
Pr(|X-E[X]|>δ) ≤ Var(X)/δ², for every δ>0. -/
theorem finite_chebyshev (P : Design Ω) (X : Ω → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    probability P (fun z => δ < |X z-expectation P X|) ≤ variance P X / δ^2 := by
  classical
  rw [variance_centered]
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).2
  rw [probability, sum_mul]
  apply sum_le_sum
  intro z _
  by_cases hz : δ < |X z-expectation P X|
  · simp only [hz, if_true]
    apply mul_le_mul_of_nonneg_left _ (P.positive z).le
    nlinarith [sq_abs (X z-expectation P X), abs_nonneg (X z-expectation P X)]
  · simp only [hz, if_false, zero_mul]
    exact mul_nonneg (P.positive z).le (sq_nonneg _)

/-- Under conservativeness in expectation, the lower-tail event is contained
in a centered Chebyshev event (P013-T2 finite lemma (iii), p. 1943 correction). -/
theorem conservative_lower_tail (P : Design Ω) (W : Ω → ℝ) (v δ : ℝ)
    (hv : v ≤ expectation P W) (hδ : 0 < δ) :
    probability P (fun z => W z < v-δ) ≤ variance P W / δ^2 := by
  apply le_trans _ (finite_chebyshev P W δ hδ)
  unfold probability
  apply sum_le_sum
  intro z _
  by_cases hz : W z < v-δ
  · have hx : δ < |W z-expectation P W| := by
      have hneg : W z-expectation P W ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      linarith
    simp [hz,hx]
  · simp only [hz, if_false]
    split_ifs <;> linarith [(P.positive z).le]

/-- The finite one-sided inequality of the corrected Appendix A.7:
Pr(W<(1-ε)v) ≤ Var(W)/(ε²v²) (P013-T8(b), p. 1943). -/
theorem conservative_relative_lower_tail (P : Design Ω) (W : Ω → ℝ) (v ε : ℝ)
    (hv : 0 < v) (he : 0 < ε) (hcon : v ≤ expectation P W) :
    probability P (fun z => W z < (1-ε)*v) ≤ variance P W / (ε^2*v^2) := by
  have h := conservative_lower_tail P W v (ε*v) hcon (mul_pos he hv)
  convert h using 1 <;> ring

/-- The positive-joint lower bound (R) of corrected Proposition 6.2.
Only the joints actually used by (11), and only distinct units, are bounded. -/
def JointLowerBound (S : ExperimentSequence) (b : ℝ) : Prop :=
  ∀ n i j, i ≠ j →
    (jointPi (seqPopulation S n) i j (S.treated n) (S.treated n) = 0 ∨
      b ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.treated n)) ∧
    (jointPi (seqPopulation S n) i j (S.control n) (S.control n) = 0 ∨
      b ≤ jointPi (seqPopulation S n) i j (S.control n) (S.control n)) ∧
    (jointPi (seqPopulation S n) i j (S.treated n) (S.control n) = 0 ∨
      b ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.control n))

/-- The set of positive distinct-unit joints used by expression (11) is
nonempty, the natural domain of the minimum b_N in T2(R') (corrected
Appendix A.7, p. 1943). It can be empty at some small population sizes. -/
def PositiveJointDomain (S : ExperimentSequence) (n : ℕ) : Prop :=
  ∃ i j : Fin (n+1), i ≠ j ∧
    (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.treated n) ∨
     0 < jointPi (seqPopulation S n) i j (S.control n) (S.control n) ∨
     0 < jointPi (seqPopulation S n) i j (S.treated n) (S.control n))

/-- "b_N ... the smallest positive value" among the three distinct-unit
joints used by expression (11) (P013-T2(R'), corrected Appendix A.7).
Attainment is stated along with the lower-bound property; no unattained
positive lower envelope is substituted for the printed minimum. -/
def IsMinimumPositiveJoint (S : ExperimentSequence) (n : ℕ) (b : ℝ) : Prop :=
  0 < b ∧
  (∃ i j : Fin (n+1), i ≠ j ∧
    (b = jointPi (seqPopulation S n) i j (S.treated n) (S.treated n) ∨
     b = jointPi (seqPopulation S n) i j (S.control n) (S.control n) ∨
     b = jointPi (seqPopulation S n) i j (S.treated n) (S.control n))) ∧
  (∀ i j : Fin (n+1), i ≠ j →
    (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.treated n) →
      b ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.treated n)) ∧
    (0 < jointPi (seqPopulation S n) i j (S.control n) (S.control n) →
      b ≤ jointPi (seqPopulation S n) i j (S.control n) (S.control n)) ∧
    (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.control n) →
      b ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.control n)))


/-- ε_N=N⁻², q_N=1/2-ε_N, t_N=1-2ε_N in the explicit paired
counterexample P013-T1 (P013-E001). -/
def pairEpsilon (N : ℕ) : ℝ := 1/(N : ℝ)^2
/-- "t_N = 1-2ε_N", the probability that a pair is split (P013-T1). -/
def pairSplitProbability (N : ℕ) : ℝ := 1-2*pairEpsilon N

/-- The four within-pair assignment probabilities (00),(01),(10),(11) are
ε,q,q,ε, at even population size N≥4 (P013-T1). -/
def pairAtomDesign (N : ℕ) (hN : 4 ≤ N) : Design (Fin 4) where
  weight := ![pairEpsilon N, 1/2-pairEpsilon N, 1/2-pairEpsilon N, pairEpsilon N]
  positive := by
    have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
    have he : 0 < pairEpsilon N := by unfold pairEpsilon; positivity
    have hel : pairEpsilon N < 1/2 := by
      unfold pairEpsilon
      apply (div_lt_iff₀ (by nlinarith : 0 < (N : ℝ)^2)).2
      nlinarith
    intro a
    fin_cases a <;> simp <;> linarith
  total := by
    simp [Fin.sum_univ_succ]
    ring

/-- Unit i belongs to pair floor(i/2), with first/second unit determined
by i mod 2; this relabels the paper's (2r-1,2r) using zero-based Fin (P013-T1). -/
def pairIndex (r : ℕ) (i : Fin (2*r)) : Fin r := ⟨i.val/2, by omega⟩

/-- Own binary assignment from a four-state pair atom, with atoms indexed
00,01,10,11 (P013-T1). -/
def pairExposure (a : Fin 4) (second : Bool) : Fin 2 :=
  if second then (if a.val % 2 = 0 then 0 else 1) else (if a.val < 2 then 0 else 1)

/-- Full known design is the product of r independent pair randomizations,
at population size N=2r, r≥2 (P013-T1). -/
def pairedDesign (r : ℕ) (hr : 2 ≤ r) : Design (Fin r → Fin 4) :=
  replicateDesign (pairAtomDesign (2*r) (by omega)) r

/-- P013-T1 potential outcomes: +1 for the first unit of every pair and
-1 for the second, at both exposures. Existing unit outcomes never change. -/
def pairedPopulation (r : ℕ) (hr : 2 ≤ r) : Population (pairedDesign r hr) (2*r) 2 where
  exposure z i := pairExposure (z (pairIndex r i)) (decide (i.val % 2 = 1))
  outcome i _ := if i.val % 2 = 0 then 1 else -1

/-- Every marginal in the arbitrary-size paired counterexample equals 1/2.  Supporting finite lemma for the T1 counterexample to Proposition 6.2, p. 1926; P013-E001. -/
theorem paired_pi (r : ℕ) (hr : 2 ≤ r) (i : Fin (2*r)) (d : Fin 2) :
    pi (pairedPopulation r hr) i d = 1/2 := by
  change expectation (replicateDesign (pairAtomDesign (2*r) (by omega)) r)
    (fun zs => if pairExposure (zs (pairIndex r i)) (decide (i.val % 2 = 1)) = d then 1 else 0) = _
  rw [replicate_marginal (pairAtomDesign (2*r) (by omega)) r (pairIndex r i)
    (fun x : Fin 4 => if pairExposure x (decide (i.val % 2 = 1)) = d then 1 else 0)]
  by_cases hi : i.val % 2 = 1 <;> fin_cases d <;>
    norm_num [expectation,pairAtomDesign,pairExposure,hi,Fin.sum_univ_succ] <;> ring

/-- The arbitrary-size paired witness has precisely the claimed within-pair
and between-pair joint exposure probabilities (T1(a)).  Supporting finite lemma for the T1 counterexample to Proposition 6.2, p. 1926; P013-E001. -/
theorem paired_joint (r : ℕ) (hr : 2 ≤ r) (i j : Fin (2*r)) (d e : Fin 2) (hne : i ≠ j) :
    jointPi (pairedPopulation r hr) i j d e =
      if pairIndex r i = pairIndex r j then
        (if d=e then pairEpsilon (2*r) else 1/2-pairEpsilon (2*r)) else 1/4 := by
  classical
  let P := pairAtomDesign (2*r) (by omega : 4 ≤ 2*r)
  let gi : Fin 4 → ℝ := fun x => if pairExposure x (decide (i.val % 2 = 1)) = d then 1 else 0
  let gj : Fin 4 → ℝ := fun x => if pairExposure x (decide (j.val % 2 = 1)) = e then 1 else 0
  have hei : expectation P gi = 1/2 := by
    have h := replicate_marginal P r (pairIndex r i) gi
    rw [← h]
    exact paired_pi r hr i d
  have hej : expectation P gj = 1/2 := by
    have h := replicate_marginal P r (pairIndex r j) gj
    rw [← h]
    exact paired_pi r hr j e
  change expectation (replicateDesign P r)
    (fun zs => gi (zs (pairIndex r i)) * gj (zs (pairIndex r j))) = _
  by_cases hk : pairIndex r i = pairIndex r j
  · simp only [hk,if_true]
    rw [replicate_marginal P r (pairIndex r j) (fun x => gi x * gj x)]
    have hquot : i.val/2 = j.val/2 := congrArg Fin.val hk
    have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
    by_cases hi : i.val % 2 = 1
    · have hj : j.val % 2 ≠ 1 := by omega
      fin_cases d <;> fin_cases e <;>
        norm_num [P,gi,gj,expectation,pairAtomDesign,pairExposure,hi,hj,Fin.sum_univ_succ]
    · have hj : j.val % 2 = 1 := by omega
      fin_cases d <;> fin_cases e <;>
        norm_num [P,gi,gj,expectation,pairAtomDesign,pairExposure,hi,hj,Fin.sum_univ_succ]
  · rw [if_neg hk,replicate_pair_marginal P r _ _ hk gi gj,hei,hej]
    norm_num

/-- Exactly two units use each paired randomization coordinate, so every
row of the genuine pair graph has sum two (T1(a), Condition 5).  Supporting finite lemma for Condition 5 of the T1 counterexample, pp. 1925--1926; P013-E001. -/
theorem paired_row_bound (r : ℕ) (hr : 2 ≤ r) :
    RowBound (fun i j : Fin (2*r) => decide (pairIndex r i = pairIndex r j)) 2 := by
  classical
  intro i
  let j0 : Fin (2*r) := ⟨2*(i.val/2), by omega⟩
  let j1 : Fin (2*r) := ⟨2*(i.val/2)+1, by omega⟩
  have hne : j0 ≠ j1 := by simp only [ne_eq,Fin.ext_iff]; dsimp [j0,j1]; omega
  have hindex : ∀ j : Fin (2*r), pairIndex r i = pairIndex r j ↔ j=j0 ∨ j=j1 := by
    intro j
    simp only [pairIndex,Fin.ext_iff]
    dsimp [j0,j1]
    omega
  have hf : univ.filter (fun j : Fin (2*r) => pairIndex r i = pairIndex r j) = {j0,j1} := by
    ext j
    simp [hindex]
  simp only [decide_eq_true_eq]
  rw [sum_boole,hf]
  simp [hne]

/-- Pair point-estimator score T_r=4(Z_a-Z_b) (P013-T1 finite lemmas). -/
def pairScore (a : Fin 4) : ℝ :=
  4*((pairExposure a false).val-(pairExposure a true).val : ℤ)

/-- The paired reduction of the printed (11): R=2/ε_N for an unsplit pair,
and R=16-4/t_N for a split pair (P013-T1(b)). -/
def pairVarianceScore (N : ℕ) (a : Fin 4) : ℝ :=
  if pairExposure a false = pairExposure a true then 2/pairEpsilon N
  else 16-4/pairSplitProbability N

/-- Every pair is split, the event A_N of P013-T1(c). -/
def allPairsSplit (r : ℕ) (z : Fin r → Fin 4) : Prop :=
  ∀ a, pairExposure (z a) false ≠ pairExposure (z a) true

/-- Exact per-pair score moments, using the four explicit weighted
assignments rather than an asymptotic argument (P013-T1 finite lemmas). -/
theorem pair_score_moments (N : ℕ) (hN : 4 ≤ N) :
    expectation (pairAtomDesign N hN) pairScore = 0 ∧
    variance (pairAtomDesign N hN) pairScore = 16*pairSplitProbability N := by
  norm_num [expectation, variance, covariance, pairAtomDesign, pairScore,
    pairExposure, pairSplitProbability, Fin.sum_univ_succ]
  ring

/-- Exact per-pair variance-estimator moments, including the inverse
joint-probability term missed in Appendix A.7 (P013-T1(b,d)). -/
theorem pair_variance_score_moments (N : ℕ) (hN : 4 ≤ N) :
    expectation (pairAtomDesign N hN) (pairVarianceScore N) = 16*pairSplitProbability N ∧
    expectation (pairAtomDesign N hN) (fun a => pairVarianceScore N a ^ 2) =
      8/pairEpsilon N + pairSplitProbability N * (16-4/pairSplitProbability N)^2 := by
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have he : pairEpsilon N ≠ 0 := by unfold pairEpsilon; positivity
  have ht : pairSplitProbability N ≠ 0 := by
    unfold pairSplitProbability pairEpsilon
    have hsq : 0 < (N : ℝ)^2 := by nlinarith
    intro hz
    have hh : (N : ℝ)^2 = 2 := by
      field_simp at hz
      nlinarith
    nlinarith
  norm_num [expectation, pairAtomDesign, pairVarianceScore, pairExposure, Fin.sum_univ_succ]
  constructor
  · field_simp [he, ht]
    unfold pairSplitProbability
    ring
  · field_simp [he, ht]
    unfold pairSplitProbability
    ring

/-- Full finite hypotheses of the T1 witness: all marginal probabilities
are 1/2, joints are ε or q within pairs and 1/4 between pairs, the genuine
and printed graph conditions hold with degree 2, and outcomes have modulus 1. -/
theorem paired_finite_hypotheses (r : ℕ) (hr : 2 ≤ r) :
    (∀ i d, pi (pairedPopulation r hr) i d = 1/2 ∧
      |(pairedPopulation r hr).outcome i d| = 1) ∧
    (∀ i j d e, i ≠ j → jointPi (pairedPopulation r hr) i j d e =
      if pairIndex r i = pairIndex r j then
        (if d=e then pairEpsilon (2*r) else 1/2-pairEpsilon (2*r)) else 1/4) ∧
    (let h := fun i j : Fin (2*r) => decide (pairIndex r i = pairIndex r j);
      GenuineDependency (pairedDesign r hr) (pairedPopulation r hr).exposure h ∧
      PrintedDependency (pairedDesign r hr) (pairedPopulation r hr).exposure h ∧
      RowBound h 2) := by
  constructor
  · intro i d
    refine ⟨paired_pi r hr i d,?_⟩
    change |if i.val % 2 = 0 then (1:ℝ) else -1| = 1
    split_ifs <;> norm_num
  · constructor
    · exact paired_joint r hr
    · dsimp only
      refine ⟨coordinate_population_genuine_dependency
        (pairAtomDesign (2*r) (by omega)) r (pairIndex r)
        (fun i x => pairExposure x (decide (i.val % 2 = 1))),?_,paired_row_bound r hr⟩
      intro A B hdis hno a b
      have hA : A = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hj : i ∉ B := (disjoint_left.mp hdis) hi
        exact hno ⟨i,i,by simp,Or.inl ⟨hi,hj⟩⟩
      have hB : B = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hj : i ∉ A := (disjoint_right.mp hdis) hi
        exact hno ⟨i,i,by simp,Or.inr (Or.inr (Or.inl ⟨hj,hi⟩))⟩
      simp [hA,hB,probability,(pairedDesign r hr).total]


/-- Block endpoints n_0=0 and n_r=2^(2^r) for r≥1 in the fixed nested
population of counterexample P013-T7 (P013-E007). -/
def blockEnd (r : ℕ) : ℕ := if r=0 then 0 else 2^(2^r)

/-- The block of positive unit i is the least r≥1 with i≤n_r (P013-T7).
The endpoints are unbounded, so this set is nonempty for every unit. -/
def blockIndex (i : ℕ) : ℕ := sInf {r : ℕ | 1 ≤ r ∧ i ≤ blockEnd r}

/-- The fixed outcomes of P013-T7: odd blocks have (1,1), even blocks
alternate (2,0),(0,2), starting with (2,0); exposure labels are (1,0).
Unit indices here are positive integers. -/
def blockOutcome (i : ℕ) (d : Fin 2) : ℝ :=
  if blockIndex i % 2 = 1 then 1 else
    if (i-blockEnd (blockIndex i-1)-1) % 2 = 0 then (if d=1 then 2 else 0)
    else (if d=1 then 0 else 2)

/-- Independent fair Bernoulli assignments for the first N units, each
complete vector of probability 2^(-N) (P013-T7(a)). -/
def blockDesign (N : ℕ) : Design (Fin N → Fin 2) := replicateDesign sharedDesign N

/-- Own-assignment exposure and the fixed block potential outcomes
(P013-T7(a)); Conditions 1--2 hold by the population construction. -/
def blockPopulation (N : ℕ) : Population (blockDesign N) N 2 where
  exposure z i := z i
  outcome i d := blockOutcome (i.val+1) d

/-- B_N, the units in even blocks among the first N, and b_N=|B_N|
(P013-T7(b)). -/
def blockBUnits (N : ℕ) : Finset (Fin N) := univ.filter (fun i => blockIndex (i.val+1) % 2 = 0)

/-- s_i is +1 for an even-block (2,0) unit, -1 for a (0,2) unit
(P013-T7(b)). -/
def blockSign (i : ℕ) : ℝ := if (i-blockEnd (blockIndex i-1)-1) % 2 = 0 then 1 else -1

/-- R_i=2Z_i-1, a fair Rademacher variable in the T7 witness. -/
def rademacher (z : Fin 2) : ℝ := 2*(z.val : ℝ)-1

/-- The per-unit HT contrast identity used to obtain true variance 4/N:
the two outcomes sum to 2, so the error is 2R_i (P013-T7 finite lemma). -/
theorem block_unit_score_identity (a b : ℝ) (hsum : a+b=2) (z : Fin 2) :
    (if z=1 then 2*a else 0) - (if z=0 then 2*b else 0) =
      (a-b) + 2*rademacher z := by
  fin_cases z <;> norm_num [rademacher] <;> linarith

/-- Exact fair Rademacher moments underlying the block witness (P013-T7). -/
theorem rademacher_moments : expectation sharedDesign rademacher = 0 ∧
    variance sharedDesign rademacher = 1 := by
  norm_num [expectation, variance, covariance, sharedDesign, rademacher, Fin.sum_univ_succ]

/-- The squared observed outcomes in an even block are 2±2R_i; odd-block
outcomes have square 1 (P013-T7 finite lemmas). -/
theorem block_unit_square_identities (z : Fin 2) :
    (if z=1 then (2 : ℝ) else 0)^2 = 2+2*rademacher z ∧
    (if z=1 then (0 : ℝ) else 2)^2 = 2-2*rademacher z ∧ (1 : ℝ)^2 = 1 := by
  fin_cases z <;> norm_num [rademacher]


/-- Convergence in distribution to an arbitrary probability law via its CDF
at continuity points; used to assert that T7 has no single studentized limit. -/
def TendsDistribution {L : ℕ → Type*} [∀ n : ℕ, Fintype (L n)]
    (P : ∀ n : ℕ, Design (L n)) (X : ∀ n : ℕ, L n → ℝ) (μ : MeasureTheory.Measure ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt (fun t => ProbabilityTheory.cdf μ t) x →
    Tendsto (fun n : ℕ => probability (P n) (fun z => X n z ≤ x)) atTop (𝓝 (ProbabilityTheory.cdf μ x))


/-- "I_k = [I(f(z,θ_i)=d_k)]", the exact N×|Ω| exposure-indicator
matrix over every supported assignment (pp. 1916--1917). -/
def designIndicators {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) : Matrix (Fin N) Ω ℝ := fun i z => indicator F.exposure i d z

/-- "P = diag(p_z)", the diagonal matrix of exact supported assignment
probabilities (p. 1917). -/
def designProbabilityMatrix (P : Design Ω) : Matrix Ω Ω ℝ :=
  by classical exact Matrix.diagonal P.weight

/-- The (i,j) entry of I_k P I_l' is π_ij(d_k,d_l), including the
same-exposure marginal diagonal and the distinct-exposure zero diagonal
(Proposition 3.1 setup, p. 1917). -/
theorem design_matrix_entry {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (i j : Fin N) :
    (designIndicators F d * designProbabilityMatrix P * (designIndicators F e).transpose) i j =
      jointPi F i j d e := by
  classical
  rw [Matrix.mul_apply]
  simp only [designProbabilityMatrix,Matrix.mul_diagonal,
    Matrix.transpose_apply,designIndicators,jointPi,expectation]
  apply sum_congr rfl
  intro z _
  ring

/-- "Î_k", the N×R replicate indicator matrix (p. 1917); its (i,r)
entry is I(f(z_r,θ_i)=d_k). -/
def replicateIndicators {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (R : ℕ) (zs : Fin R → Ω) : Matrix (Fin N) (Fin R) ℝ :=
  fun i r => indicator F.exposure i d (zs r)

/-- The (i,j) replicate joint-exposure count, for same or different
exposures (Proposition 3.1, p. 1917). -/
def replicateJointCount {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (R : ℕ) (zs : Fin R → Ω) (i j : Fin N) :=
  ∑ r, indicator F.exposure i d (zs r) * indicator F.exposure j e (zs r)

/-- For every fixed R, the entry of Î_k Î_l' is exactly the count of
replicate assignments giving exposures k,l to units i,j (P013-T20 finite lemma). -/
theorem replicate_matrix_entry {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (R : ℕ) (zs : Fin R → Ω) (i j : Fin N) :
    (replicateIndicators F d R zs * (replicateIndicators F e R zs).transpose) i j =
      replicateJointCount F d e R zs i j := by
  rfl

/-- At fixed R independent replicates, a joint-exposure count has expectation
R π_ij(d_k,d_l), including same-exposure diagonal marginals (P013-T20 finite lemma). -/
theorem replicate_count_expectation {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (R : ℕ) (i j : Fin N) :
    expectation (replicateDesign P R) (fun zs => replicateJointCount F d e R zs i j) =
      (R : ℝ)*jointPi F i j d e := by
  change expectation (replicateDesign P R) (fun zs => ∑ r, _) = _
  rw [expectation_sum]
  have hm : ∀ r : Fin R, expectation (replicateDesign P R)
      (fun zs => indicator F.exposure i d (zs r)*indicator F.exposure j e (zs r)) =
      jointPi F i j d e := fun r => replicate_marginal P R r
        (fun z => indicator F.exposure i d z*indicator F.exposure j e z)
  simp_rw [hm]
  simp

/-- Unsmooth replicate cross- and same-exposure matrices divided by R are
unbiased entry by entry, for R≥1 (P013-T20 finite lemma, p. 1917). -/
theorem replicate_matrix_unbiased {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (R : ℕ) (hR : 1 ≤ R) (i j : Fin N) :
    expectation (replicateDesign P R) (fun zs => replicateJointCount F d e R zs i j/(R : ℝ)) =
      jointPi F i j d e := by
  simp only [div_eq_mul_inv, expectation_mul_const, replicate_count_expectation]
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast (by omega : R ≠ 0)
  field_simp

/-- The measure associated to the exact finite weights p_z (pp. 1914--1915),
used only to connect finite design probabilities to iid sampling and the SLLN. -/
def designMeasure [MeasurableSpace Ω] (P : Design Ω) : MeasureTheory.Measure Ω :=
  ∑ z, ENNReal.ofReal (P.weight z) • MeasureTheory.Measure.dirac z

/-- Integration under the finite randomization measure equals the paper's
weighted design expectation (Proposition 3.1 setup, pp. 1914--1917). -/
theorem integral_designMeasure [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : Design Ω) (g : Ω → ℝ) :
    (∫ z, g z ∂designMeasure P) = expectation P g := by
  classical
  have hint : ∀ z ∈ (univ : Finset Ω), MeasureTheory.Integrable g
      (ENNReal.ofReal (P.weight z) • MeasureTheory.Measure.dirac z) := by
    intro z _
    exact (MeasureTheory.integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  unfold designMeasure
  rw [MeasureTheory.integral_finsetSum_measure hint]
  unfold expectation
  apply sum_congr rfl
  intro z _
  rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
    ENNReal.toReal_ofReal (P.positive z).le]
  rfl

/-- Entrywise strong law for the joint-exposure indicators of independent
replicate assignment vectors (Proposition 3.1; Appendix A.1, p. 1938). -/
theorem replicate_joint_strong_law {A : Type*} [MeasurableSpace A]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ : MeasureTheory.Measure A)
    [MeasureTheory.IsProbabilityMeasure μ] {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (i j : Fin N) (Z : ℕ → A → Ω)
    (hm : ∀ r, Measurable (Z r)) (hi : ProbabilityTheory.iIndepFun Z μ)
    (hlaw : ∀ r, MeasureTheory.Measure.map (Z r) μ = designMeasure P) :
    ∀ᵐ a ∂μ, Tendsto (fun R : ℕ => (∑ r ∈ range R,
      indicator F.exposure i d (Z r a) * indicator F.exposure j e (Z r a)) / (R : ℝ))
        atTop (𝓝 (jointPi F i j d e)) := by
  let g : Ω → ℝ := fun z => indicator F.exposure i d z*indicator F.exposure j e z
  have hg : Measurable g := measurable_of_finite g
  have hb : ∀ z, ‖g z‖ ≤ 1 := by
    intro z
    dsimp [g]
    unfold indicator
    split_ifs <;> norm_num
  have hint : MeasureTheory.Integrable (fun a => g (Z 0 a)) μ :=
    MeasureTheory.Integrable.of_bound (hg.comp (hm 0)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun a => hb (Z 0 a))
  have hind : Pairwise (fun r s : ℕ => ProbabilityTheory.IndepFun
      (fun a => g (Z r a)) (fun a => g (Z s a)) μ) := by
    intro r s hrs
    exact (hi.indepFun hrs).comp hg hg
  have hid : ∀ r, ProbabilityTheory.IdentDistrib (fun a => g (Z r a))
      (fun a => g (Z 0 a)) μ μ := by
    intro r
    have hz : ProbabilityTheory.IdentDistrib (Z r) (Z 0) μ μ :=
      ⟨(hm r).aemeasurable,(hm 0).aemeasurable,(hlaw r).trans (hlaw 0).symm⟩
    exact hz.comp hg
  have hmean : (∫ a, g (Z 0 a) ∂μ) = jointPi F i j d e := by
    rw [← MeasureTheory.integral_map_of_stronglyMeasurable (hm 0) hg.stronglyMeasurable,
      hlaw 0, integral_designMeasure]
    rfl
  simpa only [hmean] using
    ProbabilityTheory.strong_law_ae_real (fun r a => g (Z r a)) hint hind hid

/-- Adding a fixed identity-matrix entry and replacing R by R+1 preserves
a limit of sample averages (Proposition 3.1 smoothing, p. 1917). -/
theorem smoothed_average_limit (f : ℕ → ℝ) (q a : ℝ)
    (h : Tendsto (fun R : ℕ => f R/(R : ℝ)) atTop (𝓝 q)) :
    Tendsto (fun R : ℕ => (f R+a)/(R+1 : ℝ)) atTop (𝓝 q) := by
  have hinv : Tendsto (fun R : ℕ => 1/(R+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : Tendsto (fun R : ℕ => 1-1/(R+1 : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
  have hmain := (h.mul hratio).add (hinv.const_mul a)
  simp only [mul_one, mul_zero, add_zero] at hmain
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast (by omega : R ≠ 0)
  have hR1 : (R+1 : ℝ) ≠ 0 := by positivity
  field_simp [hR0,hR1] <;> ring

/-- Proposition 3.1: for an infinite sequence of independent replicate
assignments, each with exactly the design law, every entry of the two printed
matrices converges almost surely to the exact joint exposure probability
(p. 1917; Appendix A.1, p. 1938). N is fixed. -/
theorem simulation_matrices_almost_sure {A : Type*} [MeasurableSpace A]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ : MeasureTheory.Measure A)
    [MeasureTheory.IsProbabilityMeasure μ] {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hne : d ≠ e) (Z : ℕ → A → Ω)
    (hm : ∀ r, Measurable (Z r)) (hi : ProbabilityTheory.iIndepFun Z μ)
    (hlaw : ∀ r, MeasureTheory.Measure.map (Z r) μ = designMeasure P) :
    ∀ᵐ a ∂μ, ∀ i j,
      Tendsto (fun R : ℕ => ((∑ r ∈ range R,
        indicator F.exposure i d (Z r a) * indicator F.exposure j d (Z r a)) +
          (if i=j then 1 else 0)) / (R+1 : ℝ)) atTop (𝓝 (jointPi F i j d d)) ∧
      Tendsto (fun R : ℕ => (∑ r ∈ range R,
        indicator F.exposure i d (Z r a) * indicator F.exposure j e (Z r a)) / (R : ℝ))
          atTop (𝓝 (jointPi F i j d e)) := by
  rw [MeasureTheory.ae_all_iff]
  intro i
  rw [MeasureTheory.ae_all_iff]
  intro j
  filter_upwards [replicate_joint_strong_law μ F d d i j Z hm hi hlaw,
    replicate_joint_strong_law μ F d e i j Z hm hi hlaw] with a hd he
  exact ⟨smoothed_average_limit _ _ (if i=j then 1 else 0) hd,he⟩


/-- Every event has nonnegative randomization probability.
Supporting finite-design lemma for corrected Appendix A.7, p. 1943 (P013-T2,T8). -/
theorem probability_nonneg (P : Design Ω) (A : Ω → Prop) : 0 ≤ probability P A := by
  classical
  unfold probability
  apply sum_nonneg
  intro z _
  split_ifs <;> linarith [(P.positive z).le]

/-- An event contained in another event has no greater randomization probability.
Supporting finite-design lemma for corrected Appendix A.7, p. 1943 (P013-T2,T8). -/
theorem probability_mono (P : Design Ω) (A B : Ω → Prop) (h : ∀ z, A z → B z) :
    probability P A ≤ probability P B := by
  classical
  unfold probability
  apply sum_le_sum
  intro z _
  by_cases ha : A z
  · simp [ha, h z ha]
  · simp only [ha, ite_false]
    split_ifs <;> linarith [(P.positive z).le]

/-- The probability of A∩B is at least Pr(A)-Pr(Bᶜ); no independence is
needed in the corrected Appendix A.7 coverage step (P013-T2, T8). -/
theorem probability_inter_lower (P : Design Ω) (A B : Ω → Prop) :
    probability P A-probability P (fun z => ¬ B z) ≤ probability P (fun z => A z ∧ B z) := by
  classical
  unfold probability
  rw [← sum_sub_distrib]
  apply sum_le_sum
  intro z _
  by_cases ha : A z <;> by_cases hb : B z <;> simp [ha,hb,(P.positive z).le]

/-- On a lower-bound event for estimated variance, a narrower true-variance
standardized interval implies actual Wald coverage (P013-T2(iv), T8 finite lemma). -/
theorem wald_event_inclusion (x target V Vhat ε z : ℝ) (hV : 0 < V)
    (hε : 0 < ε) (hε1 : ε < 1) (hz : 0 ≤ z)
    (hhat : (1-ε)*V ≤ Vhat) (hx : |(x-target)/Real.sqrt V| ≤ z*Real.sqrt (1-ε)) :
    0 ≤ Vhat ∧ |x-target| ≤ z*Real.sqrt Vhat := by
  have hp : 0 ≤ 1-ε := by linarith
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hhat0 : 0 ≤ Vhat := le_trans (mul_nonneg hp hV.le) hhat
  have habs : |(x-target)/Real.sqrt V| = |x-target|/Real.sqrt V := by
    rw [abs_div, abs_of_pos hs]
  rw [habs] at hx
  have hx' := (div_le_iff₀ hs).mp hx
  have hb : Real.sqrt (1-ε)*Real.sqrt V ≤ Real.sqrt Vhat := by
    rw [← Real.sqrt_mul hp V]
    exact Real.sqrt_le_sqrt hhat
  refine ⟨hhat0, hx'.trans ?_⟩
  have hm := mul_le_mul_of_nonneg_left hb hz
  nlinarith

/-- The exact probability lower bound behind corrected Wald coverage:
Pr(coverage) ≥ Pr(|Z|≤z√(1-ε))-Pr(Vhat<(1-ε)V), for 0<ε<1
(P013-T2(iv), P013-T8(c), corrected Appendix A.7). -/
theorem finite_wald_coverage_bound (P : Design Ω) (X Vhat : Ω → ℝ)
    (target V ε z : ℝ) (hV : 0 < V) (hε : 0 < ε) (hε1 : ε < 1) (hz : 0 ≤ z) :
    probability P (fun a => |(X a-target)/Real.sqrt V| ≤ z*Real.sqrt (1-ε)) -
      probability P (fun a => Vhat a < (1-ε)*V) ≤
    probability P (fun a => 0 ≤ Vhat a ∧ |X a-target| ≤ z*Real.sqrt (Vhat a)) := by
  have h := probability_inter_lower P
    (fun a => |(X a-target)/Real.sqrt V| ≤ z*Real.sqrt (1-ε))
    (fun a => (1-ε)*V ≤ Vhat a)
  simp only [not_le] at h
  refine h.trans (probability_mono P _ _ ?_)
  intro a ha
  exact wald_event_inclusion (X a) target V (Vhat a) ε z hV hε hε1 hz ha.2 ha.1

/-- Every marginal exposure probability lies between zero and one.
Supporting finite lemma for Appendix A.6, p. 1942 (P013-T19). -/
theorem pi_bounds {N K : ℕ} {P : Design Ω} (F : Population P N K) (i : Fin N) (d : Fin K) :
    0 ≤ pi F i d ∧ pi F i d ≤ 1 := by
  constructor
  · exact expectation_nonneg P fun z => indicator_nonneg _ _ _ _
  · have hh := expectation_mono P (X := indicator F.exposure i d) (Y := fun _ => 1) (by
      intro z; unfold indicator; split <;> norm_num)
    simpa [pi, expectation_const] using hh

/-- Every joint exposure probability lies between zero and one.
Supporting finite lemma for Appendix A.6, p. 1942 (P013-T19). -/
theorem jointPi_bounds {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (i j : Fin N) (d e : Fin K) : 0 ≤ jointPi F i j d e ∧ jointPi F i j d e ≤ 1 := by
  refine ⟨jointPi_nonneg F i j d e,?_⟩
  have hh := expectation_mono P
    (X := fun z => indicator F.exposure i d z * indicator F.exposure j e z)
    (Y := fun _ => 1) (by intro z; unfold indicator; split <;> split <;> norm_num)
  simpa [jointPi, expectation_const] using hh

/-- The absolute difference between a joint exposure probability and the product of its marginals is at most one.
Supporting finite lemma for Appendix A.6, p. 1942 (P013-T19). -/
theorem joint_covariance_abs_le_one {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (i j : Fin N) (d e : Fin K) : |jointPi F i j d e-pi F i d*pi F j e| ≤ 1 := by
  have hi := pi_bounds F i d
  have hj := pi_bounds F j e
  have hp := jointPi_bounds F i j d e
  have hn := mul_nonneg hi.1 hj.1
  have hu : pi F i d*pi F j e ≤ 1 := by nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Dividing a random variable by a fixed real scale divides its variance by the scale squared.
Supporting finite lemma for Appendix A.6, p. 1942 (P013-T19). -/
theorem variance_div (P : Design Ω) (X : Ω → ℝ) (c : ℝ) :
    variance P (fun z => X z/c) = variance P X/c^2 := by
  change covariance P (fun z => X z * c⁻¹) (fun z => X z * c⁻¹) = _
  rw [covariance_mul_const]
  unfold variance
  ring

/-- The exact finite variance bound used in Appendix A.6:
N² Var(μ̂_HT) ≤ c₃²N+c₃²Σg_ij, when |y_i(d)/π_i(d)|≤c₃ and zero
g entries imply pairwise independence (P013-T19, P013-T9(i), p. 1942).
The proof obtains the slightly stronger bound c₃²Σg_ij first. -/
theorem htMean_variance_bound {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (hN : 0 < N) (d : Fin K) (c3 : ℝ) (hc3 : 0 ≤ c3)
    (hy : ∀ i, |F.outcome i d/pi F i d| ≤ c3) (g : Fin N → Fin N → Bool)
    (hg : ∀ i j, g i j = false → PairIndependent F i j) :
    (N : ℝ)^2*variance P (htMean F d) ≤ c3^2*(N : ℝ) +
      c3^2*∑ i, ∑ j, (if g i j = true then 1 else 0 : ℝ) := by
  have htotal : variance P (htTotal F d) ≤ c3^2 *
      ∑ i, ∑ j, (if g i j = true then 1 else 0 : ℝ) := by
    rw [variance, ht_covariance_full, mul_sum]
    apply sum_le_sum
    intro i _
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    cases hx : g i j
    · rw [(hg i j hx) d d]
      simp [hx]
    · simp only [hx, ite_true, mul_one]
      calc
        _ ≤ |(jointPi F i j d d-pi F i d*pi F j d)*
            (F.outcome i d/pi F i d)*(F.outcome j d/pi F j d)| := le_abs_self _
        _ = |jointPi F i j d d-pi F i d*pi F j d| *
            |F.outcome i d/pi F i d| *|F.outcome j d/pi F j d| := by simp [abs_mul]
        _ ≤ 1*c3*c3 := by
          gcongr
          · exact joint_covariance_abs_le_one F i j d d
          · exact hy i
          · exact hy j
        _ = c3^2 := by ring
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hscale : (N : ℝ)^2*variance P (htMean F d) = variance P (htTotal F d) := by
    change (N : ℝ)^2*variance P (fun z => htTotal F d z/(N : ℝ)) = _
    rw [variance_div]
    field_simp
  rw [hscale]
  have hdiag : 0 ≤ c3^2*(N : ℝ) := by positivity
  linarith

/-- Chebyshev with the correct population centering μ(d), the fixed-N
probability inequality needed by Appendix A.6 (P013-T9(i), P013-T19). -/
theorem htMean_chebyshev {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hd : Positivity F d) (ε : ℝ) (he : 0 < ε) :
    probability P (fun z => ε < |htMean F d z-potentialMean F d|) ≤
      variance P (htMean F d)/ε^2 := by
  simpa [htMean_unbiased F d hd] using finite_chebyshev P (htMean F d) ε he

/-- A pair-count bound N C is o(N²) for a constant C: the asymptotic
counting implication used in corrected Condition 5 ⇒ Condition 4 (P013-T6(c)). -/
theorem linear_count_is_little_o (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ (n+1 : ℝ)*C) :
    Tendsto (fun n : ℕ => a n/(n+1 : ℝ)^2) atTop (𝓝 0) := by
  apply squeeze_zero (fun n : ℕ => div_nonneg (ha n).1 (sq_nonneg _))
    (g := fun n : ℕ => C*(1/(n+1 : ℝ)))
  · intro n
    have hn : (0 : ℝ) < n+1 := by positivity
    apply (div_le_iff₀ (sq_pos_of_pos hn)).2
    have heq : C*(1/(n+1 : ℝ))*(n+1 : ℝ)^2 = (n+1 : ℝ)*C := by
      field_simp <;> ring
    rw [heq]
    exact (ha n).2
  · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C


/-- The shared-exposure witness violates little-o Condition 4 along every
population size, since its normalized pair count is constantly 1 (P013-T5(c)). -/
theorem shared_condition4_failure :
    ¬ Tendsto (fun n : ℕ => ((n+1 : ℝ)^2)/((n+1 : ℝ)^2)) atTop (𝓝 0) := by
  have heq : (fun n : ℕ => ((n+1 : ℝ)^2)/((n+1 : ℝ)^2)) = (fun _ : ℕ => (1 : ℝ)) := by
    funext n
    have hn0 : (n+1 : ℝ) ≠ 0 := by positivity
    exact div_self (pow_ne_zero _ hn0)
  rw [heq]
  intro ht
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at he


/-- Chebyshev proves centered concentration whenever finite-design variances
tend to zero (corrected Appendix A.7, P013-T8(a), p. 1943). -/
theorem variance_concentration {L : ℕ → Type*} [∀ n, Fintype (L n)]
    (P : ∀ n, Design (L n)) (X : ∀ n, L n → ℝ)
    (hv : Tendsto (fun n : ℕ => variance (P n) (X n)) atTop (𝓝 0)) :
    ConvergesInProbability P (fun (n : ℕ) z => X n z-expectation (P n) (X n)) 0 := by
  intro ε he
  simp only [sub_zero]
  exact squeeze_zero (fun n : ℕ => probability_nonneg _ _)
    (fun n : ℕ => finite_chebyshev (P n) (X n) ε he)
    (by simpa using hv.div_const (ε^2))

/-- Generic finite-design consistency argument of Appendix A.6: bounded
HT summands and an o(N²) pair-dependence count imply consistent exposure
means, with no limiting-distribution assumption (P013-T9(i), P013-T19). -/
theorem bounded_htMean_consistency {L : ℕ → Type*} [∀ n, Fintype (L n)]
    (P : ∀ n, Design (L n)) (K : ℕ → ℕ) (F : ∀ n, Population (P n) (n+1) (K n))
    (d : ∀ n, Fin (K n)) (hd : ∀ n, Positivity (F n) (d n)) (c3 : ℝ) (hc3 : 0 ≤ c3)
    (hy : ∀ n i, |(F n).outcome i (d n)/pi (F n) i (d n)| ≤ c3)
    (g : ∀ n, Fin (n+1) → Fin (n+1) → Bool)
    (hg : ∀ n i j, g n i j = false → PairIndependent (F n) i j)
    (hcount : Tendsto (fun n : ℕ => (∑ i, ∑ j, (if g n i j = true then 1 else 0 : ℝ)) /
      (n+1 : ℝ)^2) atTop (𝓝 0)) :
    ConvergesInProbability P (fun (n : ℕ) z => htMean (F n) (d n) z-potentialMean (F n) (d n)) 0 := by
  let G := fun n : ℕ => ∑ i, ∑ j, (if g n i j = true then 1 else 0 : ℝ)
  let upper := fun n : ℕ => c3^2*(1/(n+1 : ℝ)+G n/(n+1 : ℝ)^2)
  have hup : Tendsto upper atTop (𝓝 0) := by
    simpa [upper,G] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).add hcount).const_mul (c3^2)
  have hbound : ∀ n, variance (P n) (htMean (F n) (d n)) ≤ upper n := by
    intro n
    have hb := htMean_variance_bound (F n) (by omega) (d n) c3 hc3 (hy n) (g n) (hg n)
    have hn : (0 : ℝ) < n+1 := by positivity
    have hb' : variance (P n) (htMean (F n) (d n))*(n+1 : ℝ)^2 ≤
        c3^2*(n+1 : ℝ)+c3^2*G n := by
      simpa [G, Nat.cast_add, Nat.cast_one, mul_comm] using hb
    have hdiv := (le_div_iff₀ (sq_pos_of_pos hn)).2 hb'
    have heq : (c3^2*(n+1 : ℝ)+c3^2*G n)/(n+1 : ℝ)^2 = upper n := by
      dsimp [upper]
      field_simp <;> ring
    rw [heq] at hdiv
    exact hdiv
  intro ε he
  simp only [sub_zero]
  apply squeeze_zero (fun n : ℕ => probability_nonneg _ _)
    (g := fun n : ℕ => upper n/ε^2)
  · intro n
    exact (htMean_chebyshev (F n) (d n) (hd n) ε he).trans
      (div_le_div_of_nonneg_right (hbound n) (sq_nonneg ε))
  · simpa using hup.div_const (ε^2)

/-- If v_N > 0 tends to c > 0, E[W_N] ≥ v_N at every N, and Var(W_N)
tends to zero, then Pr(W_N < (1-ε)v_N) tends to zero for every ε > 0.
In the variance-estimator application, v_N = N V_N and W_N = N Vhat_N.
P013-T8(b), corrected Appendix A.7, p. 1943. -/
theorem relative_lower_tail_tends_zero {L : ℕ → Type*} [∀ n : ℕ, Fintype (L n)]
    (P : ∀ n : ℕ, Design (L n)) (W : ∀ n : ℕ, L n → ℝ) (v : ℕ → ℝ)
    (hv : ∀ n, 0 < v n) (hc : ℝ) (hcpos : 0 < hc)
    (hvl : Tendsto v atTop (𝓝 hc))
    (hex : ∀ n, v n ≤ expectation (P n) (W n))
    (hvar : Tendsto (fun n => variance (P n) (W n)) atTop (𝓝 0))
    (ε : ℝ) (he : 0 < ε) :
    Tendsto (fun n : ℕ => probability (P n) (fun z => W n z < (1-ε)*v n))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => probability_nonneg _ _)
    (fun n => conservative_relative_lower_tail (P n) (W n) (v n) ε (hv n) he (hex n))
  have hden : Tendsto (fun n => ε^2*(v n)^2) atTop (𝓝 (ε^2*hc^2)) :=
    tendsto_const_nhds.mul (hvl.pow 2)
  have hden0 : ε^2*hc^2 ≠ 0 := ne_of_gt (by positivity)
  simpa only [Pi.div_def,zero_div] using hvar.div hden hden0

/-- Under Conditions 3 and 4, both comparison-exposure means are consistent
for their population means (Appendix A.6, p. 1942). -/
theorem both_means_consistent (S : ExperimentSequence) (hc3 : ComparisonBounded S) (hc4 : Condition4 S) :
    ConvergesInProbability (seqLaw S)
      (fun (n : ℕ) z => htMean (seqPopulation S n) (S.treated n) z-potentialMean (seqPopulation S n) (S.treated n)) 0 ∧
    ConvergesInProbability (seqLaw S)
      (fun (n : ℕ) z => htMean (seqPopulation S n) (S.control n) z-potentialMean (seqPopulation S n) (S.control n)) 0 := by
  obtain ⟨c1,c2,hc1,hc2,hb⟩ := hc3
  obtain ⟨g,hg,hcount⟩ := hc4
  have hT : ∀ n i, |(seqPopulation S n).outcome i (S.treated n) /
      pi (seqPopulation S n) i (S.treated n)| ≤ c1*c2 := by
    intro n i
    rw [div_eq_mul_inv, abs_mul]
    have hpi : |(pi (seqPopulation S n) i (S.treated n))⁻¹| ≤ c2 := by
      simpa [one_div] using (hb n i).2.2.1
    exact mul_le_mul (hb n i).1 hpi (abs_nonneg _) hc1
  have hC : ∀ n i, |(seqPopulation S n).outcome i (S.control n) /
      pi (seqPopulation S n) i (S.control n)| ≤ c1*c2 := by
    intro n i
    rw [div_eq_mul_inv, abs_mul]
    have hpi : |(pi (seqPopulation S n) i (S.control n))⁻¹| ≤ c2 := by
      simpa [one_div] using (hb n i).2.2.2
    exact mul_le_mul (hb n i).2.1 hpi (abs_nonneg _) hc1
  constructor
  · exact bounded_htMean_consistency (seqLaw S) _ (seqPopulation S) (S.treated)
      S.positiveTreated (c1*c2) (mul_nonneg hc1 hc2.le) hT g hg hcount
  · exact bounded_htMean_consistency (seqLaw S) _ (seqPopulation S) (S.control)
      S.positiveControl (c1*c2) (mul_nonneg hc1 hc2.le) hC g hg hcount

/-- The event |X-Y|>ε is contained in {|X|>ε/2}∪{|Y|>ε/2}; its
probability is bounded by the sum, without independence (Proposition 6.1). -/
theorem difference_probability_bound (P : Design Ω) (X Y : Ω → ℝ) (ε : ℝ) (he : 0 < ε) :
    probability P (fun z => ε < |X z-Y z|) ≤
      probability P (fun z => ε/2 < |X z|) + probability P (fun z => ε/2 < |Y z|) := by
  classical
  unfold probability
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro z _
  by_cases hx : ε/2 < |X z| <;> by_cases hy : ε/2 < |Y z|
  · simp only [hx,hy,ite_true]
    split_ifs <;> linarith [(P.positive z).le]
  · simp only [hx,hy,ite_true,ite_false,add_zero]
    split_ifs <;> linarith [(P.positive z).le]
  · simp only [hx,hy,ite_true,ite_false,zero_add]
    split_ifs <;> linarith [(P.positive z).le]
  · have hab : ¬ ε < |X z-Y z| := by
      have htri := abs_sub_le (X z) 0 (Y z)
      simp only [sub_zero, zero_sub, abs_neg] at htri
      push_neg at hx hy ⊢
      linarith
    simp [hx,hy,hab]

/-- Differences of sequences converging to zero in probability also
converge to zero, the final step of Proposition 6.1 (Appendix A.6). -/
theorem convergence_difference {L : ℕ → Type*} [∀ n, Fintype (L n)]
    (P : ∀ n, Design (L n)) (X Y : ∀ n, L n → ℝ)
    (hx : ConvergesInProbability P X 0) (hy : ConvergesInProbability P Y 0) :
    ConvergesInProbability P (fun (n : ℕ) z => X n z-Y n z) 0 := by
  intro ε he
  have hx' := hx (ε/2) (by linarith)
  have hy' := hy (ε/2) (by linarith)
  simp only [sub_zero] at hx' hy' ⊢
  exact squeeze_zero (fun n : ℕ => probability_nonneg _ _)
    (fun n : ℕ => difference_probability_bound (P n) (X n) (Y n) ε he)
    (by simpa using hx'.add hy')

/-- Corrected centering in Appendix A.6: HT means are consistent for μ(d),
under Conditions 3 and 4 (P013-T9(i), p. 1942). -/
theorem corrected_mean_consistency (S : ExperimentSequence) (hnested : NestedPopulationSetup S) (hp : StandingPositivity S)
    (hc3 : Condition3 S)
    (hc4 : Condition4 S) :
    ConvergesInProbability (seqLaw S)
      (fun (n : ℕ) z => htMean (seqPopulation S n) (S.treated n) z -
        potentialMean (seqPopulation S n) (S.treated n)) 0 :=
  (both_means_consistent S (condition3_implies_comparison S hc3) hc4).1

/-- Proposition 6.1, faithfully centered at τ(d_k,d_l), with uniform
Condition 3 and pairwise little-o Condition 4 (P013-T19, p. 1925). -/
theorem htEffect_consistency (S : ExperimentSequence) (hnested : NestedPopulationSetup S) (hp : StandingPositivity S)
    (hc3 : Condition3 S) (hc4 : Condition4 S) :
    ConvergesInProbability (seqLaw S) (fun (n : ℕ) z => seqEstimate S n z-seqTarget S n) 0 := by
  have hm := both_means_consistent S (condition3_implies_comparison S hc3) hc4
  have heq : (fun (n : ℕ) z => seqEstimate S n z-seqTarget S n) =
      (fun (n : ℕ) z => (htMean (seqPopulation S n) (S.treated n) z-
        potentialMean (seqPopulation S n) (S.treated n)) -
        (htMean (seqPopulation S n) (S.control n) z-
          potentialMean (seqPopulation S n) (S.control n))) := by
    funext n z
    unfold seqEstimate seqTarget htEffect causalEffect htMean potentialMean
    ring
  rw [heq]
  exact convergence_difference _ _ _ hm.1 hm.2

/-- Centered concentration of the scaled estimator implies the added
one-sided condition (L), using Proposition 5.6 (P013-T2(A)). -/
theorem centered_concentration_implies_lower_tail (S : ExperimentSequence)
    (hA : ConvergesInProbability (seqLaw S) (fun (n : ℕ) z => (n+1 : ℝ) *
      (seqVarianceEstimate S n z-expectation (seqLaw S n) (seqVarianceEstimate S n))) 0) :
    LowerTailCondition S := by
  intro δ hd
  have hlim := hA δ hd
  simp only [sub_zero] at hlim
  apply squeeze_zero (fun n : ℕ => probability_nonneg _ _)
    (g := fun n : ℕ => probability (seqLaw S n) (fun z => δ < |(n+1 : ℝ)*
      (seqVarianceEstimate S n z-expectation (seqLaw S n) (seqVarianceEstimate S n))|))
  · intro n
    apply probability_mono
    intro z hz
    have hv := effectVariance_conservative (seqPopulation S n) (S.treated n) (S.control n)
      (S.distinct n) (S.positiveTreated n) (S.positiveControl n)
    have hn : (0 : ℝ) ≤ n+1 := by positivity
    have hb := mul_le_mul_of_nonneg_left hv hn
    have hneg : (n+1 : ℝ)*(seqVarianceEstimate S n z-
        expectation (seqLaw S n) (seqVarianceEstimate S n)) ≤ 0 := by
      dsimp [seqTrueVariance,seqVarianceEstimate,seqEstimate] at hz ⊢
      nlinarith
    rw [abs_of_nonpos hneg]
    dsimp [seqTrueVariance,seqVarianceEstimate,seqEstimate] at hz ⊢
    nlinarith
  · exact hlim

/-- Var(N Vhat)→0 implies the added lower-tail condition (L), without
assuming a limit of E[N Vhat] (P013-T2(A), P013-T8(a)). -/
theorem vanishing_variance_implies_lower_tail (S : ExperimentSequence)
    (hvar : Tendsto (fun n : ℕ => variance (seqLaw S n)
      (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z)) atTop (𝓝 0)) :
    LowerTailCondition S := by
  apply centered_concentration_implies_lower_tail
  have hc := variance_concentration (seqLaw S) (fun (n : ℕ) z => (n+1 : ℝ)*seqVarianceEstimate S n z) hvar
  have heq : (fun (n : ℕ) z => (n+1 : ℝ)*seqVarianceEstimate S n z-
      expectation (seqLaw S n) (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z)) =
      (fun (n : ℕ) z => (n+1 : ℝ)*(seqVarianceEstimate S n z-
        expectation (seqLaw S n) (seqVarianceEstimate S n))) := by
    funext n z
    rw [expectation_const_mul]
    ring
  rw [heq] at hc
  exact hc


/-- Explicit N=6 member of the T1 family, indexed by three four-state pair
assignments; all 64 complete assignments have their product design probability. -/
def pairSixDesign : Design (Fin 4 × Fin 4 × Fin 4) :=
  independentProduct (pairAtomDesign 6 (by norm_num))
    (independentProduct (pairAtomDesign 6 (by norm_num)) (pairAtomDesign 6 (by norm_num)))

/-- The N=6 paired witness has own-treatment exposure and fixed outcomes
(1,-1,1,-1,1,-1) at both exposures (P013-T1 finite enumeration). -/
def pairSixPopulation : Population pairSixDesign 6 2 where
  exposure z i := pairExposure (if i.val < 2 then z.1 else if i.val < 4 then z.2.1 else z.2.2)
    (decide (i.val % 2 = 1))
  outcome i _ := if i.val % 2 = 0 then 1 else -1

/-- A_6: all three pairs are split (P013-T1(c), exact 64-assignment check). -/
def pairSixSplit (z : Fin 4 × Fin 4 × Fin 4) : Prop :=
  pairExposure z.1 false ≠ pairExposure z.1 true ∧
  pairExposure z.2.1 false ≠ pairExposure z.2.1 true ∧
  pairExposure z.2.2 false ≠ pairExposure z.2.2 true

set_option maxHeartbeats 4000000 in
/-- Exact N=6 marginals, obtained by weighted enumeration of the 64
assignments, π_i(0)=π_i(1)=1/2 (P013-T1(a)). -/
theorem pairSix_pi (i : Fin 6) (d : Fin 2) : pi pairSixPopulation i d = 1/2 := by
  fin_cases i <;> fin_cases d <;>
    norm_num [pi, expectation, indicator, pairSixPopulation, pairSixDesign, independentProduct,
      pairAtomDesign, pairExposure, pairEpsilon, Fintype.sum_prod_type, Fin.sum_univ_succ]

set_option maxHeartbeats 4000000 in
/-- Exact N=6 joint exposure probabilities: 1/36 or 17/36 for distinct
units in a pair, 1/4 between pairs, and the correct same-unit diagonal
(P013-T1(a)), enumerating all assignments. -/
theorem pairSix_joint (i j : Fin 6) (d e : Fin 2) :
    jointPi pairSixPopulation i j d e = if i=j then (if d=e then 1/2 else 0) else
      if i.val/2=j.val/2 then (if d=e then 1/36 else 17/36) else 1/4 := by
  fin_cases i <;> fin_cases j <;> fin_cases d <;> fin_cases e <;>
    norm_num [jointPi, expectation, indicator, pairSixPopulation, pairSixDesign, independentProduct,
      pairAtomDesign, pairExposure, pairEpsilon, Fintype.sum_prod_type, Fin.sum_univ_succ]

set_option maxHeartbeats 4000000 in
/-- Pointwise reduction of the original HT effect and expression (11) to
three explicit pair scores in the N=6 design (P013-T1 finite lemma). -/
theorem pairSix_formulas (z : Fin 4 × Fin 4 × Fin 4) :
    htEffect pairSixPopulation 1 0 z = (pairScore z.1+pairScore z.2.1+pairScore z.2.2)/6 ∧
    effectVariance pairSixPopulation 1 0 z =
      (pairVarianceScore 6 z.1+pairVarianceScore 6 z.2.1+pairVarianceScore 6 z.2.2)/36 := by
  rcases z with ⟨a,b,c⟩
  unfold htEffect htTotal effectVariance varianceHT correctionA2 covarianceA pairTerm
  simp only [pairSix_pi,pairSix_joint]
  norm_num [pairSixPopulation,indicator,Fin.sum_univ_succ]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [pairExposure,pairScore,pairVarianceScore,pairEpsilon,pairSplitProbability]

set_option maxHeartbeats 8000000 in
/-- Exact N=6 identities for P013-T1, computed from the original
(1),(3),(7),(10),(11) on the 64-assignment weighted finite space. This is a
finite lemma, not a finite-N refutation of the asymptotic coverage theorem. -/
theorem pairSix_exact_enumeration :
    expectation pairSixDesign (htEffect pairSixPopulation 1 0) = 0 ∧
    variance pairSixDesign (htEffect pairSixPopulation 1 0) = 34/27 ∧
    expectation pairSixDesign (effectVariance pairSixPopulation 1 0) = 34/27 ∧
    probability pairSixDesign pairSixSplit = 4913/5832 ∧
    6*variance pairSixDesign (htEffect pairSixPopulation 1 0) = 68/9 ∧
    variance pairSixDesign (fun z => 6*effectVariance pairSixPopulation 1 0 z) = 65536/4131 := by
  have ht : ∀ z, htEffect pairSixPopulation 1 0 z =
      (pairScore z.1+pairScore z.2.1+pairScore z.2.2)/6 := fun z => (pairSix_formulas z).1
  have hv : ∀ z, effectVariance pairSixPopulation 1 0 z =
      (pairVarianceScore 6 z.1+pairVarianceScore 6 z.2.1+pairVarianceScore 6 z.2.2)/36 :=
    fun z => (pairSix_formulas z).2
  and_intros <;>
    norm_num [expectation, variance, covariance, probability, ht, hv, pairScore,
      pairVarianceScore, pairSplitProbability, pairSixDesign, independentProduct,
      pairAtomDesign, pairExposure, pairEpsilon, pairSixSplit,
      Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- On the all-split event in the exact N=6 design, 6 Vhat=100/17
(P013-T1(c), fixed-N identity). -/
theorem pairSix_on_split (z : Fin 4 × Fin 4 × Fin 4) (hz : pairSixSplit z) :
    6*effectVariance pairSixPopulation 1 0 z = 100/17 := by
  rw [(pairSix_formulas z).2]
  rcases z with ⟨a,b,c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals norm_num [pairSixSplit,pairExposure] at hz
  all_goals norm_num [pairVarianceScore,pairExposure,pairEpsilon,pairSplitProbability]

/-- The number of quadruples retained by the local-dependence count in
Appendix A.7 is at most 4 N m³ for symmetric binary h with row bound m
(P013-T18 valid finite lemma, p. 1943). This does not assert that Condition 3
bounds the random covariance summands. -/
theorem graph_quadruple_count {N : ℕ} (h : Fin N → Fin N → Bool)
    (hs : ∀ i j, h i j = h j i) (m : ℕ) (hb : RowBound h m) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      (if h i j=true ∧ h k l=true ∧
        (h i k=true ∨ h i l=true ∨ h j k=true ∨ h j l=true) then 1 else 0 : ℕ)) ≤
      4*N*m^3 := by
  classical
  let δ : Fin N → Fin N → ℕ := fun i j => if h i j=true then 1 else 0
  have hd : ∀ i, ∑ j, δ i j ≤ m := hb
  have hds : ∀ i j, δ i j = δ j i := fun i j => by simp only [δ,hs i j]
  have hl : ∀ i j k, (∑ l, δ i j*δ k l*δ i k) ≤ δ i j*δ i k*m := by
    intro i j k
    calc
      _ = (δ i j*δ i k)*(∑ l, δ k l) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro l _
        ring
      _ ≤ _ := Nat.mul_le_mul_left _ (hd k)
  have hk : ∀ i j, (∑ k, ∑ l, δ i j*δ k l*δ i k) ≤ δ i j*(m*m) := by
    intro i j
    calc
      _ ≤ ∑ k, δ i j*δ i k*m := sum_le_sum fun k _ => hl i j k
      _ = (δ i j*m)*(∑ k, δ i k) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        ring
      _ ≤ δ i j*m*m := Nat.mul_le_mul_left _ (hd i)
      _ = _ := by ring
  have hj : ∀ i, (∑ j, ∑ k, ∑ l, δ i j*δ k l*δ i k) ≤ m^3 := by
    intro i
    calc
      _ ≤ ∑ j, δ i j*(m*m) := sum_le_sum fun j _ => hk i j
      _ = (∑ j, δ i j)*(m*m) := by rw [sum_mul]
      _ ≤ m*(m*m) := Nat.mul_le_mul_right _ (hd i)
      _ = _ := by ring
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l, δ i j*δ k l*δ i k) ≤ N*m^3 :=
    (sum_le_sum fun i _ => hj i).trans_eq (by simp)
  have he2 : (∑ i, ∑ j, ∑ k, ∑ l, δ i j*δ k l*δ i l) =
      ∑ i, ∑ j, ∑ k, ∑ l, δ i j*δ k l*δ i k := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro l _
    rw [hds l k]
  have he3 : (∑ i, ∑ j, ∑ k, ∑ l, δ i j*δ k l*δ j k) =
      ∑ i, ∑ j, ∑ k, ∑ l, δ i j*δ k l*δ i k := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hds j i]
  have he4 : (∑ i, ∑ j, ∑ k, ∑ l, δ i j*δ k l*δ j l) =
      ∑ i, ∑ j, ∑ k, ∑ l, δ i j*δ k l*δ i l := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hds j i]
  have hp : ∀ i j k l, (if h i j=true ∧ h k l=true ∧
      (h i k=true ∨ h i l=true ∨ h j k=true ∨ h j l=true) then 1 else 0 : ℕ) ≤
      δ i j*δ k l*δ i k + δ i j*δ k l*δ i l +
      δ i j*δ k l*δ j k + δ i j*δ k l*δ j l := by
    intro i j k l
    by_cases hij : h i j=true <;> by_cases hkl : h k l=true <;>
      by_cases hik : h i k=true <;> by_cases hil : h i l=true <;>
      by_cases hjk : h j k=true <;> by_cases hjl : h j l=true <;>
      simp [δ,hij,hkl,hik,hil,hjk,hjl]
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ∑ l,
        (δ i j*δ k l*δ i k + δ i j*δ k l*δ i l +
          δ i j*δ k l*δ j k + δ i j*δ k l*δ j l) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ =>
        sum_le_sum fun k _ => sum_le_sum fun l _ => hp i j k l
    _ = (∑ i, ∑ j, ∑ k, ∑ l, δ i j*δ k l*δ i k) * 4 := by
      simp only [sum_add_distrib]
      rw [he2,he3,he4,he2]
      ring
    _ ≤ N*m^3*4 := Nat.mul_le_mul_right 4 h1
    _ = _ := by ring

/-- Finite binomial identity used in Appendix A.3: multiplying the expected
inverse smoothed probability by p gives 1-(1-p)^(R+1). This is the exact
Bernoulli-count calculation underlying corrected Proposition 4.1 (P013-T4(a),
p. 1938), before identifying the count law of the finite product design. -/
theorem binomial_inverse_moment (R : ℕ) (p : ℝ) :
    p * (∑ k ∈ range (R+1), (Nat.choose R k : ℝ) * p^k * (1-p)^(R-k) *
      (R+1 : ℝ)/(k+1 : ℝ)) = 1-(1-p)^(R+1) := by
  have hcoef : ∀ k : ℕ, (Nat.choose R k : ℝ)*(R+1 : ℝ)/(k+1 : ℝ) =
      (Nat.choose (R+1) (k+1) : ℝ) := by
    intro k
    have hk : (k+1 : ℝ) ≠ 0 := by positivity
    apply (div_eq_iff hk).2
    have hh := Nat.add_one_mul_choose_eq R k
    have hh' : (R+1 : ℝ)*(Nat.choose R k : ℝ) =
        (Nat.choose (R+1) (k+1) : ℝ)*(k+1 : ℝ) := by exact_mod_cast hh
    linarith
  have hs := add_pow p (1-p) (R+1)
  rw [show p+(1-p)=1 by ring,one_pow] at hs
  rw [sum_range_succ'] at hs
  simp only [pow_zero,Nat.sub_zero,Nat.choose_zero_right,Nat.cast_one,one_mul,mul_one] at hs
  calc
    _ = ∑ k ∈ range (R+1), p^(k+1)*(1-p)^((R+1)-(k+1))*
        (Nat.choose (R+1) (k+1) : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      rw [show (R+1)-(k+1)=R-k by omega,pow_succ]
      calc
        _ = (p^k*p)*(1-p)^(R-k)*
            ((Nat.choose R k : ℝ)*(R+1 : ℝ)/(k+1 : ℝ)) := by ring
        _ = _ := by rw [hcoef]
    _ = _ := by linarith

/-- The log replicate rule is equivalent to the power criterion for any
positive cancellation factor, target b and probability p0 in (0,1)
(P013-T4(e), Section 4 p. 1920 and its signed-outcome correction). -/
theorem replicate_log_rule_equivalence (p0 κ b : ℝ) (R : ℕ)
    (hp0 : 0 < p0) (hp1 : p0 < 1) (hk : 0 < κ) (hb : 0 < b) :
    ((R : ℝ) ≥ Real.log (b/κ)/Real.log (1-p0)-1) ↔ κ*(1-p0)^(R+1) ≤ b := by
  have hq : 0 < 1-p0 := by linarith
  have hq1 : 1-p0 < 1 := by linarith
  have hl : Real.log (1-p0) < 0 := Real.log_neg hq hq1
  have hp := pow_pos hq (R+1)
  have hbκ := div_pos hb hk
  rw [mul_comm κ,← le_div_iff₀ hk,← Real.log_le_log_iff hp hbκ,Real.log_pow]
  push_cast
  constructor
  · intro hr
    exact (div_le_iff_of_neg hl).1 (by linarith)
  · intro hr
    have hh := (div_le_iff_of_neg hl).2 hr
    linarith

/-- The signed-outcome cancellation factor is at least one whenever the
exposure-specific population total is nonzero (P013-T4(c), corrected 4.1). -/
theorem cancellation_factor_ge_one {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (ht : potentialTotal F d ≠ 0) : 1 ≤ cancellationFactor F d := by
  have ha : 0 < |potentialTotal F d| := abs_pos.mpr ht
  unfold cancellationFactor
  apply (le_div_iff₀ ha).2
  simpa [potentialTotal] using abs_sum_le_sum_abs (fun i => F.outcome i d) univ

/-- Common-sign exposure potential outcomes with nonzero total have κ=1,
which is precisely the sign-qualified repair of Proposition 4.1
(P013-T4(d), pp. 1920, 1938). -/
theorem common_sign_cancellation_factor {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (ht : potentialTotal F d ≠ 0)
    (hs : (∀ i, 0 ≤ F.outcome i d) ∨ (∀ i, F.outcome i d ≤ 0)) :
    cancellationFactor F d = 1 := by
  have hab : (∑ i, |F.outcome i d|) = |potentialTotal F d| := by
    rcases hs with hs | hs
    · have hsum : 0 ≤ ∑ i, F.outcome i d := sum_nonneg fun i _ => hs i
      simp only [abs_of_nonneg (hs _),potentialTotal,abs_of_nonneg hsum]
    · have hsum : (∑ i, F.outcome i d) ≤ 0 := sum_nonpos fun i _ => hs i
      simp only [abs_of_nonpos (hs _),potentialTotal,abs_of_nonpos hsum,sum_neg_distrib]
  unfold cancellationFactor
  rw [hab,div_self (abs_ne_zero.mpr ht)]

/-- An absolute bias bound yields the corrected relative bound by dividing
by the absolute population total, retaining κ (P013-T4(b,c), finite lemma). -/
theorem relative_bias_from_absolute {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (B q : ℝ) (habs : |B| ≤ q*(∑ i, |F.outcome i d|)) :
    |B/potentialTotal F d| ≤ cancellationFactor F d*q := by
  rw [abs_div]
  calc
    _ ≤ (q*(∑ i, |F.outcome i d|))/|potentialTotal F d| :=
      div_le_div_of_nonneg_right habs (abs_nonneg _)
    _ = _ := by unfold cancellationFactor; ring

/-- The R=1 signed-outcome witness also passes the literal logarithmic
replicate rule for b=1/2 and π0=1/3, yet exceeds that bias target
(P013-T3(b), printed Section 4 replicate rule, p. 1920). -/
theorem signed_log_rule_counterexample :
    (1 : ℝ) ≥ Real.log (1/2)/Real.log (1-1/3)-1 ∧
    (1/2 : ℝ) < |(expectation (independentProduct signedReplicationDesign signedReplicationDesign)
      (signedOneReplicate 2)-potentialTotal (signedReplicationPopulation 2) 1)/
        potentialTotal (signedReplicationPopulation 2) 1| := by
  constructor
  · have hh := (replicate_log_rule_equivalence (1/3) 1 (1/2) 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
    simpa using hh
  · norm_num [potentialTotal,expectation,independentProduct,signedOneReplicate,indicator,
      observed,signedReplicationPopulation,signedReplicationDesign,
      Fintype.sum_prod_type,Fin.sum_univ_succ]


/-- Every unit in the fixed block-family design has marginal exposure
probability 1/2 at both labels (P013-T7(a), standing positivity and C3). -/
theorem block_pi (N : ℕ) (i : Fin N) (d : Fin 2) : pi (blockPopulation N) i d = 1/2 := by
  change expectation (replicateDesign sharedDesign N) (fun zs => if zs i=d then 1 else 0) = _
  rw [replicate_marginal sharedDesign N i (fun t : Fin 2 => if t=d then 1 else 0)]
  fin_cases d <;> norm_num [expectation,sharedDesign,Fin.sum_univ_succ]

/-- Distinct units in the fixed block-family design have all four joint
exposure probabilities equal to 1/4 (P013-T7(a)). -/
theorem block_joint (N : ℕ) (i j : Fin N) (hne : i ≠ j) (d e : Fin 2) :
    jointPi (blockPopulation N) i j d e = 1/4 := by
  change expectation (replicateDesign sharedDesign N)
    (fun zs => (if zs i=d then 1 else 0)*(if zs j=e then 1 else 0)) = _
  rw [replicate_pair_marginal sharedDesign N i j hne
    (fun t : Fin 2 => if t=d then 1 else 0) (fun t : Fin 2 => if t=e then 1 else 0)]
  fin_cases d <;> fin_cases e <;> norm_num [expectation,sharedDesign,Fin.sum_univ_succ]

/-- All fixed block outcomes have modulus at most two, and the two
exposure potential outcomes of every unit sum to two (P013-T7(a)). -/
theorem block_outcome_properties (i : ℕ) :
    (∀ d : Fin 2, |blockOutcome i d| ≤ 2) ∧ blockOutcome i 1+blockOutcome i 0 = 2 := by
  constructor
  · intro d
    fin_cases d <;> unfold blockOutcome <;> split_ifs <;> norm_num at *
  · unfold blockOutcome
    split_ifs <;> norm_num at *

/-- The error of the original HT contrast on the block population is
exactly (2/N) times the sum of the independent fair Rademacher assignments
(P013-T7(a), finite identity under expressions (1),(3)). -/
theorem block_effect_error (N : ℕ) (z : Fin N → Fin 2) :
    htEffect (blockPopulation N) 1 0 z-causalEffect (blockPopulation N) 1 0 =
      (2/(N : ℝ))*∑ i, rademacher (z i) := by
  let F := blockPopulation N
  have hp : ∀ i : Fin N,
      indicator F.exposure i 1 z*(F.outcome i 1/pi F i 1) -
        indicator F.exposure i 0 z*(F.outcome i 0/pi F i 0) -
          (F.outcome i 1-F.outcome i 0) = 2*rademacher (z i) := by
    intro i
    have hi := block_unit_score_identity (F.outcome i 1) (F.outcome i 0)
      (block_outcome_properties (i.val+1)).2 (z i)
    dsimp only [F]
    rw [block_pi,block_pi]
    simp only [indicator,blockPopulation]
    by_cases hz : z i = 1
    · have h0 : z i ≠ 0 := by rw [hz]; norm_num
      norm_num [hz,h0,F,blockPopulation,rademacher] at hi ⊢
      linarith
    · have h0 : z i = 0 := by omega
      norm_num [hz,h0,F,blockPopulation,rademacher] at hi ⊢
      linarith
  calc
    _ = (∑ i, (indicator F.exposure i 1 z*(F.outcome i 1/pi F i 1) -
        indicator F.exposure i 0 z*(F.outcome i 0/pi F i 0) -
          (F.outcome i 1-F.outcome i 0)))/(N : ℝ) := by
      simp only [htEffect,causalEffect,potentialMean,potentialTotal,htTotal,sum_sub_distrib,F]
      ring
    _ = _ := by simp_rw [hp]; rw [← mul_sum]; ring

/-- For every nested population U_N, the design has exactly two assignments:
all units untreated or all treated, each of probability 1/2. Exposure is own
assignment and all potential outcomes are zero (P013-T5(c)). -/
def sharedSequence : ExperimentSequence where
  experiment n := {
    supportSize := 2
    exposureSize := 2
    design := sharedDesign
    population := sharedPopulation (n+1) }
  treated _ := 1
  control _ := 0
  distinct _ := by norm_num
  positiveTreated n := by
    intro i
    change 0 < pi (sharedPopulation (n+1)) i 1 ∧ pi (sharedPopulation (n+1)) i 1 < 1
    rw [(shared_exposure_counterexample (n+1)).2.2.1 i 1]
    norm_num
  positiveControl n := by
    intro i
    change 0 < pi (sharedPopulation (n+1)) i 0 ∧ pi (sharedPopulation (n+1)) i 0 < 1
    rw [(shared_exposure_counterexample (n+1)).2.2.1 i 0]
    norm_num

/-- The explicit shared Bernoulli family satisfies standing positivity,
Condition 3 with c1=1,c2=2, and literal printed Condition 5 with m=1, but
violates Condition 4 for every possible pairwise-dependency indicator
(P013-T5(c), counterexample to "Condition 5 subsumes Condition 4", p. 1926). -/
theorem shared_sequence_counterexample :
    StandingPositivity sharedSequence ∧ Condition3 sharedSequence ∧
      Condition5Printed sharedSequence ∧ ¬ Condition4 sharedSequence := by
  have hp : ∀ n (i : Fin (n+1)) (d : Fin 2), pi (sharedPopulation (n+1)) i d = 1/2 :=
    fun n i d => (shared_exposure_counterexample (n+1)).2.2.1 i d
  refine ⟨?_,?_,?_,?_⟩
  · intro n d i
    change Fin 2 at d
    change 0 < pi (sharedPopulation (n+1)) i d ∧ pi (sharedPopulation (n+1)) i d < 1
    rw [hp]
    norm_num
  · refine ⟨1,2,by norm_num,by norm_num,?_⟩
    intro n i d
    change Fin 2 at d
    change |(sharedPopulation (n+1)).outcome i d| ≤ 1 ∧
      |1/pi (sharedPopulation (n+1)) i d| ≤ 2
    rw [hp]
    norm_num [sharedPopulation]
  · refine ⟨1,fun n i j => decide (i=j),?_⟩
    intro n
    exact printed_identity_dependency sharedDesign (sharedPopulation (n+1)).exposure
  · rintro ⟨g,hg,hcount⟩
    have hc : ∀ n : ℕ, (∑ i, ∑ j, (if g n i j=true then 1 else 0 : ℝ)) = (n+1 : ℝ)^2 := by
      intro n
      have hh := shared_pair_count (n+1) (g n) (hg n)
      exact_mod_cast hh
    simp_rw [hc] at hcount
    exact shared_condition4_failure hcount


/-- The shifted problem has "y'_i(d) = y_i(d) + c" at every exposure
(P013-T22, Section 7.1 correction, p. 1927). The design and exposure map
are unchanged; Conditions 1--2 are still encoded by `Population`. -/
def shiftPopulation {N K : ℕ} {P : Design Ω} (F : Population P N K) (c : ℝ) :
    Population P N K where
  exposure := F.exposure
  outcome i d := F.outcome i d + c

/-- "w_ik = I(D_i=d_k)/π_i(d_k)" in the Section 7.1 correction
(P013-T22, p. 1927). Its sum W_k is `htCount`. -/
def exposureWeight {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (z : Ω) (i : Fin N) : ℝ := indicator F.exposure i d z / pi F i d

/-- "τ̂_G(d_k,d_l) = (T_k-T_l)/N": expression (3) with the difference
total of (12)--(13) substituted, as "Estimation proceeds as above"
directs (Section 7.1, p. 1927; P013-T21--T22). -/
def differenceEffect {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (gk gl : Fin N → ℝ) (z : Ω) : ℝ :=
  (differenceTotal F d gk z - differenceTotal F e gl z) / (N : ℝ)

/-- "Σ_i (1-w_ik)(h_ik-c)", the exact translation error of a difference
total when the predictions increase by h_ik (P013-T22(a),(c), p. 1927).
The prediction changes are fixed across randomized assignments. -/
def translationError {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (h : Fin N → ℝ) (c : ℝ) (z : Ω) : ℝ :=
  ∑ i, (1 - exposureWeight F d z i) * (h i - c)

/-- Translating all potential outcomes preserves every exposure probability
and changes each observed outcome by c (P013-T22 setting, p. 1927). -/
theorem shift_population_objects {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (c : ℝ) :
    (∀ i d, pi (shiftPopulation F c) i d = pi F i d) ∧
    (∀ z i, observed (shiftPopulation F c) z i = observed F z i + c) := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Conditions 1--2 put (12)--(13) in the weighted residual
form Σ_i w_ik(y_i(d_k)-g_ik)+Σ_i g_ik (P013-T22 definitions, p. 1927). -/
theorem differenceTotal_weighted {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g : Fin N → ℝ) (z : Ω) :
    differenceTotal F d g z =
      (∑ i, exposureWeight F d z i * (F.outcome i d - g i)) + ∑ i, g i := by
  unfold differenceTotal htTotal exposureWeight
  rw [← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

/-- Exact change of a difference total under any prediction changes h:
T'_k-T_k=cW_k+Σ_i(1-w_ik)h_ik (P013-T22(a), Section 7.1 correction, p. 1927).
This also holds without positive-marginal or nonempty-population assumptions. -/
private theorem differenceTotal_shift_change_algebra {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) :
    differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z -
      differenceTotal F d g z =
        c * htCount F d z + ∑ i, (1 - exposureWeight F d z i) * h i := by
  rw [differenceTotal_weighted, differenceTotal_weighted]
  change (∑ i, exposureWeight F d z i * (F.outcome i d + c - (g i + h i))) +
    (∑ i, (g i + h i)) - ((∑ i, exposureWeight F d z i * (F.outcome i d - g i)) +
    ∑ i, g i) = c * (∑ i, exposureWeight F d z i) +
      ∑ i, (1 - exposureWeight F d z i) * h i
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_sub_distrib,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  ring


/-- Exact translation error T'_k-T_k-cN equals Σ_i(1-w_ik)(h_ik-c)
(P013-T22(a), Section 7.1 correction, p. 1927).
This also holds without positive-marginal or nonempty-population assumptions. -/
private theorem differenceTotal_shift_error_algebra {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) :
    differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z -
      differenceTotal F d g z - c * N = translationError F d h c z := by
  rw [differenceTotal_shift_change_algebra]
  have hc : (∑ _ : Fin N, c) = c * N := by simp; ring
  rw [← hc]
  change c * (∑ i, exposureWeight F d z i) +
      (∑ i, (1 - exposureWeight F d z i) * h i) - (∑ _ : Fin N, c) =
    ∑ i, (1 - exposureWeight F d z i) * (h i - c)
  rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  ring


/-- Total equivariance on a supported assignment is equivalent to a zero
translation error, including arbitrary prediction changes (P013-T22(c), p. 1927).
This also holds without positive-marginal or nonempty-population assumptions. -/
private theorem differenceTotal_equivariance_iff_algebra {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) :
    (differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z =
      differenceTotal F d g z + c * N) ↔ translationError F d h c z = 0 := by
  have he := differenceTotal_shift_error_algebra F d g h c z
  constructor <;> intro hh <;> linarith


/-- Jointly translating predictions and outcomes gives T'_k=T_k+cN
assignment by assignment (P013-T22(b), corrected Section 7.1 sentence, p. 1927).
This also holds without positive-marginal or nonempty-population assumptions. -/
private theorem differenceTotal_joint_translation_algebra {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g : Fin N → ℝ) (c : ℝ) (z : Ω) :
    differenceTotal (shiftPopulation F c) d (fun i => g i + c) z =
      differenceTotal F d g z + c * N := by
  apply (differenceTotal_equivariance_iff_algebra F d g (fun _ => c) c z).2
  simp [translationError]

/-- Exact change of a difference total under any prediction changes h:
T'_k-T_k=cW_k+Σ_i(1-w_ik)h_ik (P013-T22(a), Section 7.1 correction, p. 1927). -/
theorem differenceTotal_shift_change {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d) :
    differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z -
      differenceTotal F d g z =
        c * htCount F d z + ∑ i, (1 - exposureWeight F d z i) * h i := by
  exact differenceTotal_shift_change_algebra F d g h c z

/-- Exact translation error T'_k-T_k-cN equals Σ_i(1-w_ik)(h_ik-c)
(P013-T22(a), Section 7.1 correction, p. 1927). -/
theorem differenceTotal_shift_error {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d) :
    differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z -
      differenceTotal F d g z - c * N = translationError F d h c z := by
  exact differenceTotal_shift_error_algebra F d g h c z

/-- Total equivariance on a supported assignment is equivalent to a zero
translation error, including arbitrary prediction changes (P013-T22(c), p. 1927). -/
theorem differenceTotal_equivariance_iff {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d) :
    (differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z =
      differenceTotal F d g z + c * N) ↔ translationError F d h c z = 0 := by
  exact differenceTotal_equivariance_iff_algebra F d g h c z

/-- Jointly translating predictions and outcomes gives T'_k=T_k+cN
assignment by assignment (P013-T22(b), corrected Section 7.1 sentence, p. 1927). -/
theorem differenceTotal_joint_translation {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d) :
    differenceTotal (shiftPopulation F c) d (fun i => g i + c) z =
      differenceTotal F d g z + c * N := by
  exact differenceTotal_joint_translation_algebra F d g c z

/-- With both predictions translated by c, estimated exposure means increase
by c, observed residuals are unchanged, estimated contrasts are invariant,
and both population totals/means and the true contrast transform accordingly
(P013-T22(b), p. 1927). A positive population size gives defined means. -/
theorem difference_joint_translation_properties {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K)
    (gk gl : Fin N → ℝ) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e) :
    (differenceTotal (shiftPopulation F c) d (fun i => gk i + c) z / N =
      differenceTotal F d gk z / N + c) ∧
    (differenceTotal (shiftPopulation F c) e (fun i => gl i + c) z / N =
      differenceTotal F e gl z / N + c) ∧
    (∀ i, F.exposure z i = d → observed (shiftPopulation F c) z i - (gk i + c) = observed F z i - gk i) ∧
    (∀ i, F.exposure z i = e → observed (shiftPopulation F c) z i - (gl i + c) = observed F z i - gl i) ∧
    differenceEffect (shiftPopulation F c) d e (fun i => gk i + c) (fun i => gl i + c) z =
      differenceEffect F d e gk gl z ∧
    potentialTotal (shiftPopulation F c) d = potentialTotal F d + c * N ∧
    potentialTotal (shiftPopulation F c) e = potentialTotal F e + c * N ∧
    causalEffect (shiftPopulation F c) d e = causalEffect F d e := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have ht : ∀ a : Fin K, potentialTotal (shiftPopulation F c) a = potentialTotal F a + c * N := by
    intro a
    simp [potentialTotal, shiftPopulation, sum_add_distrib]
    ring
  refine ⟨?_,?_,?_,?_,?_,ht d,ht e,?_⟩
  · rw [differenceTotal_joint_translation_algebra, add_div, mul_div_cancel_right₀ _ hn]
  · rw [differenceTotal_joint_translation_algebra, add_div, mul_div_cancel_right₀ _ hn]
  · intro i _hi; change observed F z i + c - (gk i + c) = _; ring
  · intro i _hi; change observed F z i + c - (gl i + c) = _; ring
  · unfold differenceEffect
    rw [differenceTotal_joint_translation_algebra, differenceTotal_joint_translation_algebra]
    congr 1; ring
  · unfold causalEffect potentialMean
    rw [ht,ht]; ring

/-- The change of the estimated mean contrast is (E_k-E_l)/N; it is zero
exactly when the two total translation errors agree (P013-T22(c), p. 1927). -/
theorem differenceEffect_shift_error {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K)
    (gk gl hk hl : Fin N → ℝ) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e) :
    differenceEffect (shiftPopulation F c) d e (fun i => gk i + hk i)
        (fun i => gl i + hl i) z - differenceEffect F d e gk gl z =
      (translationError F d hk c z - translationError F e hl c z) / N ∧
    (differenceEffect (shiftPopulation F c) d e (fun i => gk i + hk i)
        (fun i => gl i + hl i) z = differenceEffect F d e gk gl z ↔
      translationError F d hk c z = translationError F e hl c z) := by
  have hd := differenceTotal_shift_error_algebra F d gk hk c z
  have he := differenceTotal_shift_error_algebra F e gl hl c z
  have hh : differenceEffect (shiftPopulation F c) d e (fun i => gk i + hk i)
        (fun i => gl i + hl i) z - differenceEffect F d e gk gl z =
      (translationError F d hk c z - translationError F e hl c z) / N := by
    unfold differenceEffect
    rw [← sub_div]
    congr 1
    linarith
  refine ⟨hh,?_⟩
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [← sub_eq_zero, hh, div_eq_zero_iff, or_iff_left hn, sub_eq_zero]

/-- Predictions held numerically fixed give the changes cW_k and
c(W_k-W_l)/N, translation error c(W_k-N), and the exact nonzero-c
calibration conditions W_k=N and W_k=W_l (P013-T22(d), p. 1927). -/
theorem difference_fixed_prediction_translation {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K)
    (gk gl : Fin N → ℝ) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e) :
    differenceTotal (shiftPopulation F c) d gk z - differenceTotal F d gk z =
      c * htCount F d z ∧
    differenceTotal (shiftPopulation F c) d gk z - differenceTotal F d gk z - c * N =
      c * (htCount F d z - N) ∧
    differenceEffect (shiftPopulation F c) d e gk gl z - differenceEffect F d e gk gl z =
      c * (htCount F d z - htCount F e z) / N ∧
    (c ≠ 0 → (differenceTotal (shiftPopulation F c) d gk z =
      differenceTotal F d gk z + c * N ↔ htCount F d z = N) ∧
      (differenceEffect (shiftPopulation F c) d e gk gl z = differenceEffect F d e gk gl z ↔
        htCount F d z = htCount F e z)) := by
  have hd : differenceTotal (shiftPopulation F c) d gk z - differenceTotal F d gk z =
      c * htCount F d z := by
    simpa using differenceTotal_shift_change_algebra F d gk (fun _ => 0) c z
  have he : differenceTotal (shiftPopulation F c) e gl z - differenceTotal F e gl z =
      c * htCount F e z := by
    simpa using differenceTotal_shift_change_algebra F e gl (fun _ => 0) c z
  have hc : differenceEffect (shiftPopulation F c) d e gk gl z - differenceEffect F d e gk gl z =
      c * (htCount F d z - htCount F e z) / N := by
    unfold differenceEffect; rw [← sub_div]; congr 1; nlinarith
  refine ⟨hd,?_,hc,?_⟩
  · rw [hd]; ring
  · intro hcz
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    constructor
    · have ht := sub_mul c (htCount F d z) (N : ℝ)
      constructor <;> intro hh
      · have hm : c * (htCount F d z - N) = 0 := by nlinarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hcz)
      · rw [hh] at hd; linarith
    · rw [← sub_eq_zero, hc, div_eq_zero_iff, or_iff_left hn,
        mul_eq_zero, or_iff_right hcz, sub_eq_zero]

/-- Every inverse-probability exposure weight has expectation one when its
exposure probability is positive (P013-T22(e), p. 1927). -/
theorem exposureWeight_unbiased {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (i : Fin N) (hi : 0 < pi F i d) :
    expectation P (fun z => exposureWeight F d z i) = 1 := by
  unfold exposureWeight
  simp only [div_eq_mul_inv, expectation_mul_const]
  change pi F i d * (pi F i d)⁻¹ = 1
  exact mul_inv_cancel₀ (ne_of_gt hi)

/-- Horvitz--Thompson is exactly the zero-prediction case of (12): its
outcome-only total and contrast changes are cW_k and c(W_k-W_l)/N
(P013-T22(d), expressions (1) and (3), pp. 1919--1920, 1927). -/
theorem ht_fixed_translation {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e) :
    differenceTotal F d (fun _ => 0) z = htTotal F d z ∧
    differenceEffect F d e (fun _ => 0) (fun _ => 0) z = htEffect F d e z ∧
    htTotal (shiftPopulation F c) d z - htTotal F d z = c * htCount F d z ∧
    htEffect (shiftPopulation F c) d e z - htEffect F d e z =
      c * (htCount F d z - htCount F e z) / N := by
  have hh := difference_fixed_prediction_translation F hN d e (fun _ => 0) (fun _ => 0) c z hd he hne
  simpa [differenceTotal,differenceEffect,htEffect] using
    (show differenceTotal F d (fun _ => 0) z = htTotal F d z ∧
      differenceEffect F d e (fun _ => 0) (fun _ => 0) z = htEffect F d e z ∧
      differenceTotal (shiftPopulation F c) d (fun _ => 0) z -
        differenceTotal F d (fun _ => 0) z = c * htCount F d z ∧
      differenceEffect (shiftPopulation F c) d e (fun _ => 0) (fun _ => 0) z -
        differenceEffect F d e (fun _ => 0) (fun _ => 0) z =
        c * (htCount F d z - htCount F e z) / N from
        ⟨by simp [differenceTotal],by simp [differenceEffect,differenceTotal,htEffect],hh.1,hh.2.2.1⟩)

/-- Fixed prediction changes have mean-zero translation error; the shifted
total remains unbiased for y^T(d_k)+cN and E[W_k]=N
(P013-T22(e), Section 7.1 correction, p. 1927). Only positive marginals
are needed; no upper bound below one is used. -/
theorem translation_error_mean_zero {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ)
    (hd : ∀ i, 0 < pi F i d) :
    expectation P (translationError F d h c) = 0 ∧
    expectation P (differenceTotal (shiftPopulation F c) d (fun i => g i + h i)) =
      expectation P (differenceTotal F d g) + c * N ∧
    expectation P (differenceTotal (shiftPopulation F c) d (fun i => g i + h i)) =
      potentialTotal F d + c * N ∧
    expectation P (htCount F d) = N := by
  have hw : ∀ i, expectation P (fun z => exposureWeight F d z i) = 1 :=
    fun i => exposureWeight_unbiased F d i (hd i)
  have herr : expectation P (translationError F d h c) = 0 := by
    unfold translationError
    rw [expectation_sum]
    apply sum_eq_zero
    intro i _
    rw [expectation_mul_const, expectation_sub, expectation_const, hw]
    ring
  have hcount : expectation P (htCount F d) = N := by
    change expectation P (fun z => ∑ i, exposureWeight F d z i) = N
    rw [expectation_sum]; simp [hw]
  have hbase : expectation P (differenceTotal F d g) = potentialTotal F d := by
    change expectation P (fun z => differenceTotal F d g z) = _
    simp only [differenceTotal_weighted, expectation_add, expectation_sum,
      expectation_mul_const, hw, expectation_const, one_mul, sum_sub_distrib]
    unfold potentialTotal
    ring
  have heq : ∀ z, differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z =
      differenceTotal F d g z + c * N + translationError F d h c z := by
    intro z
    have hh := differenceTotal_shift_error_algebra F d g h c z
    linarith
  have hmean : expectation P (differenceTotal (shiftPopulation F c) d (fun i => g i + h i)) =
      expectation P (differenceTotal F d g) + c * N := by
    change expectation P (fun z => differenceTotal (shiftPopulation F c) d
      (fun i => g i + h i) z) = _
    simp_rw [heq]
    rw [expectation_add, expectation_add, expectation_const, herr, add_zero]
  exact ⟨herr,hmean,by rw [hmean,hbase],hcount⟩

/-- With numerically fixed predictions, the total error c(W_k-N) and the
contrast change c(W_k-W_l)/N both have mean zero (P013-T22(e), p. 1927). -/
theorem fixed_translation_mean_zero {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d e : Fin K) (c : ℝ)
    (hd : ∀ i, 0 < pi F i d) (he : ∀ i, 0 < pi F i e) (hN : 0 < N) (hne : d ≠ e) :
    expectation P (fun z => c * (htCount F d z - N)) = 0 ∧
    expectation P (fun z => c * (htCount F d z - htCount F e z) / N) = 0 := by
  have hw := (translation_error_mean_zero F d (fun _ => 0) (fun _ => 0) c hd).2.2.2
  have hv := (translation_error_mean_zero F e (fun _ => 0) (fun _ => 0) c he).2.2.2
  constructor
  · rw [expectation_const_mul, expectation_sub, hw, expectation_const]; ring
  · simp only [div_eq_mul_inv, expectation_mul_const, expectation_const_mul,
      expectation_sub, hw, hv, sub_self, mul_zero, zero_mul]

/-- In a fixed-count equal-marginal exposure design, W_k=N on every
assignment and numerically fixed predictions suffice for total equivariance
(P013-T22(f), p. 1927). The condition is weaker than recoding every prediction. -/
theorem fixed_count_calibration {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d : Fin K) (m : ℕ) (hm : 1 ≤ m)
    (hcount : ∀ z, ∑ i, indicator F.exposure i d z = (m : ℝ))
    (hmarg : ∀ i, pi F i d = (m : ℝ) / N) (g : Fin N → ℝ) (c : ℝ) :
    ∀ z, htCount F d z = N ∧
      differenceTotal (shiftPopulation F c) d g z = differenceTotal F d g z + c * N := by
  intro z
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hw : htCount F d z = N := by
    unfold htCount
    simp_rw [hmarg]
    rw [← sum_div, hcount]
    field_simp
  refine ⟨hw,?_⟩
  have heq := differenceTotal_shift_change_algebra F d g (fun _ => 0) c z
  have hh : differenceTotal (shiftPopulation F c) d g z - differenceTotal F d g z = c * N := by
    simpa [hw] using heq
  linarith

/-- The three supported own-treatment assignments (1,0,0), (0,1,0),
(0,0,1) have weights 1/4,1/4,1/2 (P013-T21(a);
Section 7.1, p. 1927). Index z names the unique treated unit. -/
def locationDesign : Design (Fin 3) where
  weight z := if z = 2 then 1/2 else 1/4
  positive z := by split_ifs <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- Fixed predictions "(g_1,g_2,g_3)=(2,3,5)" for both exposures, given
by a predefined lookup function of the unit's covariate label
(P013-T21(a), Section 7.1 counterexample, p. 1927). -/
def locationPrediction (i : Fin 3) : ℝ := if i = 0 then 2 else if i = 1 then 3 else 5

/-- Own assignment D_i=Z_i: exposure 1 for the uniquely selected unit,
exposure 0 otherwise. Both exposure potential-outcome vectors are (2,3,5)
(P013-T21(a), p. 1927). Conditions 1--2 hold by construction. -/
def locationPopulation : Population locationDesign 3 2 where
  exposure z i := if z = i then 1 else 0
  outcome i _ := locationPrediction i

/-- All printed finite hypotheses hold: marginals are (1/4,1/4,1/2)
and (3/4,3/4,1/2), both are strictly between zero and one, predictions
are perfect and fixed with Cov(g_i,Z_i)=0, and exactly one/two units
receive the two exposures (P013-T21(a), Section 7.1, p. 1927). -/
theorem location_counterexample_hypotheses :
    (∀ i, pi locationPopulation i 1 = locationDesign.weight i) ∧
    (∀ i, pi locationPopulation i 0 = 1 - locationDesign.weight i) ∧
    (∀ d, Positivity locationPopulation d) ∧
    (∀ i d, locationPopulation.outcome i d = locationPrediction i) ∧
    (∀ i, covariance locationDesign (fun _ => locationPrediction i)
      (fun z => indicator locationPopulation.exposure i 1 z) = 0) ∧
    (∀ z, (∑ i, indicator locationPopulation.exposure i 1 z) = 1 ∧
      (∑ i, indicator locationPopulation.exposure i 0 z) = 2) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i; fin_cases i <;>
      norm_num [pi,expectation,indicator,locationPopulation,locationDesign,Fin.sum_univ_succ]
  · intro i; fin_cases i <;>
      norm_num [pi,expectation,indicator,locationPopulation,locationDesign,Fin.sum_univ_succ]
  · intro d i; fin_cases d <;> fin_cases i <;>
      norm_num [pi,expectation,indicator,locationPopulation,locationDesign,Fin.sum_univ_succ]
  · intro i d; rfl
  · intro i
    rw [covariance,expectation_const_mul,expectation_const]
    ring
  · intro z; fin_cases z <;>
      norm_num [indicator,locationPopulation,Fin.sum_univ_succ]

/-- Before translation both true/estimated totals are 10 and both true/
estimated contrasts are zero; after translating all outcomes by one the true
totals are 13, with unchanged zero effect (P013-T21(b),(c), p. 1927). -/
theorem location_counterexample_targets :
    (∀ d, potentialTotal locationPopulation d = 10 ∧
      potentialTotal (shiftPopulation locationPopulation 1) d = 13) ∧
    causalEffect locationPopulation 1 0 = 0 ∧
    causalEffect (shiftPopulation locationPopulation 1) 1 0 = 0 ∧
    (∀ z d, differenceTotal locationPopulation d locationPrediction z = 10) ∧
    (∀ z, differenceEffect locationPopulation 1 0 locationPrediction locationPrediction z = 0) := by
  have ht : ∀ d : Fin 2, potentialTotal locationPopulation d = 10 ∧
      potentialTotal (shiftPopulation locationPopulation 1) d = 13 := by
    intro d
    norm_num [potentialTotal,locationPopulation,locationPrediction,shiftPopulation,Fin.sum_univ_succ]
  have he : ∀ z d, differenceTotal locationPopulation d locationPrediction z = 10 := by
    intro z d
    rw [differenceTotal_weighted]
    norm_num [locationPopulation,locationPrediction,Fin.sum_univ_succ]
  refine ⟨ht,?_,?_,he,?_⟩
  · simp [causalEffect,potentialMean,(ht 1).1,(ht 0).1]
  · simp [causalEffect,potentialMean,(ht 1).2,(ht 0).2]
  · intro z; simp [differenceEffect,he]

/-- Exact enumeration of the unchanged-prediction shift: W_k=(4,4,2),
W_l=(10/3,10/3,8/3), shifted totals (14,14,12) and (40/3,40/3,38/3),
and shifted contrasts (2/9,2/9,-2/9) (P013-T21(c),(d), p. 1927). -/
theorem location_counterexample_enumeration :
    ∀ z : Fin 3,
      htCount locationPopulation 1 z = (if z = 2 then 2 else 4) ∧
      htCount locationPopulation 0 z = (if z = 2 then 8/3 else 10/3) ∧
      differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction z =
        (if z = 2 then 12 else 14) ∧
      differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction z =
        (if z = 2 then 38/3 else 40/3) ∧
      differenceEffect (shiftPopulation locationPopulation 1) 1 0
        locationPrediction locationPrediction z = (if z = 2 then -2/9 else 2/9) := by
  intro z; fin_cases z <;>
    norm_num [htCount,differenceTotal,htTotal,differenceEffect,shiftPopulation,
      locationPrediction,locationPopulation,pi,expectation,indicator,locationDesign,Fin.sum_univ_succ]

/-- With c=1 and perfect fixed predictions, on every supported assignment
neither total increases by cN and the estimated effect changes, although the
true effect stays zero. This is the concrete refutation of the fixed-numerical-
prediction reading of both Section 7.1 claims (P013-T21(c),(d), p. 1927). -/
theorem location_translation_counterexample :
    (∀ d, Positivity locationPopulation d) ∧
    (∀ i, covariance locationDesign (fun _ => locationPrediction i)
      (fun z => indicator locationPopulation.exposure i 1 z) = 0) ∧
    (∀ z, (∑ i, indicator locationPopulation.exposure i 1 z) = 1 ∧
      (∑ i, indicator locationPopulation.exposure i 0 z) = 2) ∧
    causalEffect (shiftPopulation locationPopulation 1) 1 0 = causalEffect locationPopulation 1 0 ∧
    (∀ z, differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction z ≠
      differenceTotal locationPopulation 1 locationPrediction z + 1 * (3 : ℝ) ∧
      differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction z ≠
        differenceTotal locationPopulation 0 locationPrediction z + 1 * (3 : ℝ) ∧
      differenceEffect (shiftPopulation locationPopulation 1) 1 0 locationPrediction locationPrediction z ≠
        differenceEffect locationPopulation 1 0 locationPrediction locationPrediction z) := by
  refine ⟨location_counterexample_hypotheses.2.2.1,
    location_counterexample_hypotheses.2.2.2.2.1,
    location_counterexample_hypotheses.2.2.2.2.2,?_,?_⟩
  · rw [location_counterexample_targets.2.1,location_counterexample_targets.2.2.1]
  · intro z
    have hh := location_counterexample_enumeration z
    have ht := location_counterexample_targets.2.2.2.1 z
    have he := location_counterexample_targets.2.2.2.2 z
    rw [ht 1,ht 0,he,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2]
    split_ifs <;> norm_num

/-- Exact pre/post-shift means and variances for the counterexample:
unbiasedness survives, but total variances change from 0 to 1 and 1/9,
and effect variance from 0 to 4/81 (P013-T21(e), p. 1927). -/
theorem location_counterexample_moments :
    expectation locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction) = 13 ∧
    expectation locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction) = 13 ∧
    expectation locationDesign (differenceEffect (shiftPopulation locationPopulation 1) 1 0
      locationPrediction locationPrediction) = 0 ∧
    variance locationDesign (differenceTotal locationPopulation 1 locationPrediction) = 0 ∧
    variance locationDesign (differenceTotal locationPopulation 0 locationPrediction) = 0 ∧
    variance locationDesign (differenceEffect locationPopulation 1 0 locationPrediction locationPrediction) = 0 ∧
    variance locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction) = 1 ∧
    variance locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction) = 1/9 ∧
    variance locationDesign (differenceEffect (shiftPopulation locationPopulation 1) 1 0
      locationPrediction locationPrediction) = 4/81 := by
  simp only [variance,covariance,expectation,Fin.sum_univ_succ]
  norm_num [differenceTotal,htTotal,differenceEffect,shiftPopulation,locationPrediction,
    locationPopulation,pi,expectation,indicator,locationDesign,Fin.sum_univ_succ]

/-- Shifting predictions to (3,4,6) along with the outcomes restores totals
13 and effect zero on every assignment (P013-T21(f), p. 1927). -/
theorem location_counterexample_joint_repair :
    ∀ z, (∀ d, differenceTotal (shiftPopulation locationPopulation 1) d
      (fun i => locationPrediction i + 1) z = 13) ∧
    differenceEffect (shiftPopulation locationPopulation 1) 1 0
      (fun i => locationPrediction i + 1) (fun i => locationPrediction i + 1) z = 0 := by
  intro z
  have ht : ∀ d, differenceTotal (shiftPopulation locationPopulation 1) d
      (fun i => locationPrediction i + 1) z = 13 := by
    intro d
    rw [differenceTotal_joint_translation_algebra,location_counterexample_targets.2.2.2.1 z d]
    norm_num
  exact ⟨ht,by simp [differenceEffect,ht]⟩


/-- Products of functions of the two independent design coordinates factor
in expectation, the independence step in Appendix A.3 (p. 1938).  Supporting finite lemma for corrected Proposition 4.1 (T4), p. 1920 and Appendix A.3, p. 1938. -/
theorem expectation_independent_product (P : Design Ω) (Q : Design Ξ)
    (g : Ω → ℝ) (h : Ξ → ℝ) :
    expectation (independentProduct P Q) (fun z => g z.1 * h z.2) =
      expectation P g * expectation Q h := by
  unfold expectation
  simp only [independentProduct,Fintype.sum_prod_type]
  calc
    _ = ∑ z, ∑ w, (P.weight z * g z) * (Q.weight w * h w) := by
      apply sum_congr rfl
      intro z _
      apply sum_congr rfl
      intro w _
      ring
    _ = _ := by simp only [← mul_sum,← sum_mul]

/-- Correct equalities of Appendix A.3 (p. 1938): exact expectation of the
Monte Carlo HT total under independent replicates, for arbitrary outcome signs
(P013-T4(a)). -/
theorem simulated_expectation {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (hN : 0 < N) (d : Fin K) (hd : Positivity F d) (R : ℕ) (hR : 1 ≤ R) :
    expectation (independentProduct P (replicateDesign P R)) (simulatedHTTotal F d R) =
      potentialTotal F d - ∑ i, F.outcome i d * (1 - pi F i d)^(R+1) := by
  classical
  have hobs : ∀ z i, indicator F.exposure i d z * observed F z i =
      indicator F.exposure i d z * F.outcome i d := by
    intro z i
    by_cases h : F.exposure z i = d
    · simp [indicator,observed,h]
    · simp [indicator,h]
  change expectation (independentProduct P (replicateDesign P R)) (fun z => ∑ i, _) = _
  rw [expectation_sum]
  have hunit : ∀ i, expectation (independentProduct P (replicateDesign P R))
      (fun z => indicator F.exposure i d z.1 * observed F z.1 i / simulatedPi F d R z.2 i) =
      F.outcome i d * (1-(1-pi F i d)^(R+1)) := by
    intro i
    have hinv := smoothed_inverse_success P (fun z => F.exposure z i = d) R
    change pi F i d * expectation (replicateDesign P R)
      (fun zs => (R+1 : ℝ)/(replicateCount F d R zs i+1)) =
        1-(1-pi F i d)^(R+1) at hinv
    have hfun : (fun z : Ω × (Fin R → Ω) =>
        indicator F.exposure i d z.1 * observed F z.1 i / simulatedPi F d R z.2 i) =
        (fun z => (indicator F.exposure i d z.1 * F.outcome i d) *
          ((R+1 : ℝ)/(replicateCount F d R z.2 i+1))) := by
      funext z
      rw [hobs]
      unfold simulatedPi
      push_cast
      rw [div_div_eq_mul_div]
      ring
    rw [hfun,expectation_independent_product P (replicateDesign P R)
      (fun z => indicator F.exposure i d z * F.outcome i d)
      (fun zs => (R+1 : ℝ)/(replicateCount F d R zs i+1)),expectation_mul_const]
    change (pi F i d * F.outcome i d) * _ = _
    calc
      _ = F.outcome i d * (pi F i d * expectation (replicateDesign P R)
        (fun zs => (R+1 : ℝ)/(replicateCount F d R zs i+1))) := by ring
      _ = _ := by rw [hinv]
  simp_rw [hunit]
  simp [potentialTotal,mul_sub,sum_sub_distrib]

/-- Corrected Proposition 4.1 and replicate rule: absolute bias for all
totals, relative bias with κ for nonzero totals, original bound for common-sign
outcomes, and log(b/κ) replicate rule (P013-T4(b)--(e), pp. 1920, 1938). -/
theorem simulated_bias_repaired {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (hN : 0 < N) (d : Fin K) (hd : Positivity F d) (R : ℕ) (hR : 1 ≤ R)
    (p0 : ℝ) (hmin : IsMinimumPi F d p0) :
    let B := expectation (independentProduct P (replicateDesign P R)) (simulatedHTTotal F d R) -
      potentialTotal F d
    |B| ≤ (1-p0)^(R+1) * (∑ i, |F.outcome i d|) ∧
    (potentialTotal F d ≠ 0 →
      1 ≤ cancellationFactor F d ∧
      |B / potentialTotal F d| ≤ cancellationFactor F d * (1-p0)^(R+1) ∧
      (((∀ i, 0 ≤ F.outcome i d) ∨ (∀ i, F.outcome i d ≤ 0)) →
        cancellationFactor F d = 1 ∧ |B / potentialTotal F d| ≤ (1-p0)^(R+1)) ∧
      (∀ b : ℝ, 0 < b → (R : ℝ) ≥ Real.log (b / cancellationFactor F d) /
        Real.log (1-p0) - 1 → |B / potentialTotal F d| ≤ b)) := by
  classical
  dsimp only
  let B := expectation (independentProduct P (replicateDesign P R))
    (simulatedHTTotal F d R) - potentialTotal F d
  have hbias : B = -∑ i, F.outcome i d * (1-pi F i d)^(R+1) := by
    dsimp [B]
    rw [simulated_expectation F hN d hd R hR]
    ring
  have habs : |B| ≤ (1-p0)^(R+1) * (∑ i, |F.outcome i d|) := by
    rw [hbias,abs_neg]
    exact signed_bias_absolute_bound (fun i => F.outcome i d)
      (fun i => (1-pi F i d)^(R+1)) ((1-p0)^(R+1))
      (simulated_power_bound F d hd R p0 hmin)
  refine ⟨habs,?_⟩
  intro ht
  have hk := cancellation_factor_ge_one F d ht
  have hrel := relative_bias_from_absolute F d B ((1-p0)^(R+1)) habs
  refine ⟨hk,hrel,?_,?_⟩
  · intro hs
    have hκ := common_sign_cancellation_factor F d ht hs
    exact ⟨hκ,by simpa [hκ] using hrel⟩
  · intro b hb hrule
    obtain ⟨i,hi⟩ := hmin.1
    have hp0 : 0 < p0 := by rw [← hi]; exact (hd i).1
    have hp1 : p0 < 1 := by rw [← hi]; exact (hd i).2
    have hκpos : 0 < cancellationFactor F d := lt_of_lt_of_le zero_lt_one hk
    have hpow := (replicate_log_rule_equivalence p0 (cancellationFactor F d) b R
      hp0 hp1 hκpos hb).mp hrule
    exact hrel.trans hpow

/-- The positive-joint score of (7)/(10) has second moment p times its
squared deterministic coefficient, not a squared inverse-joint factor (T2(R')).  Supporting finite lemma (vi) for corrected Appendix A.7 (T2), p. 1943. -/
theorem pairTerm_second_moment_identity {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (i j : Fin N) (d e : Fin K) :
    expectation P (fun z => (pairTerm F i j d e z)^2) =
      jointPi F i j d e * (((jointPi F i j d e - pi F i d * pi F j e) /
        jointPi F i j d e) * (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e))^2 := by
  classical
  have hf : (fun z => (pairTerm F i j d e z)^2) =
      (fun z => (indicator F.exposure i d z * indicator F.exposure j e z) *
        (((jointPi F i j d e - pi F i d * pi F j e) / jointPi F i j d e) *
          (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e))^2) := by
    funext z
    by_cases hi : F.exposure z i = d <;> by_cases hj : F.exposure z j = e <;>
      simp [pairTerm,indicator,hi,hj]
  rw [hf,expectation_mul_const]
  rfl

/-- The scalar second-moment inequality used for shrinking positive joints
in corrected Appendix A.7: bounded HT scores cost one factor 1/p (T2(R')).  Supporting finite lemma (vi) for corrected Appendix A.7 (T2), p. 1943. -/
theorem positive_joint_second_moment_bound (p u v x y C : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (hC : 0 ≤ C) (hx : |x| ≤ C) (hy : |y| ≤ C) :
    p * (((p-u*v)/p)*x*y)^2 ≤ 4*C^4/p := by
  have huv0 : 0 ≤ u*v := mul_nonneg hu.1 hv.1
  have huv1 : u*v ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) hv.1]
  have hd : |p-u*v| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hdsq : (p-u*v)^2 ≤ 1 := by
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg (p-u*v)) hd 2
  have hxsq : x^2 ≤ C^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hysq : y^2 ≤ C^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hxy : x^2*y^2 ≤ C^4 := by
    calc
      _ ≤ C^2*C^2 := mul_le_mul hxsq hysq (sq_nonneg y) (sq_nonneg C)
      _ = _ := by ring
  have hprod : (p-u*v)^2*(x^2*y^2) ≤ C^4 := by
    calc
      _ ≤ 1*(x^2*y^2) := mul_le_mul_of_nonneg_right hdsq
        (mul_nonneg (sq_nonneg x) (sq_nonneg y))
      _ ≤ _ := by simpa using hxy
  have hform : p * (((p-u*v)/p)*x*y)^2 = ((p-u*v)^2*(x^2*y^2))/p := by
    field_simp [ne_of_gt hp] <;> ring
  rw [hform]
  apply div_le_div_of_nonneg_right _ hp.le
  nlinarith [pow_nonneg hC 4]

/-- The original positive-joint score in expressions (7)/(10) obeys the
corrected one-inverse-joint second-moment bound, at each fixed population
size (P013-T2 finite lemma (vi), corrected Appendix A.7, p. 1943).
C bounds each of the two inverse-marginal weighted outcomes. -/
theorem pairTerm_second_moment_bound {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (i j : Fin N) (d e : Fin K)
    (C : ℝ) (hC : 0 ≤ C) (hp : 0 < jointPi F i j d e)
    (hx : |F.outcome i d / pi F i d| ≤ C)
    (hy : |F.outcome j e / pi F j e| ≤ C) :
    expectation P (fun z => (pairTerm F i j d e z)^2) ≤
      4*C^4 / jointPi F i j d e := by
  rw [pairTerm_second_moment_identity]
  exact positive_joint_second_moment_bound _ _ _ _ _ C hp
    (jointPi_bounds F i j d e).2 (pi_bounds F i d) (pi_bounds F j e) hC hx hy

/-- Exact expectation of a fair Rademacher coordinate in the independent
assignment design of the block witness (P013-T7).  Supporting finite lemma for the T7 counterexample to the Appendix A.7 limit claims, p. 1943. -/
theorem rademacher_coordinate_mean (N : ℕ) (i : Fin N) :
    expectation (replicateDesign sharedDesign N) (fun z => rademacher (z i)) = 0 := by
  rw [replicate_marginal sharedDesign N i rademacher]
  exact rademacher_moments.1

/-- Rademacher coordinate covariance is one on the diagonal and zero off it
for the block witness's exact randomization law (P013-T7).  Supporting finite lemma for the T7 counterexample to the Appendix A.7 limit claims, p. 1943. -/
theorem rademacher_coordinate_covariance (N : ℕ) (i j : Fin N) :
    covariance (replicateDesign sharedDesign N) (fun z => rademacher (z i))
      (fun z => rademacher (z j)) = if i=j then 1 else 0 := by
  unfold covariance
  rw [rademacher_coordinate_mean,rademacher_coordinate_mean]
  by_cases hij : i=j
  · subst j
    rw [replicate_marginal sharedDesign N i (fun t => rademacher t*rademacher t)]
    norm_num [expectation,sharedDesign,rademacher,Fin.sum_univ_succ]
  · rw [replicate_pair_marginal sharedDesign N i j hij rademacher rademacher]
    simp [rademacher_moments.1,hij]

/-- Variance of the sum of N independent fair Rademacher scores equals N
(P013-T7, exact finite identity).  Supporting finite lemma for the T7 counterexample to the Appendix A.7 limit claims, p. 1943. -/
theorem rademacher_sum_variance (N : ℕ) :
    variance (replicateDesign sharedDesign N) (fun z => ∑ i, rademacher (z i)) = N := by
  unfold variance
  rw [covariance_sum_sum]
  simp_rw [rademacher_coordinate_covariance]
  simp

/-- Subtracting a deterministic population target leaves design variance
unchanged (P013-T7, finite step in the centered HT score calculation).  Supporting finite lemma for the T7 counterexample to the Appendix A.7 limit claims, p. 1943. -/
theorem variance_sub_const (P : Design Ω) (X : Ω → ℝ) (c : ℝ) :
    variance P (fun z => X z-c) = variance P X := by
  have he : (fun z => (X z-c)*(X z-c)) = fun z => X z*X z-X z*c-c*X z+c*c := by
    funext z
    ring
  simp only [variance,covariance,he,expectation_add,expectation_sub,
    expectation_mul_const,expectation_const_mul,expectation_const]
  ring

/-- The fixed block outcomes and original HT effect estimator have true
variance exactly 4/N at every nonempty size (P013-T7(a)).  Supporting finite lemma for Condition 6 (p. 1926) of the T7 counterexample, P013-E007. -/
theorem block_true_variance (N : ℕ) (hN : 0 < N) :
    variance (blockDesign N) (htEffect (blockPopulation N) 1 0) = 4/(N : ℝ) := by
  rw [← variance_sub_const (blockDesign N) (htEffect (blockPopulation N) 1 0)
    (causalEffect (blockPopulation N) 1 0)]
  have he : (fun z => htEffect (blockPopulation N) 1 0 z-causalEffect (blockPopulation N) 1 0) =
      fun z => (∑ i, rademacher (z i))*(2/(N : ℝ)) := by
    funext z
    simpa only [mul_comm] using block_effect_error N z
  rw [he,variance,covariance_mul_const]
  change variance (replicateDesign sharedDesign N) (fun z => ∑ i, rademacher (z i)) *
    (2/(N : ℝ))*(2/(N : ℝ)) = _
  rw [rademacher_sum_variance]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hn] <;> ring

/-- The block witness satisfies the nonzero limiting variance premise with
c=4 along all population sizes (P013-T7(a), Condition 6, p. 1926).  Supporting finite lemma for Condition 6 (p. 1926) of the T7 counterexample, P013-E007. -/
theorem block_condition6_limit :
    Tendsto (fun n : ℕ => (n+1 : ℝ)*variance (blockDesign (n+1))
      (htEffect (blockPopulation (n+1)) 1 0)) atTop (𝓝 4) := by
  have he : (fun n : ℕ => (n+1 : ℝ)*variance (blockDesign (n+1))
      (htEffect (blockPopulation (n+1)) 1 0)) = fun _ => 4 := by
    funext n
    rw [block_true_variance (n+1) (by omega)]
    push_cast
    have hn : (n+1 : ℝ) ≠ 0 := by positivity
    field_simp [hn] <;> ring
  rw [he]
  exact tendsto_const_nhds

/-- The block witness has the genuine degree-one dependency graph because
all assignment coordinates are independent (P013-T7(a), Condition 5).  Supporting finite lemma for genuine Condition 5 (p. 1925) of the T7 counterexample. -/
theorem block_genuine_dependency (N : ℕ) :
    GenuineDependency (blockDesign N) (blockPopulation N).exposure
      (fun i j => decide (i=j)) ∧
    (∀ i j : Fin N, decide (i=j) = decide (j=i)) ∧
    RowBound (fun i j : Fin N => decide (i=j)) 1 := by
  classical
  refine ⟨coordinate_population_genuine_dependency sharedDesign N
    (fun i : Fin N => i) (fun _ x => x),?_,?_⟩
  · intro i j
    by_cases h : i=j
    · subst j; rfl
    · simp [h,Ne.symm h]
  · intro i
    simp [eq_comm]


end
/-!
Recorded reports and wearing outcomes, P013-T23,T24,T27.
The definitions use the finite design and population objects above.
-/

noncomputable section
variable {Ω : Type*} [Fintype Ω]

/-- R_i(d)∈{0,1}, represented by Bool: whether a report
is recorded at exposure d (P013-N020). This is not a definition printed in the article. -/
abbrev Recording (N K : ℕ) := Fin N → Fin K → Bool

/-- "g_i(d)=R_i(d)y_i(d)": an absent report is scored zero.
P013-N020; corrected interpretation of Section 10, pp. 1934--1936. -/
def recordedPopulation {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (R : Recording N K) : Population P N K where
  exposure := F.exposure
  outcome i d := if R i d then F.outcome i d else 0

/-- "L(d)=N⁻¹Σ_i(1-R_i(d))y_i(d)", the mean lost wearing outcome.
The piecewise form is identical for a binary recording indicator.
P013-N020, correction P013-T24(b). -/
def lostMean {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (R : Recording N K) (d : Fin K) : ℝ :=
  (∑ i, if R i d then 0 else F.outcome i d) / (N : ℝ)

/-- Recording changes outcomes, not exposure probabilities. Supporting
lemma for the corrected Section 10 interpretation, P013-T24, pp. 1934--1936. -/
theorem recorded_pi {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (R : Recording N K) (i : Fin N) (d : Fin K) :
    pi (recordedPopulation F R) i d = pi F i d := rfl

/-- Condition 2 in finite-sum form: Y_i=Σ_d I(D_i=d)y_i(d), p. 1918.
Used for the recorded outcome in P013-T23 and wearing in P013-T27. -/
theorem observed_exposure_sum {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (z : Ω) (i : Fin N) :
    observed F z i = ∑ d, indicator F.exposure i d z * F.outcome i d := by
  classical
  simp [observed, indicator, ite_mul]

/-- Lemma 4.1 / expression (4) using the target's positive-marginal premise.
The proof needs no separate marginal upper bound. P013-T24(a), p. 1920. -/
theorem ht_positive_unbiased {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (hd : ∀ i, 0 < pi F i d) :
    expectation P (htMean F d) = potentialMean F d := by
  have ht : expectation P (htTotal F d) = potentialTotal F d := by
    unfold htTotal potentialTotal
    rw [expectation_sum]
    apply sum_congr rfl
    intro i _
    rw [expectation_mul_const]
    change pi F i d * (F.outcome i d / pi F i d) = F.outcome i d
    field_simp [ne_of_gt (hd i)]
  change expectation P (fun z => htTotal F d z / (N : ℝ)) = potentialTotal F d / (N : ℝ)
  simp only [div_eq_mul_inv, expectation_mul_const, ht]

/-- The recorded HT mean and contrast estimate the recorded potential outcomes,
with exact design probabilities. P013-T24(a), correction to Section 10. -/
theorem recorded_unbiased {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (R : Recording N K) (_hN : 0 < N)
    (d e : Fin K) (_hne : d ≠ e)
    (hd : ∀ i, 0 < pi F i d) (he : ∀ i, 0 < pi F i e) :
    expectation P (htMean (recordedPopulation F R) d) =
        potentialMean (recordedPopulation F R) d ∧
    expectation P (htEffect (recordedPopulation F R) d e) =
        causalEffect (recordedPopulation F R) d e := by
  have md := ht_positive_unbiased (recordedPopulation F R) d hd
  have me := ht_positive_unbiased (recordedPopulation F R) e he
  refine ⟨md, ?_⟩
  have hs : htEffect (recordedPopulation F R) d e =
      fun z => htMean (recordedPopulation F R) d z -
        htMean (recordedPopulation F R) e z := by
    funext z; simp only [htEffect, htMean]; ring
  rw [hs, expectation_sub, md, me]
  rfl

/-- Recorded means equal wearing means minus lost means; the recorded contrast
has the exact lost-outcome correction. P013-T24(b), P013-N020. -/
theorem recorded_mean_decomposition {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (R : Recording N K) (d e : Fin K) :
    potentialMean (recordedPopulation F R) d = potentialMean F d - lostMean F R d ∧
    causalEffect (recordedPopulation F R) d e =
      causalEffect F d e - lostMean F R d + lostMean F R e := by
  have hm : ∀ a, potentialMean (recordedPopulation F R) a =
      potentialMean F a - lostMean F R a := by
    intro a
    unfold potentialMean potentialTotal lostMean
    rw [← sub_div, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro i _
    cases h : R i a <;> simp [recordedPopulation, h]
  refine ⟨hm d, ?_⟩
  simp only [causalEffect, hm]
  ring

/-- Exact bias and necessary-and-sufficient conditions for the recorded HT
estimators to be unbiased for wearing: L(d)=L(e) for a contrast, L(d)=0 for
a mean. P013-T24(b,c). -/
theorem recorded_wearing_identification {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (R : Recording N K) (hN : 0 < N)
    (d e : Fin K) (hne : d ≠ e)
    (hd : ∀ i, 0 < pi F i d) (he : ∀ i, 0 < pi F i e) :
    (expectation P (htEffect (recordedPopulation F R) d e) - causalEffect F d e =
      lostMean F R e - lostMean F R d) ∧
    (expectation P (htEffect (recordedPopulation F R) d e) = causalEffect F d e ↔
      lostMean F R d = lostMean F R e) ∧
    (expectation P (htMean (recordedPopulation F R) d) = potentialMean F d ↔
      lostMean F R d = 0) := by
  rw [(recorded_unbiased F R hN d e hne hd he).1,
    (recorded_unbiased F R hN d e hne hd he).2,
    (recorded_mean_decomposition F R d e).1,
    (recorded_mean_decomposition F R d e).2]
  constructor
  · ring
  constructor <;> constructor <;> intro h <;> linarith

/-- For nonnegative wearing outcomes, the lost mean is nonnegative and is
zero exactly when every unrecorded potential outcome is zero. P013-T24(d). -/
theorem lost_mean_zero_iff {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (R : Recording N K) (hN : 0 < N) (d : Fin K)
    (hy : ∀ i, 0 ≤ F.outcome i d) :
    0 ≤ lostMean F R d ∧
    (lostMean F R d = 0 ↔ ∀ i, R i d = false → F.outcome i d = 0) := by
  have hn : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN : (0 : ℝ) < N)
  have hs : ∀ i : Fin N, 0 ≤ (if R i d then 0 else F.outcome i d : ℝ) := by
    intro i; cases R i d <;> simp [hy i]
  refine ⟨div_nonneg (sum_nonneg fun i _ => hs i) (Nat.cast_nonneg N), ?_⟩
  simp only [lostMean, div_eq_zero_iff, hn, or_false]
  rw [sum_eq_zero_iff_of_nonneg (fun i _ => hs i)]
  constructor
  · intro h i hi
    simpa [hi] using h i (mem_univ i)
  · intro h i _
    cases hr : R i d
    · simp [hr, h i hr]
    · simp [hr]

/-- If unrecorded wearing outcomes under both contrasted exposures are zero,
the recorded HT contrast is unbiased for wearing. P013-T24(d); the exact
condition in recorded_wearing_identification can be weaker. -/
theorem no_lost_wearing_suffices {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (R : Recording N K) (hN : 0 < N)
    (d e : Fin K) (hne : d ≠ e)
    (hd : ∀ i, 0 < pi F i d) (he : ∀ i, 0 < pi F i e)
    (hyd : ∀ i, 0 ≤ F.outcome i d) (hye : ∀ i, 0 ≤ F.outcome i e)
    (hzd : ∀ i, R i d = false → F.outcome i d = 0)
    (hze : ∀ i, R i e = false → F.outcome i e = 0) :
    expectation P (htEffect (recordedPopulation F R) d e) = causalEffect F d e := by
  apply (recorded_wearing_identification F R hN d e hne hd he).2.1.mpr
  rw [(lost_mean_zero_iff F R hN d hyd).2.mpr hzd,
    (lost_mean_zero_iff F R hN e hye).2.mpr hze]

/-- "A_d(T)=Σ_{i∈T:D_i=d}w_i G_i" with weights from the original design,
not a new randomization after exclusions. P013-N020, P013-T24(e). -/
def recordedNumerator {N K : ℕ} (D : Fin N → Fin K) (w G : Fin N → ℝ)
    (d : Fin K) (T : Finset (Fin N)) : ℝ :=
  ∑ i ∈ T, if D i = d then w i * G i else 0

/-- "B_d(T)=Σ_{i∈T:D_i=d}w_i", the Hajek denominator (15),
p. 1928; P013-N020, P013-T24(e). -/
def recordedDenominator {N K : ℕ} (D : Fin N → Fin K) (w : Fin N → ℝ)
    (d : Fin K) (T : Finset (Fin N)) : ℝ :=
  ∑ i ∈ T, if D i = d then w i else 0

/-- Dropping only zero outcomes preserves every numerator. With N = S.card
and n = SR.card, each full-sample HT mean or contrast equals n/N times its
retained-sample counterpart. When the retained exposure weight is positive,
the full-sample Hajek mean equals the retained-sample mean times its
exposure-specific retained/full weight ratio. P013-T24(e), P013-N020. -/
theorem dropping_zero_outcomes {N K : ℕ} (D : Fin N → Fin K)
    (w G : Fin N → ℝ) (S SR : Finset (Fin N)) (hsub : SR ⊆ S)
    (hS : 0 < S.card) (hSR : 0 < SR.card) (_hw : ∀ i ∈ S, 0 < w i)
    (hkeep : ∀ i ∈ S, G i ≠ 0 → i ∈ SR) (d e : Fin K) :
    (∀ a, recordedNumerator D w G a SR = recordedNumerator D w G a S) ∧
    recordedNumerator D w G d S / S.card =
      (SR.card : ℝ) / S.card * (recordedNumerator D w G d SR / SR.card) ∧
    (recordedNumerator D w G d S - recordedNumerator D w G e S) / S.card =
      (SR.card : ℝ) / S.card *
        ((recordedNumerator D w G d SR - recordedNumerator D w G e SR) / SR.card) ∧
    (0 < recordedDenominator D w d SR →
      recordedNumerator D w G d S / recordedDenominator D w d S =
        (recordedDenominator D w d SR / recordedDenominator D w d S) *
          (recordedNumerator D w G d SR / recordedDenominator D w d SR)) := by
  have ha : ∀ a, recordedNumerator D w G a SR = recordedNumerator D w G a S := by
    intro a
    apply sum_subset hsub
    intro i hi hn
    have hg : G i = 0 := by
      by_contra hnz; exact hn (hkeep i hi hnz)
    simp [hg]
  have hn : (SR.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : SR.card ≠ 0)
  refine ⟨ha, ?_, ?_, ?_⟩
  · rw [← ha d]; field_simp
  · rw [← ha d, ← ha e]; field_simp
  · intro hb
    rw [← ha d]
    field_simp [ne_of_gt hb]

/-- The two exclusion counts and exact HT factors in the reconstruction on
the public data (ICPSR 37070 V2), not the authors' unavailable outcome files.
P013-T24(f), P013-N020; the input counts are aggregates. -/
theorem public_reconstruction_factors :
    2050 - 342 = (1708 : ℕ) ∧ 2050 - 151 = (1899 : ℕ) ∧
    (1708 : ℝ) / 2050 = 854 / 1025 ∧
    (342 : ℝ) / 2050 = 171 / 1025 ∧
    (1899 : ℝ) / 2050 + 151 / 2050 = 1 ∧
    1034 + 157 + 348 + 199 + 312 = (2050 : ℕ) ∧
    198 + 25 + 51 + 25 + 43 = (342 : ℕ) ∧
    78 + 11 + 26 + 13 + 23 = (151 : ℕ) := by norm_num

/-- Two invented units, four assignments (00),(01),(10),(11), each of
probability 1/4. P013-N020, counterexample P013-T23. -/
def twoReportDesign : Design (Fin 2 × Fin 2) where
  weight _ := 1/4
  positive _ := by norm_num
  total := by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]

/-- A always reports and has wearing potentials (0,1); B never reports and
has potentials (0,0),(0,1),(1,0) in worlds 0,1,2. Exposure is own assignment.
P013-N020, counterexample P013-T23, pp. 1934--1936. -/
def twoWearPopulation (world : Fin 3) : Population twoReportDesign 2 2 where
  exposure z i := if i = 0 then z.1 else z.2
  outcome i d := if i = 0 then (if d = 1 then 1 else 0)
    else if world = 1 then (if d = 1 then 1 else 0)
    else if world = 2 then (if d = 0 then 1 else 0) else 0

/-- "R_A(0)=R_A(1)=1, R_B(0)=R_B(1)=0" (P013-N020,
P013-T23). This records only A's reports in every assignment and world. -/
def twoRecording : Recording 2 2 := fun i _ => if i = 0 then true else false

/-- Recorded data comprise exposures, zero-coded observed outcomes, and
recording indicators on every assignment. P013-N020, P013-T23(b). -/
def recordedData {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (R : Recording N K) (z : Ω) (i : Fin N) : Fin K × ℝ × Bool :=
  (F.exposure z i, observed (recordedPopulation F R) z i, R i (F.exposure z i))

/-- The invented example has binary potentials, exact marginals 1/2, and
Condition 2 for its recorded outcome, in every world. P013-T23(a). -/
theorem two_report_hypotheses (world : Fin 3) :
    (∀ i d, (twoWearPopulation world).outcome i d = 0 ∨
      (twoWearPopulation world).outcome i d = 1) ∧
    (∀ i d, pi (twoWearPopulation world) i d = 1/2 ∧
      0 < pi (twoWearPopulation world) i d ∧ pi (twoWearPopulation world) i d < 1) ∧
    (∀ z i, observed (recordedPopulation (twoWearPopulation world) twoRecording) z i =
      ∑ d, indicator (twoWearPopulation world).exposure i d z *
        (recordedPopulation (twoWearPopulation world) twoRecording).outcome i d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i d
    fin_cases world <;> fin_cases i <;> fin_cases d <;> norm_num [twoWearPopulation]
  · intro i d
    fin_cases i <;> fin_cases d <;>
      norm_num [pi, expectation, indicator, twoWearPopulation, twoReportDesign,
        Fintype.sum_prod_type, Fin.sum_univ_two]
  · intro z i; exact observed_exposure_sum _ z i

/-- The recorded data on every assignment are identical in all three worlds.
P013-T23(b), P013-N020. -/
theorem two_report_data_same (world : Fin 3) :
    recordedData (twoWearPopulation world) twoRecording =
      recordedData (twoWearPopulation 0) twoRecording := by
  funext z i
  fin_cases i <;> simp [recordedData, observed, recordedPopulation,
    twoWearPopulation, twoRecording]

/-- Full-sample zero-coded HT contrast equals z_A on each of the four
assignments, giving the values (0,0,1,1). P013-T23(c). -/
theorem two_report_estimator (world : Fin 3) (z : Fin 2 × Fin 2) :
    htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0 z =
      (z.1.val : ℝ) := by
  rcases z with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [htEffect, htTotal, pi, expectation, indicator, recordedPopulation,
      twoWearPopulation, twoRecording, twoReportDesign,
      Fin.sum_univ_two, Fintype.sum_prod_type]

/-- Each world's recorded contrast has expectation 1/2, variance 1/4 and
recorded-outcome estimand 1/2. P013-T23(c), P013-N020. -/
theorem two_report_moments (world : Fin 3) :
    expectation twoReportDesign
      (htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0) = 1/2 ∧
    variance twoReportDesign
      (htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0) = 1/4 ∧
    causalEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0 = 1/2 := by
  have he : htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0 =
      fun z => (z.1.val : ℝ) := funext (two_report_estimator world)
  rw [he]
  norm_num [expectation, variance, covariance, twoReportDesign,
    causalEffect, potentialMean, potentialTotal, recordedPopulation,
    twoWearPopulation, twoRecording, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Wearing effects are 1/2,1,0, and the lost-outcome means are (0,0),
(0,1/2),(1/2,0) in the three worlds. P013-T23(d,e). -/
theorem two_wearing_effects_and_losses (world : Fin 3) :
    causalEffect (twoWearPopulation world) 1 0 =
      (if world = 0 then 1/2 else if world = 1 then 1 else 0) ∧
    lostMean (twoWearPopulation world) twoRecording 0 =
      (if world = 2 then 1/2 else 0) ∧
    lostMean (twoWearPopulation world) twoRecording 1 =
      (if world = 1 then 1/2 else 0) := by
  fin_cases world <;>
    norm_num [causalEffect, potentialMean, potentialTotal, lostMean,
      twoWearPopulation, twoRecording, Fin.sum_univ_two]

/-- Concrete biases are 0,-1/2,+1/2; worlds 1 and 2 violate the reading
that zero-coded reports always estimate wearing. This does not refute
Proposition 4.2 with Condition 2 for wearing. P013-T23(d). -/
theorem two_report_biases (world : Fin 3) :
    expectation twoReportDesign
      (htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0) -
      causalEffect (twoWearPopulation world) 1 0 =
      (if world = 0 then 0 else if world = 1 then -(1/2) else 1/2) := by
  rw [(two_report_moments world).1, (two_wearing_effects_and_losses world).1]
  fin_cases world <;> norm_num

/-- No function of all recorded data equals the wearing effect in all three
worlds, even though every exposure and recording indicator is available.
P013-T23(d), P013-N020: an identification counterexample. -/
theorem two_report_nonidentification :
    ¬ ∃ h : ((Fin 2 × Fin 2) → Fin 2 → Fin 2 × ℝ × Bool) → ℝ,
      ∀ world : Fin 3,
        h (recordedData (twoWearPopulation world) twoRecording) =
          causalEffect (twoWearPopulation world) 1 0 := by
  rintro ⟨h, hh⟩
  have h1 := hh 1
  have h2 := hh 2
  rw [two_report_data_same 1, (two_wearing_effects_and_losses 1).1] at h1
  rw [two_report_data_same 2, (two_wearing_effects_and_losses 2).1] at h2
  norm_num at h1 h2
  linarith

/-- Respondent-only analysis keeps A alone with N=1 and the original
assignment law and probabilities. P013-N020, P013-T23(f). -/
def twoRespondentPopulation : Population twoReportDesign 1 2 where
  exposure z _ := z.1
  outcome _ d := if d = 1 then 1 else 0

/-- The respondent-only HT contrast is 2z_A with expectation 1, and the
full-sample contrast is half of it. P013-T23(f), P013-N020. -/
theorem two_respondent_comparison (world : Fin 3) :
    (∀ z, htEffect twoRespondentPopulation 1 0 z = 2 * (z.1.val : ℝ)) ∧
    expectation twoReportDesign (htEffect twoRespondentPopulation 1 0) = 1 ∧
    (∀ z, htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0 z =
      (1/2) * htEffect twoRespondentPopulation 1 0 z) ∧
    expectation twoReportDesign (htEffect twoRespondentPopulation 1 0) -
      causalEffect (twoWearPopulation world) 1 0 =
      (if world = 0 then 1/2 else if world = 1 then 0 else 1) := by
  have hr : ∀ z, htEffect twoRespondentPopulation 1 0 z = 2 * (z.1.val : ℝ) := by
    rintro ⟨a,b⟩
    fin_cases a <;> fin_cases b <;>
      norm_num [htEffect, htTotal, pi, indicator, expectation, twoRespondentPopulation,
        twoReportDesign, Fin.sum_univ_one, Fin.sum_univ_two, Fintype.sum_prod_type]
  have hm : expectation twoReportDesign (htEffect twoRespondentPopulation 1 0) = 1 := by
    simp_rw [show htEffect twoRespondentPopulation 1 0 =
      (fun z => 2 * (z.1.val : ℝ)) from funext hr]
    norm_num [expectation, twoReportDesign, Fintype.sum_prod_type, Fin.sum_univ_two]
  refine ⟨hr, hm, ?_, ?_⟩
  · intro z; rw [two_report_estimator, hr]; ring
  · rw [hm, (two_wearing_effects_and_losses world).1]
    fin_cases world <;> norm_num

/-- Section 10's five exposures (p. 1934): labels 0,1,2,3,4 denote
respectively d000,d001,d011,d101,d111. The peer flag means z'θ_i>0.
No Exposure depends only on the school's hosting indicator. -/
def section10Exposure (host own peer : Bool) : Fin 5 :=
  if host then (if own then (if peer then 4 else 3) else (if peer then 2 else 1)) else 0

/-- Section 10 population constructor using school hosting and student assignments
on the full frame of M students. The map `analysed` selects a frame index for
each analysed unit, and `neighbors` supplies its peer set, including peers
outside the analysed sample. Injectivity of `analysed`, a zero diagonal, symmetry
and within-school peer membership are separate hypotheses of
`section10_wearing_unbiased`; this constructor accepts arbitrary maps and peer sets.
The table `y` supplies fixed wearing/reporting potential outcomes.
Definition on p. 1934; Conditions 1--2 on p. 1918. -/
def section10Population {N M : ℕ} (P : Design Ω) (analysed : Fin N → Fin M)
    (school : Fin M → Fin 56) (hosts : Ω → Fin 56 → Bool) (assigned : Ω → Fin M → Bool)
    (neighbors : Fin M → Finset (Fin M)) (y : Fin N → Fin 5 → ℝ) : Population P N 5 where
  exposure z i := section10Exposure (hosts z (school (analysed i))) (assigned z (analysed i))
    (decide ((neighbors (analysed i)).filter (fun j => assigned z j)).Nonempty)
  outcome := y

/-- Printed Table 2 interpretation read with Condition 2 for each student's
binary wearing outcome: its four HT contrasts estimate the differences of
wearing proportions under the five-exposure mapping. P013-T27, pp. 1934--1936;
expression (4), p. 1920. No missing-outcome scoring rule is assumed here. -/
theorem section10_wearing_unbiased {N M : ℕ} (P : Design Ω) (hN : 0 < N)
    (analysed : Fin N → Fin M) (_hinjective : Function.Injective analysed)
    (school : Fin M → Fin 56) (hosts : Ω → Fin 56 → Bool)
    (assigned : Ω → Fin M → Bool) (neighbors : Fin M → Finset (Fin M))
    (y : Fin N → Fin 5 → ℝ) (_hbinary : ∀ i d, y i d = 0 ∨ y i d = 1)
    (_hdiag : ∀ i, i ∉ neighbors i)
    (_hsym : ∀ i j, j ∈ neighbors i ↔ i ∈ neighbors j)
    (_hschool : ∀ i j, j ∈ neighbors i → school i = school j)
    (hpos : ∀ i d, 0 < pi (section10Population P analysed school hosts assigned neighbors y) i d) :
    let F := section10Population P analysed school hosts assigned neighbors y
    (∀ z i, observed F z i = ∑ d, indicator F.exposure i d z * y i d) ∧
    (∀ d : Fin 5, d ≠ 0 →
      causalEffect F d 0 = (∑ i, y i d) / (N : ℝ) - (∑ i, y i 0) / (N : ℝ) ∧
      expectation P (htEffect F d 0) = causalEffect F d 0) := by
  dsimp only
  refine ⟨fun z i => observed_exposure_sum _ z i, ?_⟩
  intro d hd
  refine ⟨rfl, ?_⟩
  have hs : htEffect (section10Population P analysed school hosts assigned neighbors y) d 0 =
    fun z => htMean (section10Population P analysed school hosts assigned neighbors y) d z -
      htMean (section10Population P analysed school hosts assigned neighbors y) 0 z := by
    funext z; unfold htEffect htMean; ring
  rw [hs, expectation_sub, ht_positive_unbiased _ d (fun i => hpos i d),
    ht_positive_unbiased _ 0 (fun i => hpos i 0)]
  rfl

/-- Complete finite-population bias and unbiasedness correction under the
setting of P013-T24(a–d): positive comparison marginals, distinct exposures,
N>0, and exposure-specific wearing and recording potentials. Recorded HT
is unbiased for recorded reports; it is unbiased for the wearing contrast
exactly when the two lost means agree. This correction is not a printed
corrigendum. -/
theorem corrected_recorded_outcome {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (R : Recording N K) (hN : 0 < N)
    (d e : Fin K) (hne : d ≠ e)
    (hd : ∀ i, 0 < pi F i d) (he : ∀ i, 0 < pi F i e) :
    expectation P (htMean (recordedPopulation F R) d) =
      potentialMean (recordedPopulation F R) d ∧
    expectation P (htEffect (recordedPopulation F R) d e) =
      causalEffect (recordedPopulation F R) d e ∧
    (∀ a, potentialMean (recordedPopulation F R) a = potentialMean F a - lostMean F R a) ∧
    causalEffect (recordedPopulation F R) d e =
      causalEffect F d e - lostMean F R d + lostMean F R e ∧
    expectation P (htEffect (recordedPopulation F R) d e) - causalEffect F d e =
      lostMean F R e - lostMean F R d ∧
    (expectation P (htEffect (recordedPopulation F R) d e) = causalEffect F d e ↔
      lostMean F R d = lostMean F R e) ∧
    (expectation P (htMean (recordedPopulation F R) d) = potentialMean F d ↔
      lostMean F R d = 0) ∧
    (∀ a, (∀ i, 0 ≤ F.outcome i a) → 0 ≤ lostMean F R a ∧
      (lostMean F R a = 0 ↔ ∀ i, R i a = false → F.outcome i a = 0)) := by
  have hu := recorded_unbiased F R hN d e hne hd he
  have hi := recorded_wearing_identification F R hN d e hne hd he
  exact ⟨hu.1,hu.2,fun a => (recorded_mean_decomposition F R a e).1,
    (recorded_mean_decomposition F R d e).2,hi.1,hi.2.1,hi.2.2,
    fun a ha => lost_mean_zero_iff F R hN a ha⟩

/-- Conditional on the aggregate counts of the reconstruction on
ICPSR 37070 V2 public data and on zero outcomes outside the retained sets,
the original-design HT contrasts have exactly the factors 854/1025 and
1899/2050. No student data, original-author outcome file, or empirical
missingness condition is inferred by Lean. P013-T24(e,f), P013-N020. -/
theorem public_reconstruction_HT_scaling {N K : ℕ} (D : Fin N → Fin K)
    (w G : Fin N → ℝ) (S item survey : Finset (Fin N))
    (hi : item ⊆ S) (hs : survey ⊆ S) (hS : S.card = 2050)
    (hitem : item.card = 1708) (hsurvey : survey.card = 1899)
    (hw : ∀ i ∈ S, 0 < w i)
    (hki : ∀ i ∈ S, G i ≠ 0 → i ∈ item)
    (hks : ∀ i ∈ S, G i ≠ 0 → i ∈ survey) (d e : Fin K) :
    (recordedNumerator D w G d S - recordedNumerator D w G e S)/2050 =
      (854/1025) * ((recordedNumerator D w G d item - recordedNumerator D w G e item)/1708) ∧
    (recordedNumerator D w G d S - recordedNumerator D w G e S)/2050 =
      (1899/2050) * ((recordedNumerator D w G d survey - recordedNumerator D w G e survey)/1899) := by
  have hi' := (dropping_zero_outcomes D w G S item hi (by omega) (by omega) hw hki d e).1
  have hs' := (dropping_zero_outcomes D w G S survey hs (by omega) (by omega) hw hks d e).1
  constructor
  · rw [← hi' d,← hi' e]; ring
  · rw [← hs' d,← hs' e]; ring

/-- A three-unit exact instance shows why the Hajek contrasts in T24(e)
have no universal scalar after exclusion: the full contrast is −1/2 and
the retained contrast is zero. Weights 2 can arise from fair exposure
marginals; the only excluded observed outcome is zero. P013-N020, (15) p. 1928. -/
theorem hajek_exclusion_no_common_factor :
    let D : Fin 3 → Fin 2 := fun i => if i = 2 then 0 else 1
    let w : Fin 3 → ℝ := fun _ => 2
    let G : Fin 3 → ℝ := fun i => if i = 1 then 0 else 1
    let S : Finset (Fin 3) := univ
    let SR : Finset (Fin 3) := {0,2}
    (∀ i ∈ S, G i ≠ 0 → i ∈ SR) ∧
    recordedDenominator D w 1 SR / recordedDenominator D w 1 S = 1/2 ∧
    recordedDenominator D w 0 SR / recordedDenominator D w 0 S = 1 ∧
    (¬ ∃ c : ℝ,
      recordedNumerator D w G 1 S / recordedDenominator D w 1 S -
        recordedNumerator D w G 0 S / recordedDenominator D w 0 S =
      c * (recordedNumerator D w G 1 SR / recordedDenominator D w 1 SR -
        recordedNumerator D w G 0 SR / recordedDenominator D w 0 SR)) := by
  dsimp only
  constructor
  · intro i _ hi
    fin_cases i <;> simp_all
  · norm_num [recordedNumerator,recordedDenominator,Fin.sum_univ_three]

end
end AronowAudit.P013

