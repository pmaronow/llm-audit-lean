import Mathlib

/-!
P026: Aronow and Middleton, A Class of Unbiased Estimators of the Average
Treatment Effect in Randomized Experiments. All randomness below is finite
randomization. Numeric examples use ℚ, so every reported equality is exact.
No external facts or named axioms are introduced.
-/

namespace AronowAudit.P026

open Finset

set_option maxRecDepth 4000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- "The only random component is the allocation of units to treatment and
control groups" (p. 138, Section 3). A finite list of assignments, with weights;
`probabilityDesign` asserts nonnegative weights summing to one. Repeated or
zero-weight assignments are allowed, so this represents every binary design. -/
structure Design (Ω I R : Type*) where
  weight : Ω → R
  treatment : Ω → I → Bool

variable {Ω I R : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- "E" is expectation over randomization (p. 138, eq. [5]): a weighted finite sum. -/
def expectation (D : Design Ω I R) (f : Ω → R) : R := ∑ w, D.weight w * f w

/-- A finite probability distribution on assignments; standing assumptions,
Section 3, pp. 137-138. -/
def probabilityDesign (D : Design Ω I R) : Prop :=
  (∀ w, 0 ≤ D.weight w) ∧ (∑ w, D.weight w) = 1

/-- "T_i = 1 when unit i receives the treatment and T_i = 0 otherwise"
(pp. 137-138, Section 3); false denotes the control indicator 1-T_i. -/
def indicator (D : Design Ω I R) (a : Bool) (w : Ω) (i : I) : R :=
  if D.treatment w i = a then 1 else 0

/-- "π_1i ... probability ... treatment" and "π_0i ... control"
(p. 138, Section 4). -/
def marginal (D : Design Ω I R) (a : Bool) (i : I) : R :=
  expectation D (fun w => indicator D a w i)

/-- "π_1i1j", "π_0i0j", "π_1i0j" are the corresponding joint inclusion
probabilities (p. 143, eqs. [21]-[23]); primed versions p. 145. -/
def joint (D : Design Ω I R) (a b : Bool) (i j : I) : R :=
  expectation D (fun w => indicator D a w i * indicator D b w j)

/-- "We assume that, ∀ i, π_1i > 0 and π_0i > 0" (p. 138, Section 4). -/
def positiveMarginals (D : Design Ω I R) : Prop :=
  ∀ i, 0 < marginal D true i ∧ 0 < marginal D false i

/-- "Y_i = T_i Y_1i + (1-T_i) Y_0i" (p. 138, eq. [1]). Potential
outcomes are fixed functions of the unit, with no assignment argument. -/
def observed (D : Design Ω I R) (y1 y0 : I → R) (w : Ω) (i : I) : R :=
  if D.treatment w i then y1 i else y0 i

/-- "Y_1^T ... sum ... treatment" and "Y_0^T ... control" (p. 138,
eq. [3]). The same sums denote cluster-total sums in Section 6.3. -/
def populationTotal (y : I → R) : R := ∑ i, y i

/-- "Δ = (Y_1^T - Y_0^T)/N" (p. 138, eq. [3]). N is the number of
original units, also when I indexes cluster totals. -/
def ate (N : ℕ) (y1 y0 : I → R) : R :=
  (populationTotal y1 - populationTotal y0) / N

/-- "Y^T_1,HT-hat = ∑ T_i Y_1i/π_1i" and its control analogue
(p. 139, eqs. [6]-[7]); with cluster totals, pp. 144-145. -/
def htTotal (D : Design Ω I R) (a : Bool) (y : I → R) (w : Ω) : R :=
  ∑ i, indicator D a w i * y i / marginal D a i

/-- "Δ_HT-hat = (Y^T_1,HT-hat - Y^T_0,HT-hat)/N" (p. 139, eq. [8]). -/
def ht (D : Design Ω I R) (N : ℕ) (y1 y0 : I → R) (w : Ω) : R :=
  (htTotal D true y1 w - htTotal D false y0 w) / N

/-- "f(.) is a predetermined real-valued function ... X_i ... θ_i"
(p. 140, eqs. [13]-[14]). `f w i` represents the entire evaluated
prediction; its assignment argument permits data-derived parameters. -/
def generalizedTotal (D : Design Ω I R) (a : Bool) (y : I → R)
    (f : Ω → I → R) (w : Ω) : R :=
  ∑ i, (indicator D a w i * y i / marginal D a i -
    indicator D a w i * f w i / marginal D a i + f w i)

/-- "Δ_G-hat = (Y_1^{T*}-hat - Y_0^{T*}-hat)/N"
(p. 141, eq. [15]). -/
def generalized (D : Design Ω I R) (N : ℕ) (y1 y0 : I → R)
    (f : Ω → I → R) (w : Ω) : R :=
  (generalizedTotal D true y1 f w - generalizedTotal D false y0 f w) / N

/-- Covariance over randomization (p. 143, eqs. [21]-[23]). This is
E[FG]-E[F]E[G], on a normalized finite probability distribution. -/
def covariance (D : Design Ω I R) (f g : Ω → R) : R :=
  expectation D (fun w => f w * g w) - expectation D f * expectation D g

/-- Sampling variance over randomization (p. 143, eq. [20]). -/
def variance (D : Design Ω I R) (f : Ω → R) : R := covariance D f f

/-- "Pr(T'_k ≠ T'_l)>0" defines distinct cluster indicators
(pp. 144-145, Section 6.3). -/
def disagreement (D : Design Ω I R) (i j : I) : R :=
  expectation D (fun w => if D.treatment w i ≠ D.treatment w j then 1 else 0)

/-- Sums "∑_k ∑_{l ≠ k}" in Section 6, pp. 143-147, are ordered pairs. -/
def offSum (f : I → I → R) : R := ∑ i, ∑ j ∈ univ.erase i, f i j

/-- Z_ab consists of ordered, distinct cluster pairs with π'_akbl=0;
correction to eqs. [34]-[35], P026-T2(c)-(f). -/
def zeroSum (D : Design Ω I R) (a b : Bool) (f : I → I → R) : R :=
  offSum (fun i j => if joint D a b i j = 0 then f i j else 0)

/-- "ε_akbl = 1[π'_akbl=0] ... included to avoid division by zero"
(p. 147, immediately after eq. [35]). -/
def epsilon (p : R) : R := if p = 0 then 1 else 0

/-- The pair product in eq. [35] (p. 147), with its printed epsilon.
For a=b this is the same-arm term; a=true,b=false is the cross-arm term. -/
def estimatedPair (D : Design Ω I R) (a b : Bool) (y1 y0 : I → R)
    (w : Ω) (i j : I) : R :=
  indicator D a w i * indicator D b w j / (joint D a b i j + epsilon (joint D a b i j)) *
  (joint D a b i j - marginal D a i * marginal D b j) *
  (observed D y1 y0 w i / marginal D a i) *
  (observed D y1 y0 w j / marginal D b j)

/-- Eq. [35] as printed, p. 147. The two same-arm zero-pair bounds are
included; the missing cross-arm bound is deliberately absent. -/
def printedVariance (D : Design Ω I R) (N : ℕ) (y1 y0 : I → R) (w : Ω) : R :=
  ((∑ i, (indicator D true w i * (observed D y1 y0 w i / marginal D true i)^2 +
      indicator D false w i * (observed D y1 y0 w i / marginal D false i)^2)) +
    offSum (fun i j => estimatedPair D true true y1 y0 w i j +
      estimatedPair D false false y1 y0 w i j - 2 * estimatedPair D true false y1 y0 w i j) +
    zeroSum D true true (fun i j =>
      indicator D true w i * observed D y1 y0 w i ^ 2 / (2 * marginal D true i) +
      indicator D true w j * observed D y1 y0 w j ^ 2 / (2 * marginal D true j)) +
    zeroSum D false false (fun i j =>
      indicator D false w i * observed D y1 y0 w i ^ 2 / (2 * marginal D false i) +
      indicator D false w j * observed D y1 y0 w j ^ 2 / (2 * marginal D false j))) / (N : R)^2

/-- Eq. [34] (p. 146), using Lean's total division.
`positiveMarginals` supplies marginal positivity; `crossSupport` supplies
off-diagonal directed cross-arm joint positivity. -/
def printedCovariance (D : Design Ω I R) (y1 y0 : I → R) (w : Ω) : R :=
  offSum (fun i j =>
    indicator D true w i * indicator D false w j / joint D true false i j *
    (joint D true false i j - marginal D true i * marginal D false j) *
    (observed D y1 y0 w i / marginal D true i) *
    (observed D y1 y0 w j / marginal D false j)) -
  (∑ i, indicator D true w i * observed D y1 y0 w i ^ 2 / (2 * marginal D true i)) -
  (∑ i, indicator D false w i * observed D y1 y0 w i ^ 2 / (2 * marginal D false i))

/-- Positive directed cross-arm joint probabilities for distinct units or
clusters (H+ in P026-T3). Marginal positivity is specified separately by
`positiveMarginals`. -/
def crossSupport (D : Design Ω I R) : Prop :=
  ∀ i j, i ≠ j → 0 < joint D true false i j

/-- Missing cross-arm square bound, P026-T2(d)-(e), replacing eqs. [34]-[35]. -/
def crossCorrection (D : Design Ω I R) (y1 y0 : I → R) (w : Ω) : R :=
  zeroSum D true false (fun i j =>
    indicator D true w i * observed D y1 y0 w i ^ 2 / marginal D true i +
    indicator D false w j * observed D y1 y0 w j ^ 2 / marginal D false j)

/-- Corrected covariance estimator Cov_C^+ (P026-T2(d)); zero joints are
omitted from the product sum and receive the additional Young square bound. -/
def correctedCovariance (D : Design Ω I R) (y1 y0 : I → R) (w : Ω) : R :=
  printedCovariance D y1 y0 w - crossCorrection D y1 y0 w / 2

/-- Corrected Var_C^+ = printed eq. [35] + N^(-2) times the missing
cross-arm square bound (P026-T2(e)). -/
def correctedVariance (D : Design Ω I R) (N : ℕ) (y1 y0 : I → R) (w : Ω) : R :=
  printedVariance D N y1 y0 w + crossCorrection D y1 y0 w / (N : R)^2

/-- Appendix E's unnumbered display (p. 152), literally printed: the
treatment-variance diagonal and same-arm product terms, minus the two
covariance square penalties. This is distinct from eq. [34]. -/
def appendixEPrinted (D : Design Ω I R) (y1 y0 : I → R) (w : Ω) : R :=
  (∑ i, indicator D true w i * (1 - marginal D true i) *
    (observed D y1 y0 w i / marginal D true i)^2) +
  offSum (fun i j => if 0 < joint D true true i j then
    estimatedPair D true true y1 y0 w i j else 0) -
  (∑ i, indicator D true w i * observed D y1 y0 w i ^ 2 / (2 * marginal D true i)) -
  (∑ i, indicator D false w i * observed D y1 y0 w i ^ 2 / (2 * marginal D false i))

/-- Finite expectation is linear; the exact finite step used in eq. [5]. -/
theorem expectation_sub (D : Design Ω I R) (f g : Ω → R) :
    expectation D (fun w => f w - g w) = expectation D f - expectation D g := by
  simp [expectation, mul_sub, sum_sub_distrib]

/-- Finite expectation commutes with addition, as used in Appendix B, eq. [39]. -/
theorem expectation_add (D : Design Ω I R) (f g : Ω → R) :
    expectation D (fun w => f w + g w) = expectation D f + expectation D g := by
  simp [expectation, mul_add, sum_add_distrib]

/-- Finite expectation commutes with fixed scalar division, eq. [5]. -/
theorem expectation_div (D : Design Ω I R) (f : Ω → R) (c : R) :
    expectation D (fun w => f w / c) = expectation D f / c := by
  simp only [expectation, div_eq_mul_inv, ← mul_assoc, ← sum_mul]

/-- Finite expectation commutes with fixed right multiplication, Appendix B. -/
theorem expectation_mul_const (D : Design Ω I R) (f : Ω → R) (c : R) :
    expectation D (fun w => f w * c) = expectation D f * c := by
  simp only [expectation, ← mul_assoc, ← sum_mul]

/-- Finite expectation commutes with a finite sum; Appendix B, eq. [39]. -/
theorem expectation_sum {J : Type*} [Fintype J] (D : Design Ω I R) (f : J → Ω → R) :
    expectation D (fun w => ∑ i, f i w) = ∑ i, expectation D (f i) := by
  simp only [expectation, mul_sum]
  rw [sum_comm]

/-- The fixed population total is estimated without bias by its HT total;
p. 139, eqs. [6]-[7], with no assumptions on dependence of assignments. -/
theorem htTotal_unbiased (D : Design Ω I R) (a : Bool) (y : I → R)
    (h : ∀ i, marginal D a i ≠ 0) :
    expectation D (htTotal D a y) = populationTotal y := by
  unfold htTotal
  rw [expectation_sum]
  unfold populationTotal
  apply sum_congr rfl
  intro i _
  rw [expectation_div, expectation_mul_const]
  change marginal D a i * y i / marginal D a i = y i
  field_simp [h i]

/-- P026-T20, eqs. [5]-[8]: both HT totals and the ATE estimator are
unbiased for every finite design with positive marginals. -/
theorem ht_unbiased (D : Design Ω I R) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N : ℕ) (hN : 0 < N) (y1 y0 : I → R) :
    expectation D (htTotal D true y1) = populationTotal y1 ∧
    expectation D (htTotal D false y0) = populationTotal y0 ∧
    expectation D (ht D N y1 y0) = ate N y1 y0 := by
  have h1 := htTotal_unbiased D true y1 (fun i => ne_of_gt (hp i).1)
  have h0 := htTotal_unbiased D false y0 (fun i => ne_of_gt (hp i).2)
  refine ⟨h1, h0, ?_⟩
  change expectation D (fun w => (htTotal D true y1 w - htTotal D false y0 w) / (N : R)) = _
  rw [expectation_div, expectation_sub, h1, h0]
  rfl

/-- Counterexample A in P026-T1: assignments 00,01,11, each of weight 1/3;
two singleton clusters (Section 6.3), all potential outcomes one. -/
def asymmetricTwo : Design (Fin 3) (Fin 2) ℚ where
  weight := fun _ => 1/3
  treatment := ![![false, false], ![false, true], ![true, true]]

/-- P026-T1(A): every hypothesis of the printed positivity deduction and
sharp-null variance claim holds, but the directed joint is zero and the
printed variance estimate has expectation 23/8 < true variance 27/8.
The covariance continuation has expectation -9/4 > -13/4. -/
theorem asymmetricTwo_counterexample :
    probabilityDesign asymmetricTwo ∧ positiveMarginals asymmetricTwo ∧
    (∀ i j : Fin 2, i ≠ j → 0 < disagreement asymmetricTwo i j ∧
      0 < joint asymmetricTwo true true i j ∧ 0 < joint asymmetricTwo false false i j) ∧
    joint asymmetricTwo true false 0 1 = 0 ∧
    joint asymmetricTwo true false 1 0 = 1/3 ∧
    (∀ w : Fin 3, indicator asymmetricTwo true w 0 * indicator asymmetricTwo false w 1 = 0) ∧
    (∀ w : Fin 3, ht asymmetricTwo 2 (fun _ => 1) (fun _ => 1) w = (![-9/4, 0, 9/4] : Fin 3 → ℚ) w) ∧
    (∀ w : Fin 3, printedVariance asymmetricTwo 2 (fun _ => 1) (fun _ => 1) w = (![57/16, 3/2, 57/16] : Fin 3 → ℚ) w) ∧
    expectation asymmetricTwo (ht asymmetricTwo 2 (fun _ => 1) (fun _ => 1)) = 0 ∧
    variance asymmetricTwo (ht asymmetricTwo 2 (fun _ => 1) (fun _ => 1)) = 27/8 ∧
    expectation asymmetricTwo (printedVariance asymmetricTwo 2 (fun _ => 1) (fun _ => 1)) = 23/8 ∧
    (23/8 : ℚ) < 27/8 ∧
    covariance asymmetricTwo (htTotal asymmetricTwo true (fun _ => 1))
      (htTotal asymmetricTwo false (fun _ => 1)) = -13/4 ∧
    expectation asymmetricTwo (printedCovariance asymmetricTwo (fun _ => 1) (fun _ => 1)) = -9/4 ∧
    (-13/4 : ℚ) < -9/4 := by
  unfold probabilityDesign positiveMarginals
  decide +kernel

/-- Joint probabilities are nonnegative in every finite probability design;
standing assumptions, Section 4, p. 138. -/
theorem joint_nonneg (D : Design Ω I R) (hD : probabilityDesign D)
    (a b : Bool) (i j : I) : 0 ≤ joint D a b i j := by
  unfold joint expectation
  apply sum_nonneg
  intro w _
  apply mul_nonneg (hD.1 w)
  simp only [indicator]
  split_ifs <;> norm_num

/-- P026-T2(a): Pr(T'_k ≠ T'_l) is the sum of the two directed
cross-arm joints; this replaces the false inference before eq. [30], p. 145. -/
theorem disagreement_identity (D : Design Ω I R) (i j : I) :
    disagreement D i j = joint D true false i j + joint D true false j i := by
  have h : (fun w => if D.treatment w i ≠ D.treatment w j then (1 : R) else 0) =
      (fun w => indicator D true w i * indicator D false w j +
        indicator D true w j * indicator D false w i) := by
    funext w
    cases hi : D.treatment w i <;> cases hj : D.treatment w j <;> simp [indicator, hi, hj]
  unfold disagreement joint
  rw [h, expectation_add]

/-- P026-T2(a): positive disagreement is equivalent to at least one
positive direction, rather than to positivity of both directions. -/
theorem disagreement_positive_iff (D : Design Ω I R) (hD : probabilityDesign D)
    (i j : I) : 0 < disagreement D i j ↔
      0 < joint D true false i j ∨ 0 < joint D true false j i := by
  rw [disagreement_identity]
  have h1 := joint_nonneg D hD true false i j
  have h2 := joint_nonneg D hD true false j i
  constructor
  · intro h
    by_cases hh : 0 < joint D true false i j
    · exact Or.inl hh
    · exact Or.inr (by linarith)
  · intro h
    rcases h with h | h <;> linarith

/-- Diagonal same-arm joint inclusion equals its marginal; used in
eqs. [21]-[22] and [27]-[28], pp. 143,145. -/
theorem joint_diagonal (D : Design Ω I R) (a : Bool) (i : I) :
    joint D a a i i = marginal D a i := by
  unfold joint marginal expectation
  apply sum_congr rfl
  intro w _
  simp only [indicator]
  split_ifs <;> simp

/-- A unit cannot receive both arms: π_1i0i=0, eqs. [23] and [30], pp. 143,145. -/
theorem cross_diagonal (D : Design Ω I R) (i : I) :
    joint D true false i i = 0 := by
  unfold joint expectation
  have h (w : Ω) : indicator D true w i * indicator D false w i = 0 := by
    cases hi : D.treatment w i <;> simp [indicator, hi]
  simp [h]

/-- E[c]=c on a probability design; the finite version of the standing
fixed-potential-outcome convention, Section 3, p. 138. -/
theorem expectation_const (D : Design Ω I R) (hD : probabilityDesign D) (c : R) :
    expectation D (fun _ => c) = c := by
  simp only [expectation, ← sum_mul, hD.2, one_mul]

/-- Scalar bilinearity of covariance, used in eqs. [21]-[23], p. 143. -/
theorem covariance_scale (D : Design Ω I R) (f g : Ω → R) (a b : R) :
    covariance D (fun w => f w * a) (fun w => g w * b) =
      covariance D f g * a * b := by
  have h : (fun w => f w * a * (g w * b)) = (fun w => (f w * g w) * (a * b)) := by
    funext w
    ring
  unfold covariance
  rw [h, expectation_mul_const, expectation_mul_const, expectation_mul_const]
  ring

/-- Bilinearity over finite sums; exact finite expansion behind
eqs. [21]-[23] and [27]-[29], pp. 143,145. -/
theorem covariance_sum (D : Design Ω I R) (f g : I → Ω → R) :
    covariance D (fun w => ∑ i, f i w) (fun w => ∑ j, g j w) =
      ∑ i, ∑ j, covariance D (f i) (g j) := by
  have h : (fun w => (∑ i, f i w) * (∑ j, g j w)) =
      (fun w => ∑ i, ∑ j, f i w * g j w) := by
    funext w
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
  unfold covariance
  rw [h, expectation_sum]
  simp only [expectation_sum, sum_mul, mul_sum, sum_sub_distrib]
  rw [sum_comm (f := fun i j => expectation D (f j) * expectation D (g i))]

/-- Full double sum separates into diagonal and ordered off-diagonal sum;
the reindexing in eq. [21], p. 143. -/
theorem sum_diagonal_off (f : I → I → R) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) + offSum f := by
  unfold offSum
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_erase_add _ _ (mem_univ i)]
  ring

/-- Full joint-probability covariance of the two HT totals, eq. [23] at
unit level and eq. [29] at cluster level (pp. 143,145). -/
theorem ht_covariance_full (D : Design Ω I R) (a b : Bool) (x z : I → R) :
    covariance D (htTotal D a x) (htTotal D b z) =
      ∑ i, ∑ j, (joint D a b i j - marginal D a i * marginal D b j) *
        (x i / marginal D a i) * (z j / marginal D b j) := by
  have h (a : Bool) (x : I → R) : htTotal D a x =
      (fun w => ∑ i, indicator D a w i * (x i / marginal D a i)) := by
    funext w
    simp only [htTotal, mul_div_assoc]
  rw [h a x, h b z, covariance_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [covariance_scale]
  rfl

/-- Printed diagonal/off-diagonal arm-variance expression, eqs. [21],
[22], [27], [28], pp. 143,145. -/
def armVarianceExpression (D : Design Ω I R) (a : Bool) (y : I → R) : R :=
  (∑ i, marginal D a i * (1 - marginal D a i) * (y i / marginal D a i)^2) +
  offSum (fun i j => (joint D a a i j - marginal D a i * marginal D a j) *
    (y i / marginal D a i) * (y j / marginal D a j))

/-- P026-T12(b,c), T11(b), T24(b): the sampling variance of either
HT total is the exact printed arm-variance expression, with arbitrary design. -/
theorem ht_arm_variance (D : Design Ω I R) (a : Bool) (y : I → R) :
    variance D (htTotal D a y) = armVarianceExpression D a y := by
  unfold variance
  rw [ht_covariance_full, sum_diagonal_off]
  unfold armVarianceExpression
  congr 1
  apply sum_congr rfl
  intro i _
  rw [joint_diagonal]
  ring

/-- Off-diagonal population cross covariance and its diagonal product;
eq. [30] (p. 145), valid even for zero directed off-diagonal probabilities. -/
def clusterCovarianceExpression (D : Design Ω I R) (x z : I → R) : R :=
  offSum (fun i j => (joint D true false i j - marginal D true i * marginal D false j) *
    (x i / marginal D true i) * (z j / marginal D false j)) - ∑ i, x i * z i

/-- P026-T2(b), T8(a), T24(b): eq. [30] remains valid without the
paper's false cross-arm positivity inference. -/
theorem ht_cluster_covariance (D : Design Ω I R) (hp : positiveMarginals D)
    (x z : I → R) : covariance D (htTotal D true x) (htTotal D false z) =
      clusterCovarianceExpression D x z := by
  rw [ht_covariance_full, sum_diagonal_off]
  unfold clusterCovarianceExpression
  have h : (∑ i, (joint D true false i i - marginal D true i * marginal D false i) *
      (x i / marginal D true i) * (z i / marginal D false i)) = -(∑ i, x i * z i) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    rw [cross_diagonal]
    field_simp [ne_of_gt (hp i).1, ne_of_gt (hp i).2]
    ring
  rw [h]
  ring

/-- P026-T1(B), six-cluster design: the fourteen printed binary
vectors, uniform, with exactly three treated and T'_1≤T'_2. -/
def asymmetricSix : Design (Fin 14) (Fin 6) ℚ where
  weight := fun _ => 1/14
  treatment := ![
    ![false,false,false,true,true,true], ![false,false,true,false,true,true],
    ![false,false,true,true,false,true], ![false,false,true,true,true,false],
    ![false,true,false,false,true,true], ![false,true,false,true,false,true],
    ![false,true,false,true,true,false], ![false,true,true,false,false,true],
    ![false,true,true,false,true,false], ![false,true,true,true,false,false],
    ![true,true,false,false,false,true], ![true,true,false,false,true,false],
    ![true,true,false,true,false,false], ![true,true,true,false,false,false]]

/-- P026-T1(B): the six-cluster counterexample satisfies positive
marginals, positive same-arm joints, distinct indicators, and fixed nonempty
arms. Its printed eq. [35] has negative expectation -269/6300, although
the true variance is 9/700; eq. [34]'s continuation has covariance bias +1. -/
theorem asymmetricSix_counterexample :
    probabilityDesign asymmetricSix ∧ positiveMarginals asymmetricSix ∧
    (∀ w : Fin 14, (∑ i : Fin 6, indicator asymmetricSix true w i) = 3) ∧
    (∀ i j : Fin 6, i ≠ j → 0 < disagreement asymmetricSix i j ∧
      0 < joint asymmetricSix true true i j ∧ 0 < joint asymmetricSix false false i j) ∧
    (∀ i j : Fin 6, i ≠ j → (joint asymmetricSix true false i j = 0 ↔ i = 0 ∧ j = 1)) ∧
    variance asymmetricSix (ht asymmetricSix 6 (fun _ => 1) (fun _ => 1)) = 9/700 ∧
    expectation asymmetricSix (printedVariance asymmetricSix 6 (fun _ => 1) (fun _ => 1)) = -269/6300 ∧
    (-269/6300 : ℚ) < 9/700 ∧
    covariance asymmetricSix (htTotal asymmetricSix true (fun _ => 1))
      (htTotal asymmetricSix false (fun _ => 1)) = 27/175 ∧
    expectation asymmetricSix (printedCovariance asymmetricSix (fun _ => 1) (fun _ => 1)) = 202/175 := by
  unfold probabilityDesign positiveMarginals
  decide +kernel

/-- XOR written as Q(u,v)=u+v-2uv; fitting rule in the exact witnesses
for Section 5.1, p. 142, P026-T4. -/
def xorPolynomial (u v : ℚ) : ℚ := u + v - 2*u*v

/-- P026-T4(A): four equiprobable six-unit assignments (A,1-A,B,1-B,
A XOR B,1-(A XOR B)), always three treated and three control. -/
def xorSix : Design (Fin 4) (Fin 6) ℚ where
  weight := fun _ => 1/4
  treatment := ![![false,true,false,true,false,true], ![false,true,true,false,true,false],
    ![true,false,false,true,true,false], ![true,false,true,false,false,true]]

/-- θ_i is a fixed XOR function of two observed outcomes belonging to
the fitting set {Y_j:T_i independent T_j}; P026-T4(A), Section 5.1, p. 142.
Y_1j=1,Y_0j=0, so the observed outcomes are the treatment indicators. -/
def xorSixPrediction (w : Fin 4) : Fin 6 → ℚ :=
  let y := observed xorSix (fun _ => 1) (fun _ => 0) w
  ![xorPolynomial (y 2) (y 4), 1-xorPolynomial (y 2) (y 4),
    xorPolynomial (y 0) (y 4), 1-xorPolynomial (y 0) (y 4),
    xorPolynomial (y 0) (y 2), 1-xorPolynomial (y 0) (y 2)]

/-- P026-T4(A): all fitting assignments are pairwise independent of
their focal assignment (all four cells 1/4). Nevertheless θ_i=T_i,
Cov(T_i,f_i)=1/4, both generalized totals are 3, and the ATE estimate
is always zero although Δ=1. Refutes the printed general fitting rule. -/
theorem xorSix_counterexample :
    probabilityDesign xorSix ∧ positiveMarginals xorSix ∧
    (∀ i : Fin 6, marginal xorSix true i = 1/2 ∧ marginal xorSix false i = 1/2) ∧
    (∀ i j : Fin 6, i.val / 2 ≠ j.val / 2 →
      ∀ a b : Bool, joint xorSix a b i j = 1/4) ∧
    (∀ w : Fin 4, (∑ i : Fin 6, indicator xorSix true w i) = 3) ∧
    (∀ w i, xorSixPrediction w i = indicator xorSix true w i) ∧
    (∀ i, covariance xorSix (fun w => indicator xorSix true w i)
      (fun w => xorSixPrediction w i) = 1/4) ∧
    (∀ w, generalizedTotal xorSix true (fun _ => 1) xorSixPrediction w = 3 ∧
      generalizedTotal xorSix false (fun _ => 0) xorSixPrediction w = 3 ∧
      generalized xorSix 6 (fun _ => 1) (fun _ => 0) xorSixPrediction w = 0 ∧
      ht xorSix 6 (fun _ => 1) (fun _ => 0) w = 1) ∧
    ate 6 (fun _ : Fin 6 => (1 : ℚ)) (fun _ => 0) = 1 ∧
    expectation xorSix (generalized xorSix 6 (fun _ => 1) (fun _ => 0) xorSixPrediction) -
      ate 6 (fun _ : Fin 6 => (1 : ℚ)) (fun _ => 0) = -1 := by
  unfold probabilityDesign positiveMarginals
  decide +kernel

/-- P026-T4(B): the smaller pairwise independent XOR design 000,011,101,110. -/
def xorThree : Design (Fin 4) (Fin 3) ℚ where
  weight := fun _ => 1/4
  treatment := ![![false,false,false], ![false,true,true],
    ![true,false,true], ![true,true,false]]

/-- P026-T4(B-i): predictions are XORs of the other two observed outcomes. -/
def xorThreePrediction (w : Fin 4) : Fin 3 → ℚ :=
  let y := observed xorThree (fun _ => 1) (fun _ => 0) w
  ![xorPolynomial (y 1) (y 2), xorPolynomial (y 0) (y 2), xorPolynomial (y 0) (y 1)]

/-- P026-T4(B-ii): the alternative prediction f_3=Y_1Y_2, f_1=f_2=0. -/
def productPrediction (w : Fin 4) : Fin 3 → ℚ :=
  ![0,0,observed xorThree (fun _ => 1) (fun _ => 0) w 0 *
    observed xorThree (fun _ => 1) (fun _ => 0) w 1]

/-- P026-T4(B): pairwise independence fails to protect nonlinear
predictions: XOR produces bias -1, and the product produces bias +1/6. -/
theorem xorThree_counterexamples :
    probabilityDesign xorThree ∧ positiveMarginals xorThree ∧
    (∀ i j : Fin 3, i ≠ j → ∀ a b : Bool, joint xorThree a b i j = 1/4) ∧
    (∀ w i, xorThreePrediction w i = indicator xorThree true w i) ∧
    (∀ i, covariance xorThree (fun w => indicator xorThree true w i)
      (fun w => xorThreePrediction w i) = 1/4) ∧
    expectation xorThree (generalized xorThree 3 (fun _ => 1) (fun _ => 0) xorThreePrediction) = 0 ∧
    covariance xorThree (fun w => indicator xorThree true w 2)
      (fun w => productPrediction w 2) = -1/8 ∧
    expectation xorThree (generalized xorThree 3 (fun _ => 1) (fun _ => 0) productPrediction) = 7/6 ∧
    ate 3 (fun _ : Fin 3 => (1 : ℚ)) (fun _ => 0) = 1 := by
  unfold probabilityDesign positiveMarginals
  decide +kernel

/-- Uniformly treat two of four singleton clusters; Appendix E
counterexample in P026-T9 (six explicitly listed allocations). -/
def twoOfFour : Design (Fin 6) (Fin 4) ℚ where
  weight := fun _ => 1/6
  treatment := ![![true,true,false,false], ![true,false,true,false], ![true,false,false,true],
    ![false,true,true,false], ![false,true,false,true], ![false,false,true,true]]

/-- Fixed sharp-null cluster totals (1,2,4,7), P026-T9. -/
def appendixOutcomes : Fin 4 → ℚ := ![1,2,4,7]

/-- P026-T9: on full off-diagonal support, the literal Appendix E
display has expectation -42 rather than the stated covariance bound -28;
the intended eq. [34] has mean -28 and the treatment-total variance is 28. -/
theorem appendixE_counterexample :
    probabilityDesign twoOfFour ∧ positiveMarginals twoOfFour ∧ crossSupport twoOfFour ∧
    (∀ i j : Fin 4, i ≠ j → joint twoOfFour true true i j = 1/6 ∧
      joint twoOfFour false false i j = 1/6 ∧ joint twoOfFour true false i j = 1/3) ∧
    (∀ w, appendixEPrinted twoOfFour appendixOutcomes appendixOutcomes w =
      (![-68,-52,2,-62,-20,-52] : Fin 6 → ℚ) w) ∧
    expectation twoOfFour (appendixEPrinted twoOfFour appendixOutcomes appendixOutcomes) = -42 ∧
    covariance twoOfFour (htTotal twoOfFour true appendixOutcomes)
      (htTotal twoOfFour false appendixOutcomes) = -28 ∧
    clusterCovarianceExpression twoOfFour appendixOutcomes appendixOutcomes = -28 ∧
    expectation twoOfFour (printedCovariance twoOfFour appendixOutcomes appendixOutcomes) = -28 ∧
    variance twoOfFour (htTotal twoOfFour true appendixOutcomes) = 28 ∧
    (-42 : ℚ) ≠ -28 := by
  unfold probabilityDesign positiveMarginals crossSupport
  decide +kernel

/-- Uniform complete assignment of one of three units; package
`estate(HT=TRUE,X supplied)` counterexample P026-T15. -/
def oneOfThree : Design (Fin 3) (Fin 3) ℚ where
  weight := fun _ => 1/3
  treatment := fun w i => decide (w = i)

/-- Fitted values from the exact intercept-and-slope OLS solution of
`lm(Y~X)` for X=(0,1,2), Y=T (P026-T15, ri package estate's Raj-Within branch). -/
def packageFit (w : Fin 3) (i : Fin 3) : ℚ :=
  (![5/6,1/3,-1/6] : Fin 3 → ℚ) w + (![-1/2,0,1/2] : Fin 3 → ℚ) w * i.val

/-- P026-T15: full-rank OLS fits satisfy both normal equations. The
adjusted package estimates are (1/4,1,1/4), with mean 1/2 and bias -1/2
although the ATE and unadjusted HT estimates equal one. -/
theorem package_counterexample :
    probabilityDesign oneOfThree ∧ positiveMarginals oneOfThree ∧
    (∀ i, marginal oneOfThree true i = 1/3 ∧ marginal oneOfThree false i = 2/3) ∧
    (∀ w, (∑ i : Fin 3, (observed oneOfThree (fun _ => 1) (fun _ => 0) w i - packageFit w i)) = 0 ∧
      (∑ i : Fin 3, (i.val : ℚ) * (observed oneOfThree (fun _ => 1) (fun _ => 0) w i - packageFit w i)) = 0) ∧
    ((3*5-3^2 : ℚ) = 6) ∧
    (∀ w, generalized oneOfThree 3 (fun _ => 1) (fun _ => 0) packageFit w =
      (![1/4,1,1/4] : Fin 3 → ℚ) w) ∧
    (∀ i, covariance oneOfThree (fun w => indicator oneOfThree true w i)
      (fun w => packageFit w i) = (![1/6,0,1/6] : Fin 3 → ℚ) i) ∧
    expectation oneOfThree (generalized oneOfThree 3 (fun _ => 1) (fun _ => 0) packageFit) = 1/2 ∧
    ate 3 (fun _ : Fin 3 => (1 : ℚ)) (fun _ => 0) = 1 ∧
    (∀ w, ht oneOfThree 3 (fun _ => 1) (fun _ => 0) w = 1) ∧
    (1/2 : ℚ) ≠ 1 := by
  unfold probabilityDesign positiveMarginals
  decide +kernel

/-- The observed HT sum equals the potential-outcome HT sum, eqs. [6]-[7],
p. 139. This masking fact also justifies every variance estimator's use of Y. -/
theorem observed_mask (D : Design Ω I R) (a : Bool) (y1 y0 : I → R)
    (w : Ω) (i : I) : indicator D a w i * observed D y1 y0 w i =
      indicator D a w i * (if a then y1 i else y0 i) := by
  cases a <;> cases hi : D.treatment w i <;> simp [indicator, observed, hi]

/-- The generalized estimator is the HT contrast of residual outcomes,
eq. [25], p. 144. This identity allows assignment-dependent predictions. -/
theorem generalized_residual (D : Design Ω I R) (N : ℕ) (y1 y0 : I → R)
    (f : Ω → I → R) (w : Ω) : generalized D N y1 y0 f w =
      ht D N (fun i => y1 i - f w i) (fun i => y0 i - f w i) w := by
  unfold generalized generalizedTotal ht htTotal
  simp only [mul_sub, sub_div, sum_add_distrib, sum_sub_distrib]
  ring

/-- Eq. [16], p. 141: the generalized estimate is HT minus the
inverse-probability-weighted prediction contrast, on every assignment. -/
theorem generalized_adjustment (D : Design Ω I R) (N : ℕ) (y1 y0 : I → R)
    (f : Ω → I → R) (w : Ω) : generalized D N y1 y0 f w = ht D N y1 y0 w -
      (htTotal D true (f w) w - htTotal D false (f w) w) / N := by
  unfold generalized generalizedTotal ht htTotal
  simp only [sum_add_distrib, sum_sub_distrib]
  ring

/-- P026-T13(a,b), corrected eqs. [17]-[18], pp. 141-142: the
expectation of a generalized total equals the population total minus its
indicator/prediction covariance sum. The expectation covers all three sums. -/
theorem generalized_total_bias (D : Design Ω I R) (a : Bool) (y : I → R)
    (f : Ω → I → R) (hp : ∀ i, marginal D a i ≠ 0) :
    expectation D (generalizedTotal D a y f) = populationTotal y -
      ∑ i, covariance D (fun w => indicator D a w i)
        (fun w => f w i / marginal D a i) := by
  unfold generalizedTotal populationTotal
  rw [expectation_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [expectation_add, expectation_sub, expectation_div, expectation_mul_const]
  have h : (fun w => indicator D a w i * f w i / marginal D a i) =
      (fun w => indicator D a w i * (f w i / marginal D a i)) := by
    funext w
    exact mul_div_assoc _ _ _
  rw [h]
  unfold covariance
  rw [expectation_div]
  change marginal D a i * y i / marginal D a i -
    expectation D (fun w => indicator D a w i * (f w i / marginal D a i)) +
    expectation D (fun w => f w i) = y i -
      (expectation D (fun w => indicator D a w i * (f w i / marginal D a i)) -
        marginal D a i * (expectation D (fun w => f w i) / marginal D a i))
  field_simp [hp i]
  ring

/-- P026-T13(c), eq. [19], p. 142: exact ATE bias for any
randomization-dependent predictions, without an independence premise. -/
theorem generalized_bias (D : Design Ω I R) (hp : positiveMarginals D)
    (N : ℕ) (hN : 0 < N) (y1 y0 : I → R) (f : Ω → I → R) :
    expectation D (generalized D N y1 y0 f) - ate N y1 y0 =
      ((∑ i, covariance D (fun w => indicator D false w i)
        (fun w => f w i / marginal D false i)) -
       (∑ i, covariance D (fun w => indicator D true w i)
        (fun w => f w i / marginal D true i))) / N := by
  change expectation D (fun w => (generalizedTotal D true y1 f w -
    generalizedTotal D false y0 f w) / (N : R)) - ate N y1 y0 = _
  rw [expectation_div, expectation_sub,
    generalized_total_bias D true y1 f (fun i => ne_of_gt (hp i).1),
    generalized_total_bias D false y0 f (fun i => ne_of_gt (hp i).2)]
  unfold ate
  ring

/-- Right scalar division for covariance, the factor 1/π in eqs. [17]-[19]. -/
theorem covariance_div_right (D : Design Ω I R) (f g : Ω → R) (c : R) :
    covariance D f (fun w => g w / c) = covariance D f g / c := by
  simpa only [mul_one, ← div_eq_mul_inv] using covariance_scale D f g 1 c⁻¹

/-- In the paper's two-arm designs, the control indicator is 1-T_i
(p. 138, Section 4). -/
theorem indicator_complement (D : Design Ω I R) (w : Ω) (i : I) :
    indicator D false w i = 1 - indicator D true w i := by
  cases hi : D.treatment w i <;> simp [indicator, hi]

/-- Cov(1-T_i,f_i)=-Cov(T_i,f_i), the two-arm simplification of
eq. [19] and the control step in Appendix B (pp. 142,150). -/
theorem control_covariance (D : Design Ω I R) (hD : probabilityDesign D)
    (i : I) (f : Ω → R) : covariance D (fun w => indicator D false w i) f =
      -covariance D (fun w => indicator D true w i) f := by
  have h : (fun w => indicator D false w i * f w) =
      (fun w => f w - indicator D true w i * f w) := by
    funext w
    rw [indicator_complement]
    ring
  unfold covariance
  rw [h, expectation_sub]
  have hi : (fun w => indicator D false w i) = (fun w => 1 - indicator D true w i) := by
    funext w
    exact indicator_complement D w i
  rw [hi, expectation_sub, expectation_const D hD]
  ring

/-- P026-T13(c) and T16(b): two-arm exact bias is
-N⁻¹∑ Cov(T_i,f_i)(1/π_1i+1/π_0i), including fitted package predictions. -/
theorem generalized_bias_two_arm (D : Design Ω I R) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N : ℕ) (hN : 0 < N) (y1 y0 : I → R)
    (f : Ω → I → R) : expectation D (generalized D N y1 y0 f) - ate N y1 y0 =
      -(∑ i, covariance D (fun w => indicator D true w i) (fun w => f w i) *
        (1 / marginal D true i + 1 / marginal D false i)) / N := by
  rw [generalized_bias D hp N hN]
  simp only [covariance_div_right, control_covariance D hD]
  congr 1
  rw [← sum_sub_distrib, ← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  ring

/-- P026-T22, Appendix B, eqs. [39]-[40] and [5],[15]: zero
assignment/prediction covariance for each unit makes both generalized
totals and the ATE estimate unbiased. -/
theorem generalized_unbiased (D : Design Ω I R) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N : ℕ) (hN : 0 < N) (y1 y0 : I → R)
    (f : Ω → I → R)
    (hf : ∀ i, covariance D (fun w => indicator D true w i) (fun w => f w i) = 0) :
    expectation D (generalizedTotal D true y1 f) = populationTotal y1 ∧
    expectation D (generalizedTotal D false y0 f) = populationTotal y0 ∧
    expectation D (generalized D N y1 y0 f) = ate N y1 y0 := by
  have h1 : expectation D (generalizedTotal D true y1 f) = populationTotal y1 := by
    rw [generalized_total_bias D true y1 f (fun i => ne_of_gt (hp i).1)]
    simp [covariance_div_right, hf]
  have h0 : expectation D (generalizedTotal D false y0 f) = populationTotal y0 := by
    rw [generalized_total_bias D false y0 f (fun i => ne_of_gt (hp i).2)]
    simp [covariance_div_right, control_covariance D hD, hf]
  refine ⟨h1,h0,?_⟩
  change expectation D (fun w => (generalizedTotal D true y1 f w -
    generalizedTotal D false y0 f w) / (N : R)) = _
  rw [expectation_div, expectation_sub, h1, h0]
  rfl

/-- Constant predictions have zero covariance with any assignment;
p. 142, the first option for deriving θ_i. -/
theorem covariance_const_right (D : Design Ω I R) (hD : probabilityDesign D)
    (f : Ω → R) (c : R) : covariance D f (fun _ => c) = 0 := by
  unfold covariance
  rw [expectation_mul_const, expectation_const D hD]
  ring

/-- P026-T16(a), and T22's fixed-prediction special case: any
pretreatment vector g gives an unbiased generalized/residual HT contrast. -/
theorem fixed_prediction_unbiased (D : Design Ω I R) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N : ℕ) (hN : 0 < N) (y1 y0 g : I → R) :
    expectation D (generalized D N y1 y0 (fun _ => g)) = ate N y1 y0 := by
  exact (generalized_unbiased D hD hp N hN y1 y0 (fun _ => g)
    (fun i => covariance_const_right D hD _ (g i))).2.2

/-- Independence in Section 5.1, p. 142: every pair of functions of the
two finite random variables has factorizing expectation. On a finite
probability space this is equivalent to factorization of every joint cell;
it works for real-valued fits and finite observed-outcome vectors alike. -/
def independent {α β : Type*} (D : Design Ω I R) (f : Ω → α) (g : Ω → β) : Prop :=
  ∀ u : α → R, ∀ v : β → R,
    expectation D (fun w => u (f w) * v (g w)) =
      expectation D (fun w => u (f w)) * expectation D (fun w => v (g w))

/-- P026-T5(a,c): independence of a focal assignment from the whole
fitting vector survives any deterministic fitting or prediction function.
This is the corrected vector version of footnote 5, p. 142. -/
theorem independent_comp {α β γ : Type*} (D : Design Ω I R)
    (f : Ω → α) (g : Ω → β) (h : independent D f g) (G : β → γ) :
    independent D f (fun w => G (g w)) := by
  intro u v
  exact h u (fun x => v (G x))

/-- Independence implies zero covariance of real-valued random variables;
Section 5.1 and footnote 5, p. 142. -/
theorem independent_covariance_zero (D : Design Ω I R) (f g : Ω → R)
    (h : independent D f g) : covariance D f g = 0 := by
  unfold covariance
  exact sub_eq_zero.mpr (by simpa only [id_eq] using h id id)

/-- Observed fitting vector (Y_j)_{j∈J_i}; corrected Section 5.1,
P026-T5. The index set is fixed before randomization. -/
def fittingOutcomes (D : Design Ω I R) (J : Finset I) (y1 y0 : I → R) (w : Ω) :
    ↥J → R := fun j => observed D y1 y0 w j

/-- Fitting assignment vector (T_j)_{j∈J_i}, P026-T5(a,c). -/
def fittingAssignments (D : Design Ω I R) (J : Finset I) (w : Ω) :
    ↥J → Bool := fun j => D.treatment w j

/-- P026-T5(a,c), corrected fitting rule: independence from the entire
assignment vector makes θ_i and its prediction independent of T_i, hence
the covariance is zero. All potential outcomes, fitting and prediction
maps are deterministic, including their fixed covariate inputs. -/
theorem vector_fitting_independence {Θ : Type*} (D : Design Ω I R) (i : I)
    (J : Finset I) (y1 y0 : I → R) (G : (↥J → R) → Θ) (P : Θ → R)
    (h : independent D (fun w => D.treatment w i) (fittingAssignments D J)) :
    independent D (fun w => D.treatment w i) (fun w => G (fittingOutcomes D J y1 y0 w)) ∧
    independent D (fun w => D.treatment w i) (fun w => P (G (fittingOutcomes D J y1 y0 w))) ∧
    covariance D (fun w => indicator D true w i)
      (fun w => P (G (fittingOutcomes D J y1 y0 w))) = 0 := by
  let H : (↥J → Bool) → (↥J → R) := fun t j => if t j then y1 j else y0 j
  have ho : independent D (fun w => D.treatment w i) (fittingOutcomes D J y1 y0) := by
    exact independent_comp D _ _ h H
  have hg := independent_comp D _ _ ho G
  have hf := independent_comp D _ _ hg P
  refine ⟨hg,hf,?_⟩
  unfold covariance
  exact sub_eq_zero.mpr (hf (fun t => if t = true then 1 else 0) id)

/-- P026-T5(a), weaker sufficient premise: independence from the whole
observed-outcome fitting vector also suffices for arbitrary deterministic fits. -/
theorem outcome_vector_fitting_independence {Θ : Type*} (D : Design Ω I R)
    (i : I) (J : Finset I) (y1 y0 : I → R) (G : (↥J → R) → Θ) (P : Θ → R)
    (h : independent D (fun w => D.treatment w i) (fittingOutcomes D J y1 y0)) :
    independent D (fun w => D.treatment w i) (fun w => G (fittingOutcomes D J y1 y0 w)) ∧
    independent D (fun w => D.treatment w i) (fun w => P (G (fittingOutcomes D J y1 y0 w))) ∧
    covariance D (fun w => indicator D true w i)
      (fun w => P (G (fittingOutcomes D J y1 y0 w))) = 0 := by
  have hg := independent_comp D _ _ h G
  have hf := independent_comp D _ _ hg P
  refine ⟨hg,hf,?_⟩
  unfold covariance
  exact sub_eq_zero.mpr (hf (fun t => if t = true then 1 else 0) id)

/-- Exact bias-square sums for the corrections P026-T2(c)-(f): the
unit/cluster effect squares and the unavailable same-arm and cross-arm pairs. -/
def correctedBiasExpression (D : Design Ω I R) (x z : I → R) : R :=
  (∑ i, (x i-z i)^2) + zeroSum D true true (fun i j => (x i+x j)^2) / 2 +
    zeroSum D false false (fun i j => (z i+z j)^2) / 2 +
    zeroSum D true false (fun i j => (x i-z j)^2)

/-- Finite sums of squares over unavailable ordered pairs are nonnegative;
the finite inequality underlying the repaired variance claim, P026-T2(e). -/
theorem zeroSum_squares_nonneg (D : Design Ω I R) (a b : Bool) (f : I → I → R) :
    0 ≤ zeroSum D a b (fun i j => (f i j)^2) := by
  unfold zeroSum offSum
  apply sum_nonneg
  intro i _
  apply sum_nonneg
  intro j _
  change 0 ≤ if joint D a b i j = 0 then (f i j)^2 else 0
  split_ifs <;> positivity

/-- P026-T2(e), finite inequality: the repaired bias expression is a
sum of nonnegative squares, without joint-support or outcome-sign assumptions. -/
theorem correctedBiasExpression_nonneg (D : Design Ω I R) (x z : I → R) :
    0 ≤ correctedBiasExpression D x z := by
  unfold correctedBiasExpression
  have h0 : 0 ≤ ∑ i, (x i-z i)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have h1 := zeroSum_squares_nonneg D true true (fun i j => x i+x j)
  have h2 := zeroSum_squares_nonneg D false false (fun i j => z i+z j)
  have h3 := zeroSum_squares_nonneg D true false (fun i j => x i-z j)
  linarith













/-- P026-T2(f), exact witness that the repaired sharp-null equality
qualification is necessary: same six-cluster design, null totals (1,2,1,1,1,1). -/
theorem repaired_sharp_null_strict_bias :
    variance asymmetricSix (ht asymmetricSix 6 (![1,2,1,1,1,1]) (![1,2,1,1,1,1])) = 2759/12600 ∧
    expectation asymmetricSix (printedVariance asymmetricSix 6 (![1,2,1,1,1,1]) (![1,2,1,1,1,1])) = 151/1400 ∧
    expectation asymmetricSix (correctedVariance asymmetricSix 6 (![1,2,1,1,1,1]) (![1,2,1,1,1,1])) = 3109/12600 ∧
    (2759/12600 : ℚ) < 3109/12600 := by
  decide +kernel




/-- Population covariance lower bound Cov_C in Appendix E, eq. [43],
p. 152. This deterministic bound includes all off-diagonal product terms. -/
def covarianceBound (D : Design Ω I R) (x z : I → R) : R :=
  offSum (fun i j => (joint D true false i j - marginal D true i * marginal D false j) *
    (x i / marginal D true i) * (z j / marginal D false j)) -
    (∑ i, (x i)^2 / 2) - (∑ i, (z i)^2 / 2)

/-- P026-T8(b): Young's population bound [43] differs from the true
covariance by exactly one half of the within-cluster squared effect sum. -/
theorem covariance_bound_gap (D : Design Ω I R) (hp : positiveMarginals D) (x z : I → R) :
    covariance D (htTotal D true x) (htTotal D false z) - covarianceBound D x z =
      (∑ i, (x i-z i)^2) / 2 := by
  rw [ht_cluster_covariance D hp]
  unfold clusterCovarianceExpression covarianceBound
  have h : (∑ i, (x i-z i)^2) / 2 =
      (∑ i, (x i)^2 / 2) + (∑ i, (z i)^2 / 2) - ∑ i, x i*z i := by
    rw [sum_div, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [h]
  ring




/-- Same-arm conservative population upper bound in Appendix D,
pp. 151-152: replace each unavailable pair product by its Young square bound. -/
def armVarianceBound (D : Design Ω I R) (a : Bool) (y : I → R) : R :=
  (∑ i, marginal D a i * (1-marginal D a i) * (y i / marginal D a i)^2) +
  offSum (fun i j => if 0 < joint D a a i j then
    (joint D a a i j-marginal D a i*marginal D a j) *
      (y i/marginal D a i)*(y j/marginal D a j) else 0) +
  zeroSum D a a (fun i j => (y i)^2/2+(y j)^2/2)

/-- Correct cluster indicators in the Appendix D estimator display
(p. 152): eq. [32], and its control analogue [33] (p. 146). -/
def armVarianceEstimator (D : Design Ω I R) (a : Bool) (y1 y0 : I → R) (w : Ω) : R :=
  (∑ i, indicator D a w i * (1-marginal D a i) *
    (observed D y1 y0 w i / marginal D a i)^2) +
  offSum (fun i j => if 0 < joint D a a i j then estimatedPair D a a y1 y0 w i j else 0) +
  zeroSum D a a (fun i j => indicator D a w i * observed D y1 y0 w i ^ 2 / (2*marginal D a i) +
    indicator D a w j * observed D y1 y0 w j ^ 2 / (2*marginal D a j))




/-- The basic difference-of-totals variance identity, eq. [20], p. 143. -/
theorem variance_sub (D : Design Ω I R) (f g : Ω → R) :
    variance D (fun w => f w-g w) = variance D f + variance D g - 2*covariance D f g := by
  have h : (fun w => (f w-g w)*(f w-g w)) =
      (fun w => (f w*f w+g w*g w)-(f w*g w)*2) := by
    funext w
    ring
  unfold variance covariance
  rw [h, expectation_sub, expectation_add, expectation_mul_const, expectation_sub]
  ring

/-- P026-T12(a): Var((H1-H0)/N)=N⁻²(Var(H1)+Var(H0)-2Cov(H1,H0)),
the exact variance algebra of eq. [20]. -/
theorem variance_sub_div (D : Design Ω I R) (f g : Ω → R) (c : R) :
    variance D (fun w => (f w-g w)/c) =
      (variance D f+variance D g-2*covariance D f g)/c^2 := by
  simp only [div_eq_mul_inv, variance]
  rw [covariance_scale]
  change variance D (fun w => f w-g w) * c⁻¹ * c⁻¹ = _
  rw [variance_sub]
  unfold variance
  ring

/-- Split positive/nonzero and unavailable cross-arm pairs, eq. [23]
(p. 143) and second line of [29] (p. 145); the diagonal is included. -/
def splitCovarianceExpression (D : Design Ω I R) (x z : I → R) : R :=
  (∑ i, ∑ j, if joint D true false i j ≠ 0 then
    (joint D true false i j-marginal D true i*marginal D false j) *
      (x i/marginal D true i)*(z j/marginal D false j) else 0) -
  (∑ i, ∑ j, if joint D true false i j = 0 then x i*z j else 0)

/-- P026-T12(d) and T24(b): the unavailable directed cross-arm pairs
each contribute -Y_1iY_0j to the population covariance, including i=j. -/
theorem ht_covariance_split (D : Design Ω I R) (hp : positiveMarginals D) (x z : I → R) :
    covariance D (htTotal D true x) (htTotal D false z) = splitCovarianceExpression D x z := by
  rw [ht_covariance_full]
  unfold splitCovarianceExpression
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  by_cases h : joint D true false i j = 0
  · simp only [h, ne_eq, not_true_eq_false, ite_false, ite_true, zero_sub]
    field_simp [ne_of_gt (hp i).1, ne_of_gt (hp j).2] <;> ring
  · simp [h]

/-- P026-T12(e), eq. [24] with the stray full stop removed: the whole
sampling variance includes both arm expressions and all covariance terms,
including the positive 2∑ unavailable-pair products. -/
theorem ht_variance_identity (D : Design Ω I R) (hp : positiveMarginals D)
    (N : ℕ) (hN : 0 < N) (x z : I → R) : variance D (ht D N x z) =
      (armVarianceExpression D true x + armVarianceExpression D false z -
        2*splitCovarianceExpression D x z) / (N : R)^2 := by
  change variance D (fun w => (htTotal D true x w-htTotal D false z w)/(N : R)) = _
  rw [variance_sub_div, ht_arm_variance, ht_arm_variance, ht_covariance_split D hp]

/-- P026-T24(a), eq. [26]: for predictions fixed over randomizations,
the generalized estimator has the entire eq. [24] variance expression with
U_1=Y_1-f and U_0=Y_0-f, retaining every zero-joint term. -/
theorem generalized_fixed_variance (D : Design Ω I R) (hp : positiveMarginals D)
    (N : ℕ) (hN : 0 < N) (x z f : I → R) :
    variance D (generalized D N x z (fun _ => f)) =
      (armVarianceExpression D true (fun i => x i-f i) +
       armVarianceExpression D false (fun i => z i-f i) -
       2*splitCovarianceExpression D (fun i => x i-f i) (fun i => z i-f i)) / (N : R)^2 := by
  have h : generalized D N x z (fun _ => f) = ht D N (fun i => x i-f i) (fun i => z i-f i) :=
    funext (fun w => generalized_residual D N x z (fun _ => f) w)
  rw [h, ht_variance_identity D hp N hN]

/-- Scalar linearity of the HT total, used in Appendices A and C,
eqs. [38],[42], pp. 150-151. -/
theorem htTotal_affine (D : Design Ω I R) (a : Bool) (x : I → R)
    (b0 b1 : R) (w : Ω) : htTotal D a (fun i => b0+b1*x i) w =
      b0*(∑ i, indicator D a w i/marginal D a i)+b1*htTotal D a x w := by
  unfold htTotal
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  ring

/-- P026-T23(a), eq. [38], p. 150: an affine outcome change adds
the HT inverse-probability count imbalance multiplied by b0/N. -/
theorem ht_affine (D : Design Ω I R) (N : ℕ) (x z : I → R) (b0 b1 : R) (w : Ω) :
    ht D N (fun i => b0+b1*x i) (fun i => b0+b1*z i) w =
      b0/(N : R) * ((∑ i, indicator D true w i/marginal D true i) -
        (∑ i, indicator D false w i/marginal D false i)) + b1*ht D N x z w := by
  unfold ht
  rw [htTotal_affine, htTotal_affine]
  ring

/-- P026-T23(a): HT obeys location invariance on a given assignment
iff b0=0 or its two inverse-probability assignment counts balance. -/
theorem ht_affine_invariant_iff (D : Design Ω I R) (N : ℕ) (hN : 0 < N)
    (x z : I → R) (b0 b1 : R) (w : Ω) :
    ht D N (fun i => b0+b1*x i) (fun i => b0+b1*z i) w = b1*ht D N x z w ↔
      b0=0 ∨ (∑ i, indicator D true w i/marginal D true i) =
        (∑ i, indicator D false w i/marginal D false i) := by
  rw [ht_affine]
  simp only [add_eq_right, mul_eq_zero, div_eq_zero_iff,
    Nat.cast_ne_zero.mpr (ne_of_gt hN), or_false, sub_eq_zero]

/-- P026-T23(b), eqs. [41]-[42], p. 151: transforming both potential
outcomes and every prediction by b0+b1(·) scales the generalized estimator
by b1 on every assignment, even for assignment-dependent predictions. -/
theorem generalized_affine (D : Design Ω I R) (N : ℕ) (x z : I → R)
    (f : Ω → I → R) (b0 b1 : R) (w : Ω) :
    generalized D N (fun i => b0+b1*x i) (fun i => b0+b1*z i)
      (fun v i => b0+b1*f v i) w = b1*generalized D N x z f w := by
  rw [generalized_residual, generalized_residual]
  have h1 : (fun i => b0+b1*x i-(b0+b1*f w i)) = (fun i => 0+b1*(x i-f w i)) := by
    funext i
    ring
  have h0 : (fun i => b0+b1*z i-(b0+b1*f w i)) = (fun i => 0+b1*(z i-f w i)) := by
    funext i
    ring
  rw [h1,h0,ht_affine]
  simp

/-- Single-unit design with treatment probability 1/3, a witness for
"not generally location invariant", Appendix A, p. 150 (P026-T23(a)). -/
def singleAsymmetric : Design (Fin 3) (Fin 1) ℚ where
  weight := asymmetricTwo.weight
  treatment := fun w _ => asymmetricTwo.treatment w 0

/-- P026-T23(a): b0=1,b1=-1 applied to zero potential outcomes
gives transformed HT=3 on treatment, versus -1·HT=0. -/
theorem ht_location_counterexample :
    probabilityDesign singleAsymmetric ∧ positiveMarginals singleAsymmetric ∧
    ht singleAsymmetric 1 (fun _ => 1) (fun _ => 1) 2 = 3 ∧
    (-1 : ℚ)*ht singleAsymmetric 1 (fun _ => 0) (fun _ => 0) 2 = 0 ∧
    ht singleAsymmetric 1 (fun _ => 1) (fun _ => 1) 2 ≠
      (-1)*ht singleAsymmetric 1 (fun _ => 0) (fun _ => 0) 2 := by
  unfold probabilityDesign positiveMarginals
  decide +kernel

/-- Cluster total "Y'_k=∑_{i∈K_k}Y_i" (p. 144, Section 6.3).
A map c assigns each unit to exactly one cluster; its fibers partition I. -/
def clusterTotal {K : Type*} [DecidableEq K] (c : I → K) (y : I → R) (k : K) : R :=
  ∑ i ∈ univ.filter (fun i => c i=k), y i

/-- P026-T10: corrected treatment denominator π_1i in the cluster
aggregation display, and its control analogue. Grouping the finite sum by
cluster leaves both totals and the resulting ATE contrast identical. -/
theorem cluster_aggregation {K : Type*} [Fintype K] [DecidableEq K]
    (D : Design Ω I ℝ) (C : Design Ω K ℝ) (c : I → K)
    (hc : Function.Surjective c) (hw : C.weight=D.weight)
    (ht : ∀ w i, D.treatment w i=C.treatment w (c i))
    (y : I → ℝ) (a : Bool) (w : Ω) :
    htTotal D a y w = htTotal C a (clusterTotal c y) w := by
  have hmarg (i : I) : marginal D a i=marginal C a (c i) := by
    unfold marginal expectation
    rw [hw]
    apply sum_congr rfl
    intro v _
    simp only [indicator,ht v i]
  symm
  calc
    htTotal C a (clusterTotal c y) w =
        ∑ k, ∑ i, if c i=k then indicator C a w k*y i/marginal C a k else 0 := by
      unfold htTotal clusterTotal
      apply sum_congr rfl
      intro k _
      simp only [sum_filter,mul_sum,sum_div]
      apply sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = ∑ i, indicator C a w (c i)*y i/marginal C a (c i) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      simp
    _ = htTotal D a y w := by
      unfold htTotal
      apply sum_congr rfl
      intro i _
      rw [hmarg]
      simp only [indicator,ht w i]

/-- Assignment-weighted observed sum in one arm, eqs. [11]-[12],
pp. 139-140. It equals the sum over units observed in that arm. -/
def observedArmSum (D : Design Ω I R) (a : Bool) (x z : I → R) (w : Ω) : R :=
  ∑ i, indicator D a w i*observed D x z w i

/-- P026-T21(a), eq. [11]: with exactly n of N units treated and
equal marginal probabilities n/N, HT is the ordinary difference in means,
and that difference is unbiased. -/
theorem complete_units (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (N n : ℕ) (hcard : Fintype.card I=N) (hn : 0 < n) (hnN : n < N)
    (hm : ∀ i, marginal D true i=(n : ℝ)/N ∧ marginal D false i=((N-n : ℕ) : ℝ)/N)
    (hcount : ∀ w, 0 < D.weight w → (∑ i, indicator D true w i) = n) (x z : I → ℝ) :
    (∀ w, 0 < D.weight w → ht D N x z w = observedArmSum D true x z w / n -
      observedArmSum D false x z w / (N-n : ℕ)) ∧
    expectation D (fun w => observedArmSum D true x z w / n -
      observedArmSum D false x z w / (N-n : ℕ)) = ate N x z := by
  have hN : 0 < N := lt_trans hn hnN
  have hd : 0 < N-n := Nat.sub_pos_of_lt hnN
  have hp : positiveMarginals D := by
    intro i
    rw [(hm i).1,(hm i).2]
    constructor <;> positivity
  have h1 (w : Ω) : htTotal D true x w=observedArmSum D true x z w/((n : ℝ)/N) := by
    unfold htTotal observedArmSum
    rw [sum_div]
    apply sum_congr rfl
    intro i _
    rw [(hm i).1]
    exact congrArg (fun v : ℝ => v/((n : ℝ)/N)) (observed_mask D true x z w i).symm
  have h0 (w : Ω) : htTotal D false z w=observedArmSum D false x z w/(((N-n : ℕ) : ℝ)/N) := by
    unfold htTotal observedArmSum
    rw [sum_div]
    apply sum_congr rfl
    intro i _
    rw [(hm i).2]
    exact congrArg (fun v : ℝ => v/(((N-n : ℕ) : ℝ)/N)) (observed_mask D false x z w i).symm
  have he (w : Ω) : ht D N x z w=observedArmSum D true x z w/n-
      observedArmSum D false x z w/(N-n : ℕ) := by
    unfold ht
    rw [h1 w,h0 w]
    field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hN),Nat.cast_ne_zero.mpr (ne_of_gt hn),
      Nat.cast_ne_zero.mpr (ne_of_gt hd)] <;> ring
  refine ⟨fun w _ => he w,?_⟩
  have hf : (fun w => observedArmSum D true x z w/n-observedArmSum D false x z w/(N-n : ℕ))=
      ht D N x z := funext (fun w => (he w).symm)
  rw [hf]
  exact (ht_unbiased D hD hp N hN x z).2.2

/-- P026-T21(b), eq. [12]: for m of M clusters treated with common
m/M probabilities, HT is M/N times the difference in per-cluster arm
totals. The original unit count N is retained, even for unequal cluster sizes. -/
theorem complete_clusters (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N M m : ℕ) (hN : 0 < N) (hm : 0 < m) (hmM : m < M)
    (hmarg : ∀ i, marginal D true i=(m : ℝ)/M ∧
      marginal D false i=((M-m : ℕ) : ℝ)/M)
    (hcount : ∀ w, 0 < D.weight w → (∑ i, indicator D true w i) = m) (x z : I → ℝ) :
    (∀ w, ht D N x z w = (M : ℝ)/N *
      (observedArmSum D true x z w / m-observedArmSum D false x z w / (M-m : ℕ))) ∧
    expectation D (fun w => (M : ℝ)/N *
      (observedArmSum D true x z w / m-observedArmSum D false x z w / (M-m : ℕ))) = ate N x z := by
  have hM : 0 < M := lt_trans hm hmM
  have hd : 0 < M-m := Nat.sub_pos_of_lt hmM
  have h1 (w : Ω) : htTotal D true x w=observedArmSum D true x z w/((m : ℝ)/M) := by
    unfold htTotal observedArmSum
    rw [sum_div]
    apply sum_congr rfl
    intro i _
    rw [(hmarg i).1]
    exact congrArg (fun v : ℝ => v/((m : ℝ)/M)) (observed_mask D true x z w i).symm
  have h0 (w : Ω) : htTotal D false z w=observedArmSum D false x z w/(((M-m : ℕ) : ℝ)/M) := by
    unfold htTotal observedArmSum
    rw [sum_div]
    apply sum_congr rfl
    intro i _
    rw [(hmarg i).2]
    exact congrArg (fun v : ℝ => v/(((M-m : ℕ) : ℝ)/M)) (observed_mask D false x z w i).symm
  have he (w : Ω) : ht D N x z w=(M : ℝ)/N *
      (observedArmSum D true x z w/m-observedArmSum D false x z w/(M-m : ℕ)) := by
    unfold ht
    rw [h1 w,h0 w]
    field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hN),Nat.cast_ne_zero.mpr (ne_of_gt hM),
      Nat.cast_ne_zero.mpr (ne_of_gt hm),Nat.cast_ne_zero.mpr (ne_of_gt hd)] <;> ring
  refine ⟨he,?_⟩
  have hf : (fun w => (M : ℝ)/N *
      (observedArmSum D true x z w/m-observedArmSum D false x z w/(M-m : ℕ)))=ht D N x z :=
    funext (fun w => (he w).symm)
  rw [hf]
  exact (ht_unbiased D hD hp N hN x z).2.2

/-- Unequal clusters {1},{2},{3,4}; one cluster treated uniformly,
sharp-null outcomes (1,1,0,0), the witness for P026-T21(c). -/
def unequalClusterDesign : Design (Fin 3) (Fin 4) ℚ where
  weight := fun _ => 1/3
  treatment := fun w i => decide (w = (![0,1,2,2] : Fin 4 → Fin 3) i)

/-- Ordinary observed difference in unit means, eq. [11], pp. 139-140,
with its actual random arm counts, for comparison under cluster assignment. -/
def differenceInMeans (D : Design Ω I R) (x z : I → R) (w : Ω) : R :=
  observedArmSum D true x z w / (∑ i, indicator D true w i) -
  observedArmSum D false x z w / (∑ i, indicator D false w i)

/-- P026-T21(c): in the admissible unequal-cluster design the ordinary
difference in unit means has expectation 1/9 whereas Δ and E[HT] are zero. -/
theorem unequal_clusters_bias :
    probabilityDesign unequalClusterDesign ∧ positiveMarginals unequalClusterDesign ∧
    (∀ i, marginal unequalClusterDesign true i=1/3 ∧ marginal unequalClusterDesign false i=2/3) ∧
    expectation unequalClusterDesign (differenceInMeans unequalClusterDesign (![1,1,0,0]) (![1,1,0,0]))=1/9 ∧
    expectation unequalClusterDesign (ht unequalClusterDesign 4 (![1,1,0,0]) (![1,1,0,0]))=0 ∧
    ate 4 (![1,1,0,0] : Fin 4 → ℚ) (![1,1,0,0])=0 ∧ (1/9 : ℚ) ≠ 0 := by
  unfold probabilityDesign positiveMarginals
  decide +kernel

/- P026-T17(i)-(iii): the printed universal cluster claims, including
the false support deduction, covariance sign, conservative eq. [35], and
sharp-null equalities under same-arm positivity alone. These printed claims
have no H+ premise; P026-T1 refutes them. -/


/- P026-T18: the general fitting rule exactly as printed in Section
5.1, p. 142, has only pairwise independence premises for an arbitrary
deterministic vector fit. P026-T4 refutes it; the corrected premise is T5. -/


/-- Two of six clusters treated, the fifteen possibilities in Table 1's
second block (p. 147, Section 7). -/
def twoOfSix : Fin 15 → Fin 6 → Bool := ![
  ![true,true,false,false,false,false], ![true,false,true,false,false,false],
  ![true,false,false,true,false,false], ![true,false,false,false,true,false],
  ![true,false,false,false,false,true], ![false,true,true,false,false,false],
  ![false,true,false,true,false,false], ![false,true,false,false,true,false],
  ![false,true,false,false,false,true], ![false,false,true,true,false,false],
  ![false,false,true,false,true,false], ![false,false,true,false,false,true],
  ![false,false,false,true,true,false], ![false,false,false,true,false,true],
  ![false,false,false,false,true,true]]

/-- "All 90 possible randomizations" (p. 148, Section 7): independently
select two of four clusters in block 1 and two of six in block 2. -/
def tableDesign : Design (Fin 6 × Fin 15) (Fin 10) ℚ where
  weight := fun _ => 1/90
  treatment := fun w i => if h : i.val < 4 then twoOfFour.treatment w.1 ⟨i.val,h⟩
    else twoOfSix w.2 ⟨i.val-4, by omega⟩

/-- Exact cluster marginal inclusion probabilities in Table 1, p. 147:
π_1=1/2 in block 1, 1/3 in block 2, and π_0=1-π_1. -/
def tableMarginal (a : Bool) (i : Fin 10) : ℚ :=
  let p : ℚ := if i.val < 4 then 1/2 else 1/3
  if a then p else 1-p

/-- Exact joint inclusion probabilities for the independent complete
block assignment in Section 7, p. 147; derived by counting in `table_joint`. -/
def tableJoint (a b : Bool) (i j : Fin 10) : ℚ :=
  if i=j then (if a=b then tableMarginal a i else 0)
  else if (i.val < 4 ↔ j.val < 4) then
    if i.val < 4 then (if a=b then 1/6 else 1/3)
    else if a then (if b then 1/15 else 4/15) else (if b then 4/15 else 2/5)
  else tableMarginal a i*tableMarginal b j

/-- Exact finite counting of Table 1's marginal probabilities, p. 147. -/
theorem table_marginal : ∀ a i, marginal tableDesign a i = tableMarginal a i := by
  decide +kernel

/-- Exact finite counting of Table 1's joint probabilities, pp. 147-148. -/
theorem table_joint : ∀ a b i j, joint tableDesign a b i j = tableJoint a b i j := by
  decide +kernel

/-- P026-T3, numerical-design qualification: H+ holds in Table 1.
The minimum directed cross-arm joint is 1/6, TT minimum 1/15, CC minimum
1/6. Same-arm positivity and distinctness also hold. -/
theorem table_support : probabilityDesign tableDesign ∧ positiveMarginals tableDesign ∧
    crossSupport tableDesign ∧
    (∀ i j : Fin 10, i ≠ j → 1/6 ≤ joint tableDesign true false i j ∧
      1/15 ≤ joint tableDesign true true i j ∧ 1/6 ≤ joint tableDesign false false i j ∧
      0 < disagreement tableDesign i j) ∧
    (∃ i j : Fin 10, i ≠ j ∧ joint tableDesign true false i j=1/6) ∧
    (∃ i j : Fin 10, i ≠ j ∧ joint tableDesign true true i j=1/15) ∧
    (∃ i j : Fin 10, i ≠ j ∧ joint tableDesign false false i j=1/6) := by
  unfold probabilityDesign positiveMarginals crossSupport
  simp only [table_marginal, table_joint, disagreement_identity]
  decide +kernel

/-- Unit-to-cluster membership, Table 1, p. 147. Zero-based indices
represent printed units 1,...,16 and clusters 1,...,10. -/
def tableCluster : Fin 16 → Fin 10 := ![0,0,1,1,2,3,4,4,4,5,5,6,6,7,8,9]

/-- Y_1i=Y_0i=Y_i in Table 1, p. 147, the sharp-null population. -/
def tableY : Fin 16 → ℚ := ![1,1,1,1,1,0,1,1,0,1,1,1,1,0,0,0]

/-- Printed covariate X_i in Table 1, p. 147; no altered covariates are used. -/
def tableX : Fin 16 → ℚ := ![4,0,4,1,4,2,4,1,2,5,4,1,4,2,2,3]

/-- Opposite-block OLS prediction in Section 7.1, p. 148: fit block 2
for units in block 1, and vice versa. Normal equations are checked below. -/
def tableLinearPrediction (i : Fin 16) : ℚ :=
  if i.val < 6 then 1/4+tableX i/8 else 70/93+tableX i/31

/-- Exact cluster residual totals U'_k for G (Linear), P026-T6,T7;
this vector is verified against Table 1 and the opposite-block fits. -/
def tableLinearResidual : Fin 10 → ℚ :=
  ![1,7/8,1/4,-1/2,-15/31,19/93,1/3,-76/93,-76/93,-79/93]

/-- P026-T6(A), T7(a): the two full-rank univariate OLS normal
equation solutions and every residual cluster total are exact. -/
theorem table_linear_fits :
    (∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => i.val < 6),
      (tableY i-(70/93+tableX i/31))) = 0 ∧
    (∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => i.val < 6),
      tableX i*(tableY i-(70/93+tableX i/31))) = 0 ∧
    (∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => 6 ≤ i.val),
      (tableY i-(1/4+tableX i/8))) = 0 ∧
    (∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => 6 ≤ i.val),
      tableX i*(tableY i-(1/4+tableX i/8))) = 0 ∧
    (6*53-15^2 : ℚ)=93 ∧ (10*96-28^2 : ℚ)=176 ∧
    (∀ k, clusterTotal tableCluster (fun i => tableY i-tableLinearPrediction i) k=tableLinearResidual k) := by
  decide +kernel

/-- Auxiliary exact value table for Section 7.1, p. 148; P026-T6,T7.
Every value is checked against its defining estimator below; this table
is a computation certificate, not an assumed moment or replacement input. -/
def linearHTCertificate (w : Fin 6 × Fin 15) : ℚ :=
  (![![(823/1984),(895/1984),(253/1984),(253/1984),(235/1984),(1279/1984),(637/1984),(637/1984),(619/1984),(709/1984),(709/1984),(691/1984),(67/1984),(49/1984),(49/1984)],
    ![(513/1984),(585/1984),(-57/1984),(-57/1984),(-75/1984),(969/1984),(327/1984),(327/1984),(309/1984),(399/1984),(399/1984),(381/1984),(-243/1984),(-261/1984),(-261/1984)],
    ![(141/1984),(213/1984),(-429/1984),(-429/1984),(-447/1984),(597/1984),(-45/1984),(-45/1984),(-63/1984),(27/1984),(27/1984),(9/1984),(-615/1984),(-633/1984),(-633/1984)],
    ![(451/1984),(523/1984),(-119/1984),(-119/1984),(-137/1984),(907/1984),(265/1984),(265/1984),(247/1984),(337/1984),(337/1984),(319/1984),(-305/1984),(-323/1984),(-323/1984)],
    ![(79/1984),(151/1984),(-491/1984),(-491/1984),(-509/1984),(535/1984),(-107/1984),(-107/1984),(-125/1984),(-35/1984),(-35/1984),(-53/1984),(-677/1984),(-695/1984),(-695/1984)],
    ![(-231/1984),(-159/1984),(-801/1984),(-801/1984),(-819/1984),(225/1984),(-417/1984),(-417/1984),(-435/1984),(-345/1984),(-345/1984),(-363/1984),(-987/1984),(-1005/1984),(-1005/1984)]] : Fin 6 → Fin 15 → ℚ) w.1 w.2

/-- Auxiliary exact value table for Section 7.1, p. 148; P026-T6,T7.
Every value is checked against its defining estimator below; this table
is a computation certificate, not an assumed moment or replacement input. -/
def linearVarianceCertificate (w : Fin 6 × Fin 15) : ℚ :=
  (![![(153167/2952192),(169823/2952192),(94759/2214144),(94759/2214144),(12439/285696),(146783/2952192),(142535/2214144),(142535/2214144),(18839/285696),(158561/2214144),(158561/2214144),(20951/285696),(377765/8856576),(3071/71424),(3071/71424)],
    ![(349579/5904384),(382891/5904384),(887807/17713152),(887807/17713152),(29063/571392),(336811/5904384),(1270015/17713152),(1270015/17713152),(41863/571392),(1398223/17713152),(1398223/17713152),(46087/571392),(885265/17713152),(28753/571392),(28753/571392)],
    ![(707807/11808768),(774431/11808768),(1801561/35426304),(1801561/35426304),(58963/1142784),(682271/11808768),(2565977/35426304),(2565977/35426304),(84563/1142784),(2822393/35426304),(2822393/35426304),(93011/1142784),(1796477/35426304),(58343/1142784),(58343/1142784)],
    ![(707807/11808768),(774431/11808768),(1801561/35426304),(1801561/35426304),(58963/1142784),(682271/11808768),(2565977/35426304),(2565977/35426304),(84563/1142784),(2822393/35426304),(2822393/35426304),(93011/1142784),(1796477/35426304),(58343/1142784),(58343/1142784)],
    ![(349579/5904384),(382891/5904384),(887807/17713152),(887807/17713152),(29063/571392),(336811/5904384),(1270015/17713152),(1270015/17713152),(41863/571392),(1398223/17713152),(1398223/17713152),(46087/571392),(885265/17713152),(28753/571392),(28753/571392)],
    ![(153167/2952192),(169823/2952192),(94759/2214144),(94759/2214144),(12439/285696),(146783/2952192),(142535/2214144),(142535/2214144),(18839/285696),(158561/2214144),(158561/2214144),(20951/285696),(377765/8856576),(3071/71424),(3071/71424)]] : Fin 6 → Fin 15 → ℚ) w.1 w.2

/-- Exact values of G (Linear) on all 90 assignments; Section 7.1, p. 148. -/
theorem table_linear_ht_certificate : ∀ w, ht tableDesign 16 tableLinearResidual tableLinearResidual w=linearHTCertificate w := by
  simp only [ht,htTotal,table_marginal]
  decide +kernel

/-- Exact values of printed eq. [35] for G (Linear) on all 90 assignments, pp. 147-148. -/
theorem table_linear_v_certificate : ∀ w, printedVariance tableDesign 16 tableLinearResidual tableLinearResidual w=linearVarianceCertificate w := by
  simp only [printedVariance,estimatedPair,zeroSum,table_marginal,table_joint,observed,ite_self]
  decide +kernel

/-- Exact Table 2 moments of the G (Linear) estimator, Section 7.1,
p. 148, computed using eq. [25] on the verified residual cluster totals. -/
theorem table_linear_moments :
    expectation tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual)=0 ∧
    variance tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual)=38307/634880 ∧
    expectation tableDesign (printedVariance tableDesign 16 tableLinearResidual tableLinearResidual)=38307/634880 ∧
    variance tableDesign (printedVariance tableDesign 16 tableLinearResidual tableLinearResidual)=
      2400328658503/15687787688755200  := by
  simp only [variance,covariance,expectation,table_linear_ht_certificate,table_linear_v_certificate]
  decide +kernel

/-- Rounding interval for a number printed to three decimals in Table 2,
p. 149. Endpoint convention is immaterial for all established examples. -/
def rounded3 (x r : ℚ) : Prop := r-1/2000 ≤ x ∧ x < r+1/2000

/-- Three-decimal standard-deviation interval expressed by exact squares;
for the positive displayed r, this is precisely r-.0005≤√v<r+.0005.
This avoids approximate square roots in the exact rational table checks. -/
def roundedSD3 (v r : ℚ) : Prop := (r-1/2000)^2 ≤ v ∧ v < (r+1/2000)^2

/-- P026-T6(A): the exact G (Linear) variances exceed the upper
rounding endpoints for the six printed erroneous entries .026,.162,.007. -/
theorem table_linear_refutation :
    variance tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual) > 265/10000 ∧
    variance tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual) > (1625/10000)^2 ∧
    variance tableDesign (printedVariance tableDesign 16 tableLinearResidual tableLinearResidual) > (75/10000)^2 := by
  rw [table_linear_moments.2.1, table_linear_moments.2.2.2]
  norm_num

/-- P026-T7(a): corrected G (Linear) SE/RMSE=.246, variance/mean
variance estimate=.060, variance-estimator SE/RMSE=.012, with exactly zero bias. -/
theorem table_linear_corrected_rounding :
    roundedSD3 (38307/634880) (246/1000) ∧ rounded3 (38307/634880) (60/1000) ∧
    roundedSD3 (2400328658503/15687787688755200) (12/1000) := by
  unfold rounded3 roundedSD3
  norm_num

/-- Unit assignment indicators in Table 1, p. 147, obtained from the
cluster design. Shared covariates and outcomes remain fixed. -/
def tableUnitDesign : Design (Fin 6 × Fin 15) (Fin 16) ℚ where
  weight := tableDesign.weight
  treatment := fun w i => tableDesign.treatment w (tableCluster i)

/-- Block mean of the realized unit treatment indicators in the FE
regression in Section 7.1, p. 148. -/
def tableTreatmentMean (w : Fin 6 × Fin 15) (b : Bool) : ℚ :=
  (∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => if b then 6 ≤ i.val else i.val < 6),
    indicator tableUnitDesign true w i) / (if b then 10 else 6)

/-- Covariate centered within its block; the fixed block mean is 5/2
in block 1, 14/5 in block 2 (Table 1, p. 147). -/
def tableCenteredX (i : Fin 16) : ℚ := tableX i-(if i.val < 6 then 5/2 else 14/5)

/-- Outcome centered within its block; fixed means 5/6 and 3/5
from Table 1, p. 147. -/
def tableCenteredY (i : Fin 16) : ℚ := tableY i-(if i.val < 6 then 5/6 else 3/5)

/-- Treatment centered within its block, FE (Cov.), Section 7.1, p. 148. -/
def tableCenteredT (w : Fin 6 × Fin 15) (i : Fin 16) : ℚ :=
  indicator tableUnitDesign true w i-tableTreatmentMean w (decide (6 ≤ i.val))

/-- Auxiliary exact block treatment means for FE (Cov.), Section 7.1,
p. 148. The finite counts are certified below against Table 1 assignments. -/
def tableTreatmentMeanCertificate (w : Fin 6 × Fin 15) (b : Bool) : ℚ :=
  if b then (![(1/2),(1/2),(2/5),(2/5),(2/5),(2/5),(3/10),(3/10),(3/10),(3/10),(3/10),(3/10),(1/5),(1/5),(1/5)] : Fin 15 → ℚ) w.2
  else (![(2/3),(1/2),(1/2),(1/2),(1/2),(1/3)] : Fin 6 → ℚ) w.1

/-- Exact block treatment means on all 90 Table 1 allocations, p. 148. -/
theorem table_treatment_mean_certificate : ∀ w b,
    tableTreatmentMean w b=tableTreatmentMeanCertificate w b := by
  decide +kernel

/-- Auxiliary exact treatment/covariate projection sum for FE (Cov.),
Section 7.1, p. 148; its equality to the original centered sum is proved. -/
def feTXCertificate (w : Fin 6 × Fin 15) : ℚ :=
  (![-1,(1/2),(-3/2),(3/2),(-1/2),1] : Fin 6 → ℚ) w.1 +
  (![2,-2,(-11/5),(-11/5),(-6/5),(14/5),(13/5),(13/5),(18/5),(-7/5),(-7/5),(-2/5),(-8/5),(-3/5),(-3/5)] : Fin 15 → ℚ) w.2

/-- The fixed within-block X norm is positive; FE (Cov.), Section 7.1, p. 148. -/
theorem fe_x_norm : (∑ i, (tableCenteredX i)^2)=(331/10) ∧ (0 : ℚ)<(331/10) := by
  decide +kernel

/-- Exact treatment/X centered cross products on all 90 Table 1 allocations,
Section 7.1, p. 148; the cached block means are independently certified. -/
theorem fe_tx_certificate : ∀ w,
    (∑ i, tableCenteredX i*tableCenteredT w i)=feTXCertificate w := by
  simp only [tableCenteredT,table_treatment_mean_certificate]
  decide +kernel

/-- Treatment residual after projection on intercept, block dummy and X.
The Frisch-Waugh normal-equation form of the printed FE (Cov.) regression
(Section 7.1, p. 148), with all 16 observations and no weights. -/
def feTreatmentResidual (w : Fin 6 × Fin 15) (i : Fin 16) : ℚ :=
  tableCenteredT w i - (∑ j, tableCenteredX j*tableCenteredT w j) /
    (∑ j, (tableCenteredX j)^2)*tableCenteredX i

/-- The coefficient of T in OLS of Y on (1,T,block2,X), FE (Cov.)
(p. 148, Section 7.1), written as its full-rank residualized normal-equation
formula. Positivity of its residual norm is verified for every allocation. -/
def feEstimate (w : Fin 6 × Fin 15) : ℚ :=
  (∑ i, feTreatmentResidual w i*tableCenteredY i) / (∑ i, (feTreatmentResidual w i)^2)

/-- The covariate coefficient in the same OLS fit, p. 148, Section 7.1. -/
def feXCoefficient (w : Fin 6 × Fin 15) : ℚ :=
  (∑ i, tableCenteredX i*(tableCenteredY i-feEstimate w*tableCenteredT w i)) /
    (∑ i, (tableCenteredX i)^2)

/-- Auxiliary exact value table for Section 7.1, p. 148; P026-T6,T7.
Every value is checked against its defining estimator below; this table
is a computation certificate, not an assumed moment or replacement input. -/
def feCoefficientCertificate (w : Fin 6 × Fin 15) : ℚ :=
  (![![(3148/7553),(3796/7073),(131/850),(131/850),(443/3562),(421/722),(34/155),(34/155),(1300/6413),(2110/6473),(2110/6473),(1948/6701),(-319/2710),(-100/709),(-100/709)],
    ![(286/841),(1074/2603),(79/1262),(79/1262),(26/643),(101/197),(296/2191),(296/2191),(242/2047),(512/2367),(512/2367),(458/2383),(-101/507),(-229/1026),(-229/1026)],
    ![(304/2643),(520/2403),(-99/577),(-99/577),(-75/406),(47/182),(-258/2359),(-258/2359),(-104/765),(-42/2215),(-42/2215),(-96/2311),(-479/930),(-253/491),(-253/491)],
    ![(268/801),(340/881),(26/643),(26/643),(5/258),(579/1106),(242/2047),(242/2047),(188/1863),(458/2383),(458/2383),(404/2359),(-229/1026),(-128/509),(-128/509)],
    ![(250/2603),(466/2523),(-75/406),(-75/406),(-126/631),(151/619),(-104/765),(-104/765),(-366/2191),(-96/2311),(-96/2311),(-50/789),(-253/491),(-41/78),(-41/78)],
    ![(16/643),(824/7553),(-481/1832),(-481/1832),(-1043/3706),(619/3274),(-1510/6041),(-1510/6041),(-1672/5549),(-862/6809),(-862/6809),(-1024/6797),(-1805/2902),(-943/1454),(-943/1454)]] : Fin 6 → Fin 15 → ℚ) w.1 w.2

/-- Auxiliary exact value table for Section 7.1, p. 148; P026-T6,T7.
Every value is checked against its defining estimator below; this table
is a computation certificate, not an assumed moment or replacement input. -/
def feXCertificate (w : Fin 6 × Fin 15) : ℚ :=
  (![![(521/7553),(921/7073),(41/425),(41/425),(160/1781),(18/361),(11/155),(11/155),(421/6413),(681/6473),(681/6473),(629/6701),(98/1355),(53/709),(53/709)],
    ![(47/841),(261/2603),(107/1262),(107/1262),(53/643),(6/197),(151/2191),(151/2191),(137/2047),(23/263),(23/263),(193/2383),(38/507),(83/1026),(83/1026)],
    ![(211/2643),(251/2403),(36/577),(36/577),(27/406),(1/14),(201/2359),(201/2359),(23/255),(177/2215),(177/2215),(183/2311),(1/30),(24/491),(24/491)],
    ![(37/801),(77/881),(53/643),(53/643),(7/86),(15/1106),(137/2047),(137/2047),(41/621),(193/2383),(193/2383),(179/2359),(83/1026),(45/509),(45/509)],
    ![(201/2603),(241/2523),(27/406),(27/406),(45/631),(40/619),(23/255),(23/255),(213/2191),(183/2311),(183/2311),(21/263),(24/491),(5/78),(5/78)],
    ![(51/643),(641/7553),(33/458),(33/458),(148/1853),(98/1637),(657/6041),(657/6041),(685/5549),(545/6809),(545/6809),(573/6797),(102/1451),(65/727),(65/727)]] : Fin 6 → Fin 15 → ℚ) w.1 w.2

/-- Exact certificate of every FE (Cov.) treatment coefficient, Section 7.1, p. 148. -/
theorem fe_estimate_certificate : ∀ w, feEstimate w=feCoefficientCertificate w := by
  unfold feEstimate feTreatmentResidual
  simp only [fe_tx_certificate,fe_x_norm.1]
  simp only [tableCenteredT,table_treatment_mean_certificate]
  decide +kernel

/-- Exact certificate of every FE (Cov.) X coefficient, Section 7.1, p. 148. -/
theorem fe_x_certificate : ∀ w, feXCoefficient w=feXCertificate w := by
  unfold feXCoefficient
  simp only [fe_estimate_certificate,fe_x_norm.1,tableCenteredT,table_treatment_mean_certificate]
  decide +kernel

/-- OLS fitted value for FE (Cov.), reconstructed from its treatment,
covariate and two block-intercept normal-equation coefficients, p. 148. -/
def feFitted (w : Fin 6 × Fin 15) (i : Fin 16) : ℚ :=
  (if i.val < 6 then 5/6 else 3/5) + feEstimate w*tableCenteredT w i +
    feXCoefficient w*tableCenteredX i

/-- P026-T6(B), T7(b): FE (Cov.) is the full-rank printed OLS fit;
its residual is orthogonal to each of the four regressors in every allocation. -/
theorem fe_normal_equations : ∀ w : Fin 6 × Fin 15,
    0 < (∑ i, (feTreatmentResidual w i)^2) ∧
    (∑ i, (tableY i-feFitted w i))=0 ∧
    (∑ i, indicator tableUnitDesign true w i*(tableY i-feFitted w i))=0 ∧
    (∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => 6 ≤ i.val), (tableY i-feFitted w i))=0 ∧
    (∑ i, tableX i*(tableY i-feFitted w i))=0 := by
  unfold feFitted feTreatmentResidual
  simp only [fe_estimate_certificate,fe_x_certificate,fe_tx_certificate,fe_x_norm.1]
  simp only [tableCenteredT,table_treatment_mean_certificate]
  decide +kernel

/-- P026-T6(B), T7(b,c): exact rational interval certification of
FE (Cov.) mean, variance, SE and RMSE. These give corrected entries
(-.014,.078,.279,.279) and preserve G (Linear)'s smaller RMSE. -/
theorem fe_table_moments :
    (-145/10000 : ℚ) < expectation tableDesign feEstimate ∧
    expectation tableDesign feEstimate < -135/10000 ∧
    (775/10000 : ℚ) < variance tableDesign feEstimate ∧
    variance tableDesign feEstimate < 785/10000 ∧
    roundedSD3 (variance tableDesign feEstimate) (279/1000) ∧
    roundedSD3 (variance tableDesign feEstimate+(expectation tableDesign feEstimate)^2) (279/1000) ∧
    (38307/634880 : ℚ) < variance tableDesign feEstimate+(expectation tableDesign feEstimate)^2 := by
  unfold roundedSD3
  simp only [variance,covariance,expectation,fe_estimate_certificate]
  decide +kernel

/-- Cluster totals Y'_k and prior-adjusted totals in Table 1/Section
7.1, pp. 147-148: G (Prior) subtracts 0.5 from each original unit. -/
def tableClusterY : Fin 10 → ℚ := ![2,2,1,0,2,2,2,0,0,0]

/-- Prior residual U'_k (the sum of Y_i-.5 in each cluster),
Section 7.1, p. 148. -/
def tablePriorResidual : Fin 10 → ℚ := ![1,1,1/2,-1/2,1/2,1,1,-1/2,-1/2,-1/2]

/-- P026-T7(d): HT and G (Prior) columns survive unchanged. Their
expectations are zero and both variance estimators are exactly unbiased,
with variances 353/1920 and 233/2560. -/
theorem table_unchanged_columns :
    (∀ k, clusterTotal tableCluster tableY k=tableClusterY k ∧
      clusterTotal tableCluster (fun i => tableY i-1/2) k=tablePriorResidual k) ∧
    expectation tableDesign (ht tableDesign 16 tableClusterY tableClusterY)=0 ∧
    variance tableDesign (ht tableDesign 16 tableClusterY tableClusterY)=353/1920 ∧
    expectation tableDesign (printedVariance tableDesign 16 tableClusterY tableClusterY)=353/1920 ∧
    expectation tableDesign (ht tableDesign 16 tablePriorResidual tablePriorResidual)=0 ∧
    variance tableDesign (ht tableDesign 16 tablePriorResidual tablePriorResidual)=233/2560 ∧
    expectation tableDesign (printedVariance tableDesign 16 tablePriorResidual tablePriorResidual)=233/2560 ∧
    rounded3 (353/1920) (184/1000) ∧ rounded3 (233/2560) (91/1000) := by
  unfold rounded3
  simp only [variance, covariance, expectation, ht, htTotal, printedVariance, estimatedPair, zeroSum,
    table_marginal, table_joint, observed, ite_self]
  decide +kernel

/-- The same Table 1 design as a real probability space, for the real
logistic likelihood in P026-T14. -/
def realTableDesign : Design (Fin 6 × Fin 15) (Fin 10) ℝ where
  weight := fun w => (tableDesign.weight w : ℝ)
  treatment := tableDesign.treatment

/-- "σ(z)=1-1/(1+exp(z))", the logistic predictive function printed
on p. 148, Section 7.1. -/
noncomputable def sigmoid (z : ℝ) : ℝ := 1-1/(1+Real.exp z)

/-- Bernoulli logistic log likelihood for one printed training block,
P026-T14(a), Table 1/Section 7.1, pp. 147-148; false denotes block 1. -/
noncomputable def logitLikelihood (b : Bool) (β : ℝ × ℝ) : ℝ :=
  ∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => if b then 6 ≤ i.val else i.val < 6),
    ((tableY i : ℝ)*Real.log (sigmoid (β.1+β.2*(tableX i : ℝ))) +
      (1-(tableY i : ℝ))*Real.log (1-sigmoid (β.1+β.2*(tableX i : ℝ))))

/-- Global finite logistic maximum, Section 7.1, p. 148, P026-T14(a). -/
def logitMaximizer (b : Bool) (β : ℝ × ℝ) : Prop :=
  ∀ γ : ℝ × ℝ, logitLikelihood b γ ≤ logitLikelihood b β

/-- The logistic fit used by the numerical estimator (Section 7.1,
p. 148). Choose a global maximizer if one exists, and (0,0) otherwise. -/
noncomputable def logitCoefficients (b : Bool) : ℝ × ℝ := by
  classical
  exact if h : ∃ β, logitMaximizer b β then Classical.choose h else (0,0)

/-- Opposite-block logistic prediction, Section 7.1, p. 148. Block 1
units use the block 2 fit, and vice versa. -/
noncomputable def tableLogitPrediction (i : Fin 16) : ℝ :=
  let β := logitCoefficients (decide (i.val < 6))
  sigmoid (β.1+β.2*(tableX i : ℝ))

/-- Logistic residual cluster totals U'_k=∑_{i∈K_k}(Y_i-f_i),
eq. [25] and Section 7.1, pp. 144,148. -/
noncomputable def tableLogitResidual : Fin 10 → ℝ :=
  clusterTotal tableCluster (fun i => (tableY i : ℝ)-tableLogitPrediction i)

/-- P026-T14(a), finite no-separation certificate from the printed
successes at X=0,4 and failure at X=2 in block 1; analogous X=1,4,2
in block 2. Every weak separating direction is zero. -/
theorem logit_no_separation (a b : ℝ) :
    (0 ≤ a → 0 ≤ a+4*b → a+2*b ≤ 0 → a=0 ∧ b=0) ∧
    (0 ≤ a+b → 0 ≤ a+4*b → a+2*b ≤ 0 → a=0 ∧ b=0) := by
  constructor <;> intro h1 h2 h3 <;> constructor <;> linarith







/-- Covariance is additive in its second input, Section 5.1, p. 142. -/
theorem covariance_add_right (D : Design Ω I R) (f g h : Ω → R) :
    covariance D f (fun w => g w+h w)=covariance D f g+covariance D f h := by
  have hh : (fun w => f w*(g w+h w))=(fun w => f w*g w+f w*h w) := by
    funext w
    ring
  unfold covariance
  rw [hh,expectation_add,expectation_add]
  ring

/-- Finite additivity for fitted outcome vectors, Section 5.1, p. 142. -/
theorem covariance_sum_right {J : Type*} [Fintype J] (D : Design Ω I R)
    (f : Ω → R) (g : J → Ω → R) :
    covariance D f (fun w => ∑ j, g j w)=∑ j, covariance D f (g j) := by
  have h : (fun w => f w*(∑ j, g j w))=(fun w => ∑ j, f w*g j w) := by
    funext w
    simp only [mul_sum]
  unfold covariance
  rw [h,expectation_sum,expectation_sum]
  simp only [mul_sum,sum_sub_distrib]

/-- P026-T5(d): pairwise independence does suffice for an additive
prediction a+∑ b_j Y_j with fixed coefficients. The covariance is the
printed weighted sum of assignment covariances, and both quantities vanish. -/
theorem additive_fitting_unbiased (D : Design Ω I R) (hD : probabilityDesign D)
    (i : I) (J : Finset I) (x z : I → R) (a : R) (b : ↥J → R)
    (h : ∀ j : ↥J, independent D (fun w => D.treatment w i) (fun w => D.treatment w j)) :
    covariance D (fun w => indicator D true w i)
      (fun w => a+∑ j : ↥J, b j*observed D x z w j) =
        ∑ j : ↥J, b j*(x j-z j)*covariance D
          (fun w => indicator D true w i) (fun w => indicator D true w j) ∧
    covariance D (fun w => indicator D true w i)
      (fun w => a+∑ j : ↥J, b j*observed D x z w j)=0 := by
  have hc (j : ↥J) : covariance D (fun w => indicator D true w i)
      (fun w => observed D x z w j)=0 := by
    unfold covariance
    exact sub_eq_zero.mpr (by
      simpa [indicator,observed] using
        (h j (fun t : Bool => if t=true then (1 : R) else 0)
          (fun t : Bool => if t then x j else z j)))
  have ht (j : ↥J) : covariance D (fun w => indicator D true w i)
      (fun w => indicator D true w j)=0 := by
    unfold covariance
    exact sub_eq_zero.mpr (h j (fun t => if t=true then 1 else 0) (fun t => if t=true then 1 else 0))
  have hs (j : ↥J) : covariance D (fun w => indicator D true w i)
      (fun w => b j*observed D x z w j)=0 := by
    have hh := covariance_scale D (fun w => indicator D true w i)
      (fun w => observed D x z w j) 1 (b j)
    simpa only [mul_one,one_mul,mul_comm,hc,zero_mul,mul_zero] using hh
  have hz : covariance D (fun w => indicator D true w i)
      (fun w => a+∑ j : ↥J, b j*observed D x z w j)=0 := by
    rw [covariance_add_right,covariance_const_right D hD,covariance_sum_right]
    simp [hs]
  refine ⟨?_,hz⟩
  rw [hz]
  simp only [ht,mul_zero,sum_const_zero]

/-- P026-T5(b): corrected vector-independent fits for every unit make
both generalized totals and the ATE estimator unbiased, Appendix B. -/
theorem vector_fitting_unbiased (D : Design Ω I R) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N : ℕ) (hN : 0 < N) (x z : I → R)
    (J : I → Finset I) (G : ∀ i, (↥(J i) → R) → R)
    (h : ∀ i, independent D (fun w => D.treatment w i) (fittingAssignments D (J i))) :
    let f : Ω → I → R := fun w i => G i (fittingOutcomes D (J i) x z w)
    expectation D (generalizedTotal D true x f)=populationTotal x ∧
    expectation D (generalizedTotal D false z f)=populationTotal z ∧
    expectation D (generalized D N x z f)=ate N x z := by
  apply generalized_unbiased D hD hp N hN
  intro i
  exact (vector_fitting_independence D i (J i) x z (G i) id (h i)).2.2

/-- Mutual assignment independence, as in the independent-unit example
of Section 5.1, p. 142: all product test expectations factor. -/
def mutuallyIndependentAssignments (D : Design Ω I R) : Prop :=
  ∀ F : I → Bool → R, expectation D (fun w => ∏ i, F i (D.treatment w i)) =
    ∏ i, expectation D (fun w => F i (D.treatment w i))

/-- Mutual independence of whole block assignment processes, the
block-randomization example of Section 5.1, p. 142. Tests may depend on
the entire within-block assignment vector. -/
def mutuallyIndependentBlocks {B : Type*} [Fintype B] [DecidableEq B]
    (D : Design Ω I R) (c : I → B) : Prop :=
  ∀ F : ∀ b : B, (↥(univ.filter (fun i => c i=b)) → Bool) → R,
    expectation D (fun w => ∏ b, F b (fittingAssignments D (univ.filter (fun i => c i=b)) w)) =
      ∏ b, expectation D (fun w => F b (fittingAssignments D (univ.filter (fun i => c i=b)) w))







/-- P026-T16(c): under the sharp null any deterministic OLS or other
fit based only on observed outcomes and fixed quantities is constant over
assignments, so the residual-adjusted estimator is unbiased. -/
theorem sharp_null_fit_unbiased (D : Design Ω I R) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N : ℕ) (hN : 0 < N) (x : I → R)
    (G : (I → R) → (I → R)) :
    expectation D (generalized D N x x (fun w => G (observed D x x w)))=ate N x x := by
  have h : (fun w => G (observed D x x w))=(fun _ => G x) := by
    funext w
    have hy : observed D x x w=x := by funext i; simp [observed]
    rw [hy]
  rw [h]
  exact fixed_prediction_unbiased D hD hp N hN x x (G x)










/- P026-T17(iv), as printed in footnote 9, p. 147: under the sharp
null, outcome-derived fitting functions are constant over randomization;
the footnote asserts unbiasedness of printed [35] with positive same-arm
joints alone. It already fails for G=0 in P026-T1. -/


/-- P026-T20, unit-population headline with N explicitly equal to the
number of units: eqs. [5]-[8], pp. 138-139. -/
theorem unit_ht_unbiased (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (hN : 0 < Fintype.card I) (x z : I → ℝ) :
    expectation D (htTotal D true x)=populationTotal x ∧
    expectation D (htTotal D false z)=populationTotal z ∧
    expectation D (ht D (Fintype.card I) x z)=ate (Fintype.card I) x z := by
  exact ht_unbiased D hD hp (Fintype.card I) hN x z

/-- P026-T22, Appendix B: the unit-population generalized estimator is
unbiased under zero per-unit prediction covariance; N is the unit count. -/
theorem unit_generalized_unbiased (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (hN : 0 < Fintype.card I) (x z : I → ℝ) (f : Ω → I → ℝ)
    (hf : ∀ i, covariance D (fun w => indicator D true w i) (fun w => f w i)=0) :
    expectation D (generalizedTotal D true x f)=populationTotal x ∧
    expectation D (generalizedTotal D false z f)=populationTotal z ∧
    expectation D (generalized D (Fintype.card I) x z f)=ate (Fintype.card I) x z := by
  exact generalized_unbiased D hD hp (Fintype.card I) hN x z f hf

/-- P026-T12, corrected eq. [24] as a sampling variance of the unit ATE
estimator, with the paper's actual population size in the denominator. -/
theorem unit_sampling_variance_identity (D : Design Ω I ℝ) (hp : positiveMarginals D)
    (hN : 0 < Fintype.card I) (x z : I → ℝ) :
    variance D (ht D (Fintype.card I) x z)=
      (armVarianceExpression D true x+armVarianceExpression D false z-
        2*splitCovarianceExpression D x z)/(Fintype.card I : ℝ)^2 := by
  exact ht_variance_identity D hp (Fintype.card I) hN x z

/-- P026-T24(a), eq. [26], unit-population residual variance with N
explicitly the number of units, for predictions fixed across randomizations. -/
theorem unit_generalized_fixed_variance (D : Design Ω I ℝ) (hp : positiveMarginals D)
    (hN : 0 < Fintype.card I) (x z r : I → ℝ) :
    variance D (generalized D (Fintype.card I) x z (fun _ => r))=
      (armVarianceExpression D true (fun i => x i-r i)+
       armVarianceExpression D false (fun i => z i-r i)-
       2*splitCovarianceExpression D (fun i => x i-r i) (fun i => z i-r i))/(Fintype.card I : ℝ)^2 := by
  exact generalized_fixed_variance D hp (Fintype.card I) hN x z r

/-- P026-T13(c), eq. [19]: the unit-population two-arm bias identity,
with N fixed to the number of units and arbitrary randomization-dependent f. -/
theorem unit_generalized_bias (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (hN : 0 < Fintype.card I) (x z : I → ℝ) (f : Ω → I → ℝ) :
    expectation D (generalized D (Fintype.card I) x z f)-ate (Fintype.card I) x z=
      -(∑ i, covariance D (fun w => indicator D true w i) (fun w => f w i)*
        (1/marginal D true i+1/marginal D false i))/(Fintype.card I : ℝ) := by
  exact generalized_bias_two_arm D hD hp (Fintype.card I) hN x z f

/-- P026-T16(a): with the actual unit count, any fixed pretreatment
prediction vector gives the unbiased residual HT estimator described in the
qualified package documentation. -/
theorem unit_fixed_prediction_unbiased (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (hN : 0 < Fintype.card I) (x z r : I → ℝ) :
    expectation D (generalized D (Fintype.card I) x z (fun _ => r))=ate (Fintype.card I) x z := by
  exact fixed_prediction_unbiased D hD hp (Fintype.card I) hN x z r

/-- P026-T5(b): all vector-independent fits give unbiased totals and
ATE on the actual nonempty unit population; N is its cardinality. -/
theorem unit_vector_fitting_unbiased (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (hN : 0 < Fintype.card I) (x z : I → ℝ)
    (J : I → Finset I) (G : ∀ i, (↥(J i) → ℝ) → ℝ)
    (h : ∀ i, independent D (fun w => D.treatment w i) (fittingAssignments D (J i))) :
    let f : Ω → I → ℝ := fun w i => G i (fittingOutcomes D (J i) x z w)
    expectation D (generalizedTotal D true x f)=populationTotal x ∧
    expectation D (generalizedTotal D false z f)=populationTotal z ∧
    expectation D (generalized D (Fintype.card I) x z f)=ate (Fintype.card I) x z := by
  exact vector_fitting_unbiased D hD hp (Fintype.card I) hN x z J G h

end AronowAudit.P026

