import AronowAudit.P005.P005_Formalization

/-!
# P005-T24: exact decomposition in Theorem 4.1 (Econometrica, p. 1509)

`Target` contains the two assignmentwise slope decompositions, the bias
expression, the two first-component (`ν₁`) expectations and their difference.
These exact identities are separate from the third-component identity and
the P005-T20 asymptotic expansion.

`Sk` denotes a mathematical proposition; `Nk` is either `Sk` itself or an
implication from other stated propositions to `Sk`.
-/

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.ExactDecomposition

open AronowAudit.P005 Finset
open scoped BigOperators

noncomputable section

/-!
## Target
-/

/-- **Target (P005-T24).** The exact part of
Theorem 4.1, p. 1509: slope decompositions, bias expression and first-component identities. -/
def Target : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n → standardized P →
    interactedRegular P m →
    (∀ S ∈ design n m,
      armBetaHat P S P.yT = populationSlope P P.yT + armNu1 P S P.yT + armNu2 P S P.yT +
          armNu3 P S P.yT ∧
      armBetaHat P (control S) P.yC = populationSlope P P.yC + armNu1 P (control S) P.yC +
        armNu2 P (control S) P.yC + armNu3 P (control S) P.yC) ∧
    expectation m (fun S => interactedATE P S - ate P) =
      expectation m (fun S => dot (xMean P (control S))
        (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT + armNu2 P S P.yT +
        armNu3 P S P.yT)) ∧
    expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT)) =
      ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P P.yT ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) =
      (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT)) =
      (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC -
        ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P P.yT

/-! ## Mathematical statements -/

/-- **Statement S1.** Complementation is an involutive bijection
from the t-subsets to the c-subsets, so E_t[F(Sᶜ)]=E_c[F(S)]. The finite sum is
transported along this bijection, using binomial symmetry. -/
def S1 : Prop :=
  ∀ (n m : ℕ), m ≤ n → ∀ F : Finset (Fin n) → ℝ,
    expectation m (fun S => F (control S)) = expectation (n - m) F

/-- **Statement S2.** For i≠j and t≥2, counting subsets containing
{i,j} gives E_t I_iI_j=t(t-1)/(N(N-1)). For t=1, I_iI_j=0 and the same formula
is zero. Subtraction is in ℝ. The counting argument uses `inclusion_count`
with `R = {i, j}` when `2 ≤ m`, together with binomial identities. -/
def S2 : Prop :=
  ∀ (n m : ℕ), 2 ≤ n → 0 < m → m ≤ n → ∀ i j : Fin n, i ≠ j →
    expectation m (fun S => indicator S i * indicator S j) =
      (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))

/-- **Statement S3.** E_t[ā_S b̄_S] = ā b̄ +
(N-t)/(t(N-1)) [overline{ab}-ā b̄], including `t = 1`. Expanding
`mean S a * mean S b` as a double sum of indicator products and splitting
the diagonal reduces the identity to `indicator_expectation` and S2. -/
def S3 : Prop :=
  ∀ (n m : ℕ), 2 ≤ n → 0 < m → m ≤ n → ∀ a b : Fin n → ℝ,
    expectation m (fun S => mean S a * mean S b) =
      popMean a * popMean b + ((n : ℝ) - m) / ((m : ℝ) * ((n : ℝ) - 1)) * popCov a b

/-- **Statement S4.** For coordinate k, set a_i=x_ik and
b_i=y_i* x_ik and sum over k to obtain the leverage covariance. Only centered
covariates are needed (no Gram normalisation), and `y` is arbitrary. -/
def S4 : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m ≤ n → xMean P univ = 0 →
    ∀ y : Fin n → ℝ,
      expectation m (fun S => dot (xMean P S) (armNu1 P S y)) =
        ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P y

/-- **Statement S5.** The same computation for a c-subset and yC,
followed by the complement bijection, gives t/[c(N-1)] leverageCov(P,yC).
This is S1 followed by S4 at size `n - m`. -/
def S5 : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n → xMean P univ = 0 →
    ∀ y : Fin n → ℝ,
      expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) y)) =
        (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P y

/-- **Statement S6.** βhat_A=β+ν1_A+ν2_A+ν3_A for both
(A,y)=(S,yT) and (Sᶜ,yC): the first conjunct of `Target`. Both arms are nonempty
(`card S = m > 0`, `card (control S) = n - m > 0`). The identity follows from
`arm_slope_decomposition` and the two determinant facts in `interactedRegular`. -/
def S6 : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n → standardized P →
    interactedRegular P m →
    ∀ S ∈ design n m,
      armBetaHat P S P.yT = populationSlope P P.yT + armNu1 P S P.yT + armNu2 P S P.yT +
          armNu3 P S P.yT ∧
      armBetaHat P (control S) P.yC = populationSlope P P.yC + armNu1 P (control S) P.yC +
        armNu2 P (control S) P.yC + armNu3 P (control S) P.yC

/-- **Statement S7.** Substituting the two slope decompositions
into `interactedATE` gives the bias conjunct of `Target`. The outcome-mean
terms vanish by `mean_unbiased` (and S1 for controls); the population-slope
terms vanish because each `xMean` coordinate is unbiased for `0`. -/
def S7 : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n → standardized P →
    interactedRegular P m →
    expectation m (fun S => interactedATE P S - ate P) =
      expectation m (fun S => dot (xMean P (control S))
        (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT + armNu2 P S P.yT +
        armNu3 P S P.yT))

/-! ## Implications between statements -/

def N1 : Prop := S1
def N2 : Prop := S2
def N3 : Prop := S2 → S3
def N4 : Prop := S3 → S4
def N5 : Prop := S1 → S4 → S5
def N6 : Prop := S6
def N7 : Prop := S1 → S6 → S7

/-! ## Assembly -/

/-- **Assembly.** The stated implications imply `Target`. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7) :
    Target := by
  have s4 : S4 := h4 (h3 h2)
  have s5 : S5 := h5 h1 s4
  have s7 : S7 := h7 h1 h6
  intro n d m P hn hm hmn hP hreg
  have hT := s4 P hn hm hmn.le hP.1 P.yT
  have hC := s5 P hn hm hmn hP.1 P.yC
  refine ⟨h6 P hn hm hmn hP hreg, s7 P hn hm hmn hP hreg, hT, hC, ?_⟩
  rw [hT, hC]

end

end AronowAudit.P005.Wave1.ExactDecomposition
