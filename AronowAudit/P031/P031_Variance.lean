import Mathlib

/-!
P031: Samii and Aronow (2012), pp. 366--370.
The unit labels remain fixed; a finset `s` is the treated group and `sᶜ` is
the control group. This implements the paper's assignment-dependent reordering
without relabeling potential outcomes. All expectations below are actual
finite averages over the uniformly distributed size-M subsets.
-/

namespace AronowAudit.P031

open scoped BigOperators Matrix Topology
open Finset Filter

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- "1 < M < N - 1" (Section 2, p. 366): both realized arms contain
at least two units. This is equivalent to the printed condition. -/
def Admissible (s : Finset ι) : Prop := 1 < s.card ∧ 1 < sᶜ.card

/-- "X_j ∈ {0,1}" (Section 2, p. 366): the treatment indicator. -/
def treatment (s : Finset ι) (i : ι) : ℝ := if i ∈ s then 1 else 0

/-- "Y_i = X_i y_{1i} + (1-X_i)y_{0i}" (equation (1), p. 366). -/
def observed (s : Finset ι) (y1 y0 : ι → ℝ) (i : ι) : ℝ :=
  treatment s i * y1 i + (1 - treatment s i) * y0 i

/-- "v̄ = (1/N) ∑ v_i" (p. 366), restricted to a group when `s ≠ univ`. -/
def groupMean (s : Finset ι) (v : ι → ℝ) : ℝ := (∑ i ∈ s, v i) / s.card

/-- "σ²(v) = (1/N) ∑ (v_i-v̄)²" (p. 366); divisor is N, not N-1. -/
def popVariance (v : ι → ℝ) : ℝ :=
  (∑ i, (v i - groupMean univ v) ^ 2) / Fintype.card ι

/-- "σ(v,w) = (1/N) ∑ (v_i-v̄)(w_i-w̄)" (p. 366). -/
def popCovariance (v w : ι → ℝ) : ℝ :=
  (∑ i, (v i - groupMean univ v) * (w i - groupMean univ w)) / Fintype.card ι

/-- "β = ȳ₁-ȳ₀" (p. 366): finite-population average treatment effect. -/
def averageEffect (y1 y0 : ι → ℝ) : ℝ := groupMean univ y1 - groupMean univ y0

/-- "β̂ = (1/M)∑_T Y_i - (1/(N-M))∑_C Y_i" (equation (2), p. 366). -/
def estimate (s : Finset ι) (Y : ι → ℝ) : ℝ := groupMean s Y - groupMean sᶜ Y

/-- "α̂ = (1/(N-M))∑_C Y_i" (equation (4), p. 367). -/
def intercept (s : Finset ι) (Y : ι → ℝ) : ℝ := groupMean sᶜ Y

/-- "Z_i = (1,X_i)" (p. 367); column indices 0 and 1 represent 1 and 2. -/
def designMatrix (s : Finset ι) : Matrix ι (Fin 2) ℝ :=
  fun i j => if j = 0 then 1 else treatment s i

/-- "(Z'Z)⁻¹" (p. 367), represented by its explicit two-by-two formula. -/
def gramInverse (s : Finset ι) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / (sᶜ.card : ℝ), -(1 / (sᶜ.card : ℝ));
     -(1 / (sᶜ.card : ℝ)), 1 / (s.card : ℝ) + 1 / (sᶜ.card : ℝ)]

/-- "ê_i = Y_i - Z_i(Z'Z)⁻¹Z'Y" (p. 367), using the coefficient
formula in (4). -/
def residual (s : Finset ι) (Y : ι → ℝ) (i : ι) : ℝ :=
  Y i - intercept s Y - treatment s i * estimate s Y

/-- "h_ii = Z_i(Z'Z)⁻¹Z_i'" (p. 367): the leverage, before simplification. -/
def leverage (s : Finset ι) (i : ι) : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 2,
    designMatrix s i a * gramInverse s a b * designMatrix s i b

/-- The coefficient of Y_i in β̂, namely the second row of `(Z'Z)⁻¹Z'`
(equation (4), p. 367). -/
def coefficientWeight (s : Finset ι) (i : ι) : ℝ :=
  ∑ a : Fin 2, gramInverse s 1 a * designMatrix s i a

/-- "σ̂²(y_t)" (p. 366): the traditional sample variance, divisor arm size - 1. -/
def sampleVariance (s : Finset ι) (v : ι → ℝ) : ℝ :=
  (∑ i ∈ s, (v i - groupMean s v) ^ 2) / ((s.card : ℝ) - 1)


/-- "V̂_N(β̂) = σ̂²(y₁)/M + σ̂²(y₀)/(N-M)" (p. 367). -/
def neyman (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  sampleVariance s Y / s.card + sampleVariance sᶜ Y / sᶜ.card

/-- "V̂_HR = N(Z'Z)⁻¹((1/N)∑ Z_i'Z_i ê_i²)(Z'Z)⁻¹" (p. 367).
The [2,2] entry is written as its scalar contraction; N cancels 1/N. -/
def hr (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  ∑ i, coefficientWeight s i ^ 2 * residual s Y i ^ 2

/-- "ê_i²/(1-h_ii) is substituted for ê_i²" (HC2, p. 367).
This is the [2,2] entry of the printed sandwich, expanded as a finite sum. -/
def hc2 (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  ∑ i, coefficientWeight s i ^ 2 * residual s Y i ^ 2 / (1 - leverage s i)


/-- HC1 (footnote 2, p. 368; not defined there): the conventional N/(N-2)
multiple of HR, with two fitted coefficients. This convention is explicit. -/
def hc1 (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  Fintype.card ι / ((Fintype.card ι : ℝ) - 2) * hr s Y

/-- HC3 (footnote 2, p. 368; not defined there): the conventional sandwich
with ê_i²/(1-h_ii)². This convention is explicit. -/
def hc3 (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  ∑ i, coefficientWeight s i ^ 2 * residual s Y i ^ 2 / (1 - leverage s i) ^ 2

/-- "ỹ₀ᵢ = Y_i-X_i β̂" (p. 368): imputed control potential outcomes. -/
def imputed0 (s : Finset ι) (Y : ι → ℝ) (i : ι) : ℝ :=
  Y i - treatment s i * estimate s Y

/-- "ỹ₁ᵢ = Y_i+(1-X_i) β̂" (p. 368): imputed treatment potential outcomes. -/
def imputed1 (s : Finset ι) (Y : ι → ℝ) (i : ι) : ℝ :=
  Y i + (1 - treatment s i) * estimate s Y

/-- The right-hand side of equation (3), p. 366. This expression is kept
separate from the actual randomization variance, which is a finite average. -/
def varianceExpression (M K : ℝ) (y1 y0 : ι → ℝ) : ℝ :=
  Fintype.card ι / ((Fintype.card ι : ℝ) - 1) *
      (popVariance y1 / M + popVariance y0 / K) +
    (2 * popCovariance y1 y0 - popVariance y1 - popVariance y0) /
      ((Fintype.card ι : ℝ) - 1)

/-- "V̂_CE(β̂)" (equation (5), p. 368), with all moments taken from the
imputed potential outcomes, including the covariance's two tildes. -/
def constantEffects (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  varianceExpression s.card sᶜ.card (imputed1 s Y) (imputed0 s Y)

/-- "V̂_OLS = (∑ ê_i²/(N-2))(Z'Z)⁻¹" (p. 369), its [2,2] entry. -/
def ols (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  (∑ i, residual s Y i ^ 2) / ((Fintype.card ι : ℝ) - 2) * gramInverse s 1 1

/-- "E[·] averages over all (N choose M) treatment assignments, each being
equally likely" (p. 366): exactly that finite average. -/
def expectation (M : ℕ) (f : Finset ι → ℝ) : ℝ :=
  (∑ s ∈ (univ : Finset ι).powersetCard M, f s) /
    ((univ : Finset ι).powersetCard M).card

/-- "V(β̂)" (p. 366): variance over the actual uniform randomization,
defined from the estimator, rather than defined to be equation (3). -/
def randomizationVariance (M : ℕ) (y1 y0 : ι → ℝ) : ℝ :=
  expectation M (fun s =>
    (estimate s (observed s y1 y0) -
      expectation M (fun t => estimate t (observed t y1 y0))) ^ 2)


/-- Treatment and control cardinalities sum to N, as in the setting on p. 366. -/
lemma arm_card_sum (s : Finset ι) :
    (s.card : ℝ) + (sᶜ.card : ℝ) = Fintype.card ι := by
  exact_mod_cast s.card_add_card_compl

/-- Both real arm cardinalities exceed one under the standing condition on p. 366; all arm-variance divisors are positive. -/
lemma arm_pos {s : Finset ι} (h : Admissible s) :
    1 < (s.card : ℝ) ∧ 1 < (sᶜ.card : ℝ) := by
  constructor <;> exact_mod_cast (by first | exact h.1 | exact h.2)

/-- For treated units the regression residual is the observation minus the treatment mean, as in the proof of Theorem 1, p. 368. -/
lemma residual_treated (s : Finset ι) (Y : ι → ℝ) {i : ι} (hi : i ∈ s) :
    residual s Y i = Y i - groupMean s Y := by
  simp [residual, intercept, estimate, treatment, hi]

/-- For control units the regression residual is the observation minus the control mean, as in the proof of Theorem 1, p. 368. -/
lemma residual_control (s : Finset ι) (Y : ι → ℝ) {i : ι} (hi : i ∈ sᶜ) :
    residual s Y i = Y i - groupMean sᶜ Y := by
  simp [residual, intercept, treatment, mem_compl.mp hi]

/-- The treatment-coefficient weight is 1/M on treated units, obtained from equation (4), p. 367. -/
lemma weight_treated (s : Finset ι) {i : ι} (hi : i ∈ s) :
    coefficientWeight s i = 1 / (s.card : ℝ) := by
  simp [coefficientWeight, gramInverse, designMatrix, treatment, hi,
    Fin.sum_univ_two]

/-- The treatment-coefficient weight is -1/(N-M) on control units, obtained from equation (4), p. 367. -/
lemma weight_control (s : Finset ι) {i : ι} (hi : i ∈ sᶜ) :
    coefficientWeight s i = -(1 / (sᶜ.card : ℝ)) := by
  simp [coefficientWeight, gramInverse, designMatrix, treatment, mem_compl.mp hi,
    Fin.sum_univ_two]

/-- The leverage display, p. 367: h_ii=1/M on treatment and 1/(N-M)
on control, obtained from the matrix definition. -/
theorem leverage_formula (s : Finset ι) (i : ι) :
    leverage s i = if i ∈ s then 1 / (s.card : ℝ) else 1 / (sᶜ.card : ℝ) := by
  by_cases hi : i ∈ s <;>
    simp [leverage, gramInverse, designMatrix, treatment, hi, Fin.sum_univ_two] <;> ring


/-- Theorem 1 (p. 367; proof p. 368): the HC2 sandwich's treatment variance
equals Neyman's variance estimator for every admissible realized experiment. -/
theorem hc2_eq_neyman (s : Finset ι) (Y : ι → ℝ) (h : Admissible s) :
    hc2 s Y = neyman s Y := by
  have hp := arm_pos h
  have hm : (s.card : ℝ) ≠ 0 := by linarith [hp.1]
  have hk : (sᶜ.card : ℝ) ≠ 0 := by linarith [hp.2]
  have hm1 : (s.card : ℝ) - 1 ≠ 0 := by linarith [hp.1]
  have hk1 : (sᶜ.card : ℝ) - 1 ≠ 0 := by linarith [hp.2]
  unfold hc2 neyman sampleVariance
  rw [← s.sum_add_sum_compl]
  have ht : ∀ i ∈ s,
      coefficientWeight s i ^ 2 * residual s Y i ^ 2 / (1 - leverage s i) =
      (Y i - groupMean s Y) ^ 2 / ((s.card : ℝ) - 1) / s.card := by
    intro i hi
    rw [weight_treated s hi, residual_treated s Y hi, leverage_formula]
    simp only [if_pos hi]
    field_simp
  have hc : ∀ i ∈ sᶜ,
      coefficientWeight s i ^ 2 * residual s Y i ^ 2 / (1 - leverage s i) =
      (Y i - groupMean sᶜ Y) ^ 2 / ((sᶜ.card : ℝ) - 1) / sᶜ.card := by
    intro i hi
    rw [weight_control s hi, residual_control s Y hi, leverage_formula]
    simp only [if_neg (mem_compl.mp hi)]
    field_simp
  simp_rw [Finset.sum_congr rfl ht, Finset.sum_congr rfl hc, Finset.sum_div]

/-- Demeaned observations sum to zero within a nonempty arm, a finite-sum identity supporting the residual proof on p. 368. -/
lemma sum_centered (s : Finset ι) (v : ι → ℝ) (hs : (s.card : ℝ) ≠ 0) :
    ∑ i ∈ s, (v i - groupMean s v) = 0 := by
  simp [groupMean, Finset.sum_sub_distrib, hs]
  field_simp <;> ring

/-- All regression residuals sum to zero, supporting the imputed means used in the proof of Theorem 2, p. 369. -/
lemma residual_sum (s : Finset ι) (Y : ι → ℝ) (h : Admissible s) :
    ∑ i, residual s Y i = 0 := by
  have hp := arm_pos h
  rw [← s.sum_add_sum_compl]
  rw [Finset.sum_congr rfl (fun i hi => residual_treated s Y hi),
    Finset.sum_congr rfl (fun i hi => residual_control s Y hi)]
  rw [sum_centered s Y (by linarith [hp.1]),
    sum_centered sᶜ Y (by linarith [hp.2]), add_zero]

/-- Each imputed control outcome is the residual plus the fitted intercept, supporting equation (5) and Theorem 2, pp. 368--369. -/
lemma imputed0_residual (s : Finset ι) (Y : ι → ℝ) (i : ι) :
    imputed0 s Y i = residual s Y i + intercept s Y := by
  unfold imputed0 residual
  ring

/-- Each imputed treatment outcome is the residual plus the treatment mean, supporting equation (5) and Theorem 2, pp. 368--369. -/
lemma imputed1_residual (s : Finset ι) (Y : ι → ℝ) (i : ι) :
    imputed1 s Y i = residual s Y i + groupMean s Y := by
  unfold imputed1 residual intercept estimate
  ring

/-- The imputed control and treatment population means equal the observed arm means, supporting Theorem 2, p. 369. -/
lemma imputed_means (s : Finset ι) (Y : ι → ℝ) (h : Admissible s) :
    groupMean univ (imputed0 s Y) = intercept s Y ∧
    groupMean univ (imputed1 s Y) = groupMean s Y := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    have hp := arm_pos h
    have hs := arm_card_sum s
    linarith [hp.1, hp.2]
  constructor <;>
    simp [groupMean, imputed0_residual, imputed1_residual,
      Finset.sum_add_distrib, residual_sum s Y h, hn]

/-- The moments needed in the corrected proof of Theorem 2, p. 369, with
two missing tildes restored: all three imputed moments equal (1/N)∑ ê_i².
The original potential-outcome covariance is not asserted. -/
theorem imputed_moments (s : Finset ι) (Y : ι → ℝ) (h : Admissible s) :
    popVariance (imputed0 s Y) = (∑ i, residual s Y i ^ 2) / Fintype.card ι ∧
    popVariance (imputed1 s Y) = (∑ i, residual s Y i ^ 2) / Fintype.card ι ∧
    popCovariance (imputed1 s Y) (imputed0 s Y) =
      (∑ i, residual s Y i ^ 2) / Fintype.card ι := by
  have hm := imputed_means s Y h
  simp [popVariance, popCovariance, hm.1, hm.2,
    imputed0_residual, imputed1_residual, pow_two]

/-- Theorem 2 (p. 369): (N-2)/(N-1) times the homoskedastic OLS
variance estimate equals the constant-effects imputation estimate (5). -/
theorem scaled_ols_eq_constantEffects (s : Finset ι) (Y : ι → ℝ)
    (h : Admissible s) :
    ((Fintype.card ι : ℝ) - 2) / ((Fintype.card ι : ℝ) - 1) * ols s Y =
      constantEffects s Y := by
  have hp := arm_pos h
  have hs := arm_card_sum s
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by linarith [hp.1, hp.2]
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith [hp.1, hp.2]
  have hn2 : (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith [hp.1, hp.2]
  have hm := imputed_moments s Y h
  unfold constantEffects varianceExpression ols
  rw [hm.1, hm.2.1, hm.2.2]
  simp [gramInverse]
  field_simp
  ring

/-- Theorem 3 (p. 369; proof p. 370): in a balanced design the scaled CE
estimate, OLS, Neyman, and HC2 are equal, with the printed finite-N factor. -/
theorem balanced_equivalences (s : Finset ι) (Y : ι → ℝ) (h : Admissible s)
    (hb : Fintype.card ι = 2 * s.card) :
    ((Fintype.card ι : ℝ) - 1) / ((Fintype.card ι : ℝ) - 2) *
        constantEffects s Y = ols s Y ∧
      ols s Y = neyman s Y ∧ neyman s Y = hc2 s Y := by
  have hp := arm_pos h
  have hs := arm_card_sum s
  have hbR : (Fintype.card ι : ℝ) = 2 * (s.card : ℝ) := by exact_mod_cast hb
  have hk : (sᶜ.card : ℝ) = s.card := by linarith
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith [hp.1, hp.2]
  have hn2 : (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith [hp.1, hp.2]
  refine ⟨?_, ?_, (hc2_eq_neyman s Y h).symm⟩
  · rw [← scaled_ols_eq_constantEffects s Y h]
    field_simp
  · unfold ols neyman sampleVariance
    rw [← s.sum_add_sum_compl (fun i => residual s Y i ^ 2)]
    rw [Finset.sum_congr rfl (fun i hi => congrArg (· ^ 2) (residual_treated s Y hi)),
      Finset.sum_congr rfl (fun i hi => congrArg (· ^ 2) (residual_control s Y hi))]
    simp [gramInverse, hk, hbR]
    field_simp
    ring

/-! Finite randomization calculations. -/

/-- Functions agreeing on every admissible size-M assignment have equal randomization expectations, for the finite-average definition on p. 366. -/
lemma expectation_congr (M : ℕ) {f g : Finset ι → ℝ}
    (h : ∀ s ∈ (univ : Finset ι).powersetCard M, f s = g s) :
    expectation M f = expectation M g := by
  unfold expectation
  rw [Finset.sum_congr rfl h]

/-- The randomization expectation of a constant is that constant when size-M assignments exist, for the definition on p. 366. -/
lemma expectation_const (M : ℕ) (hM : M ≤ Fintype.card ι) (c : ℝ) :
    expectation M (fun _ : Finset ι => c) = c := by
  have hc : (((univ : Finset ι).powersetCard M).card : ℝ) ≠ 0 := by
    simp only [card_powersetCard, card_univ]
    exact_mod_cast (Nat.choose_pos hM).ne'
  unfold expectation
  rw [sum_const]
  simp only [nsmul_eq_mul]
  field_simp

/-- Randomization expectation is additive, a finite-sum lemma for the definition on p. 366. -/
lemma expectation_add (M : ℕ) (f g : Finset ι → ℝ) :
    expectation M (fun s => f s + g s) = expectation M f + expectation M g := by
  simp [expectation, Finset.sum_add_distrib, add_div]

/-- Randomization expectation preserves subtraction, a finite-sum lemma for the definition on p. 366. -/
lemma expectation_sub (M : ℕ) (f g : Finset ι → ℝ) :
    expectation M (fun s => f s - g s) = expectation M f - expectation M g := by
  simp [expectation, Finset.sum_sub_distrib, sub_div]

/-- A fixed real scalar factors out of randomization expectation, supporting the finite-average definition on p. 366. -/
lemma expectation_mul (M : ℕ) (c : ℝ) (f : Finset ι → ℝ) :
    expectation M (fun s => c * f s) = c * expectation M f := by
  simp [expectation, ← Finset.mul_sum, mul_div_assoc]

/-- A fixed real divisor factors out of randomization expectation, supporting the finite-average definition on p. 366. -/
lemma expectation_div (M : ℕ) (f : Finset ι → ℝ) (c : ℝ) :
    expectation M (fun s => f s / c) = expectation M f / c := by
  unfold expectation
  rw [← Finset.sum_div]
  ring

/-- Randomization expectation commutes with any finite sum, supporting equation (3) and the definition of E on p. 366. -/
lemma expectation_sum {κ : Type*} (M : ℕ) (t : Finset κ)
    (f : κ → Finset ι → ℝ) :
    expectation M (fun s => ∑ i ∈ t, f i s) = ∑ i ∈ t, expectation M (f i) := by
  unfold expectation
  rw [Finset.sum_comm, Finset.sum_div]

/-- A sum weighted by the binary treatment indicator equals the treated-set sum, implementing the treatment-first indexing on p. 366. -/
lemma treatment_sum (s : Finset ι) (v : ι → ℝ) :
    ∑ i, treatment s i * v i = ∑ i ∈ s, v i := by
  simp [treatment, ← Finset.sum_filter]

/-- A binary treatment indicator equals its square, as required by X in {0,1} on p. 366. -/
lemma treatment_square (s : Finset ι) (i : ι) : treatment s i ^ 2 = treatment s i := by
  by_cases hi : i ∈ s <;> simp [treatment, hi]

/-- The probability of containing a fixed subset b is choose(N-card(b),M-card(b))/choose(N,M), from the uniform design on p. 366. -/
lemma inclusion_count (M : ℕ) (b : Finset ι) (hb : b.card ≤ M) :
    expectation M (fun s => if b ⊆ s then (1 : ℝ) else 0) =
      ((Fintype.card ι - b.card).choose (M - b.card) : ℝ) /
        ((Fintype.card ι).choose M : ℝ) := by
  unfold expectation
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_powersetCard, card_univ]
  rw [card_filter_powersetCard_subset b univ M (subset_univ _) hb, card_univ]

/-- Uniform-size-M randomization gives E[X_i]=M/N (Section 2, p. 366).
The proof counts subsets and uses the fixed total ∑ X_i=M. -/
theorem expected_treatment (M : ℕ) (hM : 1 ≤ M) (hMN : M ≤ Fintype.card ι)
    (i : ι) : expectation M (fun s => treatment s i) = M / (Fintype.card ι : ℝ) := by
  let p : ℝ := ((Fintype.card ι - 1).choose (M - 1) : ℝ) /
    ((Fintype.card ι).choose M : ℝ)
  have he : ∀ j : ι, expectation M (fun s => treatment s j) = p := by
    intro j
    simpa [treatment, p] using inclusion_count M {j} (by simpa)
  have ht : expectation M (fun s : Finset ι => ∑ j, treatment s j) = M := by
    rw [expectation_congr M (g := fun _ => (M : ℝ))]
    · exact expectation_const M hMN M
    · intro s hs
      have hc := (mem_powersetCard.mp hs).2
      simpa [treatment, ← Finset.sum_filter, hc]
  rw [expectation_sum] at ht
  simp only [he, Finset.sum_const, card_univ, nsmul_eq_mul] at ht
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    have hnN : 0 < Fintype.card ι := by omega
    exact_mod_cast hnN.ne'
  rw [he i]
  apply (eq_div_iff hn).mpr
  nlinarith

/-- Distinct inclusion probabilities are M(M-1)/(N(N-1)), the finite
sampling fact underlying equation (3), p. 366. -/
theorem expected_treatment_pair (M : ℕ) (hM : 2 ≤ M) (hMN : M ≤ Fintype.card ι)
    (i j : ι) (hij : i ≠ j) :
    expectation M (fun s => treatment s i * treatment s j) =
      (M : ℝ) * (M - 1) / ((Fintype.card ι : ℝ) * (Fintype.card ι - 1)) := by
  let p : ℝ := ((Fintype.card ι - 2).choose (M - 2) : ℝ) /
    ((Fintype.card ι).choose M : ℝ)
  have he : ∀ a b : ι, a ≠ b →
      expectation M (fun s => treatment s a * treatment s b) = p := by
    intro a b hab
    have hf : (fun s : Finset ι => treatment s a * treatment s b) =
        (fun s => if ({a, b} : Finset ι) ⊆ s then (1 : ℝ) else 0) := by
      funext s
      by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;>
        simp [treatment, ha, hb, Finset.insert_subset_iff]
    rw [hf]
    simpa [p, hab] using inclusion_count M {a, b} (by simp [hab, hM])
  have hd : ∀ a : ι, expectation M (fun s => treatment s a * treatment s a) =
      M / (Fintype.card ι : ℝ) := by
    intro a
    simp_rw [← pow_two, treatment_square]
    exact expected_treatment M (by omega) hMN a
  have hall : ∀ a b : ι,
      expectation M (fun s => treatment s a * treatment s b) =
      if a = b then M / (Fintype.card ι : ℝ) else p := by
    intro a b
    by_cases hab : a = b
    · subst b; simp [hd]
    · simp [hab, he a b hab]
  have ht : expectation M (fun s : Finset ι =>
      ∑ a, ∑ b, treatment s a * treatment s b) = (M : ℝ) ^ 2 := by
    rw [expectation_congr M (g := fun _ => (M : ℝ) ^ 2)]
    · exact expectation_const M hMN _
    · intro s hs
      have hc := (mem_powersetCard.mp hs).2
      simp [← Finset.mul_sum, ← Finset.sum_mul, treatment,
        ← Finset.sum_filter, hc, pow_two]
  simp_rw [expectation_sum, hall] at ht
  have hi : ∀ a : ι, (∑ b : ι, if a = b then (M : ℝ) / Fintype.card ι else p) =
      M / (Fintype.card ι : ℝ) + ((Fintype.card ι : ℝ) - 1) * p := by
    intro a
    have heq : ∀ b : ι, (if a = b then (M : ℝ) / Fintype.card ι else p) =
        p + if a = b then (M : ℝ) / Fintype.card ι - p else 0 := by
      intro b
      split_ifs <;> ring
    simp_rw [heq]
    simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
      sum_ite_eq, mem_univ, ite_eq_left]
    ring
  simp_rw [hi] at ht
  simp only [sum_const, card_univ, nsmul_eq_mul] at ht
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    have hnN : 0 < Fintype.card ι := by omega
    exact_mod_cast hnN.ne'
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have hnR : 2 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 2 ≤ Fintype.card ι)
    linarith
  rw [he i j hij]
  have hc : (Fintype.card ι : ℝ) * ((M : ℝ) / Fintype.card ι) = M := by
    field_simp
  rw [mul_add, hc] at ht
  field_simp
  nlinarith

/-- Within-arm centered sum of squares equals the raw square sum minus squared raw sum divided by arm size, supporting the variance definitions on p. 366. -/
lemma group_sse_raw (s : Finset ι) (v : ι → ℝ) (hs : (s.card : ℝ) ≠ 0) :
    ∑ i ∈ s, (v i - groupMean s v) ^ 2 =
      (∑ i ∈ s, v i ^ 2) - (∑ i ∈ s, v i) ^ 2 / s.card := by
  have he : ∀ i : ι, (v i - groupMean s v) ^ 2 =
      v i ^ 2 - 2 * groupMean s v * v i + groupMean s v ^ 2 := by intro i; ring
  simp_rw [he]
  simp only [sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum, sum_const, nsmul_eq_mul]
  unfold groupMean
  field_simp
  ring

/-- Population variance equals the second raw moment minus the squared first moment, for the divisor-N definition on p. 366. -/
lemma pop_variance_raw (v : ι → ℝ) (hn : (Fintype.card ι : ℝ) ≠ 0) :
    popVariance v = (∑ i, v i ^ 2) / Fintype.card ι -
      ((∑ i, v i) / (Fintype.card ι : ℝ)) ^ 2 := by
  unfold popVariance
  rw [group_sse_raw univ v (by simpa only [card_univ] using hn)]
  simp only [card_univ]
  field_simp <;> ring

/-- The expected treated sum is M/N times the population sum, a finite sampling lemma supporting unbiasedness on p. 366. -/
lemma expected_group_sum (M : ℕ) (hM : 1 ≤ M) (hMN : M ≤ Fintype.card ι)
    (v : ι → ℝ) :
    expectation M (fun s => ∑ i ∈ s, v i) =
      (M : ℝ) / Fintype.card ι * ∑ i, v i := by
  calc
    expectation M (fun s => ∑ i ∈ s, v i) =
        expectation M (fun s => ∑ i, v i * treatment s i) := by
      apply expectation_congr
      intro s _
      simp_rw [mul_comm (v _) (treatment _ _)]
      exact (treatment_sum s v).symm
    _ = ∑ i, v i * expectation M (fun s => treatment s i) := by
      simp_rw [expectation_sum, expectation_mul]
    _ = _ := by
      simp_rw [expected_treatment M hM hMN]
      rw [← Finset.sum_mul]
      ring

/-- The second moment of a treated sum is obtained from the single- and pair-inclusion probabilities, supporting equation (3), p. 366. -/
lemma expected_group_sum_square (M : ℕ) (hM : 2 ≤ M) (hMN : M ≤ Fintype.card ι)
    (v : ι → ℝ) :
    expectation M (fun s => (∑ i ∈ s, v i) ^ 2) =
      (M : ℝ) / Fintype.card ι * (∑ i, v i ^ 2) +
      ((M : ℝ) * (M - 1) / ((Fintype.card ι : ℝ) * (Fintype.card ι - 1))) *
        ((∑ i, v i) ^ 2 - ∑ i, v i ^ 2) := by
  let p : ℝ := M / (Fintype.card ι : ℝ)
  let q : ℝ := (M : ℝ) * (M - 1) /
    ((Fintype.card ι : ℝ) * (Fintype.card ι - 1))
  have he : ∀ i j : ι, expectation M (fun s => treatment s i * treatment s j) =
      if i = j then p else q := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [ite_eq_left rfl, ← pow_two, treatment_square]
      exact expected_treatment M (by omega) hMN i
    · simp only [ite_eq_right hij]
      exact expected_treatment_pair M hM hMN i j hij
  have hs : ∀ s : Finset ι, (∑ i ∈ s, v i) ^ 2 =
      ∑ i, ∑ j, (v i * v j) * (treatment s i * treatment s j) := by
    intro s
    rw [← treatment_sum s v, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [expectation_congr M (fun s _ => hs s)]
  simp_rw [expectation_sum, expectation_mul, he]
  have ht : ∀ i j : ι, (v i * v j) * (if i = j then p else q) =
      q * (v i * v j) + if i = j then (p - q) * v i ^ 2 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j; simp; ring
    · simp [hij]; ring
  simp_rw [ht]
  simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_eq_left,
    ← Finset.mul_sum]
  simp only [← Finset.sum_mul]
  change q * ((∑ i, v i) * ∑ i, v i) + (p - q) * (∑ i, v i ^ 2) = _
  dsimp [p, q]
  ring

/-- Unbiasedness of σ̂²_FP, p. 366 (citation to Cochran): sample variance
has expectation N/(N-1) times the population variance, so the finite-
population correction has exactly the paper's expectation. -/
theorem expected_sample_variance (M : ℕ) (hM : 2 ≤ M)
    (hMN : M ≤ Fintype.card ι) (v : ι → ℝ) :
    expectation M (fun s => sampleVariance s v) =
      Fintype.card ι / ((Fintype.card ι : ℝ) - 1) * popVariance v := by
  have hmR : 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hnR : 2 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 2 ≤ Fintype.card ι)
  have hm : (M : ℝ) ≠ 0 := by linarith
  have hm1 : (M : ℝ) - 1 ≠ 0 := by linarith
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  rw [expectation_congr M (g := fun s =>
    ((∑ i ∈ s, v i ^ 2) - (∑ i ∈ s, v i) ^ 2 / M) / ((M : ℝ) - 1))]
  · rw [expectation_div, expectation_sub, expectation_div,
      expected_group_sum M (by omega) hMN, expected_group_sum_square M hM hMN,
      pop_variance_raw v hn]
    field_simp
    ring
  · intro s hs
    have hc := (mem_powersetCard.mp hs).2
    unfold sampleVariance
    rw [group_sse_raw s v (by simpa only [hc] using hm), hc]


/-- Complementing assignments changes a uniform size-M design into the uniform size-(N-M) design, supporting both arm variances on p. 366. -/
lemma expectation_compl (M : ℕ) (hMN : M ≤ Fintype.card ι) (f : Finset ι → ℝ) :
    expectation M (fun s => f sᶜ) = expectation (Fintype.card ι - M) f := by
  unfold expectation
  have hs : (∑ s ∈ (univ : Finset ι).powersetCard M, f sᶜ) =
      ∑ t ∈ (univ : Finset ι).powersetCard (Fintype.card ι - M), f t := by
    apply Finset.sum_bij (fun s _ => sᶜ)
    · intro s hs
      simp only [mem_powersetCard, subset_univ, true_and] at hs ⊢
      simp [card_compl, hs]
    · intro s _ t _ he
      simpa using congrArg (fun a : Finset ι => aᶜ) he
    · intro t ht
      refine ⟨tᶜ, ?_, by simp⟩
      simp only [mem_powersetCard, subset_univ, true_and] at ht ⊢
      rw [card_compl, ht]
      omega
    · intro s _; rfl
  rw [hs]
  simp only [card_powersetCard, card_univ, Nat.choose_symm hMN]

/-- A treated unit reveals its treatment potential outcome, exactly equation (1), p. 366. -/
lemma observed_treatment (s : Finset ι) (y1 y0 : ι → ℝ) {i : ι} (hi : i ∈ s) :
    observed s y1 y0 i = y1 i := by simp [observed, treatment, hi]


/-- A control unit reveals its control potential outcome, exactly equation (1), p. 366. -/
lemma observed_control (s : Finset ι) (y1 y0 : ι → ℝ) {i : ι} (hi : i ∈ sᶜ) :
    observed s y1 y0 i = y0 i := by simp [observed, treatment, mem_compl.mp hi]

/-- Sample variance depends only on values in the specified arm, supporting the sample-variance definitions on p. 366. -/
lemma sample_variance_congr (s : Finset ι) {v w : ι → ℝ} (h : ∀ i ∈ s, v i = w i) :
    sampleVariance s v = sampleVariance s w := by
  have hm : groupMean s v = groupMean s w := by
    unfold groupMean
    rw [Finset.sum_congr rfl h]
  unfold sampleVariance
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i hi]

/-- The observed Neyman estimate uses the treated sample variance of y1 and the control sample variance of y0, as on p. 367. -/
lemma observed_neyman (s : Finset ι) (y1 y0 : ι → ℝ) :
    neyman s (observed s y1 y0) =
      sampleVariance s y1 / s.card + sampleVariance sᶜ y0 / sᶜ.card := by
  unfold neyman
  rw [sample_variance_congr s (fun i hi => observed_treatment s y1 y0 hi),
    sample_variance_congr sᶜ (fun i hi => observed_control s y1 y0 hi)]

/-- The expectation display on p. 367: E[V̂_N] equals the Neyman
upper bound obtained by omitting the negative treatment-effect term in (3). -/
theorem expected_neyman (M : ℕ) (hM : 2 ≤ M) (hK : 2 ≤ Fintype.card ι - M)
    (hMN : M ≤ Fintype.card ι) (y1 y0 : ι → ℝ) :
    expectation M (fun s => neyman s (observed s y1 y0)) =
      Fintype.card ι / ((Fintype.card ι : ℝ) - 1) *
        (popVariance y1 / M + popVariance y0 / (Fintype.card ι - M)) := by
  rw [expectation_congr M (g := fun s =>
    sampleVariance s y1 / M + sampleVariance sᶜ y0 / (Fintype.card ι - M))]
  · rw [expectation_add, expectation_div,
      expected_sample_variance M hM hMN, expectation_div,
      expectation_compl M hMN (fun s => sampleVariance s y0),
      expected_sample_variance (Fintype.card ι - M) hK (by omega)]
    ring
  · intro s hs
    have hc := (mem_powersetCard.mp hs).2
    rw [observed_neyman, card_compl, hc, Nat.cast_sub hMN]

/-- Randomization variance equals the second raw moment minus squared expectation, supporting V in equation (3), p. 366. -/
lemma expectation_centered_square (M : ℕ) (hMN : M ≤ Fintype.card ι)
    (f : Finset ι → ℝ) :
    expectation M (fun s => (f s - expectation M f) ^ 2) =
      expectation M (fun s => f s ^ 2) - expectation M f ^ 2 := by
  have he : ∀ s : Finset ι, (f s - expectation M f) ^ 2 =
      f s ^ 2 - (2 * expectation M f) * f s + expectation M f ^ 2 := by
    intro s; ring
  simp_rw [he, expectation_add, expectation_sub, expectation_mul,
    expectation_const M hMN]
  ring

/-- A centered treated sum has variance M(N-M)/(N-1) times the population variance, the finite sampling calculation supporting equation (3), p. 366. -/
lemma expected_group_deviation (M : ℕ) (hM : 2 ≤ M) (hMN : M ≤ Fintype.card ι)
    (v : ι → ℝ) :
    expectation M (fun s => ((∑ i ∈ s, v i) - (M : ℝ) * groupMean univ v) ^ 2) =
      (M : ℝ) * ((Fintype.card ι : ℝ) - M) / ((Fintype.card ι : ℝ) - 1) *
        popVariance v := by
  have hmR : 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hnR : 2 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 2 ≤ Fintype.card ι)
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have he : (M : ℝ) * groupMean univ v =
      expectation M (fun s => ∑ i ∈ s, v i) := by
    rw [expected_group_sum M (by omega) hMN]
    simp only [groupMean, card_univ]
    ring
  rw [he, expectation_centered_square M hMN,
    expected_group_sum_square M hM hMN, expected_group_sum M (by omega) hMN,
    pop_variance_raw v hn]
  field_simp
  ring

/-- Group means preserve real linear combinations, supporting the moment definitions on p. 366. -/
lemma group_mean_linear (s : Finset ι) (a b : ℝ) (v w : ι → ℝ) :
    groupMean s (fun i => a * v i + b * w i) =
      a * groupMean s v + b * groupMean s w := by
  simp only [groupMean, sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The variance of a linear combination equals the sum of scaled variances and twice the covariance term, supporting equation (3), p. 366. -/
lemma pop_variance_linear (a b : ℝ) (v w : ι → ℝ) :
    popVariance (fun i => a * v i + b * w i) =
      a ^ 2 * popVariance v + b ^ 2 * popVariance w + 2 * a * b * popCovariance v w := by
  unfold popVariance popCovariance
  rw [group_mean_linear]
  have he : ∀ i : ι,
      (a * v i + b * w i - (a * groupMean univ v + b * groupMean univ w)) ^ 2 =
      a ^ 2 * (v i - groupMean univ v) ^ 2 + b ^ 2 * (w i - groupMean univ w) ^ 2 +
        (2 * a * b) * ((v i - groupMean univ v) * (w i - groupMean univ w)) := by
    intro i; ring
  simp_rw [he]
  simp only [sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Observed treatment and control means equal the means of the revealed potential outcomes in their respective arms, by equations (1)--(2), p. 366. -/
lemma observed_group_means (s : Finset ι) (y1 y0 : ι → ℝ) :
    groupMean s (observed s y1 y0) = groupMean s y1 ∧
      groupMean sᶜ (observed s y1 y0) = groupMean sᶜ y0 := by
  constructor <;> unfold groupMean
  · rw [Finset.sum_congr rfl (fun i hi => observed_treatment s y1 y0 hi)]
  · rw [Finset.sum_congr rfl (fun i hi => observed_control s y1 y0 hi)]

/-- The difference in means is a treated sum of y1/M+y0/(N-M) minus the fixed full control sum divided by N-M, supporting equation (3), p. 366. -/
lemma linearized_estimate (s : Finset ι) (y1 y0 : ι → ℝ) :
    estimate s (observed s y1 y0) =
      (∑ i ∈ s, (y1 i / (s.card : ℝ) + y0 i / (sᶜ.card : ℝ))) -
        (∑ i, y0 i) / sᶜ.card := by
  unfold estimate
  rw [(observed_group_means s y1 y0).1, (observed_group_means s y1 y0).2]
  unfold groupMean
  rw [sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
    ← s.sum_add_sum_compl y0]
  ring

/-- E[β̂]=β (Section 2, p. 366): the difference in means is exactly
unbiased under the uniform fixed-treatment-count randomization. -/
theorem estimate_unbiased (M : ℕ) (hM : 2 ≤ M) (hK : 2 ≤ Fintype.card ι - M)
    (hMN : M ≤ Fintype.card ι) (y1 y0 : ι → ℝ) :
    expectation M (fun s => estimate s (observed s y1 y0)) = averageEffect y1 y0 := by
  have hmR : 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hkR : 2 ≤ (Fintype.card ι : ℝ) - M := by exact_mod_cast hK
  have hnR : 2 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 2 ≤ Fintype.card ι)
  have hm : (M : ℝ) ≠ 0 := by linarith
  have hk : (Fintype.card ι : ℝ) - M ≠ 0 := by linarith
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by linarith
  rw [expectation_congr M (g := fun s =>
    (∑ i ∈ s, (y1 i / (M : ℝ) + y0 i / ((Fintype.card ι : ℝ) - M))) -
      (∑ i, y0 i) / ((Fintype.card ι : ℝ) - M))]
  · rw [expectation_sub, expectation_const M hMN,
      expected_group_sum M (by omega) hMN]
    simp only [sum_add_distrib, ← Finset.sum_div, averageEffect, groupMean, card_univ]
    field_simp
    ring
  · intro s hs
    rw [linearized_estimate, card_compl, (mem_powersetCard.mp hs).2, Nat.cast_sub hMN]

/-- Equation (3), p. 366: the variance of the actual difference-in-means
randomization distribution equals the printed finite-population formula.
Neither equation (3) nor unbiasedness is taken as an axiom. -/
theorem randomization_variance_identity (M : ℕ) (hM : 2 ≤ M)
    (hK : 2 ≤ Fintype.card ι - M) (hMN : M ≤ Fintype.card ι) (y1 y0 : ι → ℝ) :
    randomizationVariance M y1 y0 =
      varianceExpression M ((Fintype.card ι : ℝ) - M) y1 y0 := by
  have hmR : 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hkR : 2 ≤ (Fintype.card ι : ℝ) - M := by exact_mod_cast hK
  have hnR : 2 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 2 ≤ Fintype.card ι)
  have hm : (M : ℝ) ≠ 0 := by linarith
  have hk : (Fintype.card ι : ℝ) - M ≠ 0 := by linarith
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  let w : ι → ℝ := fun i => y1 i / (M : ℝ) + y0 i / ((Fintype.card ι : ℝ) - M)
  have hc : (M : ℝ) * groupMean univ w =
      averageEffect y1 y0 + (∑ i, y0 i) / ((Fintype.card ι : ℝ) - M) := by
    simp only [w, groupMean, averageEffect, sum_add_distrib, ← Finset.sum_div, card_univ]
    field_simp
    ring
  unfold randomizationVariance
  rw [estimate_unbiased M hM hK hMN]
  rw [expectation_congr M (g := fun s => ((∑ i ∈ s, w i) - (M : ℝ) * groupMean univ w) ^ 2)]
  · rw [expected_group_deviation M hM hMN]
    have hw : w = fun i => (1 / (M : ℝ)) * y1 i +
        (1 / ((Fintype.card ι : ℝ) - M)) * y0 i := by
      funext i; simp [w, div_eq_mul_inv, mul_comm]
    rw [hw, pop_variance_linear]
    unfold varianceExpression
    field_simp
    ring
  · intro s hs
    rw [linearized_estimate, card_compl, (mem_powersetCard.mp hs).2, Nat.cast_sub hMN]
    rw [hc]
    dsimp only [w]
    congr 1
    ring


/-- The bias display on p. 367: the exact bias of the Neyman estimate
is σ²(y₁-y₀)/(N-1), hence is nonnegative. -/
theorem neyman_bias_identity (M : ℕ) (hM : 2 ≤ M) (hK : 2 ≤ Fintype.card ι - M)
    (hMN : M ≤ Fintype.card ι) (y1 y0 : ι → ℝ) :
    expectation M (fun s => neyman s (observed s y1 y0)) -
        randomizationVariance M y1 y0 =
      popVariance (fun i => y1 i - y0 i) / ((Fintype.card ι : ℝ) - 1) := by
  rw [expected_neyman M hM hK hMN, randomization_variance_identity M hM hK hMN]
  have he := pop_variance_linear 1 (-1) y1 y0
  simp only [one_mul, neg_one_mul, one_pow, neg_one_sq] at he
  have he' : popVariance (fun i => y1 i - y0 i) =
      popVariance y1 + popVariance y0 - 2 * popCovariance y1 y0 := by
    convert he using 1 <;> ring
  rw [he']
  unfold varianceExpression
  ring

/-- Corollary 1 (p. 368): HC2 is conservative in expectation over all
uniform size-M assignments of this finite population. -/
theorem hc2_conservative (M : ℕ) (hM : 2 ≤ M) (hK : 2 ≤ Fintype.card ι - M)
    (hMN : M ≤ Fintype.card ι) (y1 y0 : ι → ℝ) :
    randomizationVariance M y1 y0 ≤ expectation M (fun s => hc2 s (observed s y1 y0)) := by
  have hnR : 2 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 2 ≤ Fintype.card ι)
  rw [expectation_congr M (g := fun s => neyman s (observed s y1 y0))]
  · have hb := neyman_bias_identity M hM hK hMN y1 y0
    have hnonneg : 0 ≤ popVariance (fun i => y1 i - y0 i) /
        ((Fintype.card ι : ℝ) - 1) := by
      apply div_nonneg
      · unfold popVariance; positivity
      · linarith
    linarith
  · intro s hs
    apply hc2_eq_neyman
    have hc := (mem_powersetCard.mp hs).2
    constructor
    · rw [hc]; omega
    · rw [card_compl, hc]; omega

/-- The [2,2] inverse-normal-matrix entry used in the proof of Theorem 2,
p. 369, is N/(M(N-M)). -/
theorem gram_inverse_coefficient (s : Finset ι) (h : Admissible s) :
    gramInverse s 1 1 = (Fintype.card ι : ℝ) / ((s.card : ℝ) * sᶜ.card) := by
  have hp := arm_pos h
  have hm : (s.card : ℝ) ≠ 0 := by linarith [hp.1]
  have hk : (sᶜ.card : ℝ) ≠ 0 := by linarith [hp.2]
  have hs := arm_card_sum s
  simp [gramInverse]
  field_simp
  nlinarith

/-- Regression SSE equals (M-1) times the treated sample variance plus (N-M-1) times the control sample variance, supporting the OLS formula on p. 369. -/
lemma residual_sse (s : Finset ι) (Y : ι → ℝ) (h : Admissible s) :
    (∑ i, residual s Y i ^ 2) =
      ((s.card : ℝ) - 1) * sampleVariance s Y +
        ((sᶜ.card : ℝ) - 1) * sampleVariance sᶜ Y := by
  have hp := arm_pos h
  have hm1 : (s.card : ℝ) - 1 ≠ 0 := by linarith [hp.1]
  have hk1 : (sᶜ.card : ℝ) - 1 ≠ 0 := by linarith [hp.2]
  rw [← s.sum_add_sum_compl]
  rw [Finset.sum_congr rfl (fun i hi => congrArg (· ^ 2) (residual_treated s Y hi)),
    Finset.sum_congr rfl (fun i hi => congrArg (· ^ 2) (residual_control s Y hi))]
  unfold sampleVariance
  field_simp

/-- An exact finite lemma supporting the unnumbered OLS passage, p. 369:
the expectation of OLS is expressed in terms of the population variances
and covariance. An expectation limit is kept distinct
from an estimator probability limit. -/
theorem expected_ols (M : ℕ) (hM : 2 ≤ M) (hK : 2 ≤ Fintype.card ι - M)
    (hMN : M ≤ Fintype.card ι) (y1 y0 : ι → ℝ) :
    expectation M (fun s => ols s (observed s y1 y0)) =
      Fintype.card ι / (((Fintype.card ι : ℝ) - 1) * (Fintype.card ι - 2)) *
        (((M : ℝ) - 1) * popVariance y1 +
          ((Fintype.card ι : ℝ) - M - 1) * popVariance y0) *
        (1 / (M : ℝ) + 1 / ((Fintype.card ι : ℝ) - M)) := by
  have hnR : 4 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 4 ≤ Fintype.card ι)
  have hmR : 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hkR : 2 ≤ (Fintype.card ι : ℝ) - M := by exact_mod_cast hK
  have hm : (M : ℝ) ≠ 0 := by linarith
  have hk : (Fintype.card ι : ℝ) - M ≠ 0 := by linarith
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  rw [expectation_congr M (g := fun s =>
    ((1 / (M : ℝ) + 1 / ((Fintype.card ι : ℝ) - M)) / ((Fintype.card ι : ℝ) - 2)) *
      (((M : ℝ) - 1) * sampleVariance s y1 +
        ((Fintype.card ι : ℝ) - M - 1) * sampleVariance sᶜ y0))]
  · rw [expectation_mul, expectation_add, expectation_mul, expectation_mul,
      expected_sample_variance M hM hMN,
      expectation_compl M hMN (fun s => sampleVariance s y0),
      expected_sample_variance (Fintype.card ι - M) hK (by omega)]
    field_simp <;> ring
  · intro s hs
    have hc := (mem_powersetCard.mp hs).2
    have ha : Admissible s := by
      constructor
      · rw [hc]; omega
      · rw [card_compl, hc]; omega
    unfold ols
    rw [residual_sse s (observed s y1 y0) ha]
    rw [sample_variance_congr s (fun i hi => observed_treatment s y1 y0 hi),
      sample_variance_congr sᶜ (fun i hi => observed_control s y1 y0 hi)]
    simp [gramInverse, card_compl, hc, Nat.cast_sub hMN]
    ring

/-- A leverage-adjusted scalar sandwich splits into treated and control centered-square sums for any adjustment power, supporting HC2 on p. 367 and footnote 2 on p. 368. -/
lemma robust_group_formula (s : Finset ι) (Y : ι → ℝ) (r : ℕ) :
    (∑ i, coefficientWeight s i ^ 2 * residual s Y i ^ 2 / (1 - leverage s i) ^ r) =
      (∑ i ∈ s, (Y i - groupMean s Y) ^ 2) / (s.card : ℝ) ^ 2 /
        (1 - 1 / (s.card : ℝ)) ^ r +
      (∑ i ∈ sᶜ, (Y i - groupMean sᶜ Y) ^ 2) / (sᶜ.card : ℝ) ^ 2 /
        (1 - 1 / (sᶜ.card : ℝ)) ^ r := by
  rw [← s.sum_add_sum_compl]
  have ht : ∀ i ∈ s,
      coefficientWeight s i ^ 2 * residual s Y i ^ 2 / (1 - leverage s i) ^ r =
      (Y i - groupMean s Y) ^ 2 / (s.card : ℝ) ^ 2 / (1 - 1 / (s.card : ℝ)) ^ r := by
    intro i hi
    rw [weight_treated s hi, residual_treated s Y hi, leverage_formula]
    simp only [ite_eq_left hi, div_eq_mul_inv, inv_pow]
    ring
  have hc : ∀ i ∈ sᶜ,
      coefficientWeight s i ^ 2 * residual s Y i ^ 2 / (1 - leverage s i) ^ r =
      (Y i - groupMean sᶜ Y) ^ 2 / (sᶜ.card : ℝ) ^ 2 /
        (1 - 1 / (sᶜ.card : ℝ)) ^ r := by
    intro i hi
    rw [weight_control s hi, residual_control s Y hi, leverage_formula]
    simp only [ite_eq_right (mem_compl.mp hi), div_eq_mul_inv, inv_pow, neg_sq]
    ring
  rw [Finset.sum_congr rfl ht, Finset.sum_congr rfl hc]
  simp only [← Finset.sum_div]

/-- Exact HR/HC1/HC3 relations supporting footnote 2, p. 368. They are
derived from the leverage display; they do not assert unconditional
asymptotic equivalence when an arm remains fixed. -/
theorem hc_variant_relations (s : Finset ι) (Y : ι → ℝ) (h : Admissible s) :
    hr s Y = (1 - 1 / (s.card : ℝ)) * (sampleVariance s Y / s.card) +
        (1 - 1 / (sᶜ.card : ℝ)) * (sampleVariance sᶜ Y / sᶜ.card) ∧
    hc3 s Y = (sampleVariance s Y / s.card) / (1 - 1 / (s.card : ℝ)) +
        (sampleVariance sᶜ Y / sᶜ.card) / (1 - 1 / (sᶜ.card : ℝ)) ∧
    hc1 s Y = Fintype.card ι / ((Fintype.card ι : ℝ) - 2) * hr s Y := by
  have hp := arm_pos h
  have hm : (s.card : ℝ) ≠ 0 := by linarith [hp.1]
  have hk : (sᶜ.card : ℝ) ≠ 0 := by linarith [hp.2]
  have hm1 : (s.card : ℝ) - 1 ≠ 0 := by linarith [hp.1]
  have hk1 : (sᶜ.card : ℝ) - 1 ≠ 0 := by linarith [hp.2]
  refine ⟨?_, ?_, rfl⟩
  · have hg := robust_group_formula s Y 0
    simp only [pow_zero, div_one] at hg
    change hr s Y = _ at hg
    rw [hg]
    unfold sampleVariance
    field_simp <;> ring
  · unfold hc3
    rw [robust_group_formula s Y 2]
    unfold sampleVariance
    field_simp <;> ring


/-- A finite lemma for footnote 2, p. 368.
With two treated units and zero control outcomes, HR=HC2/2 and HC3=2 HC2,
and HC1=N HC2/(2(N-2)), including assignments with zero HC2. -/
theorem two_treated_zero_controls (s : Finset ι) (Y : ι → ℝ) (h : Admissible s)
    (hM : s.card = 2) (hzero : ∀ i ∈ sᶜ, Y i = 0) :
    hr s Y = hc2 s Y / 2 ∧ hc3 s Y = 2 * hc2 s Y ∧
      hc1 s Y = Fintype.card ι / (2 * ((Fintype.card ι : ℝ) - 2)) * hc2 s Y := by
  have hz : sampleVariance sᶜ Y = 0 := by
    rw [sample_variance_congr sᶜ hzero]
    simp [sampleVariance, groupMean]
  have hv : hc2 s Y = sampleVariance s Y / 2 := by
    rw [hc2_eq_neyman s Y h]
    simp [neyman, hz, hM]
  have hh := hc_variant_relations s Y h
  have he : hr s Y = hc2 s Y / 2 := by
    rw [hh.1, hz, hM, hv]
    norm_num
    ring
  refine ⟨he, ?_, ?_⟩
  · rw [hh.2.1, hz, hM, hv]
    norm_num
    ring
  · rw [hh.2.2, he]
    have hp := arm_pos h
    have hs := arm_card_sum s
    have hn2 : (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith [hp.1, hp.2]
    field_simp <;> ring

/-- The equivalent form of equation (3), p. 366, used to compare leading
variance terms on p. 369. -/
theorem randomization_variance_alternative (M : ℕ) (hM : 2 ≤ M)
    (hK : 2 ≤ Fintype.card ι - M) (hMN : M ≤ Fintype.card ι) (y1 y0 : ι → ℝ) :
    randomizationVariance M y1 y0 = 1 / ((Fintype.card ι : ℝ) - 1) *
      ((((Fintype.card ι : ℝ) - M) / M) * popVariance y1 +
        ((M : ℝ) / ((Fintype.card ι : ℝ) - M)) * popVariance y0 + 2 * popCovariance y1 y0) := by
  have hmR : 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hkR : 2 ≤ (Fintype.card ι : ℝ) - M := by exact_mod_cast hK
  have hnR : 4 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 4 ≤ Fintype.card ι)
  have hm : (M : ℝ) ≠ 0 := by linarith
  have hk : (Fintype.card ι : ℝ) - M ≠ 0 := by linarith
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  rw [randomization_variance_identity M hM hK hMN]
  unfold varianceExpression
  field_simp
  ring


/-! Asymptotic definitions: explicit finite-population sequences and filters.
The paper does not supply these definitions. They give operational meanings
to its wording, and the additional hypotheses are stated explicitly.
-/

/-- "An experiment on a finite population U of N units ... 1<M<N-1"
(Section 2, p. 366), with both potential-outcome schedules fixed. Unit
labels are `Fin N`; a sequence may vary N, M, and both schedules. -/
structure Population where
  N : ℕ
  M : ℕ
  y1 : Fin N → ℝ
  y0 : Fin N → ℝ
  hM : 1 < M
  hMN : M < N - 1

/-- A variance estimate for a realized assignment in a population. This
dependent function type reuses the paper's estimators already defined above. -/
abbrev VarianceEstimator := (P : Population) → Finset (Fin P.N) → ℝ

/-- β̂, equation (2), p. 366, applied to a population's observed outcomes. -/
def pointEstimate (P : Population) (s : Finset (Fin P.N)) : ℝ :=
  estimate s (observed s P.y1 P.y0)

/-- β, p. 366, applied to the population's two fixed schedules. -/
def populationEffect (P : Population) : ℝ := averageEffect P.y1 P.y0

/-- V(β̂), p. 366, still the actual uniform finite randomization variance. -/
def trueVariance (P : Population) : ℝ := randomizationVariance P.M P.y1 P.y0

/-- V̂_N, p. 367, as a dependent estimator on populations. -/
def neymanEstimator : VarianceEstimator := fun P s => neyman s (observed s P.y1 P.y0)

/-- V̂_HC2, p. 367, as a dependent estimator on populations. -/
def hc2Estimator : VarianceEstimator := fun P s => hc2 s (observed s P.y1 P.y0)

/-- V̂_HR, p. 367, as a dependent estimator on populations. -/
def hrEstimator : VarianceEstimator := fun P s => hr s (observed s P.y1 P.y0)

/-- HC1, footnote 2, p. 368, with the explicit N/(N-2) convention above. -/
def hc1Estimator : VarianceEstimator := fun P s => hc1 s (observed s P.y1 P.y0)

/-- HC3, footnote 2, p. 368, with the squared-leverage adjustment above. -/
def hc3Estimator : VarianceEstimator := fun P s => hc3 s (observed s P.y1 P.y0)

/-- V̂_OLS, p. 369, as a dependent estimator on populations. -/
def olsEstimator : VarianceEstimator := fun P s => ols s (observed s P.y1 P.y0)

/-- V̂_CE, equation (5), p. 368, as a dependent estimator on populations. -/
def ceEstimator : VarianceEstimator := fun P s => constantEffects s (observed s P.y1 P.y0)

/-- Probabilities use the same equally likely (N choose M) assignments
as E[·] (p. 366); they are finite sums of event indicators. -/
def eventProbability (P : Population) (event : Finset (Fin P.N) → Prop) : ℝ := by
  classical
  exact expectation P.M (fun s => if event s then 1 else 0)

/-- N(0,1) in the p. 367 normal approximation: Mathlib's actual Gaussian
probability measure and CDF, rather than an uninterpreted function. -/
def normalCDF (x : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x

/-- "Large-sample" (pp. 367--369), operationalized as N→∞ along a sequence.
This choice is not specified in the printed paper. -/
def GrowingPopulations (P : ℕ → Population) : Prop :=
  Tendsto (fun r => (P r).N) atTop atTop

/-- "Asymptotic normality of β̂" (p. 367), interpreted as convergence
of every CDF of (β̂-β)/sqrt(V(β̂)) to the standard normal CDF. The true
variance is eventually positive so the standardization is meaningful.
The paper does not spell out this definition. -/
def StandardizedNormalLimit (P : ℕ → Population) : Prop :=
  (∀ᶠ r in atTop, 0 < trueVariance (P r)) ∧
  ∀ x : ℝ, Tendsto (fun r => eventProbability (P r) (fun s =>
    (pointEstimate (P r) s - populationEffect (P r)) / Real.sqrt (trueVariance (P r)) ≤ x))
    atTop (𝓝 (normalCDF x))

/-- Convergence in probability: every positive error-threshold event has
probability tending to zero. It is defined on each row's actual finite
randomization space. -/
def ConvergesInProbability (P : ℕ → Population) (f : VarianceEstimator) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun r =>
    eventProbability (P r) (fun s => ε < |f (P r) s - c|)) atTop (𝓝 0)

/-- "Asymptotically equivalent to HC2" (footnote 2, p. 368), interpreted
on the leading variance scale: Pr(|A-B|>ε |B|)→0 for each ε>0.
This handles B=0 without assigning an artificial ratio there. -/
def FirstOrderEquivalent (P : ℕ → Population) (A B : VarianceEstimator) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun r => eventProbability (P r)
    (fun s => ε * |B (P r) s| < |A (P r) s - B (P r) s|)) atTop (𝓝 0)

/-- The coverage of "confidence intervals ... in a normal approximation"
(p. 367): Pr(|β̂-β|≤z sqrt(V̂)), including zero-length intervals. -/
def coverage (P : Population) (V : VarianceEstimator) (z : ℝ) : ℝ :=
  eventProbability P (fun s => |pointEstimate P s - populationEffect P| ≤ z * Real.sqrt (V P s))

/-- "Approximately correct or conservative coverage" (pp. 367--369):
liminf coverage ≥ 2Φ(z)-1, expressed with eventual lower bounds.
For a usual two-sided normal critical value, 2Φ(z)-1 is 1-α. -/
def ConservativeCoverage (P : ℕ → Population) (V : VarianceEstimator) (z : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop, 2 * normalCDF z - 1 - ε ≤ coverage (P r) V z

/-- The standing condition on p. 366 entails M at least 2, N-M at least 2, and N at least 4. -/
lemma population_sizes (P : Population) :
    2 ≤ P.M ∧ 2 ≤ P.N - P.M ∧ P.M ≤ P.N ∧ 4 ≤ P.N := by
  have hM := P.hM
  have hMN := P.hMN
  omega

/-- Every size-M assignment of a population satisfying the standing condition on p. 366 has two nontrivial arms. -/
lemma population_assignment_admissible (P : Population) (s : Finset (Fin P.N))
    (hs : s ∈ (univ : Finset (Fin P.N)).powersetCard P.M) : Admissible s := by
  have hp := population_sizes P
  have hc := (mem_powersetCard.mp hs).2
  constructor
  · rw [hc]; omega
  · rw [card_compl, hc]; simp only [Fintype.card_fin]; omega


/-- A scalar limit supporting the leading-variance comparison on p. 369:
N/(N-a) tends to one for the fixed offsets a=1,2 used by the estimators.
This is a limit of deterministic coefficients, not of variance estimates. -/
theorem population_ratio_tends_one (P : ℕ → Population) (hN : GrowingPopulations P)
    (a : ℝ) (ha : a < 4) :
    Tendsto (fun r => ((P r).N : ℝ) / (((P r).N : ℝ) - a)) atTop (𝓝 1) := by
  have hn : Tendsto (fun r => ((P r).N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hd : Tendsto (fun r => ((P r).N : ℝ) - a) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-a) hn
  have hi : Tendsto (fun r => a / (((P r).N : ℝ) - a)) atTop (𝓝 (0 : ℝ)) :=
    hd.const_div_atTop a
  have hl : Tendsto (fun r => 1 + a / (((P r).N : ℝ) - a)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add hi
  apply hl.congr
  intro r
  have hnR : 4 ≤ ((P r).N : ℝ) := by exact_mod_cast (population_sizes (P r)).2.2.2
  have hna : ((P r).N : ℝ) - a ≠ 0 := by linarith
  field_simp
  ring

/-- A deterministic true-variance limit supporting p. 369.
Under the explicit additional conditions M/N→p in (0,1) and convergence
of the two variances and covariance, N V(β̂) tends to
(1-p)v1/p + p v0/(1-p) + 2c. These conditions are not printed in the paper. -/
theorem scaled_true_variance_limit (P : ℕ → Population) (hN : GrowingPopulations P)
    (p v1 v0 c : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hAlloc : Tendsto (fun r => ((P r).M : ℝ) / (P r).N) atTop (𝓝 p))
    (hV1 : Tendsto (fun r => popVariance (P r).y1) atTop (𝓝 v1))
    (hV0 : Tendsto (fun r => popVariance (P r).y0) atTop (𝓝 v0))
    (hCov : Tendsto (fun r => popCovariance (P r).y1 (P r).y0) atTop (𝓝 c)) :
    Tendsto (fun r => ((P r).N : ℝ) * trueVariance (P r)) atTop
      (𝓝 ((1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c)) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hpc : 1 - p ≠ 0 := by linarith
  have hComp : Tendsto (fun r => 1 - ((P r).M : ℝ) / (P r).N) atTop (𝓝 (1 - p)) :=
    tendsto_const_nhds.sub hAlloc
  have hl := (population_ratio_tends_one P hN 1 (by norm_num)).mul
    ((((hComp.div hAlloc hp0).mul hV1).add
      ((hAlloc.div hComp hpc).mul hV0)).add (hCov.const_mul 2))
  have hl' : Tendsto (fun r => (((P r).N : ℝ) / ((P r).N - 1 : ℝ)) *
      ((1 - ((P r).M : ℝ) / (P r).N) / (((P r).M : ℝ) / (P r).N) * popVariance (P r).y1 +
        (((P r).M : ℝ) / (P r).N) / (1 - ((P r).M : ℝ) / (P r).N) * popVariance (P r).y0 +
        2 * popCovariance (P r).y1 (P r).y0)) atTop
      (𝓝 ((1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c)) := by
    simpa only [one_mul, Pi.div_apply] using hl
  apply hl'.congr
  intro r
  have hs := population_sizes (P r)
  have hmR : 2 ≤ ((P r).M : ℝ) := by exact_mod_cast hs.1
  have hkRn : (2 : ℝ) ≤ ((P r).N - (P r).M : ℕ) := by exact_mod_cast hs.2.1
  have hkR : 2 ≤ ((P r).N : ℝ) - (P r).M := by
    simpa only [Nat.cast_sub hs.2.2.1] using hkRn
  have hnR : 4 ≤ ((P r).N : ℝ) := by exact_mod_cast hs.2.2.2
  have hm : ((P r).M : ℝ) ≠ 0 := by linarith
  have hk : ((P r).N : ℝ) - (P r).M ≠ 0 := by linarith
  have hn : ((P r).N : ℝ) ≠ 0 := by linarith
  have hn1 : ((P r).N : ℝ) - 1 ≠ 0 := by linarith
  unfold trueVariance
  rw [randomization_variance_alternative (P r).M (by simpa using hs.1)
    (by simpa using hs.2.1) (by simpa using hs.2.2.1)]
  simp only [Fintype.card_fin]
  field_simp <;> ring

/-- An expectation limit supporting p. 369.
Under explicit allocation and population-variance limits,
N E[V̂_OLS] tends to v1/(1-p)+v0/p. This does not assert convergence
in probability of V̂_OLS. -/
theorem scaled_expected_ols_limit (P : ℕ → Population) (hN : GrowingPopulations P)
    (p v1 v0 : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hAlloc : Tendsto (fun r => ((P r).M : ℝ) / (P r).N) atTop (𝓝 p))
    (hV1 : Tendsto (fun r => popVariance (P r).y1) atTop (𝓝 v1))
    (hV0 : Tendsto (fun r => popVariance (P r).y0) atTop (𝓝 v0)) :
    Tendsto (fun r => ((P r).N : ℝ) *
      expectation (P r).M (fun s => olsEstimator (P r) s)) atTop (𝓝 (v1 / (1 - p) + v0 / p)) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hpc : 1 - p ≠ 0 := by linarith
  have hn : Tendsto (fun r => ((P r).N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hInv : Tendsto (fun r => 1 / ((P r).N : ℝ)) atTop (𝓝 (0 : ℝ)) := hn.const_div_atTop 1
  have hComp : Tendsto (fun r => 1 - ((P r).M : ℝ) / (P r).N) atTop (𝓝 (1 - p)) :=
    tendsto_const_nhds.sub hAlloc
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have hl := (((population_ratio_tends_one P hN 1 (by norm_num)).mul
      (population_ratio_tends_one P hN 2 (by norm_num))).mul
      (((hAlloc.sub hInv).mul hV1).add ((hComp.sub hInv).mul hV0))).mul
      ((hOne.div hAlloc hp0).add (hOne.div hComp hpc))
  have hLimit : (1 * 1) * ((p - 0) * v1 + ((1 - p) - 0) * v0) *
      (1 / p + 1 / (1 - p)) = v1 / (1 - p) + v0 / p := by
    field_simp <;> ring
  rw [hLimit] at hl
  simp only [Pi.div_apply] at hl
  apply hl.congr
  intro r
  have hs := population_sizes (P r)
  have hmR : 2 ≤ ((P r).M : ℝ) := by exact_mod_cast hs.1
  have hkRn : (2 : ℝ) ≤ ((P r).N - (P r).M : ℕ) := by exact_mod_cast hs.2.1
  have hkR : 2 ≤ ((P r).N : ℝ) - (P r).M := by
    simpa only [Nat.cast_sub hs.2.2.1] using hkRn
  have hnR : 4 ≤ ((P r).N : ℝ) := by exact_mod_cast hs.2.2.2
  have hm : ((P r).M : ℝ) ≠ 0 := by linarith
  have hk : ((P r).N : ℝ) - (P r).M ≠ 0 := by linarith
  have hn0 : ((P r).N : ℝ) ≠ 0 := by linarith
  have hn1 : ((P r).N : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : ((P r).N : ℝ) - 2 ≠ 0 := by linarith
  simp only [olsEstimator]
  rw [expected_ols (P r).M (by simpa using hs.1)
    (by simpa using hs.2.1) (by simpa using hs.2.2.1)]
  simp only [Fintype.card_fin]
  field_simp <;> ring


/-- The "too big or too small relative to V(β̂)" passage on p. 369,
interpreted on the N-times-variance scale (the raw variances can both tend
to zero). Both OLS and CE converge in probability to a while the true
scaled variance tends to a positive v. The paper gives no sequence. -/
def UnbalancedVarianceLimit (P : ℕ → Population) (a v : ℝ) : Prop :=
  GrowingPopulations P ∧ (∀ r, (P r).N ≠ 2 * (P r).M) ∧ 0 < v ∧
    Tendsto (fun r => ((P r).N : ℝ) * trueVariance (P r)) atTop (𝓝 v) ∧
    ConvergesInProbability P (fun Q s => (Q.N : ℝ) * olsEstimator Q s) a ∧
    ConvergesInProbability P (fun Q s => (Q.N : ℝ) * ceEstimator Q s) a


/-! Corrections and counterexamples. -/

/-- Explicit potential outcomes, `(0,2,5,9)` in both arms,
for the counterexample to the untilded covariance in the proof on p. 369. -/
def proofExampleOutcomes : Fin 4 → ℝ := ![0, 2, 5, 9]

/-- Explicit assignment: the first two of four units are treated.
The labels 0,1 are the paper's labels 1,2. -/
def proofExampleTreated : Finset (Fin 4) := {0, 1}

/-- T7: the printed first sentence of Theorem 2's proof (p. 369) is
false even with actual constant effects zero. This explicit N=4,M=2
assignment is one of six possible assignments, has β̂=-6, imputed moments
5/2, and original potential-outcome covariance 23/2. -/
theorem printed_covariance_counterexample :
    Admissible proofExampleTreated ∧ proofExampleTreated.card = 2 ∧
    ((univ : Finset (Fin 4)).powersetCard 2).card = 6 ∧
    proofExampleTreated ∈ (univ : Finset (Fin 4)).powersetCard 2 ∧
    observed proofExampleTreated proofExampleOutcomes proofExampleOutcomes =
      proofExampleOutcomes ∧
    groupMean proofExampleTreated proofExampleOutcomes = 1 ∧
    intercept proofExampleTreated proofExampleOutcomes = 7 ∧
    estimate proofExampleTreated proofExampleOutcomes = -6 ∧
    imputed0 proofExampleTreated proofExampleOutcomes = ![6, 8, 5, 9] ∧
    imputed1 proofExampleTreated proofExampleOutcomes = ![0, 2, -1, 3] ∧
    (∀ i, imputed0 proofExampleTreated proofExampleOutcomes i =
      imputed1 proofExampleTreated proofExampleOutcomes i -
        estimate proofExampleTreated proofExampleOutcomes) ∧
    popVariance (imputed0 proofExampleTreated proofExampleOutcomes) = 5 / 2 ∧
    popVariance (imputed1 proofExampleTreated proofExampleOutcomes) = 5 / 2 ∧
    popCovariance proofExampleOutcomes proofExampleOutcomes = 23 / 2 ∧
    popVariance (imputed1 proofExampleTreated proofExampleOutcomes) ≠
      popCovariance proofExampleOutcomes proofExampleOutcomes := by
  have hc : proofExampleTreatedᶜ = ({2, 3} : Finset (Fin 4)) := by decide
  have hmt : groupMean proofExampleTreated proofExampleOutcomes = 1 := by
    norm_num [groupMean, proofExampleTreated, proofExampleOutcomes]
  have hmc : groupMean proofExampleTreatedᶜ proofExampleOutcomes = 7 := by
    rw [hc]; norm_num [groupMean, proofExampleOutcomes]
  have he : estimate proofExampleTreated proofExampleOutcomes = -6 := by
    rw [estimate, hmt, hmc]; norm_num
  have h0 : imputed0 proofExampleTreated proofExampleOutcomes = ![6, 8, 5, 9] := by
    unfold imputed0
    rw [he]
    ext i; fin_cases i <;>
      norm_num [treatment,
        proofExampleTreated, proofExampleOutcomes]
  have h1 : imputed1 proofExampleTreated proofExampleOutcomes = ![0, 2, -1, 3] := by
    unfold imputed1
    rw [he]
    ext i; fin_cases i <;>
      norm_num [treatment,
        proofExampleTreated, proofExampleOutcomes]
  have ho : observed proofExampleTreated proofExampleOutcomes proofExampleOutcomes =
      proofExampleOutcomes := by
    ext i; by_cases hi : i ∈ proofExampleTreated <;> simp [observed, treatment, hi]
  simp only [h0, h1, ho, Admissible, hc, hmt, he, intercept, hmc]
  norm_num [proofExampleTreated, proofExampleOutcomes, Admissible,
    observed, treatment, groupMean, intercept, estimate, imputed0, imputed1,
    popVariance, popCovariance, Fin.sum_univ_succ, hc, Nat.choose]
  intro i; fin_cases i <;> norm_num

/-- Population covariance is symmetric, for the definition on p. 366;
this lets the corrected proof use the printed order of the two tildes. -/
lemma pop_covariance_symm (v w : ι → ℝ) : popCovariance v w = popCovariance w v := by
  simp only [popCovariance, mul_comm]

/-- T8: every intermediate identity of the corrected proof of Theorem 2
(p. 369), with the two covariance tildes and residual indices restored.
No hypothesis of actual constant treatment effects is added. -/
theorem corrected_theorem_two_proof (s : Finset ι) (Y : ι → ℝ)
    (h : Admissible s) :
    let N : ℝ := Fintype.card ι
    let M : ℝ := s.card
    let K : ℝ := sᶜ.card
    let S : ℝ := ∑ i, residual s Y i ^ 2
    (∀ i, imputed0 s Y i = imputed1 s Y i - estimate s Y) ∧
    popVariance (imputed0 s Y) = popVariance (imputed1 s Y) ∧
    popVariance (imputed1 s Y) = popCovariance (imputed0 s Y) (imputed1 s Y) ∧
    constantEffects s Y = N / (N - 1) * (N / (M * K)) * popVariance (imputed0 s Y) ∧
    S / N = (∑ i, (Y i - intercept s Y - treatment s i * estimate s Y) ^ 2) / N ∧
    (∑ i, (Y i - intercept s Y - treatment s i * estimate s Y) ^ 2) / N =
      (∑ i, (imputed0 s Y i - intercept s Y) ^ 2) / N ∧
    (∑ i, (imputed0 s Y i - intercept s Y) ^ 2) / N = popVariance (imputed0 s Y) ∧
    (N - 2) / (N - 1) * ols s Y =
      (N - 2) / (N - 1) * (S / (N - 2)) * (N / (M * K)) ∧
    (N - 2) / (N - 1) * (S / (N - 2)) * (N / (M * K)) =
      N / (N - 1) * (S / N) * (N / (M * K)) ∧
    N / (N - 1) * (S / N) * (N / (M * K)) =
      N / (N - 1) * (N / (M * K)) * popVariance (imputed0 s Y) ∧
    N / (N - 1) * (N / (M * K)) * popVariance (imputed0 s Y) = constantEffects s Y := by
  dsimp only
  have hp := arm_pos h
  have hs := arm_card_sum s
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by linarith [hp.1, hp.2]
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith [hp.1, hp.2]
  have hn2 : (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith [hp.1, hp.2]
  have hm : (s.card : ℝ) ≠ 0 := by linarith [hp.1]
  have hk : (sᶜ.card : ℝ) ≠ 0 := by linarith [hp.2]
  have hi := imputed_moments s Y h
  have hce : constantEffects s Y = (Fintype.card ι : ℝ) /
      ((Fintype.card ι : ℝ) - 1) * (Fintype.card ι / ((s.card : ℝ) * sᶜ.card)) *
        popVariance (imputed0 s Y) := by
    unfold constantEffects varianceExpression
    rw [hi.1, hi.2.1, hi.2.2]
    field_simp
    simp only [← hs]
    ring
  refine ⟨?_, hi.1.trans hi.2.1.symm, ?_, hce, rfl, ?_, ?_, ?_, ?_, ?_, hce.symm⟩
  · intro i; unfold imputed0 imputed1; ring
  · rw [pop_covariance_symm]; exact hi.2.1.trans hi.2.2.symm
  · simp only [imputed0_residual, add_sub_cancel_right, residual]
  · simp only [imputed0_residual, add_sub_cancel_right]; exact hi.1.symm
  · unfold ols; rw [gram_inverse_coefficient s h]; ring
  · field_simp
  · rw [hi.1]; ring

/-- T9: the full corrected proof chain of Theorem 3 (p. 370), including
its balanced residual-sum algebra, the named sample variances, and the
finite-N CE scaling factor. The CE symbol carries its restored hat. -/
theorem corrected_theorem_three_proof (s : Finset ι) (Y : ι → ℝ)
    (h : Admissible s) (hb : Fintype.card ι = 2 * s.card) :
    let N : ℝ := Fintype.card ι
    let M : ℝ := s.card
    let S : ℝ := ∑ i, residual s Y i ^ 2
    (N - 1) / (N - 2) * constantEffects s Y = ols s Y ∧
    ols s Y = S / (2 * (M - 1)) * (2 * M / M ^ 2) ∧
    S / (2 * (M - 1)) * (2 * M / M ^ 2) =
      ((∑ i ∈ s, residual s Y i ^ 2) / (M - 1)) / M +
        ((∑ i ∈ sᶜ, residual s Y i ^ 2) / (M - 1)) / M ∧
    ((∑ i ∈ s, residual s Y i ^ 2) / (M - 1)) / M +
        ((∑ i ∈ sᶜ, residual s Y i ^ 2) / (M - 1)) / M =
      sampleVariance s Y / M + sampleVariance sᶜ Y / M ∧
    sampleVariance s Y / M + sampleVariance sᶜ Y / M = neyman s Y ∧
    neyman s Y = hc2 s Y := by
  dsimp only
  have hp := arm_pos h
  have hs := arm_card_sum s
  have hbR : (Fintype.card ι : ℝ) = 2 * (s.card : ℝ) := by exact_mod_cast hb
  have hk : (sᶜ.card : ℝ) = s.card := by linarith
  have hm : (s.card : ℝ) ≠ 0 := by linarith [hp.1]
  have hm1 : (s.card : ℝ) - 1 ≠ 0 := by linarith [hp.1]
  have he := balanced_equivalences s Y h hb
  refine ⟨he.1, ?_, ?_, ?_, ?_, he.2.2⟩
  · unfold ols
    rw [gram_inverse_coefficient s h, hbR, hk]
    field_simp <;> ring
  · rw [← s.sum_add_sum_compl (fun i => residual s Y i ^ 2)]
    field_simp
  · rw [Finset.sum_congr rfl (fun i hi => congrArg (· ^ 2) (residual_treated s Y hi)),
      Finset.sum_congr rfl (fun i hi => congrArg (· ^ 2) (residual_control s Y hi))]
    simp only [sampleVariance, hk]
  · simp only [neyman, hk]

/-- Adding a constant shifts a nonempty group's mean by that constant,
for the mean defined on p. 366. -/
lemma group_mean_add_const (s : Finset ι) (v : ι → ℝ) (c : ℝ)
    (hs : (s.card : ℝ) ≠ 0) :
    groupMean s (fun i => v i + c) = groupMean s v + c := by
  simp only [groupMean, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- Centered population variance (p. 366) is invariant under a constant
shift, the exact first-moment invariance needed for footnote 3's repair. -/
lemma pop_variance_add_const (v : ι → ℝ) (c : ℝ)
    (hn : (Fintype.card ι : ℝ) ≠ 0) :
    popVariance (fun i => v i + c) = popVariance v := by
  unfold popVariance
  rw [group_mean_add_const univ v c (by simpa using hn)]
  simp only [add_sub_add_right_eq_sub]

/-- Centered population covariance (p. 366) is invariant under independent
constant shifts of the two schedules, as used in the corrected footnote 3. -/
lemma pop_covariance_add_const (v w : ι → ℝ) (c d : ℝ)
    (hn : (Fintype.card ι : ℝ) ≠ 0) :
    popCovariance (fun i => v i + c) (fun i => w i + d) = popCovariance v w := by
  unfold popCovariance
  rw [group_mean_add_const univ v c (by simpa using hn),
    group_mean_add_const univ w d (by simpa using hn)]
  simp only [add_sub_add_right_eq_sub]

/-- Equation (1), p. 366, under the shifts y0'=y0+c, y1'=y1+c+d:
the observed vector becomes Y+c+dX for the same assignment. -/
lemma observed_shift (s : Finset ι) (y1 y0 : ι → ℝ) (c d : ℝ) :
    observed s (fun i => y1 i + (c + d)) (fun i => y0 i + c) =
      fun i => observed s y1 y0 i + c + d * treatment s i := by
  ext i; unfold observed; ring

/-- Exact regression shift identities, supporting T10 and T11:
Y+c+dX shifts α̂ by c and β̂ by d, leaving every residual and OLS variance
estimate unchanged under the standing experiment assumptions (p. 366). -/
theorem regression_shift_invariance (s : Finset ι) (Y : ι → ℝ) (c d : ℝ)
    (h : Admissible s) :
    let Y' := fun i => Y i + c + d * treatment s i
    intercept s Y' = intercept s Y + c ∧ estimate s Y' = estimate s Y + d ∧
    (∀ i, residual s Y' i = residual s Y i) ∧ ols s Y' = ols s Y := by
  dsimp only
  have hp := arm_pos h
  have hm : (s.card : ℝ) ≠ 0 := by linarith [hp.1]
  have hk : (sᶜ.card : ℝ) ≠ 0 := by linarith [hp.2]
  have ht : groupMean s (fun i => Y i + c + d * treatment s i) =
      groupMean s Y + (c + d) := by
    calc
      _ = groupMean s (fun i => Y i + (c + d)) := by
        unfold groupMean
        congr 1
        apply Finset.sum_congr rfl
        intro i hi; simp [treatment, hi, add_assoc]
      _ = _ := group_mean_add_const s Y (c + d) hm
  have hc : groupMean sᶜ (fun i => Y i + c + d * treatment s i) =
      groupMean sᶜ Y + c := by
    calc
      _ = groupMean sᶜ (fun i => Y i + c) := by
        unfold groupMean
        congr 1
        apply Finset.sum_congr rfl
        intro i hi; simp [treatment, mem_compl.mp hi]
      _ = _ := group_mean_add_const sᶜ Y c hk
  have hr : ∀ i, residual s (fun j => Y j + c + d * treatment s j) i =
      residual s Y i := by
    intro i
    unfold residual intercept estimate
    rw [ht, hc]
    ring
  refine ⟨hc, ?_, hr, ?_⟩
  · unfold estimate; rw [ht, hc]; ring
  · simp only [ols, hr]

/-- T10(a) and T11's final exact assertion: for any admissible finite
population, shifting y0 by c and y1 by c+d changes the control mean by c
and the average effect by d but preserves the actual randomization variance
and the OLS variance estimate for every possible assignment, correcting
the first-moment dependency description in footnote 3 (p. 369). -/
theorem potential_outcome_shift_invariance (M : ℕ) (hM : 2 ≤ M)
    (hK : 2 ≤ Fintype.card ι - M) (hMN : M ≤ Fintype.card ι)
    (y1 y0 : ι → ℝ) (c d : ℝ) :
    groupMean univ (fun i => y0 i + c) = groupMean univ y0 + c ∧
    averageEffect (fun i => y1 i + (c + d)) (fun i => y0 i + c) =
      averageEffect y1 y0 + d ∧
    randomizationVariance M (fun i => y1 i + (c + d)) (fun i => y0 i + c) =
      randomizationVariance M y1 y0 ∧
    ∀ s ∈ (univ : Finset ι).powersetCard M,
      let Y := observed s y1 y0
      let Y' := observed s (fun i => y1 i + (c + d)) (fun i => y0 i + c)
      intercept s Y' = intercept s Y + c ∧ estimate s Y' = estimate s Y + d ∧
      (∀ i, residual s Y' i = residual s Y i) ∧ ols s Y' = ols s Y := by
  have hnR : 4 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 4 ≤ Fintype.card ι)
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by linarith
  have hMean := group_mean_add_const univ y0 c (by simpa using hn)
  have hMean1 := group_mean_add_const univ y1 (c + d) (by simpa using hn)
  have ha : ∀ s ∈ (univ : Finset ι).powersetCard M, Admissible s := by
    intro s hs
    have hc := (mem_powersetCard.mp hs).2
    constructor
    · rw [hc]; omega
    · rw [card_compl, hc]; omega
  refine ⟨hMean, ?_, ?_, ?_⟩
  · unfold averageEffect; rw [hMean, hMean1]; ring
  · rw [randomization_variance_identity M hM hK hMN,
      randomization_variance_identity M hM hK hMN]
    simp only [varianceExpression, pop_variance_add_const _ _ hn,
      pop_covariance_add_const _ _ _ _ hn]
  · intro s hs
    dsimp only
    rw [observed_shift]
    exact regression_shift_invariance s (observed s y1 y0) c d (ha s hs)

/-- The algebraic difference in the corrected footnote 3 (p. 369):
the OLS and true leading variances differ by allocation imbalance plus
the centered variance of unit treatment effects; no first moment enters. -/
lemma leading_variance_difference (p v1 v0 c : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (v1 / (1 - p) + v0 / p) - ((1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c) =
      (2 * p - 1) * (v1 - v0) / (p * (1 - p)) + v1 + v0 - 2 * c := by
  have h0 : p ≠ 0 := ne_of_gt hp
  have h1 : 1 - p ≠ 0 := by linarith
  field_simp; ring

/-- T11's deterministic part: the full corrected footnote 3 relation
(p. 369), under explicit sequence, allocation and
centered-moment conditions. This includes both leading limits, their bias
difference, and the treatment-effect variance limit. -/
theorem corrected_footnote_three_limits (P : ℕ → Population) (hN : GrowingPopulations P)
    (p v1 v0 c : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hAlloc : Tendsto (fun r => ((P r).M : ℝ) / (P r).N) atTop (𝓝 p))
    (hV1 : Tendsto (fun r => popVariance (P r).y1) atTop (𝓝 v1))
    (hV0 : Tendsto (fun r => popVariance (P r).y0) atTop (𝓝 v0))
    (hCov : Tendsto (fun r => popCovariance (P r).y1 (P r).y0) atTop (𝓝 c)) :
    Tendsto (fun r => ((P r).N : ℝ) * trueVariance (P r)) atTop
      (𝓝 ((1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c)) ∧
    Tendsto (fun r => ((P r).N : ℝ) * expectation (P r).M (fun s => olsEstimator (P r) s))
      atTop (𝓝 (v1 / (1 - p) + v0 / p)) ∧
    Tendsto (fun r => ((P r).N : ℝ) *
      (expectation (P r).M (fun s => olsEstimator (P r) s) - trueVariance (P r))) atTop
      (𝓝 ((2 * p - 1) * (v1 - v0) / (p * (1 - p)) + v1 + v0 - 2 * c)) ∧
    Tendsto (fun r => popVariance (fun i => (P r).y1 i - (P r).y0 i)) atTop
      (𝓝 (v1 + v0 - 2 * c)) := by
  have ht := scaled_true_variance_limit P hN p v1 v0 c hp hp1 hAlloc hV1 hV0 hCov
  have he := scaled_expected_ols_limit P hN p v1 v0 hp hp1 hAlloc hV1 hV0
  refine ⟨ht, he, ?_, ?_⟩
  · have hl := he.sub ht
    rw [leading_variance_difference p v1 v0 c hp hp1] at hl
    exact hl.congr (fun r => by ring)
  · have hl := (hV1.add hV0).sub (hCov.const_mul 2)
    apply hl.congr
    intro r
    have hv := pop_variance_linear (1 : ℝ) (-1) (P r).y1 (P r).y0
    simpa [sub_eq_add_neg] using hv.symm

/-- Finite randomization expectation preserves inequalities on possible
assignments, a sum lemma for the uniform design on p. 366. -/
lemma expectation_mono (M : ℕ) {f g : Finset ι → ℝ}
    (h : ∀ s ∈ (univ : Finset ι).powersetCard M, f s ≤ g s) :
    expectation M f ≤ expectation M g := by
  unfold expectation
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

/-- Nonnegative functions have nonnegative uniform-design expectations,
for the actual finite average specified on p. 366. -/
lemma expectation_nonneg (M : ℕ) (f : Finset ι → ℝ)
    (h : ∀ s ∈ (univ : Finset ι).powersetCard M, 0 ≤ f s) :
    0 ≤ expectation M f := by
  unfold expectation
  exact div_nonneg (Finset.sum_nonneg h) (Nat.cast_nonneg _)

/-- Finite Markov inequality for the actual randomization probabilities
on p. 366. It bounds event probabilities using a nonnegative expectation. -/
lemma finite_markov (P : Population) (f : Finset (Fin P.N) → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hf : ∀ s ∈ (univ : Finset (Fin P.N)).powersetCard P.M, 0 ≤ f s) :
    eventProbability P (fun s => ε < f s) ≤ expectation P.M f / ε := by
  classical
  apply (le_div_iff₀ hε).mpr
  rw [mul_comm]
  change ε * expectation P.M (fun s => if ε < f s then 1 else 0) ≤ _
  rw [← expectation_mul]
  apply expectation_mono
  intro s hs
  split_ifs with h
  · simpa using h.le
  · simpa using hf s hs

/-- Vanishing expected absolute error implies convergence in probability
on the finite design spaces, with Markov's inequality rather than an
assumption that convergence of expectations implies estimator consistency. -/
theorem probability_limit_of_mean_absolute_error (P : ℕ → Population)
    (f : VarianceEstimator) (c : ℝ)
    (hL1 : Tendsto (fun n => expectation (P n).M (fun s => |f (P n) s - c|))
      atTop (𝓝 0)) : ConvergesInProbability P f c := by
  intro ε hε
  have hu := hL1.div_const ε
  simp only [zero_div] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro n
    exact expectation_nonneg _ _ (fun _ _ => by split_ifs <;> norm_num)
  · intro n
    exact finite_markov (P n) _ ε hε (fun _ _ => abs_nonneg _)

/-- Convergence in probability depends only on values at possible
assignments, using the same uniform finite design as p. 366. -/
lemma probability_limit_congr (P : ℕ → Population) {f g : VarianceEstimator} (c : ℝ)
    (h : ∀ n s, s ∈ (univ : Finset (Fin (P n).N)).powersetCard (P n).M →
      f (P n) s = g (P n) s) (hg : ConvergesInProbability P g c) :
    ConvergesInProbability P f c := by
  intro ε hε
  apply (hg ε hε).congr
  intro n
  unfold eventProbability
  apply expectation_congr
  intro s hs
  dsimp only
  simp only [h n s hs]

/-- An affine function of a square with vanishing expectation has its
constant-term probability limit when its deterministic multiplier tends
to one. This finite-design lemma yields limits for the explicit sequences. -/
theorem affine_square_probability_limit (P : ℕ → Population)
    (R : VarianceEstimator) (F : Population → ℝ) (A B : ℝ)
    (hF : Tendsto (fun n => F (P n)) atTop (𝓝 1))
    (hR : Tendsto (fun n => expectation (P n).M (fun s => R (P n) s ^ 2)) atTop (𝓝 0)) :
    ConvergesInProbability P (fun Q s => F Q * (A - B * R Q s ^ 2)) A := by
  apply probability_limit_of_mean_absolute_error
  have hb : Tendsto (fun n => |F (P n) - 1| * |A| + |F (P n) * B| *
      expectation (P n).M (fun s => R (P n) s ^ 2)) atTop (𝓝 0) := by
    simpa using (((hF.sub_const 1).abs.mul_const |A|).add
      ((hF.mul_const B).abs.mul hR))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
  · intro n
    exact expectation_nonneg _ _ (fun _ _ => abs_nonneg _)
  · intro n
    calc
      _ ≤ expectation (P n).M (fun s =>
          |F (P n) - 1| * |A| + |F (P n) * B| * R (P n) s ^ 2) := by
        apply expectation_mono
        intro s _
        have he : F (P n) * (A - B * R (P n) s ^ 2) - A =
            (F (P n) - 1) * A + -(F (P n) * B * R (P n) s ^ 2) := by ring
        rw [he]
        calc
          _ ≤ |(F (P n) - 1) * A| + |-(F (P n) * B * R (P n) s ^ 2)| := abs_add_le _ _
          _ = _ := by simp [abs_mul]
      _ = _ := by
        rw [expectation_add, expectation_const _ (by simpa using (population_sizes (P n)).2.2.1),
          expectation_mul]

/-- The fully specified sign population: the first 2k units have z=-1
and the last 2k have z=1, in the counterexample to footnote 3, p. 369. -/
def footnoteSigns (k : ℕ) (i : Fin (4 * k)) : ℝ := if i.val < 2 * k then -1 else 1

/-- T10's bounded population sequences: k=n+2, N=4k,
M=k, y0=z and y1=a z+2. Starting k at two ensures 1<M<N-1 in every row. -/
def footnotePopulation (a : ℝ) (n : ℕ) : Population where
  N := 4 * (n + 2)
  M := n + 2
  y0 := footnoteSigns (n + 2)
  y1 := fun i => a * footnoteSigns (n + 2) i + 2
  hM := by omega
  hMN := by omega

/-- The treated mean r of the signs, used to prove probability
limits on the explicit N=4k,M=k populations; the cutoff is 2M. -/
def footnoteTreatedMean : VarianceEstimator := fun Q s =>
  groupMean s (fun i => if i.val < 2 * Q.M then (-1 : ℝ) else 1)

/-- The sign vector has total sum zero and squared entries one.
This proves its mean zero and divisor-N population variance one exactly. -/
lemma footnote_sign_moments (k : ℕ) (hk : 2 ≤ k) :
    (∑ i, footnoteSigns k i) = 0 ∧ (∀ i, footnoteSigns k i ^ 2 = 1) ∧
    groupMean univ (footnoteSigns k) = 0 ∧ popVariance (footnoteSigns k) = 1 := by
  have hl : ((univ : Finset (Fin (4 * k))).filter (fun i => i.val < 2 * k)).card = 2 * k := by
    rw [Fin.card_filter_val_lt, min_eq_right (by omega)]
  have hr : ((univ : Finset (Fin (4 * k))).filter (fun i => ¬ i.val < 2 * k)).card = 2 * k := by
    have h := Finset.card_filter_add_card_filter_not (s := univ)
      (fun i : Fin (4 * k) => i.val < 2 * k)
    simp only [hl, card_univ, Fintype.card_fin] at h
    omega
  have hsum : (∑ i, footnoteSigns k i) = 0 := by
    simp only [footnoteSigns, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, hl, hr]
    norm_num
  have hsq : ∀ i, footnoteSigns k i ^ 2 = 1 := by
    intro i; unfold footnoteSigns; split_ifs <;> norm_num
  have hm : groupMean univ (footnoteSigns k) = 0 := by simp [groupMean, hsum]
  refine ⟨hsum, hsq, hm, ?_⟩
  have hn : (4 * k : ℝ) ≠ 0 := by
    have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  simp [popVariance, hm, hsq, hn]

/-- All first and centered second moments in T10(b), exactly for every
row and every real a: allocation 1/4, control mean 0, average effect 2,
control variance 1, treatment variance a² and covariance a. -/
lemma footnote_population_moments (a : ℝ) (n : ℕ) :
    ((footnotePopulation a n).M : ℝ) / (footnotePopulation a n).N = 1 / 4 ∧
    groupMean univ (footnotePopulation a n).y0 = 0 ∧
    groupMean univ (footnotePopulation a n).y1 = 2 ∧
    populationEffect (footnotePopulation a n) = 2 ∧
    popVariance (footnotePopulation a n).y0 = 1 ∧
    popVariance (footnotePopulation a n).y1 = a ^ 2 ∧
      popCovariance (footnotePopulation a n).y1 (footnotePopulation a n).y0 = a := by
  change ((n + 2 : ℕ) : ℝ) / (4 * (n + 2) : ℕ) = 1 / 4 ∧
    groupMean univ (footnoteSigns (n + 2)) = 0 ∧
    groupMean univ (fun i => a * footnoteSigns (n + 2) i + 2) = 2 ∧
    averageEffect (fun i => a * footnoteSigns (n + 2) i + 2) (footnoteSigns (n + 2)) = 2 ∧
    popVariance (footnoteSigns (n + 2)) = 1 ∧
    popVariance (fun i => a * footnoteSigns (n + 2) i + 2) = a ^ 2 ∧
    popCovariance (fun i => a * footnoteSigns (n + 2) i + 2) (footnoteSigns (n + 2)) = a
  have hz := footnote_sign_moments (n + 2) (by omega)
  have hn : (Fintype.card (Fin (4 * (n + 2))) : ℝ) ≠ 0 := by
    exact_mod_cast (by simp : Fintype.card (Fin (4 * (n + 2))) ≠ 0)
  have hm1 : groupMean univ (fun i => a * footnoteSigns (n + 2) i + 2) = 2 := by
    simp only [groupMean, sum_add_distrib, ← Finset.mul_sum, hz.1,
      sum_const, nsmul_eq_mul, card_univ]
    field_simp <;> ring
  refine ⟨?_, hz.2.2.1, hm1, ?_, hz.2.2.2, ?_, ?_⟩
  · push_cast
    have hk : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
  · simp only [averageEffect, hm1, hz.2.2.1]; norm_num
  · simp only [popVariance, hm1, add_sub_cancel_right, mul_pow,
      hz.2.1, mul_one, sum_const, nsmul_eq_mul, card_univ]
    field_simp
  · simp only [popCovariance, hm1, hz.2.2.1,
      add_sub_cancel_right, sub_zero]
    have hv : ∀ i, a * footnoteSigns (n + 2) i * footnoteSigns (n + 2) i = a := by
      intro i
      calc
        _ = a * footnoteSigns (n + 2) i ^ 2 := by ring
        _ = a := by rw [hz.2.1 i]; ring
    simp only [hv, sum_const, nsmul_eq_mul, card_univ]
    field_simp

/-- T10's explicit population sequences grow and are unbalanced in every
row, with N=4M and both groups nontrivial as required on p. 366. -/
lemma footnote_population_growth (a : ℝ) :
    GrowingPopulations (footnotePopulation a) ∧
    ∀ n, (footnotePopulation a n).N ≠ 2 * (footnotePopulation a n).M := by
  constructor
  · apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    change b ≤ 4 * (n + 2)
    omega
  · intro n; change 4 * (n + 2) ≠ 2 * (n + 2); omega

/-- For any arm sampled from squared-unit signs, its centered sum of
squares after the affine outcome transformation a z+b is
m a²(1-r²). This exact lemma supports T10's finite OLS formula. -/
lemma affine_sign_sse (s : Finset ι) (z : ι → ℝ) (a b : ℝ)
    (hs : (s.card : ℝ) ≠ 0) (hz : ∀ i, z i ^ 2 = 1) :
    (∑ i ∈ s, (a * z i + b - groupMean s (fun j => a * z j + b)) ^ 2) =
      (s.card : ℝ) * a ^ 2 * (1 - groupMean s z ^ 2) := by
  have hm : groupMean s (fun i => a * z i + b) = a * groupMean s z + b := by
    simp only [groupMean, sum_add_distrib, ← Finset.mul_sum, sum_const, nsmul_eq_mul]
    field_simp
  rw [hm]
  have he : ∀ i, (a * z i + b - (a * groupMean s z + b)) ^ 2 =
      a ^ 2 * (z i - groupMean s z) ^ 2 := by intro i; ring
  simp_rw [he]
  rw [← Finset.mul_sum, group_sse_raw s z hs]
  simp only [hz, sum_const, nsmul_eq_mul, mul_one, groupMean]
  field_simp <;> ring

/-- T10's exact realized-assignment identity:
N V̂_OLS=N/(N-2)[4a²/3+4-(4a²/3+4/9)r²], where r is the treated sign mean.
It is an identity of the observed-data regression, not an expectation. -/
theorem footnote_scaled_ols_formula (a : ℝ) (n : ℕ) (s : Finset (Fin (footnotePopulation a n).N))
    (hs : s ∈ (univ : Finset (Fin (footnotePopulation a n).N)).powersetCard (footnotePopulation a n).M) :
    ((footnotePopulation a n).N : ℝ) * olsEstimator (footnotePopulation a n) s =
      ((footnotePopulation a n).N : ℝ) / ((footnotePopulation a n).N - 2 : ℝ) *
        (4 * a ^ 2 / 3 + 4 - (4 * a ^ 2 / 3 + 4 / 9) *
          footnoteTreatedMean (footnotePopulation a n) s ^ 2) := by
  have ha := population_assignment_admissible (footnotePopulation a n) s hs
  have hc := (mem_powersetCard.mp hs).2
  change s.card = n + 2 at hc
  have hk : sᶜ.card = 3 * (n + 2) := by
    have h : s.card + sᶜ.card = (footnotePopulation a n).N := by
      simpa only [Fintype.card_fin] using s.card_add_card_compl
    change s.card + sᶜ.card = 4 * (n + 2) at h
    omega
  have hmR : (s.card : ℝ) ≠ 0 := by rw [hc]; positivity
  have hkR : (sᶜ.card : ℝ) ≠ 0 := by rw [hk]; positivity
  have hz := footnote_sign_moments (n + 2) (by omega)
  have hsplit := s.sum_add_sum_compl (footnoteSigns (n + 2))
  change (∑ i ∈ s, footnoteSigns (n + 2) i) + (∑ i ∈ sᶜ, footnoteSigns (n + 2) i) =
    ∑ i : Fin (4 * (n + 2)), footnoteSigns (n + 2) i at hsplit
  rw [hz.1] at hsplit
  have hcontrol : groupMean sᶜ (footnoteSigns (n + 2)) =
      -(groupMean s (footnoteSigns (n + 2))) / 3 := by
    unfold groupMean
    rw [hc, hk]
    push_cast
    field_simp
    linarith
  have hmeans := observed_group_means s (footnotePopulation a n).y1 (footnotePopulation a n).y0
  have ht : (∑ i ∈ s, residual s (observed s (footnotePopulation a n).y1
      (footnotePopulation a n).y0) i ^ 2) =
      (s.card : ℝ) * a ^ 2 * (1 - groupMean s (footnoteSigns (n + 2)) ^ 2) := by
    rw [Finset.sum_congr rfl (fun i hi => congrArg (· ^ 2)
      (residual_treated s _ hi))]
    rw [hmeans.1]
    simp_rw [Finset.sum_congr rfl (fun i hi => congrArg (fun x =>
      (x - groupMean s (footnotePopulation a n).y1) ^ 2) (observed_treatment s _ _ hi))]
    exact affine_sign_sse s (footnoteSigns (n + 2)) a 2 hmR hz.2.1
  have hct : (∑ i ∈ sᶜ, residual s (observed s (footnotePopulation a n).y1
      (footnotePopulation a n).y0) i ^ 2) =
      (sᶜ.card : ℝ) * (1 - groupMean sᶜ (footnoteSigns (n + 2)) ^ 2) := by
    rw [Finset.sum_congr rfl (fun i hi => congrArg (· ^ 2)
      (residual_control s _ hi))]
    rw [hmeans.2]
    simp_rw [Finset.sum_congr rfl (fun i hi => congrArg (fun x =>
      (x - groupMean sᶜ (footnotePopulation a n).y0) ^ 2) (observed_control s _ _ hi))]
    change (∑ i ∈ sᶜ, (footnoteSigns (n + 2) i - groupMean sᶜ (footnoteSigns (n + 2))) ^ 2) = _
    simpa only [one_mul, mul_one, add_zero, one_pow] using
      (affine_sign_sse sᶜ (footnoteSigns (n + 2)) 1 0 hkR hz.2.1)
  unfold olsEstimator ols
  rw [← s.sum_add_sum_compl (fun i => residual s
    (observed s (footnotePopulation a n).y1 (footnotePopulation a n).y0) i ^ 2), ht, hct,
    gram_inverse_coefficient s ha, hcontrol]
  have hNR : ((footnotePopulation a n).N : ℝ) = 4 * ((n : ℝ) + 2) := by
    simp only [footnotePopulation, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  have hcardN : (Fintype.card (Fin (footnotePopulation a n).N) : ℝ) = 4 * ((n : ℝ) + 2) := by
    simpa only [Fintype.card_fin] using hNR
  have hcm : (s.card : ℝ) = (n : ℝ) + 2 := by exact_mod_cast hc
  have hck : (sᶜ.card : ℝ) = 3 * ((n : ℝ) + 2) := by exact_mod_cast hk
  have hrdef : footnoteTreatedMean (footnotePopulation a n) s =
      groupMean s (footnoteSigns (n + 2)) := rfl
  rw [hNR, hcardN, hcm, hck, hrdef]
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp <;> ring

/-- T10's exact concentration input: the treated sign mean satisfies
E[r²]=3/(N-1), by finite sampling without replacement. -/
theorem footnote_treated_mean_square (a : ℝ) (n : ℕ) :
    expectation (footnotePopulation a n).M (fun s => footnoteTreatedMean
      (footnotePopulation a n) s ^ 2) = 3 / ((footnotePopulation a n).N - 1 : ℝ) := by
  change expectation (n + 2) (fun s : Finset (Fin (4 * (n + 2))) =>
    groupMean s (footnoteSigns (n + 2)) ^ 2) = 3 / ((4 * (n + 2) : ℕ) - 1 : ℝ)
  have hz := footnote_sign_moments (n + 2) (by omega)
  have he := expected_group_deviation (ι := Fin (4 * (n + 2))) (n + 2)
    (by omega) (by simp <;> omega) (footnoteSigns (n + 2))
  rw [hz.2.2.1, hz.2.2.2] at he
  simp only [mul_zero, sub_zero, Fintype.card_fin] at he
  rw [expectation_congr (n + 2) (g := fun s => (∑ i ∈ s, footnoteSigns (n + 2) i) ^ 2 /
    (n + 2 : ℝ) ^ 2)]
  · rw [expectation_div, he]
    push_cast
    have hk : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp <;> ring
  · intro s hs
    have hc := (mem_powersetCard.mp hs).2
    simp only [groupMean, hc, div_pow, Nat.cast_add, Nat.cast_ofNat]

/-- T10's exact true variance, from the actual uniform
randomization variance, for every population in its explicitly given family. -/
theorem footnote_true_variance_formula (a : ℝ) (n : ℕ) :
    trueVariance (footnotePopulation a n) =
      (3 * a ^ 2 + 2 * a + 1 / 3) / ((footnotePopulation a n).N - 1 : ℝ) := by
  change randomizationVariance (n + 2)
    (fun i : Fin (4 * (n + 2)) => a * footnoteSigns (n + 2) i + 2)
    (footnoteSigns (n + 2)) = (3 * a ^ 2 + 2 * a + 1 / 3) /
      ((4 * (n + 2) : ℕ) - 1 : ℝ)
  rcases footnote_population_moments a n with ⟨_, _, _, _, hv0, hv1, hcov⟩
  change popVariance (footnoteSigns (n + 2)) = 1 at hv0
  change popVariance (fun i => a * footnoteSigns (n + 2) i + 2) = a ^ 2 at hv1
  change popCovariance (fun i => a * footnoteSigns (n + 2) i + 2)
    (footnoteSigns (n + 2)) = a at hcov
  rw [randomization_variance_alternative (n + 2) (by omega) (by simp <;> omega)
    (by simp <;> omega), hv0, hv1, hcov]
  simp only [Fintype.card_fin]
  push_cast
  have hk : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp <;> ring

/-- Both deterministic limits for the three explicit sequences:
N V→3a²+2a+1/3 and N E[V̂_OLS]→4a²/3+4. These are separated from the
estimator probability limits, which are proved with finite concentration. -/
theorem footnote_deterministic_limits (a : ℝ) :
    Tendsto (fun n => ((footnotePopulation a n).N : ℝ) * trueVariance (footnotePopulation a n))
      atTop (𝓝 (3 * a ^ 2 + 2 * a + 1 / 3)) ∧
    Tendsto (fun n => ((footnotePopulation a n).N : ℝ) *
      expectation (footnotePopulation a n).M (fun s => olsEstimator (footnotePopulation a n) s))
      atTop (𝓝 (4 * a ^ 2 / 3 + 4)) := by
  have hg := (footnote_population_growth a).1
  have hp : Tendsto (fun n => ((footnotePopulation a n).M : ℝ) /
      (footnotePopulation a n).N) atTop (𝓝 (1 / 4 : ℝ)) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 4 : ℝ)) atTop (𝓝 _)).congr
    intro n; exact (footnote_population_moments a n).1.symm
  have hv0 : Tendsto (fun n => popVariance (footnotePopulation a n).y0) atTop (𝓝 1) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 _)).congr
    intro n; exact (footnote_population_moments a n).2.2.2.2.1.symm
  have hv1 : Tendsto (fun n => popVariance (footnotePopulation a n).y1) atTop (𝓝 (a ^ 2)) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => a ^ 2) atTop (𝓝 _)).congr
    intro n; exact (footnote_population_moments a n).2.2.2.2.2.1.symm
  have hc : Tendsto (fun n => popCovariance (footnotePopulation a n).y1
      (footnotePopulation a n).y0) atTop (𝓝 a) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 _)).congr
    intro n; exact (footnote_population_moments a n).2.2.2.2.2.2.symm
  have ht := scaled_true_variance_limit (footnotePopulation a) hg (1 / 4) (a ^ 2) 1 a
    (by norm_num) (by norm_num) hp hv1 hv0 hc
  have he := scaled_expected_ols_limit (footnotePopulation a) hg (1 / 4) (a ^ 2) 1
    (by norm_num) (by norm_num) hp hv1 hv0
  constructor
  · convert ht using 1 <;> congr 1 <;> ring
  · convert he using 1 <;> congr 1 <;> ring

/-- The Markov concentration input tends to zero: E[r²]→0 along the
explicit growing populations, independently of the treatment scale a. -/
lemma footnote_treated_square_limit (a : ℝ) :
    Tendsto (fun n => expectation (footnotePopulation a n).M
      (fun s => footnoteTreatedMean (footnotePopulation a n) s ^ 2)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => ((footnotePopulation a n).N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (footnote_population_growth a).1
  have hd : Tendsto (fun n => ((footnotePopulation a n).N : ℝ) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hn
  apply (hd.const_div_atTop 3).congr
  intro n; exact (footnote_treated_mean_square a n).symm

/-- T10(b): the realized OLS estimate has the claimed probability limit
N V̂_OLS→p 4a²/3+4. The proof uses E[r²]→0 and finite Markov, so it does
not replace a probability limit by an expectation limit. -/
theorem footnote_ols_probability_limit (a : ℝ) :
    ConvergesInProbability (footnotePopulation a) (fun Q s => (Q.N : ℝ) * olsEstimator Q s)
      (4 * a ^ 2 / 3 + 4) := by
  have hl := affine_square_probability_limit (footnotePopulation a) footnoteTreatedMean
    (fun Q => (Q.N : ℝ) / ((Q.N : ℝ) - 2)) (4 * a ^ 2 / 3 + 4)
    (4 * a ^ 2 / 3 + 4 / 9)
    (population_ratio_tends_one _ (footnote_population_growth a).1 2 (by norm_num))
    (footnote_treated_square_limit a)
  exact probability_limit_congr _ _ (fun n s hs => footnote_scaled_ols_formula a n s hs) hl

/-- The CE transfer in T6 holds as a probability limit on these witnesses:
N V̂_CE has the same limit as N V̂_OLS, through Theorem 2's exact factor. -/
theorem footnote_ce_probability_limit (a : ℝ) :
    ConvergesInProbability (footnotePopulation a) (fun Q s => (Q.N : ℝ) * ceEstimator Q s)
      (4 * a ^ 2 / 3 + 4) := by
  have hl := affine_square_probability_limit (footnotePopulation a) footnoteTreatedMean
    (fun Q => (Q.N : ℝ) / ((Q.N : ℝ) - 1)) (4 * a ^ 2 / 3 + 4)
    (4 * a ^ 2 / 3 + 4 / 9)
    (population_ratio_tends_one _ (footnote_population_growth a).1 1 (by norm_num))
    (footnote_treated_square_limit a)
  apply probability_limit_congr _ _ _ hl
  intro n s hs
  have ha := population_assignment_admissible (footnotePopulation a n) s hs
  have ho := footnote_scaled_ols_formula a n s hs
  have hc := scaled_ols_eq_constantEffects s
    (observed s (footnotePopulation a n).y1 (footnotePopulation a n).y0) ha
  simp only [Fintype.card_fin] at hc
  change ((footnotePopulation a n).N : ℝ) * constantEffects s _ = _
  rw [← hc]
  have hnR : 4 ≤ ((footnotePopulation a n).N : ℝ) := by
    exact_mod_cast (population_sizes (footnotePopulation a n)).2.2.2
  have hn1 : ((footnotePopulation a n).N : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : ((footnotePopulation a n).N : ℝ) - 2 ≠ 0 := by linarith
  calc
    _ = (((footnotePopulation a n).N : ℝ) - 2) / ((footnotePopulation a n).N - 1 : ℝ) *
      (((footnotePopulation a n).N : ℝ) * olsEstimator (footnotePopulation a n) s) := by
        unfold olsEstimator; ring
    _ = _ := by rw [ho]; field_simp <;> ring

/-- The deterministic ratio (N-1)/(N-2) tends to one on every growing
population sequence, as needed for the estimator-to-variance ratios. -/
lemma population_ratio_one_two (P : ℕ → Population) (hN : GrowingPopulations P) :
    Tendsto (fun n => ((P n).N - 1 : ℝ) / ((P n).N - 2 : ℝ)) atTop (𝓝 1) := by
  have hl := (population_ratio_tends_one P hN 2 (by norm_num)).div
    (population_ratio_tends_one P hN 1 (by norm_num)) (by norm_num)
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0)] at hl
  apply hl.congr
  intro n
  dsimp only [Pi.div_apply]
  have hnR : 4 ≤ ((P n).N : ℝ) := by exact_mod_cast (population_sizes (P n)).2.2.2
  have hn : ((P n).N : ℝ) ≠ 0 := by linarith
  have hn1 : ((P n).N : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : ((P n).N : ℝ) - 2 ≠ 0 := by linarith
  field_simp

/-- T10(b)'s estimator ratio limit: for a with nonzero leading
true variance, V̂_OLS/V→p (4a²/3+4)/(3a²+2a+1/3). The three
positive-scale cases below satisfy the nonzero hypothesis. -/
theorem footnote_ratio_probability_limit (a : ℝ)
    (hv : 3 * a ^ 2 + 2 * a + 1 / 3 ≠ 0) :
    ConvergesInProbability (footnotePopulation a)
      (fun Q s => olsEstimator Q s / trueVariance Q)
      ((4 * a ^ 2 / 3 + 4) / (3 * a ^ 2 + 2 * a + 1 / 3)) := by
  have hl := affine_square_probability_limit (footnotePopulation a) footnoteTreatedMean
    (fun Q => ((Q.N : ℝ) - 1) / ((Q.N : ℝ) - 2))
    ((4 * a ^ 2 / 3 + 4) / (3 * a ^ 2 + 2 * a + 1 / 3))
    ((4 * a ^ 2 / 3 + 4 / 9) / (3 * a ^ 2 + 2 * a + 1 / 3))
    (population_ratio_one_two _ (footnote_population_growth a).1)
    (footnote_treated_square_limit a)
  apply probability_limit_congr _ _ _ hl
  intro n s hs
  have ho := footnote_scaled_ols_formula a n s hs
  have ht := footnote_true_variance_formula a n
  have hnR : 4 ≤ ((footnotePopulation a n).N : ℝ) := by
    exact_mod_cast (population_sizes (footnotePopulation a n)).2.2.2
  have hn : ((footnotePopulation a n).N : ℝ) ≠ 0 := by linarith
  have hn1 : ((footnotePopulation a n).N : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : ((footnotePopulation a n).N : ℝ) - 2 ≠ 0 := by linarith
  have ho' : olsEstimator (footnotePopulation a n) s =
      (4 * a ^ 2 / 3 + 4 - (4 * a ^ 2 / 3 + 4 / 9) *
        footnoteTreatedMean (footnotePopulation a n) s ^ 2) /
          ((footnotePopulation a n).N - 2 : ℝ) := by
    apply (mul_left_cancel₀ hn)
    rw [ho]; ring
  rw [ho', ht]
  field_simp <;> ring

/-- One fully specified asymptotic counterexample row-family for T10,
with fixed allocation and first moments, actual deterministic and
probability limits, and a specified limiting OLS/true variance ratio q.
The equations correct the description on p. 369. -/
def FootnoteVarianceWitness (a q : ℝ) : Prop :=
  GrowingPopulations (footnotePopulation a) ∧
  (∀ n, (footnotePopulation a n).N ≠ 2 * (footnotePopulation a n).M) ∧
  (∀ n, ((footnotePopulation a n).M : ℝ) / (footnotePopulation a n).N = 1 / 4 ∧
    groupMean univ (footnotePopulation a n).y0 = 0 ∧
    groupMean univ (footnotePopulation a n).y1 = 2 ∧
    populationEffect (footnotePopulation a n) = 2 ∧
    popVariance (footnotePopulation a n).y0 = 1 ∧
    popVariance (footnotePopulation a n).y1 = a ^ 2 ∧
    popCovariance (footnotePopulation a n).y1 (footnotePopulation a n).y0 = a) ∧
  Tendsto (fun n => ((footnotePopulation a n).N : ℝ) * trueVariance (footnotePopulation a n))
    atTop (𝓝 (3 * a ^ 2 + 2 * a + 1 / 3)) ∧
  Tendsto (fun n => ((footnotePopulation a n).N : ℝ) *
    expectation (footnotePopulation a n).M (fun s => olsEstimator (footnotePopulation a n) s))
    atTop (𝓝 (4 * a ^ 2 / 3 + 4)) ∧
  ConvergesInProbability (footnotePopulation a) (fun Q s => (Q.N : ℝ) * olsEstimator Q s)
    (4 * a ^ 2 / 3 + 4) ∧
  ConvergesInProbability (footnotePopulation a) (fun Q s => (Q.N : ℝ) * ceEstimator Q s)
    (4 * a ^ 2 / 3 + 4) ∧
  ConvergesInProbability (footnotePopulation a) (fun Q s => olsEstimator Q s / trueVariance Q) q

/-- Every nondegenerate a supplies the explicit T10 variance witness,
with its ratio calculated from the two leading limits. -/
theorem footnote_variance_witness (a q : ℝ) (hv : 3 * a ^ 2 + 2 * a + 1 / 3 ≠ 0)
    (hq : (4 * a ^ 2 / 3 + 4) / (3 * a ^ 2 + 2 * a + 1 / 3) = q) :
    FootnoteVarianceWitness a q := by
  have hd := footnote_deterministic_limits a
  refine ⟨(footnote_population_growth a).1, (footnote_population_growth a).2,
    footnote_population_moments a, hd.1, hd.2, footnote_ols_probability_limit a,
    footnote_ce_probability_limit a, ?_⟩
  rw [← hq]; exact footnote_ratio_probability_limit a hv

/-- Shifts as finite populations, retaining N, M and the
standing design while changing y0 by c and y1 by c+d. -/
def shiftedPopulation (P : Population) (c d : ℝ) : Population where
  N := P.N
  M := P.M
  y1 := fun i => P.y1 i + (c + d)
  y0 := fun i => P.y0 i + c
  hM := P.hM
  hMN := P.hMN

/-- Exact invariance, expressed on population records so it can
be applied to every row of any asymptotic sequence. -/
theorem population_shift_invariance (P : Population) (c d : ℝ) :
    groupMean univ (shiftedPopulation P c d).y0 = groupMean univ P.y0 + c ∧
    populationEffect (shiftedPopulation P c d) = populationEffect P + d ∧
    trueVariance (shiftedPopulation P c d) = trueVariance P ∧
    ∀ s ∈ (univ : Finset (Fin P.N)).powersetCard P.M,
      intercept s (observed s (shiftedPopulation P c d).y1 (shiftedPopulation P c d).y0) =
        intercept s (observed s P.y1 P.y0) + c ∧
      pointEstimate (shiftedPopulation P c d) s = pointEstimate P s + d ∧
      (∀ i, residual s (observed s (shiftedPopulation P c d).y1
        (shiftedPopulation P c d).y0) i = residual s (observed s P.y1 P.y0) i) ∧
      olsEstimator (shiftedPopulation P c d) s = olsEstimator P s := by
  exact potential_outcome_shift_invariance P.M (by simpa using (population_sizes P).1)
    (by simpa using (population_sizes P).2.1) (by simpa using (population_sizes P).2.2.1)
    P.y1 P.y0 c d


/-- T10: an exact and asymptotic counterexample to footnote 3's
first-moment dependency description (p. 369). The explicit families
have identical allocation, control mean and average effect but limiting
OLS/true variance ratios 1,4/7,52/25. Arbitrary first-moment shifts leave
both variances unchanged. -/
theorem footnote_three_counterexample :
    FootnoteVarianceWitness 1 1 ∧ FootnoteVarianceWitness 2 (4 / 7) ∧
    FootnoteVarianceWitness (1 / 2) (52 / 25) ∧
    (4 / 7 : ℝ) ≠ 52 / 25 ∧
    ∀ (P : Population) (c d : ℝ),
      groupMean univ (shiftedPopulation P c d).y0 = groupMean univ P.y0 + c ∧
      populationEffect (shiftedPopulation P c d) = populationEffect P + d ∧
      trueVariance (shiftedPopulation P c d) = trueVariance P ∧
      ∀ s ∈ (univ : Finset (Fin P.N)).powersetCard P.M,
        olsEstimator (shiftedPopulation P c d) s = olsEstimator P s := by
  refine ⟨footnote_variance_witness 1 1 (by norm_num) (by norm_num),
    footnote_variance_witness 2 (4 / 7) (by norm_num) (by norm_num),
    footnote_variance_witness (1 / 2) (52 / 25) (by norm_num) (by norm_num), by norm_num, ?_⟩
  intro P c d
  have hi := population_shift_invariance P c d
  exact ⟨hi.1, hi.2.1, hi.2.2.1, fun s hs => (hi.2.2.2 s hs).2.2.2⟩

/-- A proved part of T6's asymptotic warning (p. 369): explicit growing
unbalanced sequences on which both OLS and CE probability limits fall
below the true leading variance, and others on which they exceed it.
This does not assert the separate standardized-normal/coverage limit. -/
theorem ols_ce_variance_limit_witnesses :
    (∃ (P : ℕ → Population) (a v : ℝ), UnbalancedVarianceLimit P a v ∧ a < v) ∧
    (∃ (P : ℕ → Population) (a v : ℝ), UnbalancedVarianceLimit P a v ∧ v < a) := by
  constructor
  · refine ⟨footnotePopulation 2, 28 / 3, 49 / 3, ?_, by norm_num⟩
    refine ⟨(footnote_population_growth 2).1, (footnote_population_growth 2).2,
      by norm_num, ?_, ?_, ?_⟩
    · convert (footnote_deterministic_limits 2).1 using 1 <;> norm_num
    · convert footnote_ols_probability_limit 2 using 1 <;> norm_num
    · convert footnote_ce_probability_limit 2 using 1 <;> norm_num
  · refine ⟨footnotePopulation (1 / 2), 13 / 3, 25 / 12, ?_, by norm_num⟩
    refine ⟨(footnote_population_growth (1 / 2)).1, (footnote_population_growth (1 / 2)).2,
      by norm_num, ?_, ?_, ?_⟩
    · convert (footnote_deterministic_limits (1 / 2)).1 using 1 <;> norm_num
    · convert footnote_ols_probability_limit (1 / 2) using 1 <;> norm_num
    · convert footnote_ce_probability_limit (1 / 2) using 1 <;> norm_num

/-- "If in addition the sample second moments converge" in corrected
T11: both arm sample centered second moments consistently
estimate their divisor-N population variances. This hypothesis is explicit. -/
def ArmSecondMomentsConverge (P : ℕ → Population) : Prop :=
  ConvergesInProbability P (fun Q s => sampleVariance s Q.y1 - popVariance Q.y1) 0 ∧
  ConvergesInProbability P (fun Q s => sampleVariance sᶜ Q.y0 - popVariance Q.y0) 0

/-- "Potential outcomes are uniformly bounded along the sequence"
(corrected T11): one real bound controls both schedules
for every unit in every finite population. -/
def UniformlyBoundedOutcomes (P : ℕ → Population) : Prop :=
  ∃ B : ℝ, ∀ n i, |(P n).y1 i| ≤ B ∧ |(P n).y0 i| ≤ B


/-- The exact finite sampling identity underlying corrected T11:
the mean-squared error of a sample mean is (N-M)/(M(N-1)) σ²(v).
The expectation is over the actual equally likely size-M assignments. -/
theorem sample_mean_squared_error (M : ℕ) (hM : 2 ≤ M)
    (hMN : M ≤ Fintype.card ι) (v : ι → ℝ) :
    expectation M (fun s => (groupMean s v - groupMean univ v) ^ 2) =
      ((Fintype.card ι : ℝ) - M) / ((M : ℝ) * ((Fintype.card ι : ℝ) - 1)) * popVariance v := by
  have hmR : 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hnR : 2 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 2 ≤ Fintype.card ι)
  have hm : (M : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  rw [expectation_congr M (g := fun s =>
    ((∑ i ∈ s, v i) - (M : ℝ) * groupMean univ v) ^ 2 / (M : ℝ) ^ 2)]
  · rw [expectation_div, expected_group_deviation M hM hMN]
    field_simp <;> ring
  · intro s hs
    have hc := (mem_powersetCard.mp hs).2
    change ((∑ i ∈ s, v i) / s.card - groupMean univ v) ^ 2 = _
    rw [hc]
    field_simp <;> ring

/-- A bounded population has divisor-N variance at most the square of
the bound. This finite lemma supports the uniformly bounded sufficient
condition in corrected T11; no first-moment limit is required. -/
lemma bounded_population_variance (v : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hn : 0 < (Fintype.card ι : ℝ)) (hv : ∀ i, |v i| ≤ B) : popVariance v ≤ B ^ 2 := by
  have hsq : ∀ i, v i ^ 2 ≤ B ^ 2 := by
    intro i
    have hi := abs_le.mp (hv i)
    have hm := mul_nonneg (by linarith [hi.2] : 0 ≤ B - v i)
      (by linarith [hi.1] : 0 ≤ B + v i)
    nlinarith
  have hs : (∑ i, v i ^ 2) ≤ (Fintype.card ι : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _i : ι, B ^ 2 := Finset.sum_le_sum (fun i _ => hsq i)
      _ = _ := by simp
  rw [pop_variance_raw v hn.ne']
  have hd : (∑ i, v i ^ 2) / Fintype.card ι ≤ B ^ 2 := by
    apply (div_le_iff₀ hn).mpr
    simpa [mul_comm] using hs
  linarith [sq_nonneg ((∑ i, v i) / (Fintype.card ι : ℝ))]

/-- Corrected T11's finite bounded-moment concentration inputs: the sampled
first and second raw moments have mean-squared errors bounded by the sampling coefficient times B² and B⁴ respectively.
These inequalities are exact at every fixed population size. -/
theorem bounded_raw_sample_moment_errors (M : ℕ) (hM : 2 ≤ M)
    (hMN : M ≤ Fintype.card ι) (v : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ i, |v i| ≤ B) :
    expectation M (fun s => (groupMean s v - groupMean univ v) ^ 2) ≤
      ((Fintype.card ι : ℝ) - M) / ((M : ℝ) * ((Fintype.card ι : ℝ) - 1)) * B ^ 2 ∧
    expectation M (fun s => (groupMean s (fun i => v i ^ 2) -
      groupMean univ (fun i => v i ^ 2)) ^ 2) ≤
      ((Fintype.card ι : ℝ) - M) / ((M : ℝ) * ((Fintype.card ι : ℝ) - 1)) * B ^ 4 := by
  have hmR : 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hnR : 2 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 2 ≤ Fintype.card ι)
  have hmn : (M : ℝ) ≤ Fintype.card ι := by exact_mod_cast hMN
  have hcoef : 0 ≤ ((Fintype.card ι : ℝ) - M) /
      ((M : ℝ) * ((Fintype.card ι : ℝ) - 1)) := by
    apply div_nonneg (by linarith)
    apply mul_nonneg <;> linarith
  constructor
  · rw [sample_mean_squared_error M hM hMN]
    exact mul_le_mul_of_nonneg_left (bounded_population_variance v B hB (by linarith) hv) hcoef
  · rw [sample_mean_squared_error M hM hMN]
    have hv2 : ∀ i, |v i ^ 2| ≤ B ^ 2 := by
      intro i
      rw [abs_of_nonneg (sq_nonneg (v i))]
      have hi := abs_le.mp (hv i)
      have hm := mul_nonneg (by linarith [hi.2] : 0 ≤ B - v i)
        (by linarith [hi.1] : 0 ≤ B + v i)
      nlinarith
    have hl := bounded_population_variance (fun i => v i ^ 2) (B ^ 2) (sq_nonneg B)
      (by linarith) hv2
    simpa [← pow_mul] using mul_le_mul_of_nonneg_left hl hcoef


end
end AronowAudit.P031
