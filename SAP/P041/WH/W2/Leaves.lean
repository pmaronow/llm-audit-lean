import SAP.P041.Defs.WholeW2
import SAP.P041.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W2

open Matrix MeasureTheory
open scoped BigOperators

/-- Covariance under a finite linear change of random coefficients, including
existence of the transformed second moments. Prove the moment clause using
`MemLp.const_mul` and `memLp_finsetSum`. For each matrix entry, expand `mulVec`,
apply `ProbabilityTheory.covariance_fun_sum_fun_sum`, and pull out both scalar
factors with `covariance_const_mul_left/right`. Expand the matrix products and
reorder the finite double sum. No independence or nonsingularity is needed.
The tenure matrix is a specialization, so this leaf also covers every nuisance
coordinate and every cross covariance. Estimated covariance matrices use the
same congruence rule. Expected size: approximately 80–150 lines. -/
def T10_L1 : Prop :=
  ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix ι ι ℝ) (X : Ω → ι → ℝ),
    (∀ i, MemLp (fun ω => X ω i) 2 μ) →
    (∀ i, MemLp (fun ω => (A *ᵥ X ω) i) 2 μ) ∧
    covarianceMatrixW2 μ (fun ω => A *ᵥ X ω) =
      A * covarianceMatrixW2 μ X * A.transpose

/-- Both S9 Table B rounding rectangles give a two-sided normal Wald p value
below 0.01. Positivity of r and s follows from the rectangles. The inequality
`Real.one_sub_inv_le_log_of_pos` gives r*log(r) ≥ r-1, and hence
`hazardWald r s > 2.7`, uniformly even at the largest possible s=0.0205.
Specialize `AronowAudit.P041.Wave1.normal_tail_bound` at x=2.7, n=8;
`norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial]` supplies an
exact rational certificate for the endpoint p<0.01. Use
`AronowAudit.P041.Wave1.normal_tail_antitone` to reach every statistic in the
rectangles. All uses of the Gaussian integral are in the certified donor.
Expected size: approximately 60–120 lines. -/
def T10_L2 : Prop :=
  ∀ (r s : ℝ), printedInterval 1.056 r →
    (printedInterval 0.020 s ∨ printedInterval 0.019 s) →
    normalTwoSided (hazardWald r s) < 0.01

private theorem coefficients_eqW2 (n : ℕ) (C : ℝ) (β : Fin 3 ⊕ Fin n → ℝ) :
    tenureCoefficientsW2 n C β = tenureChangeW2 n C *ᵥ β := by
  ext i
  rcases i with i | j
  · fin_cases i <;>
      simp [tenureCoefficientsW2, tenureChangeW2, tenureCoreW2, Matrix.mulVec,
        dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ]
  · simp [tenureCoefficientsW2, tenureChangeW2, Matrix.mulVec,
      dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

private theorem coefficients_twiceW2 (n : ℕ) (C : ℝ) (β : Fin 3 ⊕ Fin n → ℝ) :
    tenureCoefficientsW2 n C (tenureCoefficientsW2 n C β) = β := by
  ext i
  rcases i with i | j
  · fin_cases i <;> simp [tenureCoefficientsW2]
  · rfl

private theorem variance_eqW2 (n : ℕ) (C : ℝ)
    (V : Matrix (Fin 3 ⊕ Fin n) (Fin 3 ⊕ Fin n) ℝ) :
    (tenureChangeW2 n C * V * (tenureChangeW2 n C).transpose)
      (Sum.inl 2) (Sum.inl 2) = V (Sum.inl 2) (Sum.inl 2) := by
  simp [tenureChangeW2, tenureCoreW2, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_succ]

private theorem hazard_ratioW2 (h₀ a b g C L w : ℝ) (hh : h₀ ≠ 0) :
    tenureHazard h₀ b a g C L 1 w / tenureHazard h₀ b a g C L 0 w =
      Real.exp ((a + C * g) + (-g) * L) := by
  simp only [tenureHazard, mul_one, mul_zero, add_zero]
  rw [mul_div_mul_left _ _ (mul_ne_zero hh (Real.exp_ne_zero _)), ← Real.exp_sub]
  congr 1
  ring

private theorem main_incrementW2 (h₀ b C L w : ℝ) :
    Real.exp (-b) = 1 / Real.exp b ∧
    tenureHazard h₀ b 0 0 C (L + 1) 0 w =
      tenureHazard h₀ b 0 0 C L 0 w * (1 / Real.exp b) := by
  constructor
  · simp [Real.exp_neg]
  · have he : (-b) * (L + 1) + w = ((-b) * L + w) + (-b) := by ring
    simp only [tenureHazard, mul_zero, zero_mul, add_zero]
    rw [he, Real.exp_add, Real.exp_neg, one_div]
    simp only [mul_assoc]

private theorem reciprocal_waldW2 (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    hazardWald (1 / r) (s / r ^ 2) = -hazardWald r s := by
  simp only [hazardWald, one_div, Real.log_inv]
  field_simp [ne_of_gt hr, ne_of_gt hs]

/-- Assemble every clause of the corrected claim. Only the covariance rule and
the uniform numerical three-star verification are left to the leaf writers. -/
theorem T10_assembly (h1 : T10_L1) (h2 : T10_L2) : T10WholeStatement := by
  refine ⟨Bridge.year_tenure_reparameterization, hazard_ratioW2,
    Bridge.tenure_multiplier_is_reciprocal, main_incrementW2, ?_, ?_, variance_eqW2,
    ?_, ?_, ?_, ?_, Bridge.year_tenure_exact_instance, ?_⟩
  · obtain ⟨hA, hB, hC, hD⟩ := Bridge.printed_tenure_reciprocal_enclosures
    refine ⟨(fun r hr => hA r hr.1 hr.2), (fun r hr => hB r hr.1 hr.2),
      ?_, (fun r hr => hD r hr.1 hr.2)⟩
    intro r hr
    obtain ⟨hl, hu, hd⟩ := hC r hr.1 hr.2
    refine ⟨hl, hu, hd, ?_⟩
    simp only [one_div] at hl hu
    constructor <;> norm_num [roundsWhole] <;> linarith
  · intro n C β
    exact ⟨coefficients_eqW2 n C β, coefficients_twiceW2 n C β⟩
  · intro n Ω _ μ _ C X hX
    obtain ⟨hm, hc⟩ := h1 Ω (Fin 3 ⊕ Fin n) μ (tenureChangeW2 n C) X hX
    constructor
    · intro i
      simpa only [coefficients_eqW2] using hm i
    · simpa only [coefficients_eqW2] using hc
  · intro g V s hV hs
    simpa only [Real.exp_neg, one_div] using
      (Bridge.reciprocal_standard_error_and_wald g V s hV hs).1
  · intro g V _
    simp [neg_div, normalTwoSided]
  · intro r s hr hs
    have hr0 : 0 < r := by rcases hr with ⟨hr, _⟩; linarith
    have hs0 : 0 < s := by
      rcases hs with hs | hs <;> rcases hs with ⟨hs, _⟩ <;> linarith
    have hp := h2 r s hr hs
    have he : normalTwoSided (hazardWald (1 / r) (s / r ^ 2)) =
        normalTwoSided (hazardWald r s) := by
      rw [reciprocal_waldW2 r s hr0 hs0]
      simp [normalTwoSided]
    refine ⟨hp, he, ?_, ?_⟩
    · unfold significanceTier
      simp only [hp, ite_true]
    · rw [significanceTier, he]
      simp only [hp, ite_true]
  · norm_num [tenureFromYear]

end SAP.P041.WH.W2
