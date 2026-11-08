import SAP.P039.WH.W1.Facts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.WH.W1
open scoped BigOperators Matrix NNReal ENNReal
open MeasureTheory ProbabilityTheory

/-- Split the product Gaussian into its first coordinate and a gamma denominator,
then derive the normal scale-mixture density. Use `standard_pair_squares`,
`gaussian_squares_eq_gamma`, and `erase_zero_sum`. The denominator is positive
almost surely. For each positive denominator, scale the Gaussian density; use
Tonelli on nonnegative integrands to exchange the mixture and Lebesgue integrals.
This is a density identification, not an assumption about nominal tails. -/
def T3_L1 : Prop :=
  ∀ ν : ℕ, 0 < ν →
    studentLaw ν = volume.withDensity (studentMixtureDensity ν)

/-- Evaluate the one-dimensional gamma mixture. Expand the Gaussian and gamma
densities on w>0, combine powers to w^((nu+1)/2-1), and apply
`Real.integral_rpow_mul_exp_neg_mul_Ioi` at rate (1+t²/nu)/2.
Use the integrability criterion for a power times an exponential before converting
the nonnegative integral to a real integral. Both shape and rate are positive. -/
def T3_L2 : Prop :=
  ∀ ν : ℕ, 0 < ν → ∀ t : ℝ,
    studentMixtureDensity ν t = ENNReal.ofReal (wholeStudentDensity ν t)

/-- Integrate the t4 density on the two rays outside [-t,t]. Simplify the gamma
constants, differentiate (3z-z³)/4 for z=t/sqrt(4+t²), and take its limits at
infinity. Symmetry handles the negative ray. The integral is finite, including
t=0, and the formula is nonnegative. About 150--250 lines of calculus. -/
def T3_L3 : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (volume.withDensity (fun s => ENNReal.ofReal (wholeStudentDensity 4 s)))
      {s : ℝ | t ≤ |s|} = ENNReal.ofReal (studentFourTail t) ∧
    0 ≤ studentFourTail t

/-- Integrate the t3 density on the two rays. Its positive-side primitive is
(arctan q+q/(1+q²))/pi, q=t/sqrt(3). Use `Real.hasDerivAt_arctan`, the gamma
recurrence and Gamma(1/2)=sqrt(pi); the limit of arctan at infinity gives the
normalization. Include t=0 and certify nonnegativity and finite mass. -/
def T3_L4 : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (volume.withDensity (fun s => ENNReal.ofReal (wholeStudentDensity 3 s)))
      {s : ℝ | t ≤ |s|} = ENNReal.ofReal (studentThreeTail t) ∧
    0 ≤ studentThreeTail t

/-- Alternating polynomial bounds for arctan on the nonnegative half-line.
Subtract the proposed polynomials and compare derivatives: the remaining
terms are x^4/(1+x²) and x^6/(1+x²), with the required signs. All three functions
vanish at zero. The mean-value monotonicity theorem or FTC proves both bounds.
Only the specialization x=1/5 is used in the decimal certificates. -/
def T3_L5 : Prop :=
  ∀ x : ℝ, 0 ≤ x →
    x - x ^ 3 / 3 ≤ Real.arctan x ∧
    Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5

/-- Full-regression projection geometry and exact numerator/SE identities.
Use `full_fit`, `ols_projection_identities`, `residual_quadratic` and
`residual_rank`. The contrast is Mx/sqrt(x'Mx), of norm one, and is killed by
the full residual projection. Its rank is n-k-1. The null controls drop out
of the numerator and residual vector. All denominators are positive by full
rank and x outside the controls. Estimated 200--350 lines. -/
def T4_L1 : Prop :=
  ∀ {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ),
    FullColumnRank Z → (¬ ∃ c, Z *ᵥ c = x) → k + 1 < n →
    WholeRegressionGeometry Z x

/-- Complete a unit contrast orthogonal to the range of a symmetric idempotent
matrix to an orthonormal row frame. Choose the standard orthonormal basis of
range(Q), reindex it using rank(Q)=nu, and prepend e. Parseval gives the energy
identity; orthogonality gives BB'=I. This finite-dimensional statement also
includes nu=0; no basis is chosen on an empty or incorrectly sized range.
Estimated 200--350 lines, adapting the corestriction/basis construction in
`stdGaussian_map_normSq_orthogonalProjection`. -/
def T4_L2 : Prop :=
  ∀ {n ν : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ),
    Qᵀ = Q → Q * Q = Q → Q *ᵥ e = 0 → dotProduct e e = 1 → Q.rank = ν →
    ∃ B : Matrix (Fin (ν + 1)) (Fin n) ℝ, WholeProjectionFrame Q e B

/-- Infer the full-model Student law from the exact geometry and frame, under
actual product Gaussian noise. Generalize `contrasts_standard_law` to B using
`matrixCLM_coisometry` and `gaussian_coisometry`; normalize the noise using
`normalize_gaussian` and `Measure.pi_map_pi`. The frame then expresses the
OLS statistic as coordinate 0 over sqrt(sum of the remaining squares / df),
pointwise even at zero SSE. `erase_zero_sum` identifies `studentLaw` exactly.
The tail-coordinate sum is positive almost surely: its chi-square/gamma law
has positive shape and is supported on (0,infinity). Estimated 200--350 lines.
No Student sampling law is a premise. -/
def T4_L3 : Prop :=
  ∀ {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ)
    (γ : Fin k → ℝ) (σ : ℝ≥0),
    0 < σ → k + 1 < n → WholeRegressionGeometry Z x →
    (∃ B : Matrix (Fin (n - k - 1 + 1)) (Fin n) ℝ,
      WholeProjectionFrame (residualMaker (fullDesign Z x)) (wholeRegressorContrast Z x) B) →
    let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 (σ ^ 2))
    μ.map (fun ε => olsT (fullDesign Z x) (Z *ᵥ γ + ε) (Fin.last k)) =
      studentLaw (n - k - 1) ∧
    (∀ᵐ ε ∂μ, 0 < olsSSE (fullDesign Z x) (Z *ᵥ γ + ε))

/-- The inverse second moment of a chi-square variable at df>4. Transport
`gaussian_squares_eq_gamma`, apply `integrable_rpow_gamma` at q=-2, and integrate
the density using `gamma_rpow_integrand` and the power-exponential integral.
Two applications of `Real.Gamma_add_one` give 1/((nu-2)(nu-4)). The explicit
integrability conclusion rules out totalized integrals. About 100--180 lines. -/
def T7_L1 : Prop :=
  ∀ ν : ℕ, 4 < ν →
    Integrable (fun w : ℝ => (w⁻¹) ^ 2) (chiSquaredLaw ν) ∧
    (∫ w : ℝ, (w⁻¹) ^ 2 ∂chiSquaredLaw ν) =
      1 / (((ν : ℝ) - 2) * ((ν : ℝ) - 4))

/-- Transfer the inverse second moment to the Student fourth moment. Split
the independent Gaussian numerator and chi-square denominator using
`standard_pair_squares`. The fourth power factors as G^4 * nu² * (W^-1)²;
the Gaussian fourth moment is three (derive it from the one-coordinate square
law and `StatLean.MultipleTesting.variance_gammaMeasure`). Product integrability and
`integral_prod_mul` give the result. The premises are discharged by T7_L1;
the density identification used in T3 is unnecessary. About 100--180 lines. -/
def T7_L2 : Prop :=
  ∀ ν : ℕ, 4 < ν →
    Integrable (fun w : ℝ => (w⁻¹) ^ 2) (chiSquaredLaw ν) →
    (∫ w : ℝ, (w⁻¹) ^ 2 ∂chiSquaredLaw ν) =
      1 / (((ν : ℝ) - 2) * ((ν : ℝ) - 4)) →
    Integrable (fun t : ℝ => t ^ 4) (studentLaw ν) ∧
    (∫ t : ℝ, t ^ 4 ∂studentLaw ν) =
      3 * (ν : ℝ) ^ 2 / (((ν : ℝ) - 2) * ((ν : ℝ) - 4))

theorem T3_assembly (h1 : T3_L1) (h2 : T3_L2) (h3 : T3_L3)
    (h4 : T3_L4) (h5 : T3_L5) : T3WholeStatement := by
  have htail : ∀ t : ℝ, 0 ≤ t →
      studentTailProbability 4 t = studentFourTail t ∧
      studentTailProbability 3 t = studentThreeTail t := by
    intro t ht
    have hd (ν : ℕ) (hν : 0 < ν) : studentLaw ν =
        volume.withDensity (fun s => ENNReal.ofReal (wholeStudentDensity ν s)) := by
      rw [h1 ν hν]
      congr 1
      funext s
      exact h2 ν hν s
    obtain ⟨hf, hf0⟩ := h3 t ht
    obtain ⟨hg, hg0⟩ := h4 t ht
    constructor
    · simp only [studentTailProbability, hd 4 (by decide), hf, ENNReal.toReal_ofReal hf0]
    · simp only [studentTailProbability, hd 3 (by decide), hg, ENNReal.toReal_ofReal hg0]
  have ha := h5 (1 / 5) (by norm_num)
  have hdec := witness_tail_decimals ha.1 ha.2
  have hf := (htail 3 (by norm_num)).1
  have hg := (htail (3 * Real.sqrt 3 / 2) (by positivity)).2
  refine ⟨Bridge.T3_correspondence, ?_, htail, witness_tail_comparisons, ?_, ?_⟩
  · rw [show olsResidual witnessZ witnessY = ![0, 0, (3 / 2 : ℝ), -3 / 2, 1, -1]
      from AronowAudit.P039.witness_baseline.2.2.2.2.1]
    ext i
    fin_cases i <;> norm_num [witnessV, witnessW]
  · rw [hf, hg]
    exact ⟨AronowAudit.P039.residual_test_five_percent_disagreement.1,
      AronowAudit.P039.residual_test_five_percent_disagreement.2.1,
      AronowAudit.P039.residual_test_five_percent_disagreement.2.2.1,
      witness_tail_comparisons.2.2.2.2.2.2.2.2.2.1⟩
  · rwa [hf, hg]

theorem T4_assembly (h1 : T4_L1) (h2 : T4_L2) (h3 : T4_L3) : T4WholeStatement := by
  refine ⟨Bridge.T4_correspondence, ?_⟩
  intro Ω _ μ _ n k Z x γ ε σ hσ hZ hone hx hn hε hlaw
  have hg := h1 Z x hZ hx hn
  have hf : ∃ B : Matrix (Fin (n - k - 1 + 1)) (Fin n) ℝ,
      WholeProjectionFrame (residualMaker (fullDesign Z x)) (wholeRegressorContrast Z x) B := by
    obtain ⟨_, he, hQt, hQQ, hQe, hQr, _⟩ := hg
    exact h2 _ _ hQt hQQ hQe he hQr
  have hs := h3 Z x γ σ hσ hn hg hf
  dsimp only at hs ⊢
  have htf : Measurable (fun z : Fin n → ℝ =>
      olsT (fullDesign Z x) (Z *ᵥ γ + z) (Fin.last k)) := by
    exact (AronowAudit.P039.CovarianceCompletion.measurable_olsT _ _).comp (by fun_prop)
  have ht : μ.map (fun ω => olsT (fullDesign Z x) (Z *ᵥ γ + ε ω) (Fin.last k)) =
      studentLaw (n - k - 1) := by
    change μ.map ((fun z => olsT (fullDesign Z x) (Z *ᵥ γ + z) (Fin.last k)) ∘ ε) = _
    rw [← Measure.map_map htf hε, hlaw]
    exact hs.1
  have hp : ∀ᵐ ω ∂μ, 0 < olsSSE (fullDesign Z x) (Z *ᵥ γ + ε ω) := by
    apply ae_of_ae_map (μ := μ)
      (p := fun z => 0 < olsSSE (fullDesign Z x) (Z *ᵥ γ + z)) hε.aemeasurable
    rw [hlaw]
    exact hs.2
  refine ⟨ht, hp, ?_, ?_⟩
  · filter_upwards [hp] with ω hω
    exact lt_of_lt_of_le hω (residual_sse_bound Z x _ hZ hone hx hn)
  · intro horth
    have hr : μ.map (fun ω =>
        olsT (residualLine x) (residualMaker Z *ᵥ (Z *ᵥ γ + ε ω)) 1) =
        (studentLaw (n - k - 1)).map
          (fun t => Real.sqrt (((n : ℝ) - 2) / ((n : ℝ) - k - 1)) * t) := by
      simp_rw [show ∀ y : Fin n → ℝ,
        olsT (residualLine x) (residualMaker Z *ᵥ y) 1 =
          Real.sqrt (((n : ℝ) - 2) / ((n : ℝ) - k - 1)) *
            olsT (fullDesign Z x) y (Fin.last k) from
        fun y => AronowAudit.P039.CovarianceCompletion.orthogonal_t_scale
          Z x y hZ hone hx hn horth]
      change μ.map ((fun t => Real.sqrt (((n : ℝ) - 2) / ((n : ℝ) - k - 1)) * t) ∘
        (fun ω => olsT (fullDesign Z x) (Z *ᵥ γ + ε ω) (Fin.last k))) = _
      have htm : Measurable (fun ω => olsT (fullDesign Z x) (Z *ᵥ γ + ε ω) (Fin.last k)) :=
        htf.comp hε
      rw [← Measure.map_map (by fun_prop) htm, ht]
    refine ⟨hr, ?_⟩
    intro hk
    rw [hr]
    exact scaled_student_ne hn hk

theorem T7_assembly (h1 : T7_L1) (h2 : T7_L2) : T7WholeStatement := by
  have moment (ν : ℕ) (hν : 4 < ν) :
      Integrable (fun t : ℝ => t ^ 4) (studentLaw ν) ∧
      (∫ t : ℝ, t ^ 4 ∂studentLaw ν) =
        3 * (ν : ℝ) ^ 2 / (((ν : ℝ) - 2) * ((ν : ℝ) - 4)) :=
    h2 ν hν (h1 ν hν).1 (h1 ν hν).2
  have ha := moment 14 (by decide)
  have hb := moment 13 (by decide)
  have hc := moment 12 (by decide)
  refine ⟨Bridge.T7_correspondence, alternative_rmsq, ?_, ?_, ?_⟩
  · calc
      studentTailProbability 14 |olsT tableA1 tableTwoOutcome 1| ≤
          (∫ t : ℝ, t ^ 4 ∂studentLaw 14) / 6 ^ 4 :=
        student_six_tail _ _ ha.1 table_income_statistics.1.le
      _ < 1 / 100 := by rw [ha.2]; norm_num
  · calc
      studentTailProbability 13 |olsT tableA2 tableTwoOutcome 1| ≤
          (∫ t : ℝ, t ^ 4 ∂studentLaw 13) / 6 ^ 4 :=
        student_six_tail _ _ hb.1 table_income_statistics.2.1.le
      _ < 1 / 100 := by rw [hb.2]; norm_num
  · calc
      studentTailProbability 12 |olsT tableA3 tableTwoOutcome 1| ≤
          (∫ t : ℝ, t ^ 4 ∂studentLaw 12) / 6 ^ 4 :=
        student_six_tail _ _ hc.1 table_income_statistics.2.2.le
      _ < 1 / 100 := by rw [hc.2]; norm_num

end SAP.P039.WH.W1
