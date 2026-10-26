import AronowAudit.P015.P015_Regression
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Poisson.Basic

namespace AronowAudit.P015.Wave1

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

open scoped BigOperators Topology NNReal
open Finset Matrix MeasureTheory ProbabilityTheory Filter

/-- The standard Bernoulli response at the logistic mean, with unit dispersion. -/
noncomputable def bernoulliResponseLaw (η : ℝ) : MeasureTheory.Measure ℝ :=
  ProbabilityTheory.bernoulliMeasure (1 : ℝ) 0
    ⟨AronowAudit.P015.logistic η, by
      constructor
      · exact (Real.sigmoid_pos η).le
      · exact (Real.sigmoid_lt_one η).le⟩

/-- The standard Poisson response at rate `exp η`, with unit dispersion. -/
noncomputable def poissonResponseLaw (η : ℝ) : MeasureTheory.Measure ℕ :=
  ProbabilityTheory.poissonMeasure
    ⟨Real.exp η, (Real.exp_pos η).le⟩

lemma p015T8_poisson_probability (r : ℝ≥0) :
    MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.poissonMeasure r) := by
  unfold ProbabilityTheory.poissonMeasure
  exact HasSum.isProbabilityMeasure_sum_dirac
    (fun n => div_nonneg
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg r.coe_nonneg n))
      (Nat.cast_nonneg _))
    (ProbabilityTheory.hasSum_one_poissonMeasure r)

lemma p015T8_poisson_firstMoment_succ (r : ℝ≥0) (n : ℕ) :
    (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) /
        ((n + 1).factorial : ℝ)) * ((n + 1 : ℕ) : ℝ) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) := by
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hn, hf]

/-- Shifting the normalized Poisson series gives its absolute first moment. -/
lemma p015T8_poisson_firstMoment_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ =>
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) * (n : ℝ))
      (r : ℝ) := by
  have htail : HasSum (fun n : ℕ =>
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) /
        ((n + 1).factorial : ℝ)) * ((n + 1 : ℕ) : ℝ)) (r : ℝ) := by
    simpa only [p015T8_poisson_firstMoment_succ, mul_one] using
      (ProbabilityTheory.hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have hall := (hasSum_nat_add_iff (f := fun n : ℕ =>
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) * (n : ℝ)) 1).mp htail
  simpa only [Finset.sum_range_one, Nat.cast_zero, mul_zero, add_zero] using hall

lemma p015T8_poisson_integrable (r : ℝ≥0) :
    MeasureTheory.Integrable (fun n : ℕ => (n : ℝ))
      (ProbabilityTheory.poissonMeasure r) := by
  apply ProbabilityTheory.integrable_poissonMeasure_iff.mpr
  simpa only [Real.norm_natCast] using (p015T8_poisson_firstMoment_hasSum r).summable

lemma p015T8_poisson_integral (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r)) = (r : ℝ) := by
  rw [ProbabilityTheory.integral_poissonMeasure' (p015T8_poisson_integrable r)]
  simpa only [smul_eq_mul] using (p015T8_poisson_firstMoment_hasSum r).tsum_eq

/-- The named response laws are normalized and integrable, and their coordinate
means equal the derivatives of the corresponding cumulants. -/
theorem canonical_named_model_means (η : ℝ) :
    (MeasureTheory.IsProbabilityMeasure
        (AronowAudit.P015.Wave1.bernoulliResponseLaw η) ∧
      MeasureTheory.Integrable (fun y : ℝ => y)
        (AronowAudit.P015.Wave1.bernoulliResponseLaw η) ∧
      (∫ y : ℝ, y ∂(AronowAudit.P015.Wave1.bernoulliResponseLaw η)) =
        AronowAudit.P015.logistic η ∧
      AronowAudit.P015.logistic η =
        deriv (fun a : ℝ => Real.log (1 + Real.exp a)) η) ∧
    (MeasureTheory.IsProbabilityMeasure
        (AronowAudit.P015.Wave1.poissonResponseLaw η) ∧
      MeasureTheory.Integrable (fun n : ℕ => (n : ℝ))
        (AronowAudit.P015.Wave1.poissonResponseLaw η) ∧
      (∫ n : ℕ, (n : ℝ) ∂(AronowAudit.P015.Wave1.poissonResponseLaw η)) =
        Real.exp η ∧
      Real.exp η = deriv Real.exp η) := by
  constructor
  · refine ⟨?_, ?_, ?_, (AronowAudit.P015.canonical_named_means.1 η).symm⟩
    · unfold bernoulliResponseLaw
      infer_instance
    · unfold bernoulliResponseLaw
      exact ProbabilityTheory.integrable_bernoulliMeasure _ _ _ _
    · unfold bernoulliResponseLaw
      rw [ProbabilityTheory.integral_bernoulliMeasure]
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
  · refine ⟨?_, ?_, ?_, (AronowAudit.P015.canonical_named_means.2 η).symm⟩
    · exact p015T8_poisson_probability ⟨Real.exp η, (Real.exp_pos η).le⟩
    · exact p015T8_poisson_integrable ⟨Real.exp η, (Real.exp_pos η).le⟩
    · exact p015T8_poisson_integral ⟨Real.exp η, (Real.exp_pos η).le⟩

/-- Affine reparametrization gives both the observation predictors and the
corresponding residual-score identity under a unit intercept. -/
theorem affine_predictor (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K + 2)) ℝ)
    (hW : ∀ i, W i 0 = 1) (b c : ℝ)
    (θ : Fin (K + 2) → ℝ) (Y : Fin N → ℝ) :
    (∀ i, W.mulVec (AronowAudit.P015.affineTheta 0 b c θ) i =
      b + c * W.mulVec θ i) ∧
    W.transpose.mulVec (fun i => Y i - b - c * W.mulVec θ i) =
      W.transpose.mulVec (fun i =>
        Y i - W.mulVec (AronowAudit.P015.affineTheta 0 b c θ) i) := by
  have hp := AronowAudit.P015.affine_predictor W 0 hW b c θ
  refine ⟨hp, ?_⟩
  apply congrArg W.transpose.mulVec
  funext i
  rw [hp i]
  ring

/-- The complete fixed-center, all-degree Taylor counterexample, including
the exact complex radius and the finite-data certificates. -/
theorem taylor_counterexample :
    AronowAudit.P015.TaylorCounterexample := by
  exact AronowAudit.P015.TaylorCounterexample_checked

end
end AronowAudit.P015.Wave1
