import AronowAudit.P006.P006_CounterfactualMetrics

/-!
# P006-T13: statements for corrected ranking on a measurable covariate domain

The file contains three statements: lifting indicator ignorability to the
integrable treated outcome, change of measure with the normalized
Radon–Nikodym weight `referenceWeight`, and ranking consequences of the
positive-part best-value formula. The covariate domain requires only a
measurable space.
-/

set_option autoImplicit false

universe u v

namespace AronowAudit.P006.Wave1.CorrectedRanking

open AronowAudit.P006 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section




/-! ## Mathematical statements -/

/-- **Statement S1.** Lifting indicator ignorability to the integrable
test `Y1` gives Eμ[T Y1|X]=π(X) μ1(X). For a `σ(X_i)`-set A, the finite
measures B ↦ ∫_A T·1_B(Y0,Y1) and B ↦ ∫_A π(X)·1_B(Y0,Y1) on ℝ×ℝ agree
on every measurable B by ignorability and the defining property of conditional
expectation. Integrating the second coordinate against the equal measures,
then using the conditional mean of Y1, gives the stated identity. -/
def S1 : Prop :=
  ∀ {Ω : Type v} {C : Type u} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n), Standing E → ∀ π, Admissible π → ∀ i,
      (E.law π)[fun ω => bit (E.T π i ω) * E.Y1 i ω | E.covariateSigma i]
        =ᵐ[E.law π] fun ω => π (E.X i ω) * E.μ1 (E.X i ω)


/-- **Statement S3.** Generic normalized change of measure. For n>0
and g=ρ/n, the Radon–Nikodym formula for an integrable Q-function f gives
n∫ f g dP=∫ fρ dP=∫ f dQ, with integrability of the weighted function. -/
def S3 : Prop :=
  ∀ {C : Type u} [MeasurableSpace C] (Q P : Measure C) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure P], Q ≪ P → ∀ n : ℕ, 0 < n → ∀ f : C → ℝ, Integrable f Q →
      Integrable (fun x => f x * referenceWeight n Q P x) P ∧
      (n : ℝ) * ∫ x, f x * referenceWeight n Q P x ∂P = ∫ x, f x ∂Q


/-- **Statement S6.** Ranking consequences of the best-value formula.
Pointwise dominance τj(x)≥τk(x) implies max(τj(x),0)≥max(τk(x),0);
integration against the same reference measure preserves this ordering.
If every effect is nonnegative, positivePart(τk)=τk and the best value is
the reference mean effect. The positive part of an integrable effect is
integrable. -/
def S6 : Prop :=
  ∀ {K : ℕ} {C : Type u} [MeasurableSpace C] (P0 : Measure C)
    (score : Fin K → (C → ℝ) → ℝ) (τ : Fin K → C → ℝ),
    (∀ k, Integrable (τ k) P0) →
    (∀ k, bestValue {π : C → ℝ | Admissible π} (score k) = ∫ x, positivePart (τ k x) ∂P0) →
    UniformRankPreservation (fun _ => {π : C → ℝ | Admissible π}) score τ ∧
    ((∀ k x, 0 ≤ τ k x) →
      (∀ k, bestValue {π : C → ℝ | Admissible π} (score k) = ∫ x, τ k x ∂P0) ∧
      RelativeRankPreservation P0 (fun _ => {π : C → ℝ | Admissible π}) score τ)

/-! ## Aliases for the three statements -/

def N1 : Prop := S1.{u, v}
def N3 : Prop := S3.{u}
def N6 : Prop := S6.{u}




end

end AronowAudit.P006.Wave1.CorrectedRanking
