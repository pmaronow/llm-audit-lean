import Mathlib
import SAP.P001g.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- The empirical joint law of a finite observed outcome/treatment sample.
It is used only at positive sample sizes. -/
def wholeEmpiricalPairs {n : ℕ} (y d : Fin n → ℝ) : Measure (ℝ × ℝ) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (y i, d i)

/-- The identified ATE functional on an observed outcome/treatment law.
Both arm probabilities must be positive when this functional is used. -/
def wholeATEFunctional (Q : Measure (ℝ × ℝ)) : ℝ :=
  conditionalMeanAt Q Prod.snd Prod.fst 1 - conditionalMeanAt Q Prod.snd Prod.fst 0

/-- P001-T115. Location: Definition 7.1.9, p. 244 (PDF p. 262);
Theorem 7.1.10, p. 245 (PDF p. 263); decomposition, p. 247 (PDF p. 265).
The usual measure-theoretic conditions are assumed. Random assignment identifies the population ATE. For arbitrary assignment the
observed arm difference equals the potential-outcome arm difference, then the
sum-of-effect-and-control arm difference, then ATT plus selection bias.
The plug-in estimates of the two identified potential-outcome means under the
empirical observed law are the two displayed arm averages, and their difference
is the difference-in-means estimator, whenever both sample arm counts are positive. -/
def T115WholeStatement : Prop :=
  (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : Ω → ℝ), Measurable Y0 → Measurable Y1 → Measurable D →
    Integrable Y0 μ → Integrable Y1 μ →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    (0 < prob μ {ω | D ω = 1} ∧ 0 < prob μ {ω | D ω = 0}) →
    let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
    let τ := fun ω => Y1 ω - Y0 ω
    let arm := fun Z d => conditionalMeanAt μ D Z d
    (IndepFun (fun ω => (Y0 ω, Y1 ω)) D μ →
      mean μ τ = arm Y 1 - arm Y 0) ∧
    arm Y 1 - arm Y 0 = arm Y1 1 - arm Y0 0 ∧
    arm Y1 1 - arm Y0 0 = arm (fun ω => τ ω + Y0 ω) 1 - arm Y0 0 ∧
    arm (fun ω => τ ω + Y0 ω) 1 - arm Y0 0 =
      arm τ 1 + arm Y0 1 - arm Y0 0) ∧
  (∀ {n : ℕ} (_hn : 0 < n) (y d : Fin n → ℝ),
    (∀ i, d i = 0 ∨ d i = 1) →
    0 < ∑ i, d i → 0 < ∑ i, (1 - d i) →
    IsProbabilityMeasure (wholeEmpiricalPairs y d) ∧
    conditionalMeanAt (wholeEmpiricalPairs y d) Prod.snd Prod.fst 1 =
      (∑ i, y i * d i) / (∑ i, d i) ∧
    conditionalMeanAt (wholeEmpiricalPairs y d) Prod.snd Prod.fst 0 =
      (∑ i, y i * (1 - d i)) / (∑ i, (1 - d i)) ∧
    wholeATEFunctional (wholeEmpiricalPairs y d) =
      (∑ i, y i * d i) / (∑ i, d i) -
        (∑ i, y i * (1 - d i)) / (∑ i, (1 - d i)))

/-- The augmented causal score, with finite real nuisance values.
Its expectation is used only with an explicit integrability guard. -/
def wholeAugmentedScore (y d m0 m1 q : ℝ) : ℝ :=
  m1 + d * (y - m1) / q - m0 - (1 - d) * (y - m0) / (1 - q)

/-- The inverse-propensity score. Its population expectation is certified
integrable in the whole statement. -/
def wholeIPWScore (y d p : ℝ) : ℝ := y * d / p - y * (1 - d) / (1 - p)

/-- P001-T117. Location: Theorem 7.2.5, pp. 265–266 (PDF pp. 283–284);
Theorem 7.2.8, pp. 267–269 (PDF pp. 285–287).
The usual measure-theoretic conditions are assumed. Strong ignorability gives
the population IPW identity. The augmented ATE identity holds if either both
outcome regressions are correct and the approximating propensity has overlap,
or the propensity is correct. Only the complete augmented score is required
to be integrable; separate integrability of the nuisance regressions is not
assumed in the correct-propensity alternative. -/
def T117WholeStatement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y0 Y1 D : Ω → ℝ),
    Measurable Y0 → Measurable Y1 → Measurable D → Integrable Y0 μ → Integrable Y1 μ →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    0 < prob μ {ω | D ω = 0} → 0 < prob μ {ω | D ω = 1} →
    ∀ p : (Fin K → ℝ) → ℝ, IsCEF μ X D p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) ∧ p (X ω) < 1 - ε) →
    CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D →
    let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
    Integrable (fun ω => wholeIPWScore (Y ω) (D ω) (p (X ω))) μ ∧
    mean μ (fun ω => Y1 ω - Y0 ω) =
      mean μ (fun ω => wholeIPWScore (Y ω) (D ω) (p (X ω))) ∧
    ∀ m0 m1 q : (Fin K → ℝ) → ℝ,
      Measurable m0 → Measurable m1 → Measurable q →
      Integrable (fun ω => wholeAugmentedScore (Y ω) (D ω) (m0 (X ω)) (m1 (X ω)) (q (X ω))) μ →
      ((IsCEF (μ.restrict {ω | D ω = 0}) X Y m0 ∧
        IsCEF (μ.restrict {ω | D ω = 1}) X Y m1 ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < q (X ω) ∧ q (X ω) < 1 - η) ∨
        q ∘ X =ᵐ[μ] p ∘ X) →
      mean μ (fun ω => Y1 ω - Y0 ω) =
        mean μ (fun ω => wholeAugmentedScore (Y ω) (D ω) (m0 (X ω)) (m1 (X ω)) (q (X ω)))

/-- An auxiliary stronger reading that adds strict endpoint ordering at every
positive sample size as a conclusion alongside asymptotic coverage.
This is not the canonical asymptotic coverage assertion. -/
def wholeNormalIntervalAssertion : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ), IID μ Z →
    ∀ (that vhat : ℕ → Ω → ℝ),
    (∀ n : ℕ, 0 < n → ∃ h : (Fin n → ℝ) → ℝ × ℝ,
      Measurable h ∧ ∀ ω, (that n ω, vhat n ω) = h (firstSample Z n ω)) →
    (∀ n, Measurable (that n)) → (∀ n, Measurable (vhat n)) →
    (∀ n ω, 0 ≤ vhat n ω) →
    ∀ (θ φ α z : ℝ), 0 < φ → α ∈ Set.Ioo (0 : ℝ) 1 →
    prob (gaussianReal 0 1) (Set.Iic z) = 1 - α / 2 →
    CD μ (fun n ω => Real.sqrt n * (that n ω - θ))
      (gaussianReal 0 ⟨φ ^ 2, sq_nonneg _⟩) →
    VarianceConsistent μ vhat (φ ^ 2) →
    (∀ n : ℕ, 0 < n → prob μ {ω |
      that n ω - z * Real.sqrt (vhat n ω) <
        that n ω + z * Real.sqrt (vhat n ω)} = 1) ∧
    (∃ c : ℝ, 1 - α ≤ c ∧ Tendsto (fun n : ℕ => prob μ {ω | θ ∈ Set.Ioo
      (that n ω - z * Real.sqrt (vhat n ω))
      (that n ω + z * Real.sqrt (vhat n ω))}) atTop (nhds c))

/-- Auxiliary negation of the reading that additionally concludes strict
endpoint order at every positive sample size. A zero variance estimate at n=1
can defeat that extra clause while preserving the canonical coverage limit.
The historical name is retained for the existing proof; this definition is
not used as the statement of Challenge T128. -/
def T128WholeStatement : Prop := ¬ wholeNormalIntervalAssertion

end
end SAP.P001g
