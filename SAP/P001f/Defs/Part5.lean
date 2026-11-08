import SAP.P001f.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
universe u v

def MCARMean : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y R : Ω → ℝ), Measurable Y → Measurable R → Integrable Y μ →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < (μ {ω | R ω = 0}).toReal → 0 < (μ {ω | R ω = 1}).toReal → IndepFun Y R μ →
    (∫ ω, Y ω ∂μ) = eventMean μ R (fun ω => censoredOutcome (Y ω) (R ω)) 1

def DiscreteMARMean : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y R : Ω → ℝ), Measurable Y → Measurable R →
    Integrable Y μ → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < (μ {ω | R ω = 0}).toReal → 0 < (μ {ω | R ω = 1}).toReal →
    ∀ p : E → ℝ, ConditionalMean μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    ConditionallyIndependent μ X hX Y R → ∀ m : E → ℝ,
    ConditionalMean (μ.restrict {ω | R ω = 1}) X
      (fun ω => censoredOutcome (Y ω) (R ω)) m →
    Integrable (m ∘ X) μ →
    ConditionalMean μ X Y m ∧
      Summable (fun x : E => m x * (μ {ω | X ω = x}).toReal) ∧
      (∫ ω, Y ω ∂μ) = ∑' x : E, m x * (μ {ω | X ω = x}).toReal

def VectorMARMean : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ),
    Measurable Y → Measurable R → Integrable Y μ →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < (μ {ω | R ω = 0}).toReal → 0 < (μ {ω | R ω = 1}).toReal →
    ∀ p m : (Fin K → ℝ) → ℝ, ConditionalMean μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    ConditionallyIndependent μ X hX Y R →
    ConditionalMean (μ.restrict {ω | R ω = 1}) X
      (fun ω => censoredOutcome (Y ω) (R ω)) m →
    Integrable (m ∘ X) μ →
    ConditionalMean μ X Y m ∧ (∫ ω, Y ω ∂μ) = ∫ ω, m (X ω) ∂μ

def T111Statement : Prop :=
  MCARMean.{u} ∧ DiscreteMARMean.{u, v} ∧ VectorMARMean.{u} ∧
  (respondentAverage exampleCensored exampleIndicator = 3 / 4 ∧
    poststratifiedAverage exampleCensored exampleIndicator exampleCovariate = 7 / 9)

def T112Statement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ),
    Measurable Y → Measurable R → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < (μ {ω | R ω = 0}).toReal → 0 < (μ {ω | R ω = 1}).toReal →
    ∀ (p : (Fin K → ℝ) → ℝ) (hp : ConditionalMean μ X R p),
    ConditionallyIndependent μ X hX Y R →
    ∀ ε : ℝ, 0 < ε → (∀ᵐ ω ∂μ, ε < p (X ω)) →
    ConditionallyIndependent μ (p ∘ X) (hp.1.comp hX) R X ∧
    ConditionallyIndependent μ (p ∘ X) (hp.1.comp hX) Y R ∧
    ConditionalMean μ (p ∘ X) R id ∧
    ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < id (p (X ω))

def T113Statement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ),
    Measurable Y → Measurable R → Integrable Y μ →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < (μ {ω | R ω = 0}).toReal → 0 < (μ {ω | R ω = 1}).toReal →
    ∀ p : (Fin K → ℝ) → ℝ, ConditionalMean μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    ConditionallyIndependent μ X hX Y R →
    ∀ m q : (Fin K → ℝ) → ℝ,
    Measurable m → Measurable q → Integrable (m ∘ X) μ →
    ((ConditionalMean (μ.restrict {ω | R ω = 1}) X
        (fun ω => censoredOutcome (Y ω) (R ω)) m ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < q (X ω) ∧ q (X ω) < 1 - η) ∨
      q ∘ X =ᵐ[μ] p ∘ X) →
    (∫ ω, Y ω ∂μ) =
      ∫ ω, m (X ω) + R ω * (censoredOutcome (Y ω) (R ω) - m (X ω)) / q (X ω) ∂μ

def SharpATEBounds : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : Ω → ℝ), Measurable Y0 → Measurable Y1 → Measurable D → ∀ a b : ℝ,
    (∀ᵐ ω ∂μ, Y0 ω ∈ Set.Icc a b ∧ Y1 ω ∈ Set.Icc a b) →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    0 < (μ {ω | D ω = 0}).toReal → 0 < (μ {ω | D ω = 1}).toReal →
    let Y := fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)
    let L := eventMean μ D Y 1 * (μ {ω | D ω = 1}).toReal + a * (μ {ω | D ω = 0}).toReal -
      (eventMean μ D Y 0 * (μ {ω | D ω = 0}).toReal + b * (μ {ω | D ω = 1}).toReal)
    let U := eventMean μ D Y 1 * (μ {ω | D ω = 1}).toReal + b * (μ {ω | D ω = 0}).toReal -
      (eventMean μ D Y 0 * (μ {ω | D ω = 0}).toReal + a * (μ {ω | D ω = 1}).toReal)
    (∫ ω, Y1 ω - Y0 ω ∂μ) ∈ Set.Icc L U ∧ U - L = b - a ∧
    ∀ c ∈ Set.Icc L U, ∃ Z0 Z1 : Ω → ℝ,
      Measurable Z0 ∧ Measurable Z1 ∧
      (∀ᵐ ω ∂μ, Z0 ω ∈ Set.Icc a b ∧ Z1 ω ∈ Set.Icc a b) ∧
      μ.map (fun ω => (realizedOutcome (Z0 ω) (Z1 ω) (D ω), D ω)) =
        μ.map (fun ω => (Y ω, D ω)) ∧
      (∫ ω, Z1 ω - Z0 ω ∂μ) = c

def T114Statement : Prop :=
  SharpATEBounds.{u} ∧
  ((∑ i : Fin 6, lowerATE (exampleOutcome i) (exampleIndicator i) 0 1) / 6 = -2 / 6 ∧
    (∑ i : Fin 6, upperATE (exampleOutcome i) (exampleIndicator i) 0 1) / 6 = 4 / 6)

end
end SAP.P001f
