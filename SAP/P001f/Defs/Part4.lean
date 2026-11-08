import SAP.P001f.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
universe u v

def T106Statement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
    (∀ X Y : Ω → ℝ, Integrable X μ → Integrable Y μ → ∀ a b c : ℝ,
      (∫ ω, a * X ω + b * Y ω + c ∂μ) =
        a * (∫ ω, X ω ∂μ) + b * (∫ ω, Y ω ∂μ) + c) ∧
    (∀ X : Ω → ℝ, MemLp X 2 μ → ∀ a c : ℝ,
      variance X μ = (∫ ω, (X ω) ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2 ∧
      variance (fun ω => X ω + c) μ = variance X μ ∧
      variance (fun ω => a * X ω) μ = a ^ 2 * variance X μ ∧
      Real.sqrt (variance (fun ω => X ω + c) μ) = Real.sqrt (variance X μ) ∧
      Real.sqrt (variance (fun ω => a * X ω) μ) = |a| * Real.sqrt (variance X μ) ∧
      (0 < variance X μ → ∀ ε : ℝ, 0 < ε →
        (μ {ω | ε * Real.sqrt (variance X μ) ≤ |X ω - ∫ z, X z ∂μ|}).toReal ≤ 1 / ε ^ 2))

def T107Statement : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (Y : Ω → ℝ),
    Integrable Y μ → ∀ m : E → ℝ, ConditionalMean μ X Y m →
      (∫ ω, Y ω ∂μ) = ∫ ω, m (X ω) ∂μ

def T108Statement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), IndependentCopies μ X → Integrable (X 0) μ →
    ∀ n : ℕ, 0 < n →
    (∫ ω, sampleAverage X n ω ∂μ) = (∫ ω, X 0 ω ∂μ) ∧
    (MemLp (X 0) 2 μ →
      variance (sampleAverage X n) μ = variance (X 0) μ / (n : ℝ) ∧
      (0 < variance (X 0) μ → ∀ ε : ℝ, 0 < ε →
        (μ {ω | ε ≤ |sampleAverage X n ω - ∫ z, X 0 z ∂μ|}).toReal ≤
          variance (X 0) μ / (ε ^ 2 * (n : ℝ))))

/-- Population polynomials minimize prediction MSE at every degree and their
    distance from the continuous CEF eventually falls below every positive tolerance. -/
def PolynomialCEFApproximation : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → MemLp Y 2 μ → ∀ a b : ℝ,
    (∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) →
    ((∃ f : ℝ → ℝ, RealDensity (μ.map X) f ∧ {x | 0 < f x} = Set.Icc a b) ∨
      (Set.Countable (Set.range X) ∧
        ∀ x : ℝ, 0 < (μ {ω | X ω = x}).toReal ↔ x ∈ Set.Icc a b)) →
    ∀ m : ℝ → ℝ, ConditionalMean μ X Y m → ContinuousOn m (Set.Icc a b) →
    (∃ p : ℕ → Polynomial ℝ, (∀ J, (p J).natDegree ≤ J) ∧
      (∀ (J : ℕ) (q : Polynomial ℝ), q.natDegree ≤ J →
        (∫ ω, (Y ω - (p J).eval (X ω)) ^ 2 ∂μ) ≤
          (∫ ω, (Y ω - q.eval (X ω)) ^ 2 ∂μ))) ∧
    (∀ p : ℕ → Polynomial ℝ, (∀ J, (p J).natDegree ≤ J) →
      (∀ (J : ℕ) (q : Polynomial ℝ), q.natDegree ≤ J →
        (∫ ω, (Y ω - (p J).eval (X ω)) ^ 2 ∂μ) ≤
          (∫ ω, (Y ω - q.eval (X ω)) ^ 2 ∂μ)) →
      ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ J', J ≤ J' →
        (∫ ω, (m (X ω) - (p J').eval (X ω)) ^ 2 ∂μ) < ε)

def T109Statement : Prop :=
  (∀ a b : ℝ, a ≤ b → ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) →
    ∀ ε : ℝ, 0 < ε → ∃ p : Polynomial ℝ,
      ∀ x ∈ Set.Icc a b, |f x - p.eval x| < ε) ∧
  PolynomialCEFApproximation.{u}

def T110Statement : Prop :=
  (∀ {n : ℕ}, 0 < n → ∀ Y : Fin n → Bool,
    let k := (Finset.univ.filter (fun i => Y i = true)).card
    let a := (k : ℝ) / (n : ℝ)
    a ∈ Set.Icc (0 : ℝ) 1 ∧
    a = (∑ i, if Y i then (1 : ℝ) else 0) / (n : ℝ) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (1 - t) ^ (n - k) * t ^ k ≤ (1 - a) ^ (n - k) * a ^ k ∧
      ((1 - t) ^ (n - k) * t ^ k = (1 - a) ^ (n - k) * a ^ k ↔ t = a)) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) 1,
    (1 - t) * t ^ 2 ≤ (1 - (2 / 3 : ℝ)) * (2 / 3) ^ 2 ∧
    ((1 - t) * t ^ 2 = (1 - (2 / 3 : ℝ)) * (2 / 3) ^ 2 ↔ t = 2 / 3))

end
end SAP.P001f
