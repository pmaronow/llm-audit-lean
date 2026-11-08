import SAP.P001g.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

/-- Exact minimization of squared sample residuals over polynomials of degree
at most J n. This imposes no measurability condition on the selected fit. -/
def polynomialSieveLeastSquares {Ω : Type*} (X Y : ℕ → Ω → ℝ) (J : ℕ → ℕ)
    (fit : ℕ → Ω → Polynomial ℝ) : Prop :=
  ∀ n ω, (fit n ω).natDegree ≤ J n ∧ ∀ p : Polynomial ℝ, p.natDegree ≤ J n →
    (∑ i ∈ Finset.range n, (Y i ω - (fit n ω).eval (X i ω)) ^ 2) ≤
      ∑ i ∈ Finset.range n, (Y i ω - p.eval (X i ω)) ^ 2

/-- Negation of the specified integrated squared-risk assertion on the finite
population-MSE domain. Square integrability of the outcome guards the BLP
criterion. The sample-space universe, literal ContDiff premise and absence of
fit measurability are retained; CP uses outer measure values on risk events
that are not assumed measurable. -/
def T119Statement : Prop :=
  ¬ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ℕ → Ω → ℝ), IID μ (fun i ω => (X i ω, Y i ω)) → Integrable (Y 0) μ →
    MemLp (Y 0) 2 μ →
    ∀ (a b : ℝ), a < b → ∀ (f : ℝ → ℝ), HasPDF (μ.map (X 0)) f →
    (∀ x, 0 < f x ↔ x ∈ Set.Icc a b) → ∀ (m : ℝ → ℝ), ContDiff ℝ ⊤ m →
    IsCEF μ (X 0) (Y 0) m → ∀ (J : ℕ → ℕ), Tendsto J atTop atTop →
    Tendsto (fun (n : ℕ) => (J n : ℝ) / (n : ℝ)) atTop (nhds 0) →
    ∀ (fit : ℕ → Ω → Polynomial ℝ), polynomialSieveLeastSquares X Y J fit →
    CP μ (fun n ω => ∫ x, ((fit n ω).eval x - m x) ^ 2 ∂(μ.map (X 0))) 0

end SAP.P001g
