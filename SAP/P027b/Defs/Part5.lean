import SAP.P027b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- The finite-population and samplewise clauses of the corrected comparison. -/
def StrataFixed (M : ℕ) (hM : 2 ≤ M) (y : (Fin M × Fin 2) → ℝ) : Prop :=
  let D := strataDesign M (by omega)
  let N : ℝ := 2*M
  (∀ ω, htMean D y ω = (y (ω.1,0)+y (ω.2,1))/2 ∧
    htVarianceEstimator D y ω/N^2 = ((M:ℝ)-1)/(4*M)*(y (ω.1,0)^2+y (ω.2,1)^2) ∧
    c2Estimator D y ω/N^2 = ((M:ℝ)-1)/(2*M)*(y (ω.1,0)^2+y (ω.2,1)^2) ∧
    c2Estimator D y ω/N^2 = 2*(htVarianceEstimator D y ω/N^2) ∧
    collapsedEstimator y ω = (y (ω.1,0)-y (ω.2,1))^2/4) ∧
  variance D (htMean D y) = (stratumVariance y 0+stratumVariance y 1)/4

/-- The outcome-model comparison uses actual integrals over generated populations. -/
def StrataModel {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (M : ℕ) (hM : 2 ≤ M) (α : ℝ) (ε : (Fin M × Fin 2) → Ξ → ℝ) : Prop :=
  let D := strataDesign M (by omega)
  let y := stratumOutcomes α ε
  let N : ℝ := 2*M
  let V := outcomeE μ (fun ξ => variance D (htMean D (y ξ)))
  let H := outcomeE μ (fun ξ => expect D (fun ω => htVarianceEstimator D (y ξ) ω/N^2))
  let C := outcomeE μ (fun ξ => expect D (fun ω => c2Estimator D (y ξ) ω/N^2))
  let CS := outcomeE μ (fun ξ => expect D (collapsedEstimator (y ξ)))
  let BH := H-V
  let BC := C-V
  let BS := CS-V
  V = ((M:ℝ)-1)/(2*M) ∧ H = ((M:ℝ)-1)/(2*M)*(1+α^2) ∧
  C = ((M:ℝ)-1)/M*(1+α^2) ∧ CS = α^2+1/2 ∧
  BH = ((M:ℝ)-1)/(2*M)*α^2 ∧ BC = strataC2BiasFormula M α ∧
  BS = strataCSBiasFormula M α ∧ 0 ≤ BH ∧ 0 ≤ BC ∧ 0 ≤ BS ∧
  BC-BS = ((M:ℝ)-2-2*α^2)/(2*M) ∧ BC-BS = 1/2-(1+α^2)/M ∧
  (BC < BS ↔ (M:ℝ) < 2*(1+α^2)) ∧
  (BC = BS ↔ (M:ℝ) = 2*(1+α^2)) ∧
  (BS < BC ↔ 2*(1+α^2) < (M:ℝ)) ∧
  (BC < BS ↔ ((M:ℝ)-2)/((M:ℝ)-1) < heterogeneity α) ∧
  C/CS = (1-1/(M:ℝ))*((1+α^2)/(1/2+α^2)) ∧
  C/CS = (1-1/(M:ℝ))*(2-heterogeneity α) ∧ C-CS = 1/2-(1+α^2)/M

/-- All five mathematical clauses of the parameter-qualified bias comparison. -/
def T15Statement : Prop :=
  (∀ (M : ℕ) (hM : 2 ≤ M) (y : (Fin M × Fin 2) → ℝ), StrataFixed M hM y) ∧
  (∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (M : ℕ) (hM : 2 ≤ M) (α : ℝ) (ε : (Fin M × Fin 2) → Ξ → ℝ),
    NoiseMoments μ ε 1 → StrataModel μ M hM α ε) ∧
  (∀ α : ℝ,
    Tendsto (fun M : ℕ => (1-1/(M:ℝ))*(2-heterogeneity α)) atTop
      (𝓝 (2-heterogeneity α)) ∧
    Tendsto (fun M : ℕ => (1/2:ℝ)-(1+α^2)/(M:ℝ)) atTop (𝓝 (1/2)) ∧
    Tendsto (fun M : ℕ => ((M:ℝ)-1)/(2*M)) atTop (𝓝 (1/2)))

end
end SAP.P027b
