import SAP.P039.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

/-- The conditional-null distribution of the six-observation residual-line statistic. -/
def GaussianWitnessStatement : Prop :=
  ∀ (σ : ℝ≥0), 0 < σ → ∀ γ : Fin 2 → ℝ,
    let μ := Measure.pi (fun _ : Fin 6 => gaussianReal 0 (σ^2))
    let stat := fun ε => olsT (residualLine witnessV)
      (olsResidual witnessZ (witnessZ *ᵥ γ + ε)) 1
    let U := fun ε => dotProduct witnessV ε / ((σ : ℝ)*Real.sqrt 2)
    let V := fun ε => olsSSE (fullDesign witnessZ witnessV) (witnessZ *ᵥ γ + ε) / (σ : ℝ)^2
    μ.map (fun ε => (U ε, V ε)) = (gaussianReal 0 1).prod (chiSquaredLaw 3) ∧
    (∀ ε, stat ε = U ε / Real.sqrt (V ε/4)) ∧
    μ.map stat = (studentLaw 3).map (fun t => Real.sqrt (4/3 : ℝ)*t) ∧
    (∫ ε, (stat ε)^2 ∂μ) = 4 ∧ (∫ t, t^2 ∂studentLaw 3) = 3 ∧
    (∫ t, t^2 ∂studentLaw 4) = 2 ∧
    μ.map stat ≠ studentLaw 4 ∧
    Integrable (fun ε => (stat ε)^2) μ ∧
    Integrable (fun t : ℝ => t^2) (studentLaw 3) ∧
    Integrable (fun t : ℝ => t^2) (studentLaw 4)

/-- Both exact least-squares counterexamples, their nominal tests, and the Gaussian-null discrepancy. -/
def T3Statement : Prop :=
  (witnessZᵀ * witnessZ = !![6, 0; 0, 2] ∧
    FullColumnRank witnessZ ∧
    olsResidual witnessZ witnessY = ![0, 0, (3/2 : ℝ), -3/2, 1, -1] ∧
    olsSSE witnessZ witnessY = (13/2 : ℝ) ∧
    (residualMaker witnessZ)ᵀ = residualMaker witnessZ ∧
    residualMaker witnessZ * residualMaker witnessZ = residualMaker witnessZ ∧
    (residualMaker witnessZ).rank = 4 ∧
    residualMaker witnessZ *ᵥ witnessY = olsResidual witnessZ witnessY) ∧
  (FullColumnRank (residualLine witnessV) ∧
    ols (residualLine witnessV) (olsResidual witnessZ witnessY) = ![(0/1 : ℝ), (3/2 : ℝ)] ∧
    olsResidual (residualLine witnessV) (olsResidual witnessZ witnessY) = ![(0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] ∧
    olsSSE (residualLine witnessV) (olsResidual witnessZ witnessY) = (2/1 : ℝ) ∧
    olsSESquared (residualLine witnessV) (olsResidual witnessZ witnessY) 1 = (1/4 : ℝ) ∧
    olsTSquared (residualLine witnessV) (olsResidual witnessZ witnessY) 1 = (9/1 : ℝ) ∧
    IsLeastSquares (residualLine witnessV) (olsResidual witnessZ witnessY) ![(0/1 : ℝ), (3/2 : ℝ)] ∧
    ∀ b, IsLeastSquares (residualLine witnessV) (olsResidual witnessZ witnessY) b → b=![(0/1 : ℝ), (3/2 : ℝ)]) ∧
  (FullColumnRank (fullDesign witnessZ witnessV) ∧
    ols (fullDesign witnessZ witnessV) witnessY = ![(0/1 : ℝ), (1/1 : ℝ), (3/2 : ℝ)] ∧
    olsResidual (fullDesign witnessZ witnessV) witnessY = ![(0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] ∧
    olsSSE (fullDesign witnessZ witnessV) witnessY = (2/1 : ℝ) ∧
    olsSESquared (fullDesign witnessZ witnessV) witnessY 2 = (1/3 : ℝ) ∧
    olsTSquared (fullDesign witnessZ witnessV) witnessY 2 = (27/4 : ℝ) ∧
    IsLeastSquares (fullDesign witnessZ witnessV) witnessY ![(0/1 : ℝ), (1/1 : ℝ), (3/2 : ℝ)] ∧
    ∀ b, IsLeastSquares (fullDesign witnessZ witnessV) witnessY b → b=![(0/1 : ℝ), (1/1 : ℝ), (3/2 : ℝ)]) ∧
  (FullColumnRank (residualLine (witnessU+witnessV)) ∧
    ols (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) = ![(0/1 : ℝ), (3/4 : ℝ)] ∧
    olsResidual (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) = ![(-3/4 : ℝ), (3/4 : ℝ), (3/4 : ℝ), (-3/4 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] ∧
    olsSSE (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) = (17/4 : ℝ) ∧
    olsSESquared (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) 1 = (17/64 : ℝ) ∧
    olsTSquared (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) 1 = (36/17 : ℝ) ∧
    IsLeastSquares (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) ![(0/1 : ℝ), (3/4 : ℝ)] ∧
    ∀ b, IsLeastSquares (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) b → b=![(0/1 : ℝ), (3/4 : ℝ)]) ∧
  (FullColumnRank (fullDesign witnessZ (witnessU+witnessV)) ∧
    ols (fullDesign witnessZ (witnessU+witnessV)) witnessY = ![(0/1 : ℝ), (-1/2 : ℝ), (3/2 : ℝ)] ∧
    olsResidual (fullDesign witnessZ (witnessU+witnessV)) witnessY = ![(0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] ∧
    olsSSE (fullDesign witnessZ (witnessU+witnessV)) witnessY = (2/1 : ℝ) ∧
    olsSESquared (fullDesign witnessZ (witnessU+witnessV)) witnessY 2 = (1/3 : ℝ) ∧
    olsTSquared (fullDesign witnessZ (witnessU+witnessV)) witnessY 2 = (27/4 : ℝ) ∧
    IsLeastSquares (fullDesign witnessZ (witnessU+witnessV)) witnessY ![(0/1 : ℝ), (-1/2 : ℝ), (3/2 : ℝ)] ∧
    ∀ b, IsLeastSquares (fullDesign witnessZ (witnessU+witnessV)) witnessY b → b=![(0/1 : ℝ), (-1/2 : ℝ), (3/2 : ℝ)]) ∧
  (dotProduct (witnessU+witnessV) (residualMaker witnessZ *ᵥ (witnessU+witnessV)) = 2 ∧
    squaredLength (witnessU+witnessV) = 4 ∧ (3/4 : ℝ) = (3/2 : ℝ)*2/4) ∧
  (FullColumnRank witnessZ ∧ FullColumnRank (residualLine witnessV) ∧
    FullColumnRank (fullDesign witnessZ witnessV) ∧
    olsT (residualLine witnessV) (olsResidual witnessZ witnessY) 1 = 3 ∧
    olsT (fullDesign witnessZ witnessV) witnessY 2 = 3*Real.sqrt 3/2 ∧
    studentFourTail (olsT (residualLine witnessV) (olsResidual witnessZ witnessY) 1) < (1/20 : ℝ) ∧
    (1/20 : ℝ) < studentThreeTail (olsT (fullDesign witnessZ witnessV) witnessY 2)) ∧
  (studentFourTail 3 = 1 - 45 / (13 * Real.sqrt 13) ∧
    studentFourTail 3 < (1/20 : ℝ) ∧
    studentThreeTail (3 * Real.sqrt 3 / 2) =
      1/2 - 2/Real.pi * (Real.arctan (1/5) + 6/13) ∧
    (1/20 : ℝ) < studentThreeTail (3 * Real.sqrt 3 / 2)) ∧
  (FullColumnRank witnessZ ∧ FullColumnRank (residualLine witnessV) ∧
    FullColumnRank (fullDesign witnessZ witnessV) ∧
    FullColumnRank (residualLine (witnessU+witnessV)) ∧
    FullColumnRank (fullDesign witnessZ (witnessU+witnessV)) ∧
    olsTSquared (residualLine witnessV) (olsResidual witnessZ witnessY) 1 = 9 ∧
    olsTSquared (fullDesign witnessZ witnessV) witnessY 2 = (27/4 : ℝ) ∧
    olsTSquared (residualLine witnessV) (olsResidual witnessZ witnessY) 1 ≠
      olsTSquared (fullDesign witnessZ witnessV) witnessY 2 ∧
    ols (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) 1 = (3/4 : ℝ) ∧
    ols (fullDesign witnessZ (witnessU+witnessV)) witnessY 2 = (3/2 : ℝ) ∧
    ols (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) 1 ≠
      ols (fullDesign witnessZ (witnessU+witnessV)) witnessY 2) ∧
  GaussianWitnessStatement

/-- Complete linear-OLS conclusions (a)--(e), with all t statistics guarded by positive full-model SSE. -/
def LinearResidualConclusion {n k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (x y : Fin n → ℝ) : Prop :=
    let P := controlProjection Z
    let M := residualMaker Z
    let r := M *ᵥ y
    let xbar := (∑ i, x i) / n
    let xc := x - xbar • (fun _ => (1 : ℝ))
    let sm := dotProduct x (M *ᵥ x)
    let sc := squaredLength xc
    let c := dotProduct x r
    let a := c/sc
    let b := c/sm
    let sr := squaredLength r - c^2/sc
    let sf := squaredLength r - c^2/sm
    Pᵀ = P ∧ P*P = P ∧ Mᵀ = M ∧ M*M = M ∧ M*Z = 0 ∧
    (∑ i, r i) = 0 ∧ M *ᵥ xc = M *ᵥ x ∧
    dotProduct xc r = c ∧ c = dotProduct x (M *ᵥ y) ∧
    sc = sm + squaredLength (P *ᵥ xc) ∧ 0 < sm ∧ sm ≤ sc ∧
    (sm = sc ↔ P *ᵥ xc = 0) ∧
    (P *ᵥ xc = 0 ↔ ∀ j, dotProduct xc (fun i => Z i j) = 0) ∧
    ols (residualLine x) r = ![-a*xbar, a] ∧
    IsLeastSquares (residualLine x) r ![-a*xbar, a] ∧
    olsSSE (residualLine x) r = sr ∧
    (∃! β, IsLeastSquares (fullDesign Z x) y β) ∧
    ols (fullDesign Z x) y (Fin.last k) = b ∧
    olsSSE (fullDesign Z x) y = sf ∧
    a = b*sm/sc ∧ (0<a ↔ 0<b) ∧ (a<0 ↔ b<0) ∧ |a| ≤ |b| ∧
    (a=b ↔ b=0 ∨ P *ᵥ xc = 0) ∧ sf ≤ sr ∧
    olsSESquared (residualLine x) r 1 = sr / (((n : ℝ)-2)*sc) ∧
    olsSESquared (fullDesign Z x) y (Fin.last k) = sf / (((n : ℝ)-k-1)*sm) ∧
    (0 < sf →
      olsTSquared (residualLine x) r 1 = ((n : ℝ)-2)*c^2/(sc*squaredLength r-c^2) ∧
      olsTSquared (fullDesign Z x) y (Fin.last k) =
        ((n : ℝ)-k-1)*c^2/(sm*squaredLength r-c^2) ∧
      olsTSquared (residualLine x) r 1 / ((n : ℝ)-2) ≤
        olsTSquared (fullDesign Z x) y (Fin.last k) / ((n : ℝ)-k-1) ∧
      (P *ᵥ xc = 0 → a=b ∧
        olsResidual (residualLine x) r = olsResidual (fullDesign Z x) y ∧
        olsT (residualLine x) r 1 =
          Real.sqrt (((n : ℝ)-2)/((n : ℝ)-k-1)) * olsT (fullDesign Z x) y (Fin.last k) ∧
        (2 ≤ k → olsT (fullDesign Z x) y (Fin.last k) ≠ 0 →
          |olsT (fullDesign Z x) y (Fin.last k)| < |olsT (residualLine x) r 1|)))

/-- Positive-noise covariance identities, with explicit finite first and second moments. -/
def ResidualCovarianceStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ)
    (γ : Fin k → ℝ) (ε : Ω → Fin n → ℝ) (σ : ℝ),
    0 < σ → FullColumnRank Z → (∃ c, Z *ᵥ c = fun _ => 1) →
    (¬ ∃ c, Z *ᵥ c = x) → k+1 < n →
    (∀ i, Integrable (fun ω => ε ω i) μ) →
    (∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) →
    (∀ i, (∫ ω, ε ω i ∂μ) = 0) →
    vectorCovariance μ ε = σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ) →
    let M := residualMaker Z
    let r := fun ω => M *ᵥ (Z *ᵥ γ + ε ω)
    (∀ ω, r ω = M *ᵥ ε ω) ∧
    vectorCovariance μ r = σ^2 • M ∧ M.rank = n-k ∧
    (vectorCovariance μ r).rank = n-k ∧
    vectorCovariance μ r ≠ σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Linear regression algebra and the finite-moment, positive-noise covariance clause. -/
def T4Statement : Prop :=
  (∀ {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (x y : Fin n → ℝ),
    FullColumnRank Z → (∃ c, Z *ᵥ c = fun _ => 1) →
    (¬ ∃ c, Z *ᵥ c = x) → k+1 < n → LinearResidualConclusion Z x y) ∧
  ResidualCovarianceStatement

end SAP.P039
