import SAP.P004c.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
namespace SAP.P004c
open scoped BigOperators Matrix Classical
open MeasureTheory Filter
noncomputable section

/-- Corrected T31 assertions, with unconditional counts and nonempty-arm OLS and matrices. -/
def T31Statement : Prop :=
  (∀ (N : ℕ) (X : Type u) (Y : X → Assignment N → ℝ),
    SharpNull Y ↔ ∀ x z, Y x z = Y x (fun _ => false)) ∧
  ∀ (N : ℕ) (R : CircleTable N) (z : Assignment N),
    armCount z true = (∑ i, bit (z i)) ∧
    armCount z false = N - armCount z true ∧
    armCount z false = (∑ i, (1 - bit (z i))) ∧
    (0 < armCount z true → 0 < armCount z false →
    (∀ μ τ : ℝ,
      (∑ i, (R i z-armMean R z false-hajek R z*bit (z i))^2) ≤
        (∑ i, (R i z-μ-τ*bit (z i))^2) ∧
      ((∑ i, (R i z-μ-τ*bit (z i))^2) =
        (∑ i, (R i z-armMean R z false-hajek R z*bit (z i))^2) →
          μ = armMean R z false ∧ τ = hajek R z)) ∧
    (∀ e : Fin N → ℝ,
      (∀ K : Matrix (Fin N) (Fin N) ℝ,
        sandwich z e K =
          ((designMatrix z).transpose * designMatrix z)⁻¹ *
            Matrix.of (fun a b => ∑ i, ∑ j,
              designMatrix z i a * designMatrix z j b * e i * e j * K i j) *
          ((designMatrix z).transpose * designMatrix z)⁻¹) ∧
      ∀ (values : Fin N → ℝ) (vectors : Matrix (Fin N) (Fin N) ℝ),
        vectors.transpose * vectors = 1 →
        let K := spectralKernel values vectors false
        let Q := spectralKernel values vectors true
        Q-K = spectralKernel (fun k => -values k) vectors true ∧
        Q.PosSemidef ∧ (Q-K).PosSemidef ∧
        (Matrix.of (fun i j => e i*e j*Q i j)).PosSemidef ∧
        (Matrix.of (fun i j => e i*e j*(Q-K) i j)).PosSemidef ∧
        (sandwich z e Q).PosSemidef ∧ (sandwich z e Q-sandwich z e K).PosSemidef ∧
        max ((sandwich z e K) 1 1) 0 ≤ (sandwich z e Q) 1 1))

/-- The HT upper bound obtained by dropping the negative diagonal square term. -/
def htVarianceUpper {N : ℕ} (p : ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) : ℝ :=
  ((∑ i, (marginal (fun _ => p) (fun i z => (R i z)^2) i true/p +
    marginal (fun _ => p) (fun i z => (R i z)^2) i false/(1-p))) +
    ∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
      armSign a * armSign b *
        (pairMarginal (fun _ => p) (fun z => R i z*R j z) i j a b -
          marginal (fun _ => p) R i a*marginal (fun _ => p) R j b)) / (N : ℝ)^2

/-- Exact finite expansion, corrected component bounds and their rates. -/
def T32Statement : Prop :=
  (∀ (N : ℕ) (p : ℝ) (R : CircleTable N) (B : Fin N → Finset (Fin N)),
    0 < N → (0 < p ∧ p < 1) →
    (∀ i, i ∈ B i) → (∀ i j, j ∉ B i → ¬ sharesSource R i j) →
    variance (fun _ => p) (ht (fun _ => p) R) =
      varianceExpansion (fun _ => p) R B (fun _ _ => 0) ∧
    variance (fun _ => p) (ht (fun _ => p) R) ≤ htVarianceUpper p R B) ∧
  (∀ (N : ℕ) (p b : ℝ) (R : CircleTable N) (B : Fin N → Finset (Fin N)),
    0 < N → (0 < p ∧ p < 1) → (∀ i z, |R i z| < b) →
    (∀ i, i ∈ B i) → (∀ i j, j ∈ B i ↔ i ∈ B j) →
    (∀ i j, j ∉ B i → ¬ sharesSource R i j) →
    (0 ≤ htDiagonal p R ∧ htDiagonal p R ≤ b^2/(N*p)+b^2/(N*(1-p))) ∧
    (∀ a c : Bool, |htPairCov p R B a c| ≤ 2*b^2*((maxDegree B : ℝ)-1)/N) ∧
    variance (fun _ => p) (ht (fun _ => p) R) ≤
      b^2/(N*p)+b^2/(N*(1-p))+8*b^2*((maxDegree B : ℝ)-1)/N) ∧
  (∀ (p b : ℝ) (R : ∀ N, CircleTable N),
    (0 < p ∧ p < 1) → (∀ᶠ N in atTop, ∀ i z, |R N i z| < b) →
    Asymptotics.IsBigO atTop (fun N => htDiagonal p (R N)) (fun N => (N : ℝ)⁻¹)) ∧
  (∀ (p b : ℝ) (R : ∀ N, CircleTable N)
    (B : ∀ N, Fin N → Finset (Fin N)) (D : ℕ),
    (0 < p ∧ p < 1) →
    (∀ᶠ N in atTop, (∀ i z, |R N i z| < b) ∧
      (∀ i, i ∈ B N i) ∧ maxDegree (B N) ≤ D) →
    ∀ a c : Bool, Asymptotics.IsBigO atTop
      (fun N => htPairCov p (R N) (B N) a c) (fun N => (N : ℝ)⁻¹)) ∧
  (∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ),
    (0 < p ∧ p < 1) → 0 ≤ d → SpatialLocalConditions P →
    (∀ᶠ N in atTop, WellDefined (P N) d) →
    Asymptotics.IsBigO atTop
      (fun N => variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)))
      (fun N => (N : ℝ)⁻¹))

/-- The standardized HT summand with the corrected centring and denominator. -/
def htSummand {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (i : Fin N) (z : Assignment N) : ℝ :=
  (residualContrast p R (fun _ _ => 0) i z-nodeEffect p R i) /
    (N*Real.sqrt (variance p (ht p R)))

/-- The article's C5 expression, centred explicitly at the AME. -/
def effectHomophily {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) : ℝ :=
  (∑ i, (nodeEffect p R i-ame p R) * ∑ j ∈ B i, (nodeEffect p R j-ame p R)) / N

def T33Statement : Prop :=
  (∀ (N : ℕ) (p : ℝ) (R : CircleTable N) (B : Fin N → Finset (Fin N)),
    0 < N → (0 < p ∧ p < 1) → (∀ i, i ∈ B i) →
    (∀ i j, j ∉ B i → ¬ sharesSource R i j) →
    let π := fun _ : Fin N => p
    let g := fun (_ : Fin N) a => barMu π R a
    variance π (linearHajek π R) = varianceExpansion π R B g ∧
    secondMomentBound π R B g - variance π (linearHajek π R) =
      effectHomophily π R B / N ∧
    (variance π (linearHajek π R) ≤ secondMomentBound π R B g ↔ 0 ≤ effectHomophily π R B) ∧
    (0 ≤ effectHomophily π R B → variance π (linearHajek π R) ≤ secondMomentBound π R B g)) ∧
  (∀ (N : ℕ) (p : ℝ) (R : CircleTable N),
    0 < N → (0 < p ∧ p < 1) → 0 < variance (fun _ => p) (ht (fun _ => p) R) →
    (∀ z, (∑ i, htSummand (fun _ => p) R i z) =
      (ht (fun _ => p) R z-ame (fun _ => p) R)/Real.sqrt (variance (fun _ => p) (ht (fun _ => p) R))) ∧
    (∀ i, expect (fun _ => p) (htSummand (fun _ => p) R i) = 0) ∧
    variance (fun _ => p) (fun z => ∑ i, htSummand (fun _ => p) R i z) = 1)

end
end SAP.P004c
