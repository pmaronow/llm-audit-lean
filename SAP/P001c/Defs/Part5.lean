import Mathlib
import SAP.P001c.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical
noncomputable section

def T47Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ),
    Measurable X → Measurable Y → IndepFun X Y μ → MemLp X 2 μ → MemLp Y 2 μ →
    (isConditionalMean μ X Y (fun _ => expectation μ Y) ∧
      isConditionalMean μ X (fun ω => (Y ω-expectation μ Y)^2) (fun _ => variance Y μ) ∧
      (∀ a b : ℝ, affineRisk μ X Y (expectation μ Y) 0 ≤ affineRisk μ X Y a b) ∧
      (0 < variance X μ →
        regressionSlope μ X Y=0 ∧ regressionIntercept μ X Y=expectation μ Y)) ∧
    ∀ g h : ℝ → ℝ, Measurable (g ∘ X) → Measurable (h ∘ Y) →
      AEMeasurable g (μ.map X) → AEMeasurable h (μ.map Y) →
      MemLp (g ∘ X) 2 μ → MemLp (h ∘ Y) 2 μ →
      IndepFun (g ∘ X) (h ∘ Y) μ ∧
      isConditionalMean μ (g ∘ X) (h ∘ Y) (fun _ => expectation μ (h ∘ Y)) ∧
      (∀ a b : ℝ, affineRisk μ (g ∘ X) (h ∘ Y) (expectation μ (h ∘ Y)) 0 ≤
        affineRisk μ (g ∘ X) (h ∘ Y) a b) ∧
      (0 < variance (g ∘ X) μ →
        regressionSlope μ (g ∘ X) (h ∘ Y)=0 ∧
        regressionIntercept μ (g ∘ X) (h ∘ Y)=expectation μ (h ∘ Y))

def T48Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (K : ℕ) (X : Ω → Fin K → ℝ),
    (∀ k, MemLp (fun ω => X ω k) 2 μ) →
    (∀ j k, covarianceEntries μ X j k=covariance (fun ω => X ω j) (fun ω => X ω k) μ) ∧
    (covarianceEntries μ X).IsSymm ∧
    (∀ k, covarianceEntries μ X k k=variance (fun ω => X ω k) μ) ∧
    variance (fun ω => ∑ k, X ω k) μ =
      ∑ j : Fin K, ∑ k : Fin K, covariance (fun ω => X ω j) (fun ω => X ω k) μ

def T49Statement : Prop :=
  ∀ (K : ℕ) (b : Fin (K+1) → ℝ) (x : Fin K → ℝ),
    affinePredictor b (fun _ => 0)=b 0 ∧
    ∀ k : Fin K,
      affinePredictor b (Function.update x k (x k+1))-affinePredictor b x=b k.succ ∧
      HasDerivAt (fun t : ℝ => affinePredictor b (Function.update x k t)) (b k.succ) (x k) ∧
      coordinatePartial (affinePredictor b) x k=b k.succ

def T50Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  (∀ (N : ℕ), 0 < N → ∀ x : Fin N → ℝ,
    (∀ t : ℝ, finiteProbability (equalWeights N) (fun i => x i=t) =
      ((Finset.univ.filter (fun i => x i=t)).card : ℝ)/(N : ℝ)) ∧
    finiteMean (equalWeights N) x=(∑ i, x i)/(N : ℝ) ∧
    finiteVariance (equalWeights N) x=
      (∑ i, (x i-(∑ j, x j)/(N : ℝ))^2)/(N : ℝ)) ∧
  (Set.range (![3,4,3,10] : Fin 4 → ℝ) = {3,4,10}) ∧
  finiteProbability (equalWeights 4) (fun i => (![3,4,3,10] : Fin 4 → ℝ) i=3)=1/2 ∧
  finiteProbability (equalWeights 4) (fun i => (![3,4,3,10] : Fin 4 → ℝ) i=4)=1/4 ∧
  finiteProbability (equalWeights 4) (fun i => (![3,4,3,10] : Fin 4 → ℝ) i=10)=1/4 ∧
  finiteMean (equalWeights 4) ![3,4,3,10]=5 ∧
  finiteVariance (equalWeights 4) ![3,4,3,10]=17/2 ∧
  (∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ), MemLp Z 2 μ →
    variance Z μ=expectation μ (fun ω => (Z ω)^2)-(expectation μ Z)^2 ∧
    expectation μ (fun ω => (Z ω)^2)+(expectation μ Z)^2-variance Z μ=2*(expectation μ Z)^2) ∧
  (∀ (x : ℕ → ℝ) (n : ℕ), 0 < n →
    let ν := empiricalLaw (fun i (_ : Unit) => x i) n ()
    IsProbabilityMeasure ν ∧
    expectation ν id=(∑ i ∈ Finset.range n, x i)/(n : ℝ) ∧
    variance id ν=(∑ i ∈ Finset.range n, (x i)^2)/(n : ℝ) -
      ((∑ i ∈ Finset.range n, x i)/(n : ℝ))^2)

def T51Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ),
    (∀ n, Measurable (Z n)) → ∀ c : ℝ,
    convergesInProbability μ Z c ↔
      ∀ p : ℝ, 0 ≤ p → p < 1 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ n, N ≤ n → p ≤ probability μ {ω | |Z n ω-c| < ε}

def T52Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ],
    (∀ X : Ω → ℝ, Measurable X → ∀ D : Set ℝ, MeasurableSet D →
      expectation μ (fun ω => if X ω ∈ D then (1 : ℝ) else 0)=probability μ (X ⁻¹' D)) ∧
    (∀ X : ℕ → Ω → ℝ, isIID μ X → ∀ x : ℝ,
      convergesInProbability μ
        (sampleAverage (fun i ω => if X i ω ≤ x then (1 : ℝ) else 0)) (cdfAt μ (X 0) x))

def T53Statement : Prop :=
  (∀ k : ℕ, 0 ≤ powerTailMass k) ∧
  Summable powerTailMass ∧ (∑' k, powerTailMass k)=1 ∧
  Summable (fun k => (2 : ℝ)^k*powerTailMass k) ∧
  Summable (fun k => (2 : ℝ)^(2*k)*powerTailMass k) ∧
  (∑' k, (2 : ℝ)^k*powerTailMass k)=7/6 ∧
  (∑' k, (2 : ℝ)^(2*k)*powerTailMass k)=7/4 ∧
  (∑' k : ℕ, ENNReal.ofReal ((2 : ℝ)^(4*k)*powerTailMass k))=∞ ∧
  (7/4-(7/6)^2 : ℝ)=7/18 ∧ (0 : ℝ) < 7/18

def T54Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ),
    isIID μ X → MemLp (X 0) 2 μ → 0 < variance (X 0) μ →
    (∀ n, 0 < n → expectation μ (pluginVariance X n)=((n : ℝ)-1)/n*variance (X 0) μ) ∧
    convergesInProbability μ (pluginVariance X) (variance (X 0) μ)

def T55Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (θhat Vhat : ℕ → Ω → ℝ) (θ : ℝ),
    (∀ n, Measurable (θhat n)) → (∀ n, Measurable (Vhat n)) →
    (∀ n ω, 0 ≤ Vhat n ω) →
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], MemLp id 2 ν →
    convergesInDistribution μ (fun n ω => Real.sqrt n*(θhat n ω-θ)) ν →
    (varianceConsistent μ Vhat (variance id ν) ↔
      convergesInProbability μ (fun n ω => (n : ℝ)*Vhat n ω-variance id ν) 0) ∧
    (standardErrorConsistent μ Vhat (variance id ν) ↔
      convergesInProbability μ (fun n ω => Real.sqrt n*Real.sqrt (Vhat n ω)-
        Real.sqrt (variance id ν)) 0) ∧
    (varianceConsistent μ Vhat (variance id ν) ↔ standardErrorConsistent μ Vhat (variance id ν))

end
end SAP.P001c
