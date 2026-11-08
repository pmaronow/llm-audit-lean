import Mathlib
import SAP.P001c.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical
noncomputable section

def T39Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  (∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (X : Fin n → Ω → ℝ),
    (∀ i, Measurable (X i)) → iIndepFun X μ →
    ∀ (m a : Fin n → ℝ) (v : Fin n → ℝ≥0),
    (∀ i, 0 < v i) → (∀ i, μ.map (X i)=gaussianReal (m i) (v i)) →
    (∃ i, a i ≠ 0) → ∀ b : ℝ,
      μ.map (fun ω => (∑ i, a i*X i ω)+b) =
        gaussianReal ((∑ i, a i*m i)+b) (∑ i, ⟨(a i)^2, sq_nonneg _⟩*v i) ∧
      0 < ∑ i : Fin n, (a i)^2*(v i : ℝ)) ∧
  (∀ mx my sx sy ρ : ℝ, 0 < sx → 0 < sy → ρ ∈ Set.Ioo (-1 : ℝ) 1 →
    let f := bivariatePDF mx my sx sy ρ
    let ν := volume.withDensity (fun xy => ENNReal.ofReal (f xy))
    IsProbabilityMeasure ν ∧ isJointDensity ν f ∧
    MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 ν ∧ MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 ν ∧
    expectation ν Prod.fst=mx ∧ expectation ν Prod.snd=my ∧
    Real.sqrt (variance Prod.fst ν)=sx ∧ Real.sqrt (variance Prod.snd ν)=sy ∧
    correlationCoefficient ν Prod.fst Prod.snd=ρ ∧
    (ρ=0 → IndepFun Prod.fst Prod.snd ν ∧
      ∀ xy, f xy=normalPDF mx sx xy.1*normalPDF my sy xy.2))

def T40Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  (∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ), MemLp X 2 μ →
    (∀ c : ℝ, meanSquaredError μ X c=variance X μ+(expectation μ X-c)^2) ∧
    (∀ c : ℝ, meanSquaredError μ X (expectation μ X) ≤ meanSquaredError μ X c ∧
      (meanSquaredError μ X c=meanSquaredError μ X (expectation μ X) ↔ c=expectation μ X))) ∧
  (∀ c : ℝ, fairCoinLoss c=c^2-c+1/2 ∧ 1/4 ≤ fairCoinLoss c ∧
    (fairCoinLoss c=1/4 ↔ c=1/2) ∧
    2*fairCoinLoss c=(0-c)^2+(1-c)^2) ∧
  fairCoinLoss (-2)=13/2 ∧ fairCoinLoss 2=5/2 ∧ fairCoinLoss (1/2)=1/4 ∧
  finiteMean signWeights ![0,1]=1/2 ∧ finiteVariance signWeights ![0,1]=1/4 ∧
  (∀ c : ℝ, fairCoinLoss c =
    finiteMean signWeights (fun i => ((![0,1] : Fin 2 → ℝ) i-c)^2)) ∧
  (∀ c : ℝ, 2*fairCoinLoss c=2*c^2-2*c+1) ∧
  2*fairCoinLoss (-2)=13 ∧ 2*fairCoinLoss (1/2)=1/2 ∧ 2*fairCoinLoss 2=5

def T41Statement : Prop :=
  finiteMean nullWeights ![0,1,0]=1/2 ∧
  finiteMean nullWeights ![0,1,1]=1/2 ∧ finiteMean nullWeights ![1,0,0]=1/2 ∧
  finiteVariance nullWeights ![0,1,0]=1/4 ∧ finiteVariance nullWeights ![0,1,1]=1/4 ∧
  finiteVariance nullWeights ![1,0,0]=1/4 ∧
  finiteCovariance nullWeights ![0,1,0] ![0,1,1]=1/4 ∧
  finiteCovariance nullWeights ![0,1,0] ![1,0,0]= -1/4 ∧
  finiteCorrelation nullWeights ![0,1,0] ![0,1,1]=1 ∧
  finiteCorrelation nullWeights ![0,1,0] ![1,0,0]= -1 ∧
  finiteVariance nullWeights ![0,1,0] > 0 ∧ finiteVariance nullWeights ![0,1,1] > 0 ∧
  finiteVariance nullWeights ![1,0,0] > 0 ∧
  finiteProbability nullWeights (fun i =>
    (![0,1,1] : Fin 3 → ℝ) i=(![0,1,0] : Fin 3 → ℝ) i)=1 ∧
  finiteProbability nullWeights (fun i =>
    (![1,0,0] : Fin 3 → ℝ) i=1-(![0,1,0] : Fin 3 → ℝ) i)=1 ∧
  (¬ ∃ a b : ℝ, ∀ i : Fin 3,
    (![0,1,1] : Fin 3 → ℝ) i=a+b*(![0,1,0] : Fin 3 → ℝ) i) ∧
  (¬ ∃ a b : ℝ, ∀ i : Fin 3,
    (![1,0,0] : Fin 3 → ℝ) i=a-b*(![0,1,0] : Fin 3 → ℝ) i)

def T42Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ),
    MemLp X 2 μ → MemLp Y 2 μ → 0 < variance X μ → 0 < variance Y μ →
    correlationCoefficient μ X Y ∈ Set.Icc (-1) 1 ∧
    (correlationCoefficient μ X Y=1 ↔ ∃ a b : ℝ, 0 < b ∧ Y =ᵐ[μ] (fun ω => a+b*X ω)) ∧
    (correlationCoefficient μ X Y= -1 ↔ ∃ a b : ℝ, 0 < b ∧ Y =ᵐ[μ] (fun ω => a-b*X ω))

def T43Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ),
    MemLp X 2 μ → MemLp Y 2 μ → 0 < variance X μ →
    (∀ a b : ℝ, HasDerivAt (fun t => affineRisk μ X Y t b)
      (-2*expectation μ (fun ω => Y ω-a-b*X ω)) a ∧
      HasDerivAt (fun t => affineRisk μ X Y a t)
      (-2*expectation μ (fun ω => (Y ω-a-b*X ω)*X ω)) b) ∧
    (∀ a b : ℝ, (expectation μ (fun ω => Y ω-a-b*X ω)=0 ∧
      expectation μ (fun ω => (Y ω-a-b*X ω)*X ω)=0) ↔
      a=regressionIntercept μ X Y ∧ b=regressionSlope μ X Y) ∧
    (∀ a b : ℝ, affineRisk μ X Y (regressionIntercept μ X Y) (regressionSlope μ X Y) ≤
      affineRisk μ X Y a b ∧
      (affineRisk μ X Y a b=affineRisk μ X Y (regressionIntercept μ X Y) (regressionSlope μ X Y) ↔
        a=regressionIntercept μ X Y ∧ b=regressionSlope μ X Y)) ∧
    (∀ m : ℝ → ℝ, isConditionalMean μ X Y m → MemLp (m ∘ X) 2 μ →
      (∀ a b : ℝ,
        deriv (fun t => deriv (fun u => affineRisk μ X Y u b) t) a=2 ∧
        deriv (fun t => deriv (fun u => affineRisk μ X Y a u) t) b=
          2*expectation μ (fun ω => (X ω)^2) ∧
        deriv (fun t => deriv (fun u => affineRisk μ X Y u t) a) b=2*expectation μ X) ∧
      2*(2*expectation μ (fun ω => (X ω)^2))-(2*expectation μ X)^2=4*variance X μ ∧
      0 < 4*variance X μ ∧
      (∀ a b : ℝ, affineRisk μ X (m ∘ X) (regressionIntercept μ X Y) (regressionSlope μ X Y) ≤
        affineRisk μ X (m ∘ X) a b) ∧
      expectation μ (fun ω => Y ω-(regressionIntercept μ X Y+regressionSlope μ X Y*X ω))=0 ∧
      expectation μ (fun ω => X ω*(Y ω-(regressionIntercept μ X Y+regressionSlope μ X Y*X ω)))=0 ∧
      covariance X (fun ω => Y ω-(regressionIntercept μ X Y+regressionSlope μ X Y*X ω)) μ=0 ∧
      (∀ a b : ℝ, isConditionalMean μ X Y (fun x => a+b*x) →
        ∀ᵐ ω ∂μ, m (X ω)=regressionIntercept μ X Y+regressionSlope μ X Y*X ω))

def T44Statement : Prop :=
  finiteVariance signWeights ![-1,1]=1 ∧
  finiteCovariance signWeights ![-1,1] ![-1,1]=1 ∧
  finiteCovariance signWeights ![-1,1] ![0,2]=1 ∧
  finiteMean signWeights (fun i =>
    (( ![-1,1] : Fin 2 → ℝ) i-(![0,2] : Fin 2 → ℝ) i)^2)=1 ∧
  (![0,2] : Fin 2 → ℝ) ≠ ![-1,1] ∧
  finiteMean signWeights (fun i =>
    (( ![-1,1] : Fin 2 → ℝ) i-(![-1,1] : Fin 2 → ℝ) i)^2)=0

def T45Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ),
    MemLp X 2 μ → MemLp Y 2 μ → 0 < variance X μ →
    (∀ a b : ℝ,
      (covariance X (fun ω => a+b*X ω) μ=covariance X Y μ ↔ b=regressionSlope μ X Y) ∧
      ((covariance X (fun ω => a+b*X ω) μ=covariance X Y μ ∧
        expectation μ (fun ω => a+b*X ω)=expectation μ Y) ↔
        b=regressionSlope μ X Y ∧ a=regressionIntercept μ X Y)) ∧
    (∀ a b : ℝ, affineRisk μ X Y (regressionIntercept μ X Y) (regressionSlope μ X Y) ≤
      affineRisk μ X Y a b ∧
      (affineRisk μ X Y a b=affineRisk μ X Y (regressionIntercept μ X Y) (regressionSlope μ X Y) ↔
        a=regressionIntercept μ X Y ∧ b=regressionSlope μ X Y))

def T46Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X W : Ω → ℝ),
    Measurable X → Measurable W → IndepFun X W μ →
    μ.map X=intervalUniform 0 1 → μ.map W=gaussianReal 0 1 →
    let Y := fun ω => 10*(X ω)^2+W ω
    MemLp X 2 μ ∧ MemLp Y 2 μ ∧
    isConditionalMean μ X Y (fun x => 10*x^2) ∧
    expectation μ X=1/2 ∧ expectation μ (fun ω => (X ω)^2)=1/3 ∧
    expectation μ (fun ω => (X ω)^3)=1/4 ∧ variance X μ=1/12 ∧
    expectation μ Y=10/3 ∧ covariance X Y μ=5/6 ∧
    regressionSlope μ X Y=10 ∧ regressionIntercept μ X Y= -5/3 ∧
    (∀ a b : ℝ, affineRisk μ X Y (-5/3) 10 ≤ affineRisk μ X Y a b ∧
      (affineRisk μ X Y a b=affineRisk μ X Y (-5/3) 10 ↔ a= -5/3 ∧ b=10))

end
end SAP.P001c
