import SAP.P001d.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d

def olsRSS {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
    (b : Fin (K+1) → ℝ) : ℝ := ∑ i, (Y i-(X.mulVec b) i)^2

def olsCoef {n K : ℕ} (X : Matrix (Fin n) (Fin K) ℝ) (Y : Fin n → ℝ) : Fin K → ℝ :=
  (X.transpose*X)⁻¹.mulVec (X.transpose.mulVec Y)

def T65Statement : Prop :=
  ∀ {n K : ℕ}, 0 < n → ∀ (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ),
    IsUnit (X.transpose*X).det → (∀ i, X i 0 = 1) →
    let β := olsCoef X Y
    let e := Y-X.mulVec β
    (∀ b, olsRSS X Y β ≤ olsRSS X Y b ∧ (olsRSS X Y b = olsRSS X Y β ↔ b = β)) ∧
    X.transpose.mulVec e = 0 ∧
    (∑ i, e i)/(n : ℝ) = 0 ∧
    (∀ k, (∑ i, e i*X i k)/(n : ℝ) = 0) ∧
    (∀ k, (∑ i, e i*X i k)/(n : ℝ)-((∑ i, e i)/(n : ℝ))*((∑ i, X i k)/(n : ℝ)) = 0)

def robustCov {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (e : Fin n → ℝ) :
    Matrix (Fin (K+1)) (Fin (K+1)) ℝ :=
  (X.transpose*X)⁻¹*(X.transpose*Matrix.diagonal (fun i => (e i)^2)*X)*(X.transpose*X)⁻¹

def classicalCov {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (s2 : ℝ) :
    Matrix (Fin (K+1)) (Fin (K+1)) ℝ := s2 • (X.transpose*X)⁻¹

/-- Fin index k represents the printed row and column number k.val+1. -/
def coefficientSE {K : ℕ} (V : Matrix (Fin (K+1)) (Fin (K+1)) ℝ) (k : Fin (K+1)) : ℝ :=
  Real.sqrt (V k k)

def T66Statement : Prop :=
  ∀ {n K : ℕ}, 0 < n → ∀ (X : Matrix (Fin n) (Fin (K+1)) ℝ),
    IsUnit (X.transpose*X).det → ∀ (e : Fin n → ℝ) (s2 : ℝ), 0 ≤ s2 →
    let A : Matrix (Fin (K+1)) (Fin (K+1)) ℝ := fun j k =>
      (∑ i, X i j*X i k)/(n : ℝ)
    let B : Matrix (Fin (K+1)) (Fin (K+1)) ℝ := fun j k =>
      (∑ i, (e i)^2*X i j*X i k)/(n : ℝ)
    A = (n : ℝ)⁻¹ • (X.transpose*X) ∧
    B = (n : ℝ)⁻¹ • (X.transpose*Matrix.diagonal (fun i => (e i)^2)*X) ∧
    (n : ℝ)⁻¹ • (A⁻¹*B*A⁻¹) = robustCov X e ∧
    (s2/(n : ℝ)) • A⁻¹ = classicalCov X s2 ∧
    (∀ k : Fin (K+1), 0 ≤ robustCov X e k k → 0 ≤ classicalCov X s2 k k →
      coefficientSE ((n : ℝ)⁻¹ • (A⁻¹*B*A⁻¹)) k = Real.sqrt (robustCov X e k k) ∧
      coefficientSE ((s2/(n : ℝ)) • A⁻¹) k = Real.sqrt (classicalCov X s2 k k))

def populationGram {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K : ℕ} (X : Ω → Fin K → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  fun j k => ∫ ω, X ω j*X ω k ∂μ

def populationMeat {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K : ℕ} (X : Ω → Fin K → ℝ) (ε : Ω → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  fun j k => ∫ ω, (ε ω)^2*X ω j*X ω k ∂μ

def T67Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ} (X : Ω → Fin K → ℝ),
    Measurable X → ∀ ε : Ω → ℝ, MemLp ε 2 μ → IsCEF μ X ε (fun _ => 0) →
    ∀ σ2 : ℝ, 0 ≤ σ2 → IsCEF μ X (fun ω => (ε ω-0)^2) (fun _ => σ2) →
    (∀ j k, Integrable (fun ω => X ω j*X ω k) μ) →
    (∀ j k, Integrable (fun ω => (ε ω)^2*X ω j*X ω k) μ) →
    IsUnit (populationGram μ X).det →
    IsCEF μ X (fun ω => (ε ω)^2) (fun _ => σ2) ∧
    populationMeat μ X ε = σ2 • populationGram μ X ∧
    (populationGram μ X)⁻¹*populationMeat μ X ε*(populationGram μ X)⁻¹ =
      σ2 • (populationGram μ X)⁻¹

def T68Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X W : Ω → ℝ),
    Measurable X → Measurable W → IndepFun X W μ → Integrable W μ →
    (∫ ω, W ω ∂μ) = 0 → ∀ g : ℝ → ℝ, Measurable g → Integrable (g ∘ X) μ →
      IsCEF μ X (fun ω => g (X ω)+W ω) g

def apdExample (x y : ℝ) : ℝ := if y ≤ 4/5 then -x else 9*x

def T69Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X1 X2 Y : Ω → ℝ),
    Measurable X1 → Measurable X2 → Integrable Y μ → IndepFun X1 X2 μ →
    μ.map X1 = uniformLaw 0 1 → μ.map X2 = uniformLaw 0 1 →
    IsCEF μ (fun ω => (X1 ω, X2 ω)) Y (fun xy => apdExample xy.1 xy.2) →
    (∀ x y : ℝ, deriv (fun t => apdExample t y) x = if y ≤ 4/5 then -1 else 9) ∧
    (∫ ω, X1 ω ∂μ) = 1/2 ∧ (∫ ω, X2 ω ∂μ) = 1/2 ∧
    (∫ ω, deriv (fun t => apdExample t (X2 ω)) (X1 ω) ∂μ) = 1 ∧
    deriv (fun t => apdExample t (∫ ω, X2 ω ∂μ)) (∫ ω, X1 ω ∂μ) = -1 ∧
    (∫ ω, deriv (fun t => apdExample t (X2 ω)) (X1 ω) ∂μ) ≠
      deriv (fun t => apdExample t (∫ ω, X2 ω ∂μ)) (∫ ω, X1 ω ∂μ)

end SAP.P001d
