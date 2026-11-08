import SAP.P001f.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def logisticProbability (a b x : ℝ) : ℝ := Real.exp (a + b * x) / (1 + Real.exp (a + b * x))

def causalSizes : Fin 3 → ℝ := fun _ => 6
def causalTreatedCounts : Fin 3 → ℝ := ![3, 1, 5]
def causalTreatedSums : Fin 3 → ℝ := ![12, 3, 20]
def causalControlSums : Fin 3 → ℝ := ![9, 10, 3]

/-- Log likelihood of the three grouped binomial cells at covariates -1, 0, 1. -/
def groupedLogLikelihood (N r : Fin 3 → ℝ) (a b : ℝ) : ℝ :=
  ∑ j, (r j * Real.log (logisticProbability a b ((![-1, 0, 1] : Fin 3 → ℝ) j)) +
    (N j - r j) * Real.log (1 - logisticProbability a b ((![-1, 0, 1] : Fin 3 → ℝ) j)))

def cellIPW {E : Type*} [Fintype E] (n : ℕ) (q st sc : E → ℝ) : ℝ :=
  (∑ x, (st x / q x - sc x / (1 - q x))) / (n : ℝ)

def cellPoststratification {E : Type*} [Fintype E] (n : ℕ) (nt nc st sc : E → ℝ) : ℝ :=
  (∑ x, (nt x + nc x) * (st x / nt x - sc x / nc x)) / (n : ℝ)

/-- Actual coordinate derivative; its use in the sample formula is guarded by differentiability. -/
def coordinateDerivative {K : ℕ} (m : (Fin K → ℝ) → ℝ) (x : Fin K → ℝ) (k : Fin K) : ℝ :=
  deriv (fun t : ℝ => m (Function.update x k (x k + t))) 0

def samplePDA {Ω : Type*} {K : ℕ} (X : ℕ → Ω → Fin K → ℝ)
    (mhat : ℕ → Ω → (Fin K → ℝ) → ℝ) (n : ℕ) (ω : Ω) (k : Fin K) : ℝ :=
  coordinateDerivative (mhat n ω) (fun j => sampleAverage (fun i z => X i z j) n ω) k

universe u

/-- Historical prior contract, retained for source/evidence comparison but no
longer credited by T102. Its coordinate-only regularity admits a null-set
version artifact at an interior mean. -/
def PDAWellDefined : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : Ω → Fin K → ℝ) (Y : Ω → ℝ),
    Measurable X → Measurable Y →
    (∀ j, Integrable (fun ω => X ω j) μ) → Integrable Y μ →
    ∀ (f : (Fin K → ℝ) → ℝ) (q : ((Fin K → ℝ) × ℝ) → ℝ),
    RealDensity (μ.map X) f → RealDensity (μ.map (fun ω => (X ω, Y ω))) q →
    ∀ (m0 m1 : (Fin K → ℝ) → ℝ),
    ConditionalMean μ X Y m0 → ConditionalMean μ X Y m1 →
    ∀ k : Fin K,
    (∀ x, 0 < f x →
      DifferentiableAt ℝ (fun t => m0 (Function.update x k (x k + t))) 0) →
    (∀ x, 0 < f x →
      DifferentiableAt ℝ (fun t => m1 (Function.update x k (x k + t))) 0) →
    let xbar : Fin K → ℝ := fun j => ∫ ω, X ω j ∂μ
    ∃ a : ℝ,
      HasDerivAt (fun t => m0 (Function.update xbar k (xbar k + t))) a 0 ∧
      HasDerivAt (fun t => m1 (Function.update xbar k (xbar k + t))) a 0

/-- The PDA identification assertion under the printed differentiability
condition, strengthened to globally differentiable CEF versions. Their
values agree almost surely under the same joint law, but the assertion asks
whether their coordinate derivatives at the covariate mean must agree. The
mean is not assumed to lie in the covariate support. -/
def PDAIdentified : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : Ω → Fin K → ℝ) (Y : Ω → ℝ),
    Measurable X → Measurable Y →
    (∀ j, Integrable (fun ω => X ω j) μ) → Integrable Y μ →
    ∀ (f : (Fin K → ℝ) → ℝ) (q : ((Fin K → ℝ) × ℝ) → ℝ),
    RealDensity (μ.map X) f → RealDensity (μ.map (fun ω => (X ω, Y ω))) q →
    ∀ (m0 m1 : (Fin K → ℝ) → ℝ),
    ConditionalMean μ X Y m0 → ConditionalMean μ X Y m1 →
    Differentiable ℝ m0 → Differentiable ℝ m1 →
    ∀ k : Fin K,
    let xbar : Fin K → ℝ := fun j => ∫ ω, X ω j ∂μ
    coordinateDerivative m0 xbar k = coordinateDerivative m1 xbar k

/-- The printed-support-saturated PDA identification assertion. Definition
1.2.20 calls the chosen PDF's positive set `Supp[X]`, and the standing
footnote-14 condition equates it with the sample range. The two globally
differentiable CEF versions otherwise obey the same joint-density and
conditional-mean requirements as `PDAIdentified`. -/
def PDAIdentifiedPDFSupportSaturated : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : Ω → Fin K → ℝ) (Y : Ω → ℝ),
    Measurable X → Measurable Y →
    (∀ j, Integrable (fun ω => X ω j) μ) → Integrable Y μ →
    ∀ (f : (Fin K → ℝ) → ℝ) (q : ((Fin K → ℝ) × ℝ) → ℝ),
    RealDensity (μ.map X) f → RealDensity (μ.map (fun ω => (X ω, Y ω))) q →
    Set.range X = {x | 0 < f x} →
    ∀ (m0 m1 : (Fin K → ℝ) → ℝ),
    ConditionalMean μ X Y m0 → ConditionalMean μ X Y m1 →
    Differentiable ℝ m0 → Differentiable ℝ m1 →
    ∀ k : Fin K,
    let xbar : Fin K → ℝ := fun j => ∫ ω, X ω j ∂μ
    coordinateDerivative m0 xbar k = coordinateDerivative m1 xbar k

def gaussianDensity (m s y : ℝ) : ℝ :=
  Real.exp (-(y - m) ^ 2 / (2 * s ^ 2)) / (s * Real.sqrt (2 * Real.pi))

def lognormalPDF (m s y : ℝ) : ℝ :=
  if 0 < y then gaussianDensity m s (Real.log y) / y else 0

def exponentialPDF (r y : ℝ) : ℝ := if 0 ≤ y then r * Real.exp (-r * y) else 0

def mixturePDF (θ : Fin 7 → ℝ) (y : ℝ) : ℝ :=
  θ 0 * gaussianDensity (θ 2) (θ 3) y + θ 1 * lognormalPDF (θ 4) (θ 5) y +
    (1 - θ 0 - θ 1) * exponentialPDF (θ 6) y

def ValidMixture (θ : Fin 7 → ℝ) : Prop :=
  0 ≤ θ 0 ∧ 0 ≤ θ 1 ∧ θ 0 + θ 1 ≤ 1 ∧ 0 < θ 3 ∧ 0 < θ 5 ∧ 0 < θ 6

def mixtureSampleLikelihood {n : ℕ} (y : Fin n → ℝ) (θ : Fin 7 → ℝ) : ℝ :=
  ∏ i, mixturePDF θ (y i)

/-- The unqualified equivalence on countably many covariate cells; t and c
    are treated and control joint masses, not conditional masses. -/
def OverlapUniformPositivityEquivalence : Prop :=
  ∀ t c : ℕ → ℝ, (∀ k, 0 ≤ t k) → (∀ k, 0 ≤ c k) →
    Summable t → Summable c → 0 < ∑' k, t k → 0 < ∑' k, c k →
    (∑' k, t k) + (∑' k, c k) = 1 →
    ({k | 0 < t k} = {k | 0 < c k} ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ k, 0 < t k + c k →
        ε < t k / (t k + c k) ∧ t k / (t k + c k) < 1 - ε)

end
end SAP.P001f
