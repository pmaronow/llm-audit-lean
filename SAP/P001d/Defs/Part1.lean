import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d

def prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) : ℝ :=
  (μ A).toReal

def CP {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (c : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => prob μ {ω | ε ≤ dist (Z n ω) c}) atTop (nhds 0)

def cdf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  prob μ {ω | X ω ≤ x}

def CD {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : ℕ → Ω → ℝ) (ν : Measure ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt (fun t => prob ν (Set.Iic t)) x →
    Tendsto (fun n => cdf μ (Z n) x) atTop (nhds (prob ν (Set.Iic x)))

def IID {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧ ∀ i, IdentDistrib (X i) (X 0) μ μ

/-- An integrable version of a conditional mean, specified by its event integrals. -/
def IsCEF {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (m : E → ℝ) : Prop :=
  Measurable m ∧ Integrable Y μ ∧ Integrable (m ∘ X) μ ∧
    ∀ A : Set E, MeasurableSet A →
      (∫ ω in X ⁻¹' A, Y ω ∂μ) = ∫ ω in X ⁻¹' A, m (X ω) ∂μ

def uniformLaw (a b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (if x ∈ Set.Icc a b then (b-a)⁻¹ else 0))

def firstSample {Ω E : Type*} (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : Fin n → E :=
  fun i => X i ω

def finiteSampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i)/(n : ℝ)

def bootMean {n : ℕ} (T : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ a : Fin n → Fin n, T (x ∘ a))/((n : ℝ)^n)

def bootVar {n : ℕ} (T : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ a : Fin n → Fin n, (T (x ∘ a)-bootMean T x)^2)/((n : ℝ)^n)

def bootstrapTestMean {n : ℕ} (T : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (f : ℝ → ℝ) : ℝ :=
  (∑ a : Fin n → Fin n, f (Real.sqrt n*(T (fun i => x (a i))-T x)))/((n : ℝ)^n)

def BootstrapWeakCP {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (sizes : ℕ → ℕ) (T : {n : ℕ} → (Fin n → ℝ) → ℝ)
    (ν : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    CP μ (fun k ω => bootstrapTestMean T (firstSample X (sizes k) ω) f) (∫ x, f x ∂ν)

def kernelDensity {n : ℕ} (K : ℝ → ℝ) (h : ℝ) (X : Fin n → ℝ) (x : ℝ) : ℝ :=
  (∑ i, K ((x-X i)/h)/h)/(n : ℝ)

def kernelCDF {n : ℕ} (K : ℝ → ℝ) (h : ℝ) (X : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∫ u in Set.Iic x, kernelDensity K h X u

def signedKernel (t : ℝ) : ℝ := if |t| ≤ 1 then 1 else if |t| ≤ 2 then -1/2 else 0
def rectangleKernel (t : ℝ) : ℝ := if |t| ≤ 1 then 1/2 else 0

/-- The endpoint of the uniform variable in the tail maps is a null event. -/
def heavyBootstrapLaw : Measure ℝ :=
  (1/2 : ℝ≥0∞) • uniformLaw (-1) 1 +
  (1/4 : ℝ≥0∞) • (uniformLaw 0 1).map (fun u : ℝ => (2 : ℝ)^(1/u^2)) +
  (1/4 : ℝ≥0∞) • (uniformLaw 0 1).map (fun u : ℝ => -((2 : ℝ)^(1/u^2)))

/-- On the positive odd sizes used below, this is the unique middle order statistic. -/
def sampleMedian {n : ℕ} (X : Fin n → ℝ) : ℝ :=
  ((List.ofFn X).mergeSort (fun a b => a ≤ b)).getD (n/2) 0

def regularHeavyStatistic {n : ℕ} (X : Fin n → ℝ) : ℝ :=
  let a := ((Finset.univ.filter (fun i => X i ≤ 0)).card : ℝ)/(n : ℝ)
  if a ∈ Set.Icc (1/4 : ℝ) (3/4) then a-1/2 else sampleMedian X

/-- Only its local, linear branch is asserted for arbitrary functions below. -/
def regularHeavyFunctional (G : ℝ → ℝ) : ℝ :=
  if G 0 ∈ Set.Icc (1/4 : ℝ) (3/4) then G 0-1/2 else sInf {x : ℝ | 1/2 ≤ G x}

def T58Statement : Prop :=
  (∀ t : ℝ, signedKernel t = signedKernel (-t)) ∧ Integrable signedKernel volume ∧
  (∫ t, signedKernel t) = 1 ∧
  ∀ a : ℝ, (∀ x, kernelDensity signedKernel 1 (fun _ : Fin 1 => a) x = signedKernel (x-a)) ∧
    kernelCDF signedKernel 1 (fun _ : Fin 1 => a) (a-1) = -1/2

def T59Statement : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (X : Fin n → ℝ) (K : ℝ → ℝ),
    (∀ᵐ t ∂volume, 0 ≤ K t) → (∫ t, K t) = 1 → (∀ t, K t = K (-t)) →
    ∀ h : ℝ, 0 < h →
    (∀ᵐ x ∂volume, 0 ≤ kernelDensity K h X x) ∧
    (∫ x, kernelDensity K h X x) = 1 ∧ Monotone (kernelCDF K h X) ∧
    Continuous (kernelCDF K h X) ∧ Tendsto (kernelCDF K h X) atBot (nhds 0) ∧
    Tendsto (kernelCDF K h X) atTop (nhds 1)

def T60Statement : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (X : Fin n → ℝ) (h : ℝ), 0 < h →
    (∀ K : ℝ → ℝ, Integrable K volume → ∀ x : ℝ,
      kernelCDF K h X x = (∑ i, ∫ t in Set.Iic ((x-X i)/h), K t)/(n : ℝ)) ∧
    (∀ x : ℝ, (∀ i, X i ≠ x-h) → kernelDensity rectangleKernel h X x =
      (((∑ i, if X i ≤ x+h then (1 : ℝ) else 0)/(n : ℝ))-
        ((∑ i, if X i ≤ x-h then (1 : ℝ) else 0)/(n : ℝ)))/(2*h))

def T61Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ),
    IID μ X → μ.map (X 0) = heavyBootstrapLaw →
    (CD μ (fun k ω => Real.sqrt (2*k+1)*sampleMedian (firstSample X (2*k+1) ω))
        (gaussianReal 0 4) ∧
      BootstrapWeakCP μ X (fun k => 2*k+1) (fun {n} => @sampleMedian n) (gaussianReal 0 4) ∧
      (∀ n : ℕ, Odd n → 5 ≤ n → (3/16 : ℝ) ≤ prob μ {ω |
        5 < (n : ℝ)*bootVar sampleMedian (firstSample X n ω)}) ∧
      ¬ CP μ (fun k ω => ((2*k+1 : ℕ) : ℝ)*bootVar sampleMedian
        (firstSample X (2*k+1) ω)) 4) ∧
    ( (∀ G : ℝ → ℝ, (∀ x, |G x-cdf heavyBootstrapLaw id x| < 1/4) →
        regularHeavyFunctional G-regularHeavyFunctional (cdf heavyBootstrapLaw id) =
          G 0-cdf heavyBootstrapLaw id 0) ∧
      CD μ (fun k ω => Real.sqrt (2*k+1)*regularHeavyStatistic
        (firstSample X (2*k+1) ω)) (gaussianReal 0 (1/4)) ∧
      (∀ n : ℕ, Odd n → 5 ≤ n → (3/16 : ℝ) ≤ prob μ {ω |
        5 < (n : ℝ)*bootVar regularHeavyStatistic (firstSample X n ω)}) ∧
      ¬ CP μ (fun k ω => ((2*k+1 : ℕ) : ℝ)*bootVar regularHeavyStatistic
        (firstSample X (2*k+1) ω)) (1/4))

end SAP.P001d
