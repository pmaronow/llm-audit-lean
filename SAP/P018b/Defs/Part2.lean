import SAP.P018b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

def meanVec {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (μ : Measure Ω) (f : Ω → Vec k) : Vec k :=
  fun a => ∫ ω, f ω a ∂ μ

def meanMat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (μ : Measure Ω) (f : Ω → Mat k) : Mat k :=
  fun a b => ∫ ω, f ω a b ∂ μ

def covMat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (f g : Ω → Vec k) : Mat k :=
  fun a b => ProbabilityTheory.covariance (fun ω => f ω a) (fun ω => g ω b) μ

def varMat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (μ : Measure Ω) (f : Ω → Vec k) : Mat k :=
  covMat μ f f

def inProbability {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)]
    {E : Type*} [NormedAddCommGroup E] (μ : ∀ N : ℕ, Measure (Ω N))
    (f : ∀ N : ℕ, Ω N → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N : ℕ => (μ N {ω | ε ≤ ‖f N ω‖}).toReal) atTop (𝓝 0)

def weakLimit {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)]
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : ∀ N : ℕ, Measure (Ω N)) (f : ∀ N : ℕ, Ω N → E) (ν : Measure E) : Prop :=
  (∀ N : ℕ, AEMeasurable (f N) (μ N)) ∧ IsProbabilityMeasure ν ∧
  ∀ g : E →ᵇ ℝ, Tendsto (fun N : ℕ => ∫ ω, g (f N ω) ∂ μ N) atTop (𝓝 (∫ x, g x ∂ ν))

def centeredNormalLaw {k : ℕ} (ν : Measure (Vec k)) (V : Mat k) : Prop :=
  V.PosSemidef ∧ IsProbabilityMeasure ν ∧ ∀ c : Vec k,
    ν.map (fun x => dot c x) = gaussianReal 0 (dot c (V.mulVec c)).toNNReal

structure Kernel (U : Type*) [MeasurableSpace U] (k : ℕ) where
  μ : Measure U
  X : U → U → Vec k
  Y : U → U → ℝ

def unitSampleLaw {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (N : ℕ) :
    Measure (Fin N → U) := Measure.pi (fun _ => K.μ)

def populationGram {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  meanMat (K.μ.prod K.μ) (fun uv => outer (K.X uv.1 uv.2) (K.X uv.1 uv.2))

def populationBeta {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Vec k :=
  (populationGram K)⁻¹.mulVec (meanVec (K.μ.prod K.μ) (fun uv => score (K.X uv.1 uv.2) (K.Y uv.1 uv.2)))

def populationResidual {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (u v : U) : ℝ := K.Y u v - dot (K.X u v) (populationBeta K)

def firstUnit {N : ℕ} (d : Dyad N) : Fin N :=
  (members d).min' (Finset.card_pos.mp (by rw [members_card]; omega))

def secondUnit {N : ℕ} (d : Dyad N) : Fin N :=
  (members d).max' (Finset.card_pos.mp (by rw [members_card]; omega))

def design {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (ω : Fin N → U) : Dyad N → Vec k :=
  fun d => K.X (ω (firstUnit d)) (ω (secondUnit d))

def response {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (ω : Fin N → U) : Dyad N → ℝ :=
  fun d => K.Y (ω (firstUnit d)) (ω (secondUnit d))

def epsilon {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (ω : Fin N → U) (d : Dyad N) : ℝ :=
  populationResidual K (ω (firstUnit d)) (ω (secondUnit d))

def populationScore {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (u v : U) : Vec k := score (K.X u v) (populationResidual K u v)

def scoreSum {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k) (ω : Fin N → U) : Vec k :=
  ∑ d : Dyad N, score (design K ω d) (epsilon K ω d)

def Standing {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Prop :=
  IsProbabilityMeasure K.μ ∧
  Measurable (fun uv : U × U => K.X uv.1 uv.2) ∧
  Measurable (fun uv : U × U => K.Y uv.1 uv.2) ∧
  (∀ u v, K.X u v = K.X v u ∧ K.Y u v = K.Y v u) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ uv ∂ K.μ.prod K.μ, ‖K.X uv.1 uv.2‖ ≤ C ∧ |K.Y uv.1 uv.2| ≤ C) ∧
  (∃ j : Fin k, ∀ u v, K.X u v j = 1) ∧ (populationGram K).det ≠ 0

def Proposition1Extra {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ᵐ ω ∂ unitSampleLaw K N,
    ∀ d, |fittedResidual (design K ω) (response K ω) d| ≤ C) ∧
  (∀ a b, (populationGram K) a b ≠ 0) ∧
  (∀ a b, (meanMat (Measure.pi (fun _ : Fin 3 => K.μ)) (fun u =>
    outer (K.X (u 0) (u 1)) (K.X (u 0) (u 2)))) a b ≠ 0) ∧
  (∀ᶠ N : ℕ in atTop,
    (∀ d : Dyad N, (∫ ω, (fittedResidual (design K ω) (response K ω) d)^2
      ∂ unitSampleLaw K N) ≠ 0) ∧
    (∀ d f : Dyad N, f ∈ neighbors d →
      (∫ ω, fittedResidual (design K ω) (response K ω) d *
        fittedResidual (design K ω) (response K ω) f ∂ unitSampleLaw K N) ≠ 0))

def SampleRank {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Prop :=
  ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ᵐ ω ∂ unitSampleLaw K N, (sampleGram (design K ω)).det ≠ 0

def Dreal (N : ℕ) : ℝ := (N : ℝ) * ((N : ℝ)-1) / 2

def trueTarget {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (N : ℕ) : Mat k :=
  ((N : ℝ) / (Dreal N)^2) • sandwich (populationGram K)⁻¹
    (varMat (unitSampleLaw K N) (scoreSum K))

def designSigma {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k) :
    MeasurableSpace (Fin N → U) := MeasurableSpace.comap (design K) inferInstance

def conditionalResidualMean {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d : Dyad N) : (Fin N → U) → ℝ :=
  MeasureTheory.condExp (designSigma K) (unitSampleLaw K N) (fun ω => epsilon K ω d)

def conditionalResidualCov {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d f : Dyad N) : (Fin N → U) → ℝ :=
  MeasureTheory.condExp (designSigma K) (unitSampleLaw K N) (fun ω =>
    (epsilon K ω d - conditionalResidualMean K d ω) *
    (epsilon K ω f - conditionalResidualMean K f ω))

def conditionalTerm {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d f : Dyad N) : Mat k :=
  meanMat (unitSampleLaw K N) (fun ω =>
    conditionalResidualCov K d f ω • outer (design K ω d) (design K ω f))

def printedSigma {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (N : ℕ) : Mat k :=
  ∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then conditionalTerm K d f else 0

def projection {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (u : U) : Vec k :=
  meanVec K.μ (populationScore K u)

def projectionGamma {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  meanMat K.μ (fun u => outer (projection K u) (projection K u))

def limitingTarget {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  (4 : ℝ) • sandwich (populationGram K)⁻¹ (projectionGamma K)

def coefficientError {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (ω : Fin N → U) : Vec k := sampleOLS (design K ω) (response K ω) - populationBeta K

def fairLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

def signValue (b : Bool) : ℝ := if b then 1 else -1

def signKernel : Kernel Bool 1 :=
  ⟨fairLaw, fun _ _ => ![1], fun b c => signValue b + signValue c⟩

def finiteUnitLaw : Measure (Fin 4 × Bool) :=
  (PMF.uniformOfFintype (Fin 4 × Bool)).toMeasure

def heterogeneityTable : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,1,-1,0;1,0,0,-1;-1,0,0,1;0,-1,1,0]

def finiteNegativeKernel : Kernel (Fin 4 × Bool) 2 :=
  ⟨finiteUnitLaw,
    fun u v => ![1, |(u.1.val : ℝ)-(v.1.val : ℝ)|],
    fun u v => |(u.1.val : ℝ)-(v.1.val : ℝ)| + heterogeneityTable u.1 v.1 + signValue u.2 + signValue v.2⟩


end SAP.P018b
