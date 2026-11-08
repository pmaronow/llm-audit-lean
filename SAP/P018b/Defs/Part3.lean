import SAP.P018b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

structure RepeatedKernel (U : Type*) [MeasurableSpace U] (k : ℕ) where
  μ : Measure U
  T : (N : ℕ) → Dyad N → ℕ
  X : (N : ℕ) → (d : Dyad N) → Fin (T N d) → U → U → Vec k
  Y : (N : ℕ) → (d : Dyad N) → Fin (T N d) → U → U → ℝ

def repeatedLaw {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) :
    Measure (Fin N → U) := Measure.pi (fun _ => R.μ)

def repeatedL {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) : ℝ :=
  ∑ d : Dyad N, (R.T N d : ℝ)

def repeatedX {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (ω : Fin N → U) (d : Dyad N) (t : Fin (R.T N d)) : Vec k :=
  R.X N d t (ω (firstUnit d)) (ω (secondUnit d))

def repeatedY {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (ω : Fin N → U) (d : Dyad N) (t : Fin (R.T N d)) : ℝ :=
  R.Y N d t (ω (firstUnit d)) (ω (secondUnit d))

def repeatedGram {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k) (ω : Fin N → U) : Mat k :=
  ∑ d : Dyad N, ∑ t, outer (repeatedX R ω d t) (repeatedX R ω d t)

def repeatedBeta {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) : Vec k :=
  (meanMat (repeatedLaw R N) (repeatedGram R))⁻¹.mulVec
    (meanVec (repeatedLaw R N) (fun ω => ∑ d : Dyad N, ∑ t, score (repeatedX R ω d t) (repeatedY R ω d t)))

def repeatedOLS {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k) (ω : Fin N → U) : Vec k :=
  (repeatedGram R ω)⁻¹.mulVec (∑ d : Dyad N, ∑ t, score (repeatedX R ω d t) (repeatedY R ω d t))

def repeatedBlockScore {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (β : Vec k) (ω : Fin N → U) (d : Dyad N) : Vec k :=
  ∑ t, score (repeatedX R ω d t) (repeatedY R ω d t - dot (repeatedX R ω d t) β)

def repeatedVariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (ω : Fin N → U) : Mat k :=
  sandwich (repeatedGram R ω)⁻¹ (meat members (repeatedBlockScore R (repeatedOLS R ω) ω))

def RepeatedStanding {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) : Prop :=
  IsProbabilityMeasure R.μ ∧
  (∀ N : ℕ, 2 ≤ N → ∀ d : Dyad N, 0 < R.T N d) ∧
  (∀ N d t, Measurable (fun uv : U × U => R.X N d t uv.1 uv.2) ∧
    Measurable (fun uv : U × U => R.Y N d t uv.1 uv.2)) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ N d t, ∀ᵐ uv ∂ R.μ.prod R.μ,
    ‖R.X N d t uv.1 uv.2‖ ≤ C ∧ |R.Y N d t uv.1 uv.2| ≤ C) ∧
  (∃ j : Fin k, ∀ N d t u v, R.X N d t u v j = 1)

def uiSquares {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)] {k : ℕ}
    (μ : ∀ N : ℕ, Measure (Ω N)) (ξ : ∀ N : ℕ, Ω N → Vec k) : Prop :=
  (∀ N a, MemLp (fun ω => ξ N ω a) 2 (μ N)) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    (∫ ω, (if C < ∑ a, (ξ N ω a)^2 then ∑ a, (ξ N ω a)^2 else 0) ∂ μ N) < ε

abbrev SimulationIndex (N T : ℕ) := Fin N ⊕ (Fin N ⊕ (Dyad N × Fin T))

def simulationLaw (N T : ℕ) : Measure (SimulationIndex N T → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

def simulationX {N T : ℕ} (ω : SimulationIndex N T → ℝ) (i : Fin N) : ℝ := ω (Sum.inl i)

def simulationError {N T : ℕ} (ω : SimulationIndex N T → ℝ) (d : Dyad N) (t : Fin T) : ℝ :=
  (∑ i ∈ members d, ω (Sum.inr (Sum.inl i))) + ω (Sum.inr (Sum.inr (d,t)))

def endpointZ1 (N : ℕ) : Matrix (Dyad N) (Fin N) ℝ :=
  fun d i => if firstUnit d = i then 1 else 0

def endpointZ2 (N : ℕ) : Matrix (Dyad N) (Fin N) ℝ :=
  fun d i => if secondUnit d = i then 1 else 0

def sharedCov (N : ℕ) (τ σ : ℝ) : Matrix (Dyad N) (Dyad N) ℝ :=
  τ • ((endpointZ1 N + endpointZ2 N) * (endpointZ1 N + endpointZ2 N).transpose) + σ • 1

def twoRoleCov (N : ℕ) (t1 t2 σ : ℝ) : Matrix (Dyad N) (Dyad N) ℝ :=
  t1 • (endpointZ1 N * (endpointZ1 N).transpose) +
    t2 • (endpointZ2 N * (endpointZ2 N).transpose) + σ • 1

def genericScoreMeat {Ω Θ : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (ψ : Ω → Θ → Vec k) (θ : Θ) : Mat k :=
  meanMat μ (fun data => outer (ψ data θ) (ψ data θ))


end SAP.P018b
