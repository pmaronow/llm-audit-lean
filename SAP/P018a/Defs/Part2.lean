import Mathlib
import SAP.P018a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
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

def correctedSigma {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (N : ℕ) : Mat k :=
  meanMat (unitSampleLaw K N) (fun ω => meat members (fun d => score (design K ω d) (epsilon K ω d)))

def scoreH {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  meanMat (K.μ.prod K.μ) (fun uv => outer (populationScore K uv.1 uv.2) (populationScore K uv.1 uv.2))

def projection {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (u : U) : Vec k :=
  meanVec K.μ (populationScore K u)

def projectionGamma {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  meanMat K.μ (fun u => outer (projection K u) (projection K u))

def limitingTarget {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  (4 : ℝ) • sandwich (populationGram K)⁻¹ (projectionGamma K)

def coefficientError {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (ω : Fin N → U) : Vec k := sampleOLS (design K ω) (response K ω) - populationBeta K

def uniformUnitLaw : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)

def nonlinearKernel : Kernel ℝ 2 :=
  ⟨uniformUnitLaw, fun z t => ![1,2+z+t], fun z t => (z+t)^2⟩

def nonlinearQ : Mat 2 := !![1,2;2,14/3]

def nonlinearH : Mat 2 := !![28/45,56/45;56/45,3448/945]

def nonlinearGamma : Mat 2 := !![4/45,8/45;8/45,632/945]

def nonlinearVstar : Mat 2 := !![3664/315,-592/105;-592/105,296/105]

def fairLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

def signValue (b : Bool) : ℝ := if b then 1 else -1

def signKernel : Kernel Bool 1 :=
  ⟨fairLaw, fun _ _ => ![1], fun b c => signValue b + signValue c⟩

def fairAverage : (N : ℕ) → ((Fin N → ℝ) → ℝ) → ℝ
  | 0, f => f (Fin.elim0)
  | N+1, f => (fairAverage N (fun u => f (Matrix.vecCons 1 u)) +
      fairAverage N (fun u => f (Matrix.vecCons (-1) u))) / 2

def signResidual4 (u : Fin 4 → ℝ) (d : Fin 6) : ℝ :=
  (∑ i ∈ sixMembers d, u i) - (∑ i, u i)/2

def concentratedWeight {N : ℕ} (d : Dyad N) : ℝ :=
  (2 : ℝ) ^ (-((firstUnit d).val + (secondUnit d).val + 2 : ℤ))

def weightedGram {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (w : Dyad N → ℝ) (ω : Fin N → U) : Mat k :=
  ∑ d, w d • outer (design K ω d) (design K ω d)

def weightedOLS {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (w : Dyad N → ℝ) (ω : Fin N → U) : Vec k :=
  (weightedGram K w ω)⁻¹.mulVec (∑ d, score (design K ω d) (w d * response K ω d))

def weightedPopulationGram {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) : Mat k :=
  (Dreal N)⁻¹ • meanMat (unitSampleLaw K N) (weightedGram K w)

def weightedPopulationBeta {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) : Vec k :=
  (meanMat (unitSampleLaw K N) (weightedGram K w))⁻¹.mulVec
    (meanVec (unitSampleLaw K N) (fun ω => ∑ d, score (design K ω d) (w d * response K ω d)))

def weightedScoreSum {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) (ω : Fin N → U) : Vec k :=
  ∑ d, score (design K ω d) (w d * (response K ω d - dot (design K ω d) (weightedPopulationBeta K w)))

def weightedVariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) (ω : Fin N → U) : Mat k :=
  sandwich (weightedGram K w ω)⁻¹ (meat members (fun d =>
    score (design K ω d) (w d * (response K ω d - dot (design K ω d) (weightedOLS K w ω)))))

def weightedTarget {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) : Mat k :=
  ((N : ℝ)/(Dreal N)^2) • sandwich (weightedPopulationGram K w)⁻¹
    (varMat (unitSampleLaw K N) (weightedScoreSum K w))

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

def repeatedH {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) : Mat k :=
  (repeatedL R N)⁻¹ • meanMat (repeatedLaw R N) (repeatedGram R)

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

def repeatedTarget {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) : Mat k :=
  ((N : ℝ)/(repeatedL R N)^2) • sandwich (repeatedH R N)⁻¹
    (varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N, repeatedBlockScore R (repeatedBeta R N) ω d))

def RepeatedStanding {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) : Prop :=
  IsProbabilityMeasure R.μ ∧
  (∀ N : ℕ, 2 ≤ N → ∀ d : Dyad N, 0 < R.T N d) ∧
  (∀ N d t, Measurable (fun uv : U × U => R.X N d t uv.1 uv.2) ∧
    Measurable (fun uv : U × U => R.Y N d t uv.1 uv.2)) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ N d t, ∀ᵐ uv ∂ R.μ.prod R.μ,
    ‖R.X N d t uv.1 uv.2‖ ≤ C ∧ |R.Y N d t uv.1 uv.2| ≤ C) ∧
  (∃ j : Fin k, ∀ N d t u v, R.X N d t u v j = 1)

def RepeatedAtSize {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) : Prop :=
  IsProbabilityMeasure R.μ ∧
  (∀ d : Dyad N, 0 < R.T N d) ∧
  (∀ d t, Measurable (fun uv : U × U => R.X N d t uv.1 uv.2) ∧
    Measurable (fun uv : U × U => R.Y N d t uv.1 uv.2)) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ d t, ∀ᵐ uv ∂ R.μ.prod R.μ,
    ‖R.X N d t uv.1 uv.2‖ ≤ C ∧ |R.Y N d t uv.1 uv.2| ≤ C)

def recordWeightedGram {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (ω : Fin N → U) : Mat k :=
  ∑ d : Dyad N, ∑ t, w d t • outer (repeatedX R ω d t) (repeatedX R ω d t)

def recordWeightedXY {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (ω : Fin N → U) : Vec k :=
  ∑ d : Dyad N, ∑ t, score (repeatedX R ω d t) (w d t * repeatedY R ω d t)

def recordWeightedOLS {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (ω : Fin N → U) : Vec k :=
  (recordWeightedGram R w ω)⁻¹.mulVec (recordWeightedXY R w ω)

def recordWeightedBeta {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ) : Vec k :=
  (meanMat (repeatedLaw R N) (recordWeightedGram R w))⁻¹.mulVec
    (meanVec (repeatedLaw R N) (recordWeightedXY R w))

def recordWeightedBlockScore {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (β : Vec k) (ω : Fin N → U) (d : Dyad N) : Vec k :=
  ∑ t, score (repeatedX R ω d t)
    (w d t * (repeatedY R ω d t - dot (repeatedX R ω d t) β))

end SAP.P018a
