import Mathlib
import SAP.P018a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def recordWeightedH {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ) : Mat k :=
  (Dreal N)⁻¹ • meanMat (repeatedLaw R N) (recordWeightedGram R w)

def recordWeightedVariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (ω : Fin N → U) : Mat k :=
  sandwich (recordWeightedGram R w ω)⁻¹
    (meat members (recordWeightedBlockScore R w (recordWeightedOLS R w ω) ω))

def recordWeightedTarget {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ) : Mat k :=
  ((N : ℝ)/(Dreal N)^2) • sandwich (recordWeightedH R w)⁻¹
    (varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
      recordWeightedBlockScore R w (recordWeightedBeta R w) ω d))

def logLikelihood {k : ℕ} (x : Vec k) (y : ℝ) (β : Vec k) : ℝ :=
  y * dot x β - Real.log (1 + Real.exp (dot x β))

def endpointZ1 (N : ℕ) : Matrix (Dyad N) (Fin N) ℝ :=
  fun d i => if firstUnit d = i then 1 else 0

def endpointZ2 (N : ℕ) : Matrix (Dyad N) (Fin N) ℝ :=
  fun d i => if secondUnit d = i then 1 else 0

def sharedCov (N : ℕ) (τ σ : ℝ) : Matrix (Dyad N) (Dyad N) ℝ :=
  τ • ((endpointZ1 N + endpointZ2 N) * (endpointZ1 N + endpointZ2 N).transpose) + σ • 1

def twoRoleCov (N : ℕ) (t1 t2 σ : ℝ) : Matrix (Dyad N) (Dyad N) ℝ :=
  t1 • (endpointZ1 N * (endpointZ1 N).transpose) +
    t2 • (endpointZ2 N * (endpointZ2 N).transpose) + σ • 1

def eightMembers : Fin 28 → Finset (Fin 8) :=
  ![{0,1},{0,2},{0,3},{0,4},{0,5},{0,6},{0,7},
    {1,2},{1,3},{1,4},{1,5},{1,6},{1,7},
    {2,3},{2,4},{2,5},{2,6},{2,7},
    {3,4},{3,5},{3,6},{3,7},{4,5},{4,6},{4,7},{5,6},{5,7},{6,7}]

def degeneracyZ : Fin 8 → ℝ := ![1,1,-1,-1,1,1,-1,-1]

def degeneracyW : Fin 8 → ℝ := ![1,-1,1,-1,1,-1,1,-1]

def degeneracyX : Fin 28 → Vec 2 := fun d => ![1, 1+∏ i ∈ eightMembers d, degeneracyZ i]

def degeneracyY : Fin 28 → ℝ := fun d => ∑ i ∈ eightMembers d, degeneracyW i

def signPairKernel : Kernel (Bool × Bool) 2 :=
  ⟨fairLaw.prod fairLaw, fun u v => ![1,1+signValue u.1*signValue v.1],
    fun u v => signValue u.2+signValue v.2⟩

def signResidual8 (u : Fin 8 → ℝ) (i j : Fin 8) : ℝ := u i+u j-(∑ l,u l)/4

def fairCov8 (f g : (Fin 8 → ℝ) → ℝ) : ℝ :=
  fairAverage 8 (fun u => f u*g u)-fairAverage 8 f*fairAverage 8 g

def normalQuantile (p : ℝ) : ℝ := sInf {z : ℝ | p ≤ ((gaussianReal 0 1) (Set.Iic z)).toReal}

def inverseSpikeLaw (N : ℕ) : Measure ℝ :=
  ENNReal.ofReal ((N : ℝ)⁻¹) • Measure.dirac (N : ℝ) +
    ENNReal.ofReal (1-(N : ℝ)⁻¹) • Measure.dirac 1

def paretoUnitLaw : Measure ℝ := volume.withDensity (fun t =>
  if 1 ≤ t then ENNReal.ofReal ((t⁻¹)^2) else 0)

def inverseKernel : Kernel ℝ 2 :=
  ⟨paretoUnitLaw, fun u v => ![1,Real.exp (-u)+Real.exp (-v)], fun _ _ => 0⟩

def euclideanSq {k : ℕ} (x : Vec k) : ℝ := ∑ a, (x a)^2

def matrixOperatorNorm {k : ℕ} (M : Mat k) : ℝ :=
  sSup {r : ℝ | ∃ x : Vec k, euclideanSq x ≤ 1 ∧ r=Real.sqrt (euclideanSq (M.mulVec x))}

def concentratedRepeated : RepeatedKernel Bool 1 :=
  ⟨fairLaw, fun _ d => 2^((firstUnit d).val+(secondUnit d).val+2),
    fun _ _ _ _ _ => ![1], fun _ _ _ u v => signValue u+signValue v⟩

def singleRecord {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : RepeatedKernel U k :=
  ⟨K.μ, fun _ _ => 1, fun _ _ _ u v => K.X u v, fun _ _ _ u v => K.Y u v⟩

/-- The packaged mathematical content of P018-T1. -/
def T1Statement : Prop :=
    (Standing nonlinearKernel ∧
    (∀ N : ℕ, 3 ≤ N → ∀ᵐ ω ∂ unitSampleLaw nonlinearKernel N, (sampleGram (design nonlinearKernel ω)).det ≠ 0) ∧
    populationGram nonlinearKernel = nonlinearQ ∧ nonlinearQ.det = 2/3 ∧
    populationBeta nonlinearKernel = ![2/3,0] ∧
    scoreH nonlinearKernel = nonlinearH ∧ projectionGamma nonlinearKernel = nonlinearGamma ∧
    nonlinearGamma.PosDef ∧
    (∀ N : ℕ, 3 ≤ N →
      (∀ d f : Dyad N, conditionalResidualCov nonlinearKernel d f =ᵐ[unitSampleLaw nonlinearKernel N] 0) ∧
      printedSigma nonlinearKernel N = 0 ∧
      varMat (unitSampleLaw nonlinearKernel N) (scoreSum nonlinearKernel) =
        (Dreal N) • nonlinearH + ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • nonlinearGamma ∧
      varMat (unitSampleLaw nonlinearKernel N) (scoreSum nonlinearKernel) ≠ 0) ∧
    varMat (unitSampleLaw nonlinearKernel 3) (scoreSum nonlinearKernel) = !![12/5,24/5;24/5,4712/315] ∧
    Tendsto (trueTarget nonlinearKernel) atTop (𝓝 nonlinearVstar) ∧
    nonlinearVstar.PosDef ∧
    (∃ ν : Measure (Vec 2), centeredNormalLaw ν nonlinearVstar ∧
      weakLimit (unitSampleLaw nonlinearKernel) (fun N ω => Real.sqrt N • coefficientError nonlinearKernel ω) ν) ∧
    inProbability (unitSampleLaw nonlinearKernel) (fun N ω =>
      (N : ℝ) • sampleVariance members (design nonlinearKernel ω) (response nonlinearKernel ω) - nonlinearVstar)) ∧

    (∀ z t : ℝ, (-1 ≤ z ∧ z ≤ 1) → (-1 ≤ t ∧ t ≤ 1) →
      0 ≤ 2+z+t ∧ 2+z+t ≤ 4 ∧ 0 ≤ (z+t)^2 ∧ (z+t)^2 ≤ 4 ∧
      -(2/3 : ℝ) ≤ (z+t)^2-2/3 ∧ (z+t)^2-2/3 ≤ 10/3) ∧
    meanVec (uniformUnitLaw.prod uniformUnitLaw) (fun uv =>
      score (nonlinearKernel.X uv.1 uv.2) (nonlinearKernel.Y uv.1 uv.2)) = ![2/3,4/3] ∧
    nonlinearGamma.det = 1184/42525 ∧ nonlinearVstar.det = 4736/4725

/-- The packaged mathematical content of P018-T2. -/
def T2Statement : Prop :=
    ∀ {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k), Standing K →
    ((meanVec (K.μ.prod K.μ) (fun uv => populationScore K uv.1 uv.2) = 0) ∧
    (∀ N : ℕ, 2 ≤ N →
      (∀ d : Dyad N, meanVec (unitSampleLaw K N) (fun ω => score (design K ω d) (epsilon K ω d)) = 0) ∧
      (∀ d f : Dyad N, ¬overlap d f →
        meanMat (unitSampleLaw K N) (fun ω => outer (score (design K ω d) (epsilon K ω d))
          (score (design K ω f) (epsilon K ω f))) = 0) ∧
      varMat (unitSampleLaw K N) (scoreSum K) = correctedSigma K N ∧
      let M := varMat (unitSampleLaw K N) (fun ω => ∑ d : Dyad N,
        score (design K ω d) (conditionalResidualMean K d ω))
      varMat (unitSampleLaw K N) (scoreSum K) = (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) + M ∧
      M.PosSemidef ∧
      (varMat (unitSampleLaw K N) (scoreSum K) = (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) ↔ M = 0) ∧
      varMat (unitSampleLaw K N) (scoreSum K) - printedSigma K N =
        M + (∑ d : Dyad N, ∑ f : Dyad N, if ¬overlap d f then conditionalTerm K d f else 0) ∧
      correctedSigma K N = (Dreal N) • scoreH K +
        ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • projectionGamma K) ∧
    (projectionGamma K).PosSemidef ∧
    Tendsto (trueTarget K) atTop (𝓝 (limitingTarget K))) ∧
    (∀ N : ℕ, 2 ≤ N → correctedSigma K N = (∑ d : Dyad N, ∑ f : Dyad N,
      if overlap d f then meanMat (unitSampleLaw K N) (fun ω =>
        (MeasureTheory.condExp (designSigma K) (unitSampleLaw K N)
          (fun w => epsilon K w d*epsilon K w f) ω) •
          outer (design K ω d) (design K ω f)) else 0) ∧
    ((∀ d : Dyad N, conditionalResidualMean K d =ᵐ[unitSampleLaw K N] 0) →
      varMat (unitSampleLaw K N) (fun ω => ∑ d : Dyad N,
        score (design K ω d) (conditionalResidualMean K d ω)) = 0))

/-- The packaged mathematical content of P018-T3. -/
def T3Statement : Prop :=
    (Standing signKernel ∧ SampleRank signKernel ∧ Proposition1Extra signKernel ∧
    populationBeta signKernel = 0 ∧
    (∀ N : ℕ, 4 ≤ N → trueTarget signKernel N = !![4] ∧
      meanMat (unitSampleLaw signKernel N) (fun ω =>
        meat members (fun d => score (design signKernel ω d)
          (fittedResidual (design signKernel ω) (response signKernel ω) d))) =
          !![((N : ℝ)-1)*((N : ℝ)-2)*((N : ℝ)-3)] ∧
      (∫ ω, (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 ∂ unitSampleLaw signKernel N) =
        4*((N : ℝ)-2)*((N : ℝ)-3)/((N : ℝ)^2*((N : ℝ)-1))) ∧
    Tendsto (fun N : ℕ => (∫ ω,
      (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 ∂ unitSampleLaw signKernel N)-4)
      atTop (𝓝 (-4)) ∧
    inProbability (unitSampleLaw signKernel) (fun N ω =>
      (N : ℝ) • sampleVariance members (design signKernel ω) (response signKernel ω) - (!![4] : Mat 1))) ∧
    ((∀ N : ℕ, (∫ _ : Unit, (1 : ℝ)-1 ∂ Measure.dirac ()) = 0 ∧
      ProbabilityTheory.variance (fun _ : Unit => (N : ℝ)*1) (Measure.dirac ()) = 0) ∧
    ¬Tendsto (fun N : ℕ => (N : ℝ)*1-1) atTop (𝓝 0) ∧
    ¬inProbability (fun _ : ℕ => Measure.dirac ())
      (fun (N : ℕ) (_ : Unit) => (N : ℝ)*1-1)) ∧
    ((∀ N : ℕ, 1 ≤ N → IsProbabilityMeasure (inverseSpikeLaw N)) ∧
    inProbability inverseSpikeLaw (fun _ x => x-1) ∧
    (∀ N : ℕ, 1 ≤ N → (∫ x, x ∂ inverseSpikeLaw N) = 2-(N : ℝ)⁻¹ ∧
      ProbabilityTheory.variance id (inverseSpikeLaw N) =
        (N : ℝ)-3+3/(N : ℝ)-1/(N : ℝ)^2) ∧
    Tendsto (fun N : ℕ => ∫ x, x ∂ inverseSpikeLaw N) atTop (𝓝 2) ∧
    Tendsto (fun N : ℕ => ProbabilityTheory.variance id (inverseSpikeLaw N)) atTop atTop) ∧
    (fairCov8 (fun u => signResidual8 u 0 1*signResidual8 u 0 2)
      (fun u => signResidual8 u 3 4*signResidual8 u 3 5) = 7/16 ∧
    fairCov8 (fun u => (u 0+u 1)*(u 0+u 2)) (fun u => (u 3+u 4)*(u 3+u 5)) = 0 ∧
    fairCov8 (fun u => signResidual8 u 0 1*signResidual8 u 0 2)
      (fun u => signResidual8 u 0 3*signResidual8 u 0 4) = -1/16) ∧
    Standing inverseKernel ∧
    inProbability (unitSampleLaw inverseKernel) (fun N ω =>
      ((Dreal N)⁻¹ • sampleGram (design inverseKernel ω))⁻¹ - (populationGram inverseKernel)⁻¹) ∧
    (∃ N0 : ℕ, 3 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (∀ᵐ ω ∂ unitSampleLaw inverseKernel N, (sampleGram (design inverseKernel ω)).det ≠ 0) ∧
      (∀ m : ℕ, 1 ≤ m → ENNReal.ofReal (Real.exp (2*m)/(4*(m : ℝ)^N)) ≤
        ∫⁻ ω, ENNReal.ofReal (matrixOperatorNorm
          (((Dreal N)⁻¹ • sampleGram (design inverseKernel ω))⁻¹)) ∂ unitSampleLaw inverseKernel N) ∧
      (∫⁻ ω, ENNReal.ofReal (matrixOperatorNorm
        (((Dreal N)⁻¹ • sampleGram (design inverseKernel ω))⁻¹)) ∂ unitSampleLaw inverseKernel N) = ∞)

/-- The packaged mathematical content of P018-T4. -/
def T4Statement : Prop :=
    (∀ {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k), Standing K → inProbability (unitSampleLaw K) (fun N ω =>
      (N : ℝ) • sampleVariance members (design K ω) (response K ω) - trueTarget K N)) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Z : Ω → ℝ), MemLp Z 2 μ → ∀ V c : ℝ, 0 < c → (μ {ω | c < |Z ω - V|}).toReal ≤
      (c⁻¹)^2 * (ProbabilityTheory.variance Z μ + ((∫ ω, Z ω ∂ μ)-V)^2)) ∧
    (∀ {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
      (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
      (Z : ∀ N, Ω N → ℝ), (∀ N, MemLp (Z N) 2 (μ N)) → ∀ V : ℝ,
      Tendsto (fun N => (∫ ω, Z N ω ∂ μ N)-V) atTop (𝓝 0) →
      Tendsto (fun N => ProbabilityTheory.variance (Z N) (μ N)) atTop (𝓝 0) →
      ∀ c : ℝ, 0 < c → Tendsto (fun N => (μ N {ω | c < |Z N ω-V|}).toReal)
        atTop (𝓝 0))

end SAP.P018a
