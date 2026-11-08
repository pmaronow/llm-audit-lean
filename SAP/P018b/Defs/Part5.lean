import SAP.P018b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

/-- A bounded iid two-record model with divergent moments and valid distributional limits. -/
def T19Statement : Prop :=
  ∃ (U : Type) (mU : MeasurableSpace U) (R : RepeatedKernel U 2) (v : ℝ),
    RepeatedStanding R ∧ (∀ N d, R.T N d = 2) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ ω : Fin N → U, (repeatedGram R ω).det > 0 ∧
      (∀ d : Dyad N, ∀ t : Fin (R.T N d), |repeatedY R ω d t -
        dot (repeatedX R ω d t) (repeatedOLS R ω)| ≤ 8)) ∧
    (∀ N : ℕ, 3 ≤ N →
      (∫⁻ ω, ENNReal.ofReal ((repeatedOLS R ω 1)^2) ∂ repeatedLaw R N) = ∞ ∧
      (∫⁻ ω, ENNReal.ofReal |repeatedOLS R ω 1| ∂ repeatedLaw R N) = ∞) ∧
    (∀ N : ℕ, 4 ≤ N →
      (∫⁻ ω, ENNReal.ofReal (max ((repeatedVariance R ω) 1 1) 0) ∂ repeatedLaw R N) = ∞ ∧
      (∫⁻ ω, ENNReal.ofReal (max (-((repeatedVariance R ω) 1 1)) 0) ∂ repeatedLaw R N) < ∞) ∧
    (0 < v ∧ inProbability (repeatedLaw R) (fun N ω =>
      (N : ℝ) • repeatedVariance R ω - (!![4+v,-v;-v,v] : Mat 2)) ∧
      ∃ ν : Measure (Vec 2), centeredNormalLaw ν (!![4+v,-v;-v,v]) ∧
        weakLimit (repeatedLaw R)
          (fun N ω => Real.sqrt N • repeatedOLS R ω) ν)

def T20Statement : Prop :=
  ∀ {Ω : ℕ → Type} [∀ N : ℕ, MeasurableSpace (Ω N)] {k : ℕ}
    (μ : ∀ N : ℕ, Measure (Ω N)) (hμ : ∀ N : ℕ, IsProbabilityMeasure (μ N))
    (ξ : ∀ N : ℕ, Ω N → Vec k) (ν : Measure (Vec k)),
    weakLimit μ ξ ν → uiSquares μ ξ → (∀ a, MemLp (fun x : Vec k => x a) 2 ν) →
    meanVec ν id = 0 →
    Tendsto (fun N : ℕ => meanVec (μ N) (ξ N)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => varMat (μ N) (ξ N)) atTop (𝓝 (varMat ν id))

def T21Statement : Prop :=
  ∀ {U : Type} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k), Standing K → 2 ≤ N →
    (∑ d : Dyad N, (conditionalTerm K d d + ∑ f ∈ neighbors d, conditionalTerm K d f)) =
      printedSigma K N

def T22Statement : Prop :=
  ∀ N T : ℕ, 2 ≤ N → 1 ≤ T →
    IsGaussian ((simulationLaw N T).map (fun ω =>
      fun dt : Dyad N × Fin T => simulationError ω dt.1 dt.2)) ∧
    IndepFun (fun ω => fun dt : Dyad N × Fin T => simulationError ω dt.1 dt.2)
      (fun ω => fun i : Fin N => simulationX ω i) (simulationLaw N T) ∧
    (∀ d t, (∫ ω, simulationError ω d t ∂ simulationLaw N T) = 0) ∧
    (∀ d f : Dyad N, ∀ t u : Fin T, ProbabilityTheory.covariance
      (fun ω => simulationError ω d t) (fun ω => simulationError ω f u) (simulationLaw N T) =
        ((members d ∩ members f).card : ℝ) + (if d=f ∧ t=u then 1 else 0)) ∧
    (∀ d t, MeasureTheory.condExp (MeasurableSpace.comap
      (fun ω : SimulationIndex N T → ℝ => fun i : Fin N => simulationX ω i) inferInstance)
      (simulationLaw N T) (fun ω => simulationError ω d t) =ᵐ[simulationLaw N T] 0)

def T23Statement : Prop :=
  (∀ {k : ℕ} (x : Vec k) (y : ℝ) (β : Vec k),
    (0 < expit (dot x β) ∧ expit (dot x β) < 1) ∧
    (∀ a, HasDerivAt (fun t => logLikelihood x y (Function.update β a t))
      (logisticScore x y β a) (β a)) ∧
    logisticNegativeJacobian x y β =
      (expit (dot x β)*(1-expit (dot x β))) • outer x x ∧
    (logisticNegativeJacobian x y β).PosSemidef ∧
    outer (logisticScore x y β) (logisticScore x y β) =
      ((y-expit (dot x β))^2) • outer x x) ∧
  (∀ {E : Type} [Fintype E] {k : ℕ} (X : E → Vec k) (Y : E → ℝ) (β : Vec k),
    (∑ d, logisticNegativeJacobian (X d) (Y d) β) = logisticBread X β ∧
    (∑ d, outer (logisticScore (X d) (Y d) β) (logisticScore (X d) (Y d) β)) =
      ∑ d, ((Y d-expit (dot (X d) β))^2) • outer (X d) (X d)) ∧
  (∀ {Ω Θ : Type} [MeasurableSpace Ω] {k : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ψ : Ω → Θ → Vec k) (θ : Θ),
    (∀ a, MemLp (fun ω => ψ ω θ a) 2 μ) → (genericScoreMeat μ ψ θ).PosSemidef)

def tableExactFacts : Prop :=
tableSE.map (fun r => r.2.2/r.1) =
      [265/69,7/2,3,24749/10734,4,5/2,51/13,172/39,840/211] ∧
    tableSE.map (fun r => (r.2.2+1/2000)/(r.1-1/2000)) =
      [531/137,47/13,31/9,49499/21467,17/3,53/21,205/51,689/155,1681/421]
def tableMagnitudeFacts : Prop :=
(24749/1000 : ℚ)/(10734/1000) = 24749/10734 ∧
    (344/1000 : ℚ)/(78/1000) = 172/39 ∧
    (∀ r ∈ tableSE, 24749/10734 ≤ r.2.2/r.1 ∧ r.2.2/r.1 ≤ 172/39 ∧ r.2.2/r.1 < 5 ∧
      r.1 < r.2.1 ∧ r.2.1 < r.2.2 ∧ 185/181 ≤ r.2.2/r.2.1 ∧ r.2.2/r.2.1 ≤ 86/47) ∧
    (∀ (r : ℚ × ℚ × ℚ), r ∈ tableSE → ∀ h d : ℝ,
      (r.1 : ℝ)-1/2000 ≤ h → d ≤ (r.2.2 : ℝ)+1/2000 → d/h < 10) ∧
    (11/8 : ℝ) < 41/25

def T24Statement : Prop := tableExactFacts ∧ tableMagnitudeFacts ∧
  (∀ r ∈ tableSE, 0 < (r.1 : ℝ)-1/2000 ∧
    (r.2.2 : ℝ)+1/2000 < 10*((r.1 : ℝ)-1/2000) ∧
    ((r.2.2 : ℝ)+1/2000)/((r.1 : ℝ)-1/2000) ≤ 17/3) ∧
  (∀ b dyadic hc : ℝ, (21/2000 ≤ |b| ∧ |b| ≤ 23/2000) →
    (15/2000 ≤ dyadic ∧ dyadic ≤ 17/2000) → (3/2000 ≤ hc ∧ hc ≤ 5/2000) →
    |b|/dyadic ≤ 23/15 ∧ (23/15 : ℝ) < 41/25 ∧
    21/5 ≤ |b|/hc ∧ (41/25 : ℝ) < 21/5) ∧
  (185/1000 : ℚ)/(181/1000) = 185/181 ∧
  (344/1000 : ℚ)/(188/1000) = 86/47 ∧
  (11/1000 : ℝ)/(8/1000) = 11/8

end SAP.P018b
