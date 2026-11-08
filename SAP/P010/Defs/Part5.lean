import SAP.P010.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P010

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology BigOperators

/-! SAP population laws, quantiles, sharpness sets, and explicit witnesses. -/

noncomputable def conditionalLaw {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (μ : Measure Ω) (f : Ω → B) (E : Set Ω) : Measure B :=
  (μ E)⁻¹ • (μ.restrict E).map f

noncomputable def trimmingRatio {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K) : ℝ :=
  (∑ b : Fin K, if b ≠ a then 1 - passRate μ b else 0) / passRate μ a

noncomputable def passerDistribution {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K) : Measure ℝ :=
  conditionalLaw μ response (passed ∩ assigned a)

noncomputable def leftQuantile (ν : Measure ℝ) (u : ℝ) : EReal :=
  sInf {x : EReal | u ≤ (ν {y : ℝ | (y : EReal) ≤ x}).toReal}

noncomputable def realQuantile (ν : Measure ℝ) (u : ℝ) : ℝ := (leftQuantile ν u).toReal

def noAtoms (ν : Measure ℝ) : Prop := ∀ x : ℝ, ν {x} = 0

def fullRealSupport {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∀ l u : ℝ, l < u → 0 < μ {ω | l < f ω ∧ f ω < u}

def allMoments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∀ n : ℕ, Integrable (fun ω => |f ω| ^ n) μ

noncomputable def lowerEndpoint {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K) : ℝ :=
  meanOn μ response ((passed ∩ assigned a) ∩
    {ω | (response ω : EReal) ≤ leftQuantile (passerDistribution μ a) (1 - trimmingRatio μ a)})

noncomputable def upperEndpoint {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K) : ℝ :=
  meanOn μ response ((passed ∩ assigned a) ∩
    {ω | leftQuantile (passerDistribution μ a) (trimmingRatio μ a) ≤ (response ω : EReal)})

def compatiblePopulations {K d : ℕ} (μ ν : Measure (Population K d)) : Prop :=
  populationAssumptions ν ∧ 0 < ν allPass ∧
  ν.map (fun ω => (response ω, check ω, arm ω)) =
    μ.map (fun ω => (response ω, check ω, arm ω))

noncomputable def compatibleMeans {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K) : Set ℝ :=
  {m | ∃ ν : Measure (Population K d), compatiblePopulations μ ν ∧ meanOn ν (potentialOutcome a) allPass = m}

noncomputable def extendedCompatibleMeans {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K) : Set EReal :=
  {m | ∃ x ∈ compatibleMeans μ a, (x : EReal) = m}

noncomputable def passerEssentialInf {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K) : EReal :=
  essInf (fun y : ℝ => (y : EReal)) (passerDistribution μ a)

noncomputable def passerEssentialSup {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K) : EReal :=
  essSup (fun y : ℝ => (y : EReal)) (passerDistribution μ a)

def otherArmsPass {K d : ℕ} (a : Fin K) : Set (Population K d) := {ω | ∀ b, b ≠ a → potentialCheck b ω = true}

noncomputable def potentialTrimShare {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K) : ℝ :=
  (∑ b : Fin K, if b ≠ a then (μ {ω | potentialCheck b ω = false}).toReal else 0) /
    (μ (wouldPass a)).toReal

def tailCoupling (F : Measure ℝ) (p : ℝ) (γ : Measure (ℝ × Bool)) : Prop :=
  IsProbabilityMeasure γ ∧ γ.map Prod.fst = F ∧ (γ {ω | ω.2 = false}).toReal = p

noncomputable def upperTailMean (F : Measure ℝ) (p : ℝ) : ℝ :=
  meanOn F id {y | leftQuantile F p ≤ (y : EReal)}

noncomputable def finitePopulation {n K d : ℕ} (atoms : Fin n → Population K d)
    (mass : Fin n → ℝ≥0∞) : Measure (Population K d) :=
  Measure.sum (fun i => mass i • Measure.dirac (atoms i))

def jointDependenceAtoms : Fin 4 → Population 2 0 :=
  ![(![0,0], ![true,true], 0, fun _ => 0),
    (![1,1], ![true,true], 0, fun _ => 0),
    (![0,1], ![true,true], 1, fun _ => 0),
    (![1,0], ![true,true], 1, fun _ => 0)]

noncomputable def jointDependencePopulation : Measure (Population 2 0) := finitePopulation jointDependenceAtoms (fun _ => ENNReal.ofReal (1/4:ℝ))

def selectionPopulationAtoms : Fin 6 → Population 2 1 :=
  ![(![1,1], ![false,true], 0, fun _ => 0),
    (![0,0], ![true,false], 0, fun _ => 0),
    (![0,0], ![true,true], 0, fun _ => 0),
    (![1,1], ![false,true], 1, fun _ => 0),
    (![0,0], ![true,false], 1, fun _ => 0),
    (![0,0], ![true,true], 1, fun _ => 0)]

noncomputable def selectionPopulation (q : ℝ) : Measure (Population 2 1) :=
  finitePopulation selectionPopulationAtoms (fun i => ENNReal.ofReal (if i.val < 3 then q/3 else (1-q)/3))

noncomputable def unitExponential : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (if 0 < x then Real.exp (-x) else 0))

noncomputable def laplaceDistribution (r : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (r/2 * Real.exp (-r * |x|)))

noncomputable def fairArmDistribution : Measure (Fin 2) :=
  (1/2 : ℝ≥0∞) • Measure.dirac 0 + (1/2 : ℝ≥0∞) • Measure.dirac 1

noncomputable def stratumPopulation (s₁ s₂ : Bool) (F₁ F₂ : Measure ℝ) : Measure (Population 2 0) :=
  ((F₁.prod F₂).prod fairArmDistribution).map
    (fun ω => (![ω.1.1,ω.1.2], ![s₁,s₂], ω.2, fun _ => 0))

noncomputable def missingPassingPopulation (upper : Bool) : Measure (Population 2 0) :=
  (1/4 : ℝ≥0∞) • stratumPopulation true true
    (if upper then unitExponential else unitExponential.map (fun x => -x)) (laplaceDistribution 1) +
  (1/4 : ℝ≥0∞) • stratumPopulation true false
    (if upper then unitExponential.map (fun x => -x) else unitExponential) (laplaceDistribution 1) +
  (1/2 : ℝ≥0∞) • stratumPopulation false true (laplaceDistribution 2) (laplaceDistribution 1)

noncomputable def betaPasserDistribution : Measure ℝ := volume.withDensity
  (fun x => ENNReal.ofReal (if 0 < x ∧ x < 1 then 30*x^2*(1-x)^2 else 0))

noncomputable def heavyTailDistribution : Measure ℝ := volume.withDensity
  (fun x => ENNReal.ofReal (5 / (2*(1+|x|)^6)))

noncomputable def commonOutcomePopulation (s : Bool) (F : Measure ℝ) : Measure (Population 2 0) :=
  (F.prod fairArmDistribution).map (fun ω => (![ω.1,ω.1], ![s,s], ω.2, fun _ => 0))

noncomputable def boundedPasserPopulation : Measure (Population 2 0) :=
  (1/3 : ℝ≥0∞) • commonOutcomePopulation true betaPasserDistribution + (2/3 : ℝ≥0∞) • commonOutcomePopulation false heavyTailDistribution

noncomputable def betaEndpointPopulation (t : ℝ) (upper : Bool) : Measure (Population 2 0) :=
  let E := if upper then Ioo (1-t) 1 else Ioo 0 t
  let q := (betaPasserDistribution E).toReal
  let F := conditionalLaw betaPasserDistribution id E
  let G := conditionalLaw betaPasserDistribution id (Ioo 0 1 \ E)
  ENNReal.ofReal (q/3) • stratumPopulation true true F F +
  ENNReal.ofReal ((1-q)/3) • stratumPopulation true false G heavyTailDistribution +
  ENNReal.ofReal ((1-q)/3) • stratumPopulation false true heavyTailDistribution G +
  ENNReal.ofReal ((1+q)/3) • stratumPopulation false false heavyTailDistribution heavyTailDistribution

noncomputable def normalCommonPopulation : Measure (Population 2 0) :=
  (4/5 : ℝ≥0∞) • commonOutcomePopulation true (gaussianReal 0 1) +
  (1/5 : ℝ≥0∞) • commonOutcomePopulation false (gaussianReal 0 1)

noncomputable def simulationSubject (s₁ s₂ : Bool) (lam : ℝ) (ω : ℝ × Fin 2) : Population 2 0 :=
  let y := lam*((if s₂ then (1:ℝ) else 0)-(if s₁ then (1:ℝ) else 0)) + ω.1
  (![y,y], ![s₁,s₂], ω.2, fun _ => 0)

noncomputable def simulationPopulation (p₁ p₂ ρ lam σ : ℝ) : Measure (Population 2 0) :=
  let a := p₁*p₂ + ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))
  let base := (gaussianReal 0 ⟨σ^2, sq_nonneg σ⟩).prod fairArmDistribution
  ENNReal.ofReal (1-p₁-p₂+a) • base.map (simulationSubject false false lam) +
  ENNReal.ofReal (p₁-a) • base.map (simulationSubject true false lam) +
  ENNReal.ofReal (p₂-a) • base.map (simulationSubject false true lam) +
  ENNReal.ofReal a • base.map (simulationSubject true true lam)

noncomputable def checkCorrelation {K d : ℕ} (μ : Measure (Population K d)) (a b : Fin K) : ℝ :=
  let p := (μ (wouldPass a)).toReal
  let q := (μ (wouldPass b)).toReal
  ((μ (wouldPass a ∩ wouldPass b)).toReal - p*q) /
    Real.sqrt (p*(1-p)*q*(1-q))

noncomputable def effectIntervalWidth (μ : Measure (Population 2 0)) : ℝ :=
  (upperEndpoint μ 1 - lowerEndpoint μ 0) - (lowerEndpoint μ 1 - upperEndpoint μ 0)

noncomputable def normalMixture (w : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1-w) • gaussianReal 0 1 + ENNReal.ofReal w • gaussianReal (-1) 1

noncomputable def mixtureLowerMean (w : ℝ) : ℝ :=
  meanOn (normalMixture w) id {y | (y : EReal) ≤ leftQuantile (normalMixture w) (3/4)}

noncomputable def mixtureUpperMean (w : ℝ) : ℝ := upperTailMean (normalMixture w) (1/4)

noncomputable def correctedEndpoints {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K) : EReal × EReal :=
  if trimmingRatio μ a < 1 then ((lowerEndpoint μ a : EReal),(upperEndpoint μ a : EReal))
  else (passerEssentialInf μ a,passerEssentialSup μ a)

end SAP.P010
