import SAP.P023.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P023
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def T1Statement : Prop := LinearWitness ∧
  close (1/200 : ℝ) linearX = {2, 3} ∧
  rd (1/200 : ℝ) linearX linearD linearY = linearY 3 - linearY 2 ∧
  Localized (1/200 : ℝ) linearX (rd (1/200 : ℝ) linearX linearD) ∧
  (∀ (y y' : Fin 6 → ℝ) (β β' : ℝ),
    (∀ i ∈ close (1/200 : ℝ) linearX, y i = y' i) →
    CoarsenedOLS (1/200 : ℝ) linearX linearD y β →
    CoarsenedOLS (1/200 : ℝ) linearX linearD y' β' → β = β')

def T2Statement : Prop := DegreeSevenWitness ∧
  close (1/5 : ℝ) degree7X = {7, 8} ∧
  rd (1/5 : ℝ) degree7X degree7D degree7Y = degree7Y 8 - degree7Y 7

def T3Statement : Prop := PrintedBinEquivalence ∧ CoarsenedWeights ∧
  CoarsenedLocalization ∧ FinitePolynomialWeights ∧ FiniteNonlocality ∧
  ConditionalMoments ∧ UniformIllustration ∧ SharedConsistency

def T4Statement : Prop := SigmoidPopulation ∧ SigmoidFit ∧ SigmoidSampling ∧
  UniformSymmetry ∧ residualVariance uniformMargins 1 = 1/16 ∧
  residualVariance uniformMargins 7 = 1225/65536 ∧
  (∀ J, 1 ≤ J →
    let ν := witnessLaw uniformMargins (sigmoid (1/20) (1/10000))
    (fittedRisk ν J - 1/100) / fittedRisk ν J ≤ 1/120000) ∧
  (∀ a : ℝ, Tendsto (fun η : ℝ => a^2*η/3)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
  (∀ (a : ℝ) (J : ℕ), ∃ c : Fin (J+2) → ℝ,
    ∀ x : ℝ, predict (polynomialDesign J (fun x : ℝ => x) party) c x =
      1/2 + a*(2*party x-1))

def T5Statement : Prop := ClusteredPopulation ∧ ClusteredFit ∧
  (∀ J : ℕ, (0 : Polynomial ℝ).natDegree ≤ J ∧
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |clusterSmooth (1/1000) x - (0 : Polynomial ℝ).eval x| ≤ 1/2000) ∧
  Tendsto (fun d : ℝ => d/2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- No continuous function with the prescribed growing bias subsequence is Lipschitz. -/
def NoLipschitzContinuityCounterexample : Prop :=
  ∀ (h : ℝ → ℝ) (degrees : ℕ → ℕ),
    ContinuousOn h (Set.Icc (-1) 1) → h 0 = 0 →
    (∀ x ∈ Set.Icc (-1) 1, |h x| ≤ 1/12) → StrictMono degrees →
    (∀ m, 1 ≤ m → biasFunctional uniformMargins (degrees m) h ≥ (m : ℝ)/4) →
    ¬ (∃ L : ℝ, ∀ x ∈ Set.Icc (-1) 1, ∀ x' ∈ Set.Icc (-1) 1,
      |h x-h x'| ≤ L*|x-x'|)

def T6Statement : Prop := ProbabilityLaw uniformMargins ∧
  MarginSupport uniformMargins ∧ ContinuityWitness ∧ NoLipschitzContinuityCounterexample

def T7Statement : Prop := PopulationBias ∧ UniformConstants ∧ FinitePolynomialWeights ∧ FiniteConditionalBias

def T8Statement : Prop := CorrectedAsymptotics

def T9Statement : Prop := PairIndexedAppendix

def T10Statement : Prop := CoarsenedLocalization ∧ PolynomialLocalizationRefutation

def T11Statement : Prop := PropositionOne

def T12Statement : Prop := ¬ PrintedPropositionTwo
end
end SAP.P023
