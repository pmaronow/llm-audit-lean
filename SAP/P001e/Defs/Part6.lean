import SAP.P001e.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e
universe u v
noncomputable section

def PotentialPopulationMean : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : Ω → Fin K → ℝ) (D Y0 Y1 : Ω → ℝ)
   (hX : Measurable X) (hD : Measurable D) (h0 : Integrable Y0 μ) (h1 : Integrable Y1 μ)
   (hbinary : ∀ ω,D ω=0 ∨ D ω=1) (p : (Fin K → ℝ) → ℝ) (hp : IsConditionalMean μ X D p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω) ∧ p (X ω) < 1-ε)
   (hind : CondIndependent μ X hX (fun ω => (Y0 ω,Y1 ω)) D)
   (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ)
   (hinner : ∀ d ∈ ({0,1} : Set ℝ), ∀ᵐ ω ∂μ, Integrable (fun y : ℝ => y*g y d (X ω) θ) volume)
   (hm : IsConditionalMean μ (fun ω => (D ω,X ω))
     (fun ω => Y1 ω*D ω+Y0 ω*(1-D ω)) (fun dx => integratedModelMean g dx.1 dx.2 θ))
   (hmi : ∀ d∈({0,1} : Set ℝ),Integrable (fun ω => integratedModelMean g d (X ω) θ) μ),
  expectation μ Y0=expectation μ (fun ω => integratedModelMean g 0 (X ω) θ) ∧
   expectation μ Y1=expectation μ (fun ω => integratedModelMean g 1 (X ω) θ)

def PotentialEstimator : Prop :=
  ∀ {n K τ : ℕ} (hn : 0 < n)
    (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (d : ℝ) (X : Fin n → Fin K → ℝ) (θ : Fin τ → ℝ) (x : Fin K → ℝ)
    (hi : ∀ i, Integrable (fun y => y*g y d (X i) θ))
    (hx : Integrable (fun y => y*g y d x θ)),
    fittedPotentialAverage g d X θ=(∑ i, ∫ y, y*g y d (X i) θ)/(n : ℝ) ∧
    (∑ _i : Fin n, integratedModelMean g d x θ)/(n : ℝ)=integratedModelMean g d x θ

def T94Statement : Prop := PotentialPopulationMean.{u} ∧ PotentialEstimator

def matchingDonor : Fin 6 → Fin 6 := ![1,0,5,1,5,2]

def matchingControl : Fin 6 → ℝ :=
  fun i => if exampleD i=0 then exampleY i else exampleY (matchingDonor i)

def matchingTreatment : Fin 6 → ℝ :=
  fun i => if exampleD i=1 then exampleY i else exampleY (matchingDonor i)

def MatchingDonors : Prop :=
  UniqueNearest 0 1 nonrespondents ∧ UniqueNearest 2 5 nonrespondents ∧
  UniqueNearest 3 1 nonrespondents ∧ UniqueNearest 4 5 nonrespondents

def T95Statement : Prop :=
  DonorDistances ∧ HotDeckDonors ∧ MatchingDonors ∧
  matchingControl = ![5,5,0,5,0,0] ∧ matchingTreatment = ![2,2,3,10,2,3] ∧
  (∑ i, matchingTreatment i)/6=22/6 ∧ (∑ i, matchingControl i)/6=15/6 ∧
  (∑ i, (matchingTreatment i-matchingControl i))/6=7/6

end
end SAP.P001e
