import Mathlib
import SAP.P015b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P015b

universe u v

noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal
attribute [local instance] Classical.propDecidable

def squareProfile : Fin 6 → ℝ := ![-1,-1,0,0,1,1]

def squareTreatment : Fin 6 → ℝ := ![0,1,0,1,0,1]

def squarePopulation : Fin 6 → ℝ := ![1/4,1/12,1/6,1/6,1/12,1/4]

def squarePropensity (x : ℝ) : ℝ := 1/2+x/4

def squareBaseline (a x : ℝ) : ℝ := 1/4+a*(3*x^2-2)

def squareDesign : Matrix (Fin 6) (Fin 3) ℝ := fun i => ![1,squareTreatment i-squarePropensity (squareProfile i),squareProfile i]

def squarePotential (a ε x u d : ℝ) : ℝ := if u  ≤  squareBaseline a x+ε*(d-squarePropensity x) then 1 else 0

def squareProbability (a ε : ℝ) (i : Fin 6) : ℝ :=
  squareBaseline a (squareProfile i)+ε*(squareTreatment i-squarePropensity (squareProfile i))

def squareMean (η : ℝ) : ℝ := η^2

def squareLogLikelihood (a ε : ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  ∑ i, squarePopulation i*binomialLogLikelihoodSAP squareMean 1 (squareProbability a ε i) (squareDesign.mulVec θ i)

def SquareAdmissible (θ : Fin 3 → ℝ) : Prop := ∀ i, 0  <  squareDesign.mulVec θ i ∧ squareDesign.mulVec θ i  <  1

def SquareMLDerivative (a b : ℝ) : Prop :=
  ∃ θ : ℝ → Fin 3 → ℝ, θ 0 = ![1/2,0,0] ∧
    (∃ r : ℝ, 0  <  r ∧ r  ≤  1/16 ∧ ∀ ε, |ε|  <  r → SquareAdmissible (θ ε) ∧
      (∀ t, SquareAdmissible t → squareLogLikelihood a ε t  ≤  squareLogLikelihood a ε (θ ε)) ∧
      (∀ t, SquareAdmissible t → squareLogLikelihood a ε t = squareLogLikelihood a ε (θ ε) → t = θ ε)) ∧
    HasDerivAt (fun ε => θ ε 1) b 0

def squareUniformLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

def squareUnitLaw : Measure ((ℝ×ℝ)×ℝ) :=
  ∑ i : Fin 6, (squarePopulation i).toNNReal •
    (Measure.dirac (squareProfile i,squareTreatment i)).prod squareUniformLaw

def squareUnitProfile (s : (ℝ×ℝ)×ℝ) : ℝ := s.1.1

def squareUnitTreatment (s : (ℝ×ℝ)×ℝ) : ℝ := s.1.2

def squareUnitUniform (s : (ℝ×ℝ)×ℝ) : ℝ := s.2

def squareUnitOutcome (a ε d : ℝ) (s : (ℝ×ℝ)×ℝ) : ℝ :=
  squarePotential a ε (squareUnitProfile s) (squareUnitUniform s) d

def squareUnitEffect (a ε : ℝ) (s : (ℝ×ℝ)×ℝ) : ℝ :=
  squareUnitOutcome a ε 1 s-squareUnitOutcome a ε 0 s

/-- A genuine square-link ML derivative differs from the first-order OLS derivative. -/
def SquareLinkFailure : Prop :=
  ∃ hunit : IsProbabilityMeasure squareUnitLaw,
  letI : IsProbabilityMeasure squareUnitLaw := hunit
  IsFiniteLaw squarePopulation ∧
  (fun j k => finiteMean squarePopulation (fun i => squareDesign i j*squareDesign i k)) =
    (!![1,0,0;0,5/24,0;0,0,2/3] : Matrix (Fin 3) (Fin 3) ℝ) ∧
  Matrix.det (fun j k => finiteMean squarePopulation
    (fun i => squareDesign i j*squareDesign i k)) ≠ 0 ∧
  SquareMLDerivative (1/16) (120/119) ∧ SquareMLDerivative 0 1 ∧
  (∀ ε, |ε|  ≤  1/16 →
    finiteMean squarePopulation (squareProbability (1/16) ε)=1/4 ∧
    populationCoefficients squarePopulation squareDesign (squareProbability (1/16) ε) 1=ε) ∧
  deriv squareMean (1/2)=1 ∧ (120/119 : ℝ) ≠ 1 ∧
  IsProbabilityMeasure squareUniformLaw ∧ IsProbabilityMeasure squareUnitLaw ∧
  (∀ (a ε : ℝ) (ha : a=0 ∨ a=1/16) (hε : |ε| ≤ 1/16),
    (∀ x ∈ ({-1,0,1} : Finset ℝ), squareUnitLaw {s | squareUnitProfile s=x}=1/3) ∧
    (∀ᵐ s ∂squareUnitLaw, squareUnitTreatment s=0 ∨ squareUnitTreatment s=1) ∧
    (∀ᵐ s ∂squareUnitLaw, 0 ≤ squareUnitUniform s ∧ squareUnitUniform s ≤ 1) ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      squareUnitLaw {s | squareUnitUniform s ≤ u}=ENNReal.ofReal u) ∧
    IndepFun squareUnitUniform (fun s => (squareUnitProfile s,squareUnitTreatment s)) squareUnitLaw ∧
    CondIndepFun (MeasurableSpace.comap squareUnitProfile inferInstance)
      (Measurable.comap_le (show Measurable squareUnitProfile from measurable_fst.fst))
      (fun s => (squareUnitOutcome a ε 0 s,squareUnitEffect a ε s)) squareUnitTreatment squareUnitLaw ∧
    squareUnitLaw[squareUnitTreatment | MeasurableSpace.comap squareUnitProfile inferInstance] =ᵐ[squareUnitLaw]
      (fun s => squarePropensity (squareUnitProfile s)) ∧
    (∀ᵐ s ∂squareUnitLaw, squareUnitOutcome a ε (squareUnitTreatment s) s=
      squareUnitOutcome a ε 0 s+squareUnitEffect a ε s*squareUnitTreatment s) ∧
    squareUnitLaw[(fun s => squareUnitOutcome a ε (squareUnitTreatment s) s) |
      MeasurableSpace.comap (fun s => (squareUnitProfile s,squareUnitTreatment s)) inferInstance] =ᵐ[squareUnitLaw]
      (fun s => squareBaseline a (squareUnitProfile s)+ε*(squareUnitTreatment s-squarePropensity (squareUnitProfile s))) ∧
    (∫ s, squareUnitOutcome a ε (squareUnitTreatment s) s ∂squareUnitLaw)=1/4)

/-- Finite logistic likelihood maximizers solve the residual equation. -/
def LogisticMLStationarity : Prop :=
  ∀ (N K : ℕ) (W : Matrix (Fin N) (Fin (K+2)) ℝ)
    (Y : Fin N → ℝ) (_hY : ∀ i, Y i=0 ∨ Y i=1)
    (θ : Fin (K+2) → ℝ),
    (∀ γ, binaryLogLikelihood W (fun _ => 1) Y sigmoidMean γ  ≤ 
      binaryLogLikelihood W (fun _ => 1) Y sigmoidMean θ) →
    residualEquation W (fun _ => 1) Y sigmoidMean θ=0

def T18Statement : Prop := LogisticMLStationarity ∧ SquareLinkFailure

end
end SAP.P015b
