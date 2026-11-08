import SAP.P001e.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e
universe u v
noncomputable section

def spikeResponse (d : ℝ) : ℝ := if d=1/2 then 1 else 0

def exampleCoef : Fin 4 → ℝ := ![13563/2437,6178/2437,-759/2437,-1778/2437]

def exampleY : Fin 6 → ℝ := ![2,5,3,10,2,0]

def exampleD : Fin 6 → ℝ := ![1,0,1,1,1,0]

def exampleX1 : Fin 6 → ℝ := ![1,8,10,3,5,7]

def exampleX2 : Fin 6 → ℝ := ![7,2,3,1,2,0]

def examplePrediction (x1 x2 d : ℝ) : ℝ := exampleCoef 0+exampleCoef 1*d+
  exampleCoef 2*x1+exampleCoef 3*x2

def partialImputation (x1 : Fin 6 → ℝ) : ℝ :=
  (∑ i,if exampleD i=1 then exampleY i-examplePrediction (x1 i) (exampleX2 i) 0
    else examplePrediction (x1 i) (exampleX2 i) 1-exampleY i)/6

def exampleDesign : Matrix (Fin 6) (Fin 4) ℝ :=
  fun i => ![1,exampleD i,exampleX1 i,exampleX2 i]

def integratedModelMean {K τ : ℕ} (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (d : ℝ) (x : Fin K → ℝ) (θ : Fin τ → ℝ) : ℝ := ∫ y,y*g y d x θ

def fittedPotentialAverage {n K τ : ℕ} (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (d : ℝ) (X : Fin n → Fin K → ℝ) (θ : Fin τ → ℝ) : ℝ :=
  (∑ i,integratedModelMean g d (X i) θ)/(n : ℝ)

def logisticProbability (a b x : ℝ) : ℝ := Real.exp (a+b*x)/(1+Real.exp (a+b*x))

def cellLogLikelihood (N r : Fin 3 → ℝ) (a b : ℝ) : ℝ :=
  ∑ j, (r j*Real.log (logisticProbability a b ((![-1,0,1] : Fin 3 → ℝ) j))+
    (N j-r j)*Real.log (1-logisticProbability a b ((![-1,0,1] : Fin 3 → ℝ) j)))

def cellSize : Fin 3 → ℝ := fun _ => 4

def cellResponses : Fin 3 → ℝ :=![2,3,2]

def cellOutcomeSum : Fin 3 → ℝ :=![3/4,3/2,3/4]

def boundsRecorded : Fin 6 → ℝ := ![1,-99,1,0,1,-99]

def boundsResponse : Fin 6 → ℝ := ![1,0,1,1,1,0]

def postOutcome : Fin 6 → ℝ := ![0,1,1,0,1,1]

def postCovariate : Fin 6 → ℝ := ![0,0,1,0,1,1]

def postAssignment : Fin 6 → ℝ := ![0,0,0,1,1,1]

def postCovariate0 : Fin 6 → ℝ := ![0,0,1,0,0,1]

def postCovariate1 : Fin 6 → ℝ := ![0,1,1,0,1,1]

def finiteProbability {n : ℕ} (w : Fin n → ℝ) (A : Fin n → Prop) : ℝ :=
  ∑ i, if A i then w i else 0

def finiteExpectation {n : ℕ} (w Y : Fin n → ℝ) : ℝ := ∑ i, w i * Y i

def FiniteCondIndependent {n : ℕ} {E F G : Type*} (w : Fin n → ℝ)
    (Y : Fin n → E) (Z : Fin n → F) (X : Fin n → G) : Prop :=
  ∀ (x : G) (y : E) (z : F), 0 < finiteProbability w (fun i => X i=x) →
    finiteProbability w (fun i => X i=x ∧ Y i=y ∧ Z i=z) *
      finiteProbability w (fun i => X i=x) =
    finiteProbability w (fun i => X i=x ∧ Y i=y) *
      finiteProbability w (fun i => X i=x ∧ Z i=z)

def finiteCellMean {n : ℕ} (w Y X D : Fin n → ℝ) (x d : ℝ) : ℝ :=
  (∑ i, if X i=x ∧ D i=d then w i*Y i else 0) /
    finiteProbability w (fun i => X i=x ∧ D i=d)

def postWeights : Fin 6 → ℝ := fun _ => 1/6

def fullImputation (x1 : Fin 6 → ℝ) : ℝ :=
  (∑ i, (examplePrediction (x1 i) (exampleX2 i) 1 -
    examplePrediction (x1 i) (exampleX2 i) 0))/6

def cellIPW {E : Type*} [Fintype E] (S q : E → ℝ) (n : ℝ) : ℝ :=
  (∑ x, S x/q x)/n

def cellPlugIn {E : Type*} [Fintype E] (N r S : E → ℝ) (n : ℝ) : ℝ :=
  (∑ x, N x*S x/r x)/n

def cellWeightMean {E : Type*} [Fintype E] (r q : E → ℝ) (n : ℝ) : ℝ :=
  (∑ x, r x/q x)/n

def cellStabilized {E : Type*} [Fintype E] (S r q : E → ℝ) (n : ℝ) : ℝ :=
  cellIPW S q n / cellWeightMean r q n

/-- Only positive-probability covariate cells require conditional means. -/
def standardizedDoseMean {Ω E : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → E) (D Y : Ω → ℝ) (d : ℝ) : ℝ :=
  ∑' x : E, if 0 < probability μ {ω | X ω=x} then
    cellMean μ (fun ω => (X ω,D ω)) Y (x,d) * probability μ {ω | X ω=x} else 0

def postAdjustedContrast : ℝ :=
  (finiteCellMean postWeights postOutcome postCovariate postAssignment 0 1 *
      finiteProbability postWeights (fun i => postCovariate i=0) +
    finiteCellMean postWeights postOutcome postCovariate postAssignment 1 1 *
      finiteProbability postWeights (fun i => postCovariate i=1)) -
  (finiteCellMean postWeights postOutcome postCovariate postAssignment 0 0 *
      finiteProbability postWeights (fun i => postCovariate i=0) +
    finiteCellMean postWeights postOutcome postCovariate postAssignment 1 0 *
      finiteProbability postWeights (fun i => postCovariate i=1))

end
end SAP.P001e
