import Mathlib
import SAP.P015b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P015b

universe u v

noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal
attribute [local instance] Classical.propDecidable

def binaryProfile : Fin 4 → ℝ := ![0,0,1,1]

def binaryTreatment : Fin 4 → ℝ := ![0,1,0,1]

def firstGroupDesign : Matrix (Fin 3) (Fin 2) ℝ := !![1,0;1,1;1,1]

def secondGroupDesign : Matrix (Fin 3) (Fin 2) ℝ := !![1,0;1,0;1,1]

def firstGroupPrecision : Matrix (Fin 2) (Fin 2) ℝ := !![5/8,1/4;1/4,1/2]

def secondGroupPrecision : Matrix (Fin 2) (Fin 2) ℝ := !![5/7,1/7;1/7,3/7]

def poolingInverse : Matrix (Fin 2) (Fin 2) ℝ := !![52/61,-22/61;-22/61,75/61]

def leveragePopulation : Fin 4 → ℝ := ![1/20,1/5,11/20,1/5]

def leverageDesign : Matrix (Fin 4) (Fin 3) ℝ := fun i => ![1,binaryTreatment i,binaryProfile i]

def leverageMoment : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j k => finiteMean leveragePopulation (fun i => leverageDesign i j*leverageDesign i k)

def leverageMomentInverse : Matrix (Fin 3) (Fin 3) ℝ :=
  !![52/7,-30/7,-44/7;-30/7,75/14,20/7;-44/7,20/7,48/7]

def scaledLeverage (i : Fin 4) : ℝ := dotProduct (leverageDesign i) (leverageMoment⁻¹.mulVec (leverageDesign i))

def RoundsWithin (x display resolution : ℝ) : Prop := |x-display|  <  resolution/2

def PoolingCounterexample : Prop :=
    (firstGroupDesign.transpose*firstGroupDesign).det = 2 ∧
    (secondGroupDesign.transpose*secondGroupDesign).det = 2 ∧
    sampleCoefficients firstGroupDesign ![0,0,0] = ![0,0] ∧ sampleCoefficients secondGroupDesign ![2,2,2] = ![2,0] ∧
    firstGroupPrecision = (1+(firstGroupDesign.transpose*firstGroupDesign)⁻¹)⁻¹ ∧
    secondGroupPrecision = (1+(secondGroupDesign.transpose*secondGroupDesign)⁻¹)⁻¹ ∧
    (firstGroupPrecision+secondGroupPrecision)⁻¹ = poolingInverse ∧
    (firstGroupPrecision+secondGroupPrecision)⁻¹.mulVec (firstGroupPrecision.mulVec (sampleCoefficients firstGroupDesign ![0,0,0])+secondGroupPrecision.mulVec (sampleCoefficients secondGroupDesign ![2,2,2])) = ![68/61,-10/61] ∧
    (∀ a₁ a₂ : ℝ, a₁*0+a₂*0 ≠ -10/61) ∧
    (∀ t₁ t₂ : Fin 2 → ℝ,
      ((firstGroupPrecision+secondGroupPrecision)⁻¹.mulVec (firstGroupPrecision.mulVec t₁+secondGroupPrecision.mulVec t₂)) 1 =
        (5/61)*t₁ 0-(5/61)*t₂ 0+(32/61)*t₁ 1+(29/61)*t₂ 1)

def RawPoolingCounterexample : Prop :=
    let V₁ : Matrix (Fin 3) (Fin 3) ℝ :=
      firstGroupDesign*(1 : Matrix (Fin 2) (Fin 2) ℝ)*firstGroupDesign.transpose+1
    let V₂ : Matrix (Fin 3) (Fin 3) ℝ :=
      secondGroupDesign*(1 : Matrix (Fin 2) (Fin 2) ℝ)*secondGroupDesign.transpose+1
    let raw := (firstGroupDesign.transpose*V₁⁻¹*firstGroupDesign+secondGroupDesign.transpose*V₂⁻¹*secondGroupDesign)⁻¹.mulVec
      ((firstGroupDesign.transpose*V₁⁻¹).mulVec 0+(secondGroupDesign.transpose*V₂⁻¹).mulVec (fun _ => 2))
    (1 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef ∧
    raw=![68/61,-10/61] ∧ sampleCoefficients firstGroupDesign 0 1=0 ∧ sampleCoefficients secondGroupDesign (fun _ => 2) 1=0 ∧
    (∀ a₁ a₂ : ℝ, raw 1≠a₁*sampleCoefficients firstGroupDesign 0 1+a₂*sampleCoefficients secondGroupDesign (fun _ => 2) 1)

def T9Statement : Prop := PoolingCounterexample ∧ RawPoolingCounterexample

def MatrixPooling : Prop :=
  ∀ (G q : ℕ) (hG : 1  ≤  G) (hq : 1  ≤  q)
    (n : Fin G → ℕ) (Z : ∀ g, Matrix (Fin (n g)) (Fin q) ℝ)
    (y : ∀ g, Fin (n g) → ℝ) (S : Matrix (Fin q) (Fin q) ℝ)
    (σ₂ : Fin G → ℝ) (hS : S.PosSemidef)
    (hσ : ∀ g, 0  <  σ₂ g) (hQ : ∀ g, ((Z g).transpose * Z g).det ≠ 0),
    let P := fun g => precisionMatrix S ((Z g).transpose*Z g) (σ₂ g)
    let H := ∑ g, P g
    let A := fun g => H⁻¹*P g
    let t := fun g => sampleCoefficients (Z g) (y g)
    let V : ∀ g, Matrix (Fin (n g)) (Fin (n g)) ℝ := fun g => Z g*S*(Z g).transpose+σ₂ g • 1
    (∀ m, precisionLoss P t (pooledCoefficients P t)  ≤  precisionLoss P t m) ∧
    (∀ m, precisionLoss P t m = precisionLoss P t (pooledCoefficients P t) → m = pooledCoefficients P t) ∧
    pooledCoefficients P t = ∑ g, (A g).mulVec (t g) ∧ (∑ g, A g) = 1 ∧
    (∀ g, (Z g).transpose*(V g)⁻¹*Z g = P g ∧
      ((Z g).transpose*(V g)⁻¹).mulVec (y g) = (P g).mulVec (t g)) ∧
    pooledCoefficients P t = (∑ g, (Z g).transpose*(V g)⁻¹*Z g)⁻¹.mulVec
      (∑ g, ((Z g).transpose*(V g)⁻¹).mulVec (y g)) ∧
    (∀ b : Fin q, (∀ g j, j ≠ b → (P g) b j = 0 ∧ (P g) j b = 0) →
      (∀ g, 0  <  (P g) b b) →
      ∀ g j, A g b j = if j=b then P g b b/(∑ h, P h b b) else 0)

def ScalarPoolingCriterion : Prop :=
  ∀ (G q : ℕ) (hG : 1 ≤ G) (hq : 1 ≤ q)
    (n : Fin G → ℕ) (Z : ∀ g, Matrix (Fin (n g)) (Fin q) ℝ)
    (S : Matrix (Fin q) (Fin q) ℝ) (σ₂ : Fin G → ℝ) (hS : S.PosSemidef)
    (hσ : ∀ g, 0 < σ₂ g) (hQ : ∀ g, ((Z g).transpose*Z g).det≠0)
    (a : Fin G → ℝ) (b : Fin q),
    let P := fun g => precisionMatrix S ((Z g).transpose*Z g) (σ₂ g)
    let A := fun g => (∑ h, P h)⁻¹*P g
    (∀ t : Fin G → Fin q → ℝ, (∑ g, ∑ j, A g b j*t g j)=∑ g, a g*t g b) ↔
      ∀ g j, A g b j=if j=b then a g else 0

def T10Statement : Prop := MatrixPooling ∧ ScalarPoolingCriterion

def T20Statement : Prop :=
    IsFiniteLaw leveragePopulation ∧
    finiteCellMean leveragePopulation binaryProfile (finiteWeight leveragePopulation binaryProfile binaryTreatment) 0 = 4/25 ∧
    finiteCellMean leveragePopulation binaryProfile (finiteWeight leveragePopulation binaryProfile binaryTreatment) 1 = 44/225 ∧
    leverageMoment = !![1,2/5,3/4;2/5,2/5,1/5;3/4,1/5,3/4] ∧
    leverageMoment⁻¹ = leverageMomentInverse ∧
    scaledLeverage = ![52/7,59/14,12/7,59/14] ∧
    finiteCellMean leveragePopulation binaryProfile scaledLeverage 0 = 34/7 ∧
    finiteCellMean leveragePopulation binaryProfile scaledLeverage 1 = 50/21 ∧
    (44/225 : ℝ)/(4/25) = 11/9 ∧ (1 : ℝ)-(50/21)/(34/7) = 26/51 ∧
    RoundsWithin (4/25) (160/1000) (1/1000) ∧ RoundsWithin (44/225) (196/1000) (1/1000) ∧
    RoundsWithin (52/7) (743/100) (1/100) ∧ RoundsWithin (59/14) (421/100) (1/100) ∧
    RoundsWithin (12/7) (171/100) (1/100) ∧ RoundsWithin (34/7) (486/100) (1/100) ∧
    RoundsWithin (50/21) (238/100) (1/100) ∧
    RoundsWithin (100*(11/9-1)) 22 1 ∧ RoundsWithin (100*26/51) 51 1

def T14Statement : Prop :=
  ∀ (α β x d d' p : ℝ)
    (hβ : β ≠ 0) (hd : d ≠ d'),
    ¬ (p=sigmoidMean (α+β*d+x) ∧ p=sigmoidMean (α+β*d'+x))

def AffinePredictorIdentity : Prop :=
  ∀ (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K + 2)) ℝ)
    (hW : ∀ i, W i 0 = 1) (b c : ℝ)
    (θ : Fin (K + 2) → ℝ) (Y : Fin N → ℝ),
    (∀ i, W.mulVec (affineCoefficients 0 b c θ) i =
      b + c * W.mulVec θ i) ∧
    W.transpose.mulVec (fun i => Y i - b - c * W.mulVec θ i) =
      W.transpose.mulVec (fun i =>
        Y i - W.mulVec (affineCoefficients 0 b c θ) i)

def FullRankLogisticLinearization : Prop :=
  ∀ (N K : ℕ) (W : Matrix (Fin N) (Fin (K+2)) ℝ)
    (Y : Fin N → ℝ) (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (hQ : (W.transpose*W).det ≠ 0) (b c : ℝ) (hc : c ≠ 0),
    (∀ θ v : Fin (K+2) → ℝ,
      HasDerivAt (fun t => binaryLogLikelihood W (fun _ => 1) Y sigmoidMean (fun j => θ j+t*v j))
        (∑ i, (Y i-sigmoidMean (W.mulVec θ i))*W.mulVec v i) 0) ∧
    (∃! θ : Fin (K+2) → ℝ, residualEquation W (fun _ => 1) Y (fun a => b+c*a) θ = 0) ∧
    (∀ θ, residualEquation W (fun _ => 1) Y (fun a => b+c*a) θ = 0 →
      affineCoefficients 0 b c θ = sampleCoefficients W Y ∧ sampleCoefficients W Y 1 = c*θ 1)

def T21Statement : Prop := AffinePredictorIdentity ∧ FullRankLogisticLinearization

end
end SAP.P015b
