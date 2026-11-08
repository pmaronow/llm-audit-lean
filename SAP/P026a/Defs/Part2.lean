import SAP.P026a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section

variable {Ω I R : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]

def asymmetricPairLaw : AssignmentDesign (Fin 3) (Fin 2) ℚ where
  weight := fun _ => 1/3
  treatment := ![![false, false], ![false, true], ![true, true]]

def armPopulationVariance (D : AssignmentDesign Ω I R) (a : Bool) (y : I → R) : R :=
  (∑ i, inclusion D a i * (1 - inclusion D a i) * (y i / inclusion D a i)^2) +
  orderedOffDiagonalSum (fun i j => (jointInclusion D a a i j - inclusion D a i * inclusion D a j) *
    (y i / inclusion D a i) * (y j / inclusion D a j))

def populationCrossCovariance (D : AssignmentDesign Ω I R) (x z : I → R) : R :=
  orderedOffDiagonalSum (fun i j => (jointInclusion D true false i j - inclusion D true i * inclusion D false j) *
    (x i / inclusion D true i) * (z j / inclusion D false j)) - ∑ i, x i * z i

def asymmetricSixLaw : AssignmentDesign (Fin 14) (Fin 6) ℚ where
  weight := fun _ => 1/14
  treatment := ![
    ![false,false,false,true,true,true], ![false,false,true,false,true,true],
    ![false,false,true,true,false,true], ![false,false,true,true,true,false],
    ![false,true,false,false,true,true], ![false,true,false,true,false,true],
    ![false,true,false,true,true,false], ![false,true,true,false,false,true],
    ![false,true,true,false,true,false], ![false,true,true,true,false,false],
    ![true,true,false,false,false,true], ![true,true,false,false,true,false],
    ![true,true,false,true,false,false], ![true,true,true,false,false,false]]

def xorFitPolynomial (u v : ℚ) : ℚ := u + v - 2*u*v

def xorSixLaw : AssignmentDesign (Fin 4) (Fin 6) ℚ where
  weight := fun _ => 1/4
  treatment := ![![false,true,false,true,false,true], ![false,true,true,false,true,false],
    ![true,false,false,true,true,false], ![true,false,true,false,false,true]]

def xorSixFit (w : Fin 4) : Fin 6 → ℚ :=
  let y := response xorSixLaw (fun _ => 1) (fun _ => 0) w
  ![xorFitPolynomial (y 2) (y 4), 1-xorFitPolynomial (y 2) (y 4),
    xorFitPolynomial (y 0) (y 4), 1-xorFitPolynomial (y 0) (y 4),
    xorFitPolynomial (y 0) (y 2), 1-xorFitPolynomial (y 0) (y 2)]

def xorThreeLaw : AssignmentDesign (Fin 4) (Fin 3) ℚ where
  weight := fun _ => 1/4
  treatment := ![![false,false,false], ![false,true,true],
    ![true,false,true], ![true,true,false]]

def xorThreeFit (w : Fin 4) : Fin 3 → ℚ :=
  let y := response xorThreeLaw (fun _ => 1) (fun _ => 0) w
  ![xorFitPolynomial (y 1) (y 2), xorFitPolynomial (y 0) (y 2), xorFitPolynomial (y 0) (y 1)]

def productFit (w : Fin 4) : Fin 3 → ℚ :=
  ![0,0,response xorThreeLaw (fun _ => 1) (fun _ => 0) w 0 *
    response xorThreeLaw (fun _ => 1) (fun _ => 0) w 1]

def twoOfFourLaw : AssignmentDesign (Fin 6) (Fin 4) ℚ where
  weight := fun _ => 1/6
  treatment := ![![true,true,false,false], ![true,false,true,false], ![true,false,false,true],
    ![false,true,true,false], ![false,true,false,true], ![false,false,true,true]]

def appendixNullOutcomes : Fin 4 → ℚ := ![1,2,4,7]

def finiteIndependent {α β : Type*} (D : AssignmentDesign Ω I R) (f : Ω → α) (g : Ω → β) : Prop :=
  ∀ u : α → R, ∀ v : β → R,
    mean D (fun w => u (f w) * v (g w)) =
      mean D (fun w => u (f w)) * mean D (fun w => v (g w))

def fittingResponses (D : AssignmentDesign Ω I R) (J : Finset I) (y1 y0 : I → R) (w : Ω) :
    ↥J → R := fun j => response D y1 y0 w j

def fittingIndicators (D : AssignmentDesign Ω I R) (J : Finset I) (w : Ω) :
    ↥J → Bool := fun j => D.treatment w j

def repairedBias (D : AssignmentDesign Ω I R) (x z : I → R) : R :=
  (∑ i, (x i-z i)^2) + unavailablePairSum D true true (fun i j => (x i+x j)^2) / 2 +
    unavailablePairSum D false false (fun i j => (z i+z j)^2) / 2 +
    unavailablePairSum D true false (fun i j => (x i-z j)^2)

def populationCovarianceBound (D : AssignmentDesign Ω I R) (x z : I → R) : R :=
  orderedOffDiagonalSum (fun i j => (jointInclusion D true false i j - inclusion D true i * inclusion D false j) *
    (x i / inclusion D true i) * (z j / inclusion D false j)) -
    (∑ i, (x i)^2 / 2) - (∑ i, (z i)^2 / 2)

def armPopulationBound (D : AssignmentDesign Ω I R) (a : Bool) (y : I → R) : R :=
  (∑ i, inclusion D a i * (1-inclusion D a i) * (y i / inclusion D a i)^2) +
  orderedOffDiagonalSum (fun i j => if 0 < jointInclusion D a a i j then
    (jointInclusion D a a i j-inclusion D a i*inclusion D a j) *
      (y i/inclusion D a i)*(y j/inclusion D a j) else 0) +
  unavailablePairSum D a a (fun i j => (y i)^2/2+(y j)^2/2)

def armVarianceEstimate (D : AssignmentDesign Ω I R) (a : Bool) (y1 y0 : I → R) (w : Ω) : R :=
  (∑ i, armIndicator D a w i * (1-inclusion D a i) *
    (response D y1 y0 w i / inclusion D a i)^2) +
  orderedOffDiagonalSum (fun i j => if 0 < jointInclusion D a a i j then estimatedPairTerm D a a y1 y0 w i j else 0) +
  unavailablePairSum D a a (fun i j => armIndicator D a w i * response D y1 y0 w i ^ 2 / (2*inclusion D a i) +
    armIndicator D a w j * response D y1 y0 w j ^ 2 / (2*inclusion D a j))

def splitPopulationCovariance (D : AssignmentDesign Ω I R) (x z : I → R) : R :=
  (∑ i, ∑ j, if jointInclusion D true false i j ≠ 0 then
    (jointInclusion D true false i j-inclusion D true i*inclusion D false j) *
      (x i/inclusion D true i)*(z j/inclusion D false j) else 0) -
  (∑ i, ∑ j, if jointInclusion D true false i j = 0 then x i*z j else 0)

def fiberTotal {K : Type*} [DecidableEq K] (c : I → K) (y : I → R) (k : K) : R :=
  ∑ i ∈ univ.filter (fun i => c i=k), y i

def independentAssignments (D : AssignmentDesign Ω I R) : Prop :=
  ∀ F : I → Bool → R, mean D (fun w => ∏ i, F i (D.treatment w i)) =
    ∏ i, mean D (fun w => F i (D.treatment w i))

def independentBlocks {B : Type*} [Fintype B] [DecidableEq B]
    (D : AssignmentDesign Ω I R) (c : I → B) : Prop :=
  ∀ F : ∀ b : B, (↥(univ.filter (fun i => c i=b)) → Bool) → R,
    mean D (fun w => ∏ b, F b (fittingIndicators D (univ.filter (fun i => c i=b)) w)) =
      ∏ b, mean D (fun w => F b (fittingIndicators D (univ.filter (fun i => c i=b)) w))

/-- Equation [31]; its theorem requires positive same-arm joint probabilities. -/
def fullSupportArmEstimate (D : AssignmentDesign Ω I R) (a : Bool)
    (x z : I → R) (w : Ω) : R :=
  (∑ i, armIndicator D a w i * (1 - inclusion D a i) *
    (response D x z w i / inclusion D a i)^2) +
  orderedOffDiagonalSum (fun i j =>
    armIndicator D a w i * armIndicator D a w j / jointInclusion D a a i j *
    (jointInclusion D a a i j - inclusion D a i * inclusion D a j) *
    (response D x z w i / inclusion D a i) * (response D x z w j / inclusion D a j))

end
end SAP.P026a
