import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section

variable {Ω I R : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]

structure AssignmentDesign (Ω I R : Type*) where
  weight : Ω → R
  treatment : Ω → I → Bool

def mean (D : AssignmentDesign Ω I R) (f : Ω → R) : R := ∑ w, D.weight w * f w

def isProbability (D : AssignmentDesign Ω I R) : Prop :=
  (∀ w, 0 ≤ D.weight w) ∧ (∑ w, D.weight w) = 1

def armIndicator (D : AssignmentDesign Ω I R) (a : Bool) (w : Ω) (i : I) : R :=
  if D.treatment w i = a then 1 else 0

def inclusion (D : AssignmentDesign Ω I R) (a : Bool) (i : I) : R :=
  mean D (fun w => armIndicator D a w i)

def jointInclusion (D : AssignmentDesign Ω I R) (a b : Bool) (i j : I) : R :=
  mean D (fun w => armIndicator D a w i * armIndicator D b w j)

def hasPositiveMarginals (D : AssignmentDesign Ω I R) : Prop :=
  ∀ i, 0 < inclusion D true i ∧ 0 < inclusion D false i

def response (D : AssignmentDesign Ω I R) (y1 y0 : I → R) (w : Ω) (i : I) : R :=
  if D.treatment w i then y1 i else y0 i

def fixedTotal (y : I → R) : R := ∑ i, y i

def averageEffect (N : ℕ) (y1 y0 : I → R) : R :=
  (fixedTotal y1 - fixedTotal y0) / N

def htSum (D : AssignmentDesign Ω I R) (a : Bool) (y : I → R) (w : Ω) : R :=
  ∑ i, armIndicator D a w i * y i / inclusion D a i

def htContrast (D : AssignmentDesign Ω I R) (N : ℕ) (y1 y0 : I → R) (w : Ω) : R :=
  (htSum D true y1 w - htSum D false y0 w) / N

def adjustedSum (D : AssignmentDesign Ω I R) (a : Bool) (y : I → R)
    (f : Ω → I → R) (w : Ω) : R :=
  ∑ i, (armIndicator D a w i * y i / inclusion D a i -
    armIndicator D a w i * f w i / inclusion D a i + f w i)

def adjustedContrast (D : AssignmentDesign Ω I R) (N : ℕ) (y1 y0 : I → R)
    (f : Ω → I → R) (w : Ω) : R :=
  (adjustedSum D true y1 f w - adjustedSum D false y0 f w) / N

def designCovariance (D : AssignmentDesign Ω I R) (f g : Ω → R) : R :=
  mean D (fun w => f w * g w) - mean D f * mean D g

def designVariance (D : AssignmentDesign Ω I R) (f : Ω → R) : R := designCovariance D f f

def disagreementProbability (D : AssignmentDesign Ω I R) (i j : I) : R :=
  mean D (fun w => if D.treatment w i ≠ D.treatment w j then 1 else 0)

def orderedOffDiagonalSum (f : I → I → R) : R := ∑ i, ∑ j ∈ univ.erase i, f i j

def unavailablePairSum (D : AssignmentDesign Ω I R) (a b : Bool) (f : I → I → R) : R :=
  orderedOffDiagonalSum (fun i j => if jointInclusion D a b i j = 0 then f i j else 0)

def zeroAdjustment (p : R) : R := if p = 0 then 1 else 0

def estimatedPairTerm (D : AssignmentDesign Ω I R) (a b : Bool) (y1 y0 : I → R)
    (w : Ω) (i j : I) : R :=
  armIndicator D a w i * armIndicator D b w j / (jointInclusion D a b i j + zeroAdjustment (jointInclusion D a b i j)) *
  (jointInclusion D a b i j - inclusion D a i * inclusion D b j) *
  (response D y1 y0 w i / inclusion D a i) *
  (response D y1 y0 w j / inclusion D b j)

def printedVarianceEstimate (D : AssignmentDesign Ω I R) (N : ℕ) (y1 y0 : I → R) (w : Ω) : R :=
  ((∑ i, (armIndicator D true w i * (response D y1 y0 w i / inclusion D true i)^2 +
      armIndicator D false w i * (response D y1 y0 w i / inclusion D false i)^2)) +
    orderedOffDiagonalSum (fun i j => estimatedPairTerm D true true y1 y0 w i j +
      estimatedPairTerm D false false y1 y0 w i j - 2 * estimatedPairTerm D true false y1 y0 w i j) +
    unavailablePairSum D true true (fun i j =>
      armIndicator D true w i * response D y1 y0 w i ^ 2 / (2 * inclusion D true i) +
      armIndicator D true w j * response D y1 y0 w j ^ 2 / (2 * inclusion D true j)) +
    unavailablePairSum D false false (fun i j =>
      armIndicator D false w i * response D y1 y0 w i ^ 2 / (2 * inclusion D false i) +
      armIndicator D false w j * response D y1 y0 w j ^ 2 / (2 * inclusion D false j))) / (N : R)^2

/-- Equation [34] with zero-joint pairs explicitly omitted.
This continuation is used only as such; the literal printed statistic requires directed support. -/
def covarianceWithZeroOmission (D : AssignmentDesign Ω I R) (y1 y0 : I → R) (w : Ω) : R :=
  orderedOffDiagonalSum (fun i j =>
    if jointInclusion D true false i j = 0 then 0 else
    armIndicator D true w i * armIndicator D false w j / jointInclusion D true false i j *
    (jointInclusion D true false i j - inclusion D true i * inclusion D false j) *
    (response D y1 y0 w i / inclusion D true i) *
    (response D y1 y0 w j / inclusion D false j)) -
  (∑ i, armIndicator D true w i * response D y1 y0 w i ^ 2 / (2 * inclusion D true i)) -
  (∑ i, armIndicator D false w i * response D y1 y0 w i ^ 2 / (2 * inclusion D false i))

def directedSupport (D : AssignmentDesign Ω I R) : Prop :=
  ∀ i j, i ≠ j → 0 < jointInclusion D true false i j

def directedPairCorrection (D : AssignmentDesign Ω I R) (y1 y0 : I → R) (w : Ω) : R :=
  unavailablePairSum D true false (fun i j =>
    armIndicator D true w i * response D y1 y0 w i ^ 2 / inclusion D true i +
    armIndicator D false w j * response D y1 y0 w j ^ 2 / inclusion D false j)

def repairedCovarianceEstimate (D : AssignmentDesign Ω I R) (y1 y0 : I → R) (w : Ω) : R :=
  covarianceWithZeroOmission D y1 y0 w - directedPairCorrection D y1 y0 w / 2

def repairedVarianceEstimate (D : AssignmentDesign Ω I R) (N : ℕ) (y1 y0 : I → R) (w : Ω) : R :=
  printedVarianceEstimate D N y1 y0 w + directedPairCorrection D y1 y0 w / (N : R)^2

def appendixDisplay (D : AssignmentDesign Ω I R) (y1 y0 : I → R) (w : Ω) : R :=
  (∑ i, armIndicator D true w i * (1 - inclusion D true i) *
    (response D y1 y0 w i / inclusion D true i)^2) +
  orderedOffDiagonalSum (fun i j => if 0 < jointInclusion D true true i j then
    estimatedPairTerm D true true y1 y0 w i j else 0) -
  (∑ i, armIndicator D true w i * response D y1 y0 w i ^ 2 / (2 * inclusion D true i)) -
  (∑ i, armIndicator D false w i * response D y1 y0 w i ^ 2 / (2 * inclusion D false i))

end
end SAP.P026a
