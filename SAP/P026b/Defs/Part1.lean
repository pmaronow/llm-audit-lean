import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b
open Finset
open scoped BigOperators
noncomputable section

structure Design (Ω I R : Type*) where
  weight : Ω → R
  treatment : Ω → I → Bool

variable {Ω I R : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]

def expectation (D : Design Ω I R) (f : Ω → R) : R := ∑ w, D.weight w * f w

def probabilityDesign (D : Design Ω I R) : Prop :=
  (∀ w, 0 ≤ D.weight w) ∧ (∑ w, D.weight w) = 1

def indicator (D : Design Ω I R) (a : Bool) (w : Ω) (i : I) : R :=
  if D.treatment w i = a then 1 else 0

def marginal (D : Design Ω I R) (a : Bool) (i : I) : R :=
  expectation D (fun w => indicator D a w i)

def joint (D : Design Ω I R) (a b : Bool) (i j : I) : R :=
  expectation D (fun w => indicator D a w i * indicator D b w j)

def positiveMarginals (D : Design Ω I R) : Prop :=
  ∀ i, 0 < marginal D true i ∧ 0 < marginal D false i

def observed (D : Design Ω I R) (y1 y0 : I → R) (w : Ω) (i : I) : R :=
  if D.treatment w i then y1 i else y0 i

def populationTotal (y : I → R) : R := ∑ i, y i

def ate (N : ℕ) (y1 y0 : I → R) : R :=
  (populationTotal y1 - populationTotal y0) / N

def htTotal (D : Design Ω I R) (a : Bool) (y : I → R) (w : Ω) : R :=
  ∑ i, indicator D a w i * y i / marginal D a i

def ht (D : Design Ω I R) (N : ℕ) (y1 y0 : I → R) (w : Ω) : R :=
  (htTotal D true y1 w - htTotal D false y0 w) / N

def generalizedTotal (D : Design Ω I R) (a : Bool) (y : I → R)
    (f : Ω → I → R) (w : Ω) : R :=
  ∑ i, (indicator D a w i * y i / marginal D a i -
    indicator D a w i * f w i / marginal D a i + f w i)

def generalized (D : Design Ω I R) (N : ℕ) (y1 y0 : I → R)
    (f : Ω → I → R) (w : Ω) : R :=
  (generalizedTotal D true y1 f w - generalizedTotal D false y0 f w) / N

def covariance (D : Design Ω I R) (f g : Ω → R) : R :=
  expectation D (fun w => f w * g w) - expectation D f * expectation D g

def variance (D : Design Ω I R) (f : Ω → R) : R := covariance D f f

def disagreement (D : Design Ω I R) (i j : I) : R :=
  expectation D (fun w => if D.treatment w i ≠ D.treatment w j then 1 else 0)

def offSum (f : I → I → R) : R := ∑ i, ∑ j ∈ univ.erase i, f i j

def zeroSum (D : Design Ω I R) (a b : Bool) (f : I → I → R) : R :=
  offSum (fun i j => if joint D a b i j = 0 then f i j else 0)

def epsilon (p : R) : R := if p = 0 then 1 else 0

def estimatedPair (D : Design Ω I R) (a b : Bool) (y1 y0 : I → R)
    (w : Ω) (i j : I) : R :=
  indicator D a w i * indicator D b w j / (joint D a b i j + epsilon (joint D a b i j)) *
  (joint D a b i j - marginal D a i * marginal D b j) *
  (observed D y1 y0 w i / marginal D a i) *
  (observed D y1 y0 w j / marginal D b j)

def printedVariance (D : Design Ω I R) (N : ℕ) (y1 y0 : I → R) (w : Ω) : R :=
  ((∑ i, (indicator D true w i * (observed D y1 y0 w i / marginal D true i)^2 +
      indicator D false w i * (observed D y1 y0 w i / marginal D false i)^2)) +
    offSum (fun i j => estimatedPair D true true y1 y0 w i j +
      estimatedPair D false false y1 y0 w i j - 2 * estimatedPair D true false y1 y0 w i j) +
    zeroSum D true true (fun i j =>
      indicator D true w i * observed D y1 y0 w i ^ 2 / (2 * marginal D true i) +
      indicator D true w j * observed D y1 y0 w j ^ 2 / (2 * marginal D true j)) +
    zeroSum D false false (fun i j =>
      indicator D false w i * observed D y1 y0 w i ^ 2 / (2 * marginal D false i) +
      indicator D false w j * observed D y1 y0 w j ^ 2 / (2 * marginal D false j))) / (N : R)^2

def crossSupport (D : Design Ω I R) : Prop :=
  ∀ i j, i ≠ j → 0 < joint D true false i j

def armVarianceExpression (D : Design Ω I R) (a : Bool) (y : I → R) : R :=
  (∑ i, marginal D a i * (1 - marginal D a i) * (y i / marginal D a i)^2) +
  offSum (fun i j => (joint D a a i j - marginal D a i * marginal D a j) *
    (y i / marginal D a i) * (y j / marginal D a j))

def clusterCovarianceExpression (D : Design Ω I R) (x z : I → R) : R :=
  offSum (fun i j => (joint D true false i j - marginal D true i * marginal D false j) *
    (x i / marginal D true i) * (z j / marginal D false j)) - ∑ i, x i * z i

def independent {α β : Type*} (D : Design Ω I R) (f : Ω → α) (g : Ω → β) : Prop :=
  ∀ u : α → R, ∀ v : β → R,
    expectation D (fun w => u (f w) * v (g w)) =
      expectation D (fun w => u (f w)) * expectation D (fun w => v (g w))

def fittingOutcomes (D : Design Ω I R) (J : Finset I) (y1 y0 : I → R) (w : Ω) :
    ↥J → R := fun j => observed D y1 y0 w j

def splitCovarianceExpression (D : Design Ω I R) (x z : I → R) : R :=
  (∑ i, ∑ j, if joint D true false i j ≠ 0 then
    (joint D true false i j-marginal D true i*marginal D false j) *
      (x i/marginal D true i)*(z j/marginal D false j) else 0) -
  (∑ i, ∑ j, if joint D true false i j = 0 then x i*z j else 0)

def clusterTotal {K : Type*} [DecidableEq K] (c : I → K) (y : I → R) (k : K) : R :=
  ∑ i ∈ univ.filter (fun i => c i=k), y i

def observedArmSum (D : Design Ω I R) (a : Bool) (x z : I → R) (w : Ω) : R :=
  ∑ i, indicator D a w i*observed D x z w i

def differenceInMeans (D : Design Ω I R) (x z : I → R) (w : Ω) : R :=
  observedArmSum D true x z w / (∑ i, indicator D true w i) -
  observedArmSum D false x z w / (∑ i, indicator D false w i)

/-- A probability law on every binary allocation with positive marginals. -/
structure UnitExperiment (I : Type*) [Fintype I] [DecidableEq I] where
  weight : (I → Bool) → ℝ
  nonnegative : ∀ w, 0 ≤ weight w
  normalized : ∑ w, weight w = 1
  positive : ∀ i, 0 < ∑ w, weight w * (if w i = true then 1 else 0) ∧
    0 < ∑ w, weight w * (if w i = false then 1 else 0)

def UnitExperiment.design {I : Type*} [Fintype I] [DecidableEq I]
    (E : UnitExperiment I) : Design (I → Bool) I ℝ := ⟨E.weight, fun w => w⟩

/-- A nonempty partition of units and a probability law on cluster allocations. -/
structure ClusterExperiment (U C : Type*) [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] where
  cluster : U → C
  covers : Function.Surjective cluster
  assignment : UnitExperiment C

def ClusterExperiment.clusterDesign {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] (E : ClusterExperiment U C) : Design (C → Bool) C ℝ :=
  E.assignment.design

def ClusterExperiment.unitDesign {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] (E : ClusterExperiment U C) : Design (C → Bool) U ℝ :=
  ⟨E.assignment.weight, fun w i => w (E.cluster i)⟩

def ClusterExperiment.totals {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] (E : ClusterExperiment U C) (y : U → ℝ) (c : C) : ℝ :=
  ∑ i ∈ univ.filter (fun i => E.cluster i = c), y i

/-- The branch's observed-outcome contrast of residuals. -/
def residualContrast {Ω I : Type*} [Fintype Ω] [Fintype I]
    (D : Design Ω I ℝ) (N : ℕ) (x z : I → ℝ) (f : Ω → I → ℝ) (w : Ω) : ℝ :=
  ((∑ i, indicator D true w i * (observed D x z w i - f w i) / marginal D true i) -
   (∑ i, indicator D false w i * (observed D x z w i - f w i) / marginal D false i)) / N

end
end SAP.P026b
