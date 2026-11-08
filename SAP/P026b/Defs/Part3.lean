import Mathlib
import SAP.P026b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b
open Finset
open scoped BigOperators
noncomputable section

/-- Adjoin an intercept to the supplied covariates. -/
def designWithIntercept {I : Type*} (K : ℕ)
    (X : Matrix I (Fin K) ℝ) : Matrix I (Fin (K + 1)) ℝ :=
  fun i => Fin.cases (1 : ℝ) (X i)

def olsDesignMap {I : Type*} [Fintype I] (K : ℕ)
    (V : Matrix I (Fin K) ℝ) : (Fin K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ I :=
  ((EuclideanSpace.equiv I ℝ).symm.toLinearEquiv.toLinearMap).comp V.mulVecLin

def olsColumnSpace {I : Type*} [Fintype I] (K : ℕ)
    (V : Matrix I (Fin K) ℝ) : Submodule ℝ (EuclideanSpace ℝ I) :=
  LinearMap.range (olsDesignMap K V)

/-- Ordinary least-squares fitted responses, defined even for a deficient rank. -/
def olsFitted {I : Type*} [Fintype I] (K : ℕ)
    (V : Matrix I (Fin K) ℝ) (y : I → ℝ) : I → ℝ :=
  (EuclideanSpace.equiv I ℝ)
    ((olsColumnSpace K V).starProjection ((EuclideanSpace.equiv I ℝ).symm y))

def IsLeastSquaresFitted {I : Type*} [Fintype I] (K : ℕ)
    (V : Matrix I (Fin K) ℝ) (y z : I → ℝ) : Prop :=
  (∃ β : Fin K → ℝ, V.mulVec β = z) ∧
  ∀ β : Fin K → ℝ,
    (∑ i, (y i - z i)^2) ≤ (∑ i, (y i - (V.mulVec β) i)^2)

/-- Equations [17] (corrected), [18], and [19], for arbitrary random predictions. -/
def T13Statement : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (y1 y0 : I → ℝ) (f : (I → Bool) → I → ℝ),
  (∀ a : Bool,
    expectation E.design (generalizedTotal E.design a (if a then y1 else y0) f) =
      populationTotal (if a then y1 else y0) -
        ∑ i, covariance E.design (fun w => indicator E.design a w i)
          (fun w => f w i / marginal E.design a i)) ∧
  expectation E.design (generalized E.design (Fintype.card I) y1 y0 f) -
      ate (Fintype.card I) y1 y0 =
    ((∑ i, covariance E.design (fun w => indicator E.design false w i)
        (fun w => f w i / marginal E.design false i)) -
     (∑ i, covariance E.design (fun w => indicator E.design true w i)
        (fun w => f w i / marginal E.design true i))) / Fintype.card I

/-- Exact normal-equation and moment certificate for the three-unit OLS example. -/
def packageFacts : Prop :=
  probabilityDesign oneOfThree ∧ positiveMarginals oneOfThree ∧
  (∀ i, marginal oneOfThree true i = 1/3 ∧ marginal oneOfThree false i = 2/3) ∧
  (∀ w, (∑ i : Fin 3, (observed oneOfThree (fun _ => 1) (fun _ => 0) w i - packageFit w i)) = 0 ∧
    (∑ i : Fin 3, (i.val : ℚ) *
      (observed oneOfThree (fun _ => 1) (fun _ => 0) w i - packageFit w i)) = 0) ∧
  ((3*5-3^2 : ℚ) = 6) ∧
  (∀ w, generalized oneOfThree 3 (fun _ => 1) (fun _ => 0) packageFit w =
    (![1/4,1,1/4] : Fin 3 → ℚ) w) ∧
  (∀ i, covariance oneOfThree (fun w => indicator oneOfThree true w i)
    (fun w => packageFit w i) = (![1/6,0,1/6] : Fin 3 → ℚ) i) ∧
  expectation oneOfThree (generalized oneOfThree 3 (fun _ => 1) (fun _ => 0) packageFit) = 1/2 ∧
  ate 3 (fun _ : Fin 3 => (1 : ℚ)) (fun _ => 0) = 1 ∧
  (∀ w, ht oneOfThree 3 (fun _ => 1) (fun _ => 0) w = 1) ∧ (1/2 : ℚ) ≠ 1

/-- The exact rational fits, interpreted as real responses, are the unique OLS fitted vectors. -/
def packageLeastSquares : Prop :=
  ∀ w : Fin 3,
  let V := designWithIntercept 1 (fun (i : Fin 3) (_ : Fin 1) => (i.val : ℝ))
  let y := fun i => ((observed oneOfThree (fun _ => 1) (fun _ => 0) w i : ℚ) : ℝ)
  let z := fun i => (packageFit w i : ℝ)
  IsLeastSquaresFitted 2 V y z ∧
    ∀ z' : Fin 3 → ℝ, IsLeastSquaresFitted 2 V y z' → z' = z

def T15Statement : Prop :=
  probabilityDesign oneOfThree ∧ positiveMarginals oneOfThree ∧
  (∀ i, marginal oneOfThree true i = 1/3 ∧ marginal oneOfThree false i = 2/3) ∧
  (∀ w i, packageFit w i =
    (![![5/6,1/3,-1/6], ![1/3,1/3,1/3], ![-1/6,1/3,5/6]] : Fin 3 → Fin 3 → ℚ) w i) ∧
  packageLeastSquares ∧
  (∀ w, generalized oneOfThree 3 (fun _ => 1) (fun _ => 0) packageFit w =
    (![1/4,1,1/4] : Fin 3 → ℚ) w) ∧
  (∀ i, covariance oneOfThree (fun w => indicator oneOfThree true w i)
    (fun w => packageFit w i) = (![1/6,0,1/6] : Fin 3 → ℚ) i) ∧
  expectation oneOfThree (generalized oneOfThree 3 (fun _ => 1) (fun _ => 0) packageFit) = 1/2 ∧
  ate 3 (fun _ : Fin 3 => (1 : ℚ)) (fun _ => 0) = 1 ∧
  expectation oneOfThree (generalized oneOfThree 3 (fun _ => 1) (fun _ => 0) packageFit) -
    ate 3 (fun _ : Fin 3 => (1 : ℚ)) (fun _ => 0) = -1/2 ∧
  -(1/3 : ℚ)*(3+3/2)*(1/6+0+1/6) = -1/2 ∧
  (∀ w, ht oneOfThree 3 (fun _ => 1) (fun _ => 0) w = 1) ∧ (1/2 : ℚ) ≠ 1

/-- The mathematical estimators in the two HT branches of the repaired help text. -/
def T16Statement : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (y1 y0 g : I → ℝ),
    (∀ w, generalized E.design (Fintype.card I) y1 y0 (fun _ => g) w =
      residualContrast E.design (Fintype.card I) y1 y0 (fun _ => g) w) ∧
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 (fun _ => g)) =
      ate (Fintype.card I) y1 y0) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (K : ℕ) (X : Matrix I (Fin K) ℝ) (y1 y0 : I → ℝ),
    let V := designWithIntercept K X
    let f : (I → Bool) → I → ℝ :=
      fun w => olsFitted (K + 1) V (observed E.design y1 y0 w)
    (∀ w, IsLeastSquaresFitted (K + 1) V (observed E.design y1 y0 w) (f w)) ∧
    (∀ w, generalized E.design (Fintype.card I) y1 y0 f w =
      residualContrast E.design (Fintype.card I) y1 y0 f w) ∧
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 f) -
        ate (Fintype.card I) y1 y0 =
      -(∑ i, covariance E.design (fun w => indicator E.design true w i) (fun w => f w i) *
        (1 / marginal E.design true i + 1 / marginal E.design false i)) / Fintype.card I) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (y1 y0 : I → ℝ) (f : (I → Bool) → I → ℝ),
    (∀ i, covariance E.design (fun w => indicator E.design true w i) (fun w => f w i) = 0) →
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 f) =
      ate (Fintype.card I) y1 y0) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (x : I → ℝ) (G : (I → ℝ) → I → ℝ),
    expectation E.design (generalized E.design (Fintype.card I) x x
      (fun w => G (observed E.design x x w))) = ate (Fintype.card I) x x) ∧
  T15Statement

end
end SAP.P026b
