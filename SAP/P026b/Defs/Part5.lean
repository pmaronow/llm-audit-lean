import Mathlib
import SAP.P026b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b
open Finset
open scoped BigOperators
noncomputable section

def T20Statement : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (y1 y0 : I → ℝ),
  (∀ a w, htTotal E.design a (if a then y1 else y0) w =
    ∑ i, indicator E.design a w i * observed E.design y1 y0 w i / marginal E.design a i) ∧
  expectation E.design (htTotal E.design true y1) = populationTotal y1 ∧
  expectation E.design (htTotal E.design false y0) = populationTotal y0 ∧
  expectation E.design (ht E.design (Fintype.card I) y1 y0) = ate (Fintype.card I) y1 y0

/-- Complete assignment identities, with the actual unit and cluster counts. -/
def T21Statement : Prop :=
  (∀ (Ω I : Type) [Fintype Ω] [Fintype I] [DecidableEq I]
    (D : Design Ω I ℝ), probabilityDesign D →
    ∀ (n : ℕ), 0 < n → n < Fintype.card I →
    (∀ i, marginal D true i = (n : ℝ) / Fintype.card I ∧
      marginal D false i = ((Fintype.card I-n : ℕ) : ℝ) / Fintype.card I) →
    (∀ w, 0 < D.weight w → (∑ i, indicator D true w i) = n) →
    ∀ (x z : I → ℝ),
    (∀ w, 0 < D.weight w → ht D (Fintype.card I) x z w =
      observedArmSum D true x z w / n - observedArmSum D false x z w / (Fintype.card I-n : ℕ)) ∧
    expectation D (fun w => observedArmSum D true x z w / n -
      observedArmSum D false x z w / (Fintype.card I-n : ℕ)) = ate (Fintype.card I) x z) ∧
  (∀ (U : Type) [Fintype U] [DecidableEq U] [Nonempty U]
    (M m : ℕ) (_hm : 0 < m) (_hmM : m < M) (E : ClusterExperiment U (Fin M)),
    (∀ i, marginal E.clusterDesign true i = (m : ℝ)/M ∧
      marginal E.clusterDesign false i = ((M-m : ℕ) : ℝ)/M) →
    (∀ w, 0 < E.clusterDesign.weight w → (∑ i, indicator E.clusterDesign true w i) = m) →
    ∀ (x z : U → ℝ),
    (∀ w, ht E.unitDesign (Fintype.card U) x z w = (M : ℝ)/Fintype.card U *
      (observedArmSum E.clusterDesign true (E.totals x) (E.totals z) w/m -
       observedArmSum E.clusterDesign false (E.totals x) (E.totals z) w/(M-m : ℕ))) ∧
    expectation E.unitDesign (ht E.unitDesign (Fintype.card U) x z) = ate (Fintype.card U) x z) ∧
  probabilityDesign unequalClusterDesign ∧ positiveMarginals unequalClusterDesign ∧
  (∀ i, marginal unequalClusterDesign true i = 1/3 ∧ marginal unequalClusterDesign false i = 2/3) ∧
  (∀ w, 0 < ∑ i, indicator unequalClusterDesign true w i) ∧
  (∀ w, 0 < ∑ i, indicator unequalClusterDesign false w i) ∧
  expectation unequalClusterDesign
    (differenceInMeans unequalClusterDesign (![1,1,0,0]) (![1,1,0,0])) = 1/9 ∧
  expectation unequalClusterDesign (ht unequalClusterDesign 4 (![1,1,0,0]) (![1,1,0,0])) = 0 ∧
  ate 4 (![1,1,0,0] : Fin 4 → ℚ) (![1,1,0,0]) = 0 ∧ (1/9 : ℚ) ≠ 0

/-- Zero covariance gives unbiased totals and ATE; fixed predictions are included. -/
def T22Statement : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (y1 y0 : I → ℝ) (f : (I → Bool) → I → ℝ),
  ((∀ i, covariance E.design (fun w => indicator E.design true w i) (fun w => f w i) = 0) →
    expectation E.design (generalizedTotal E.design true y1 f) = populationTotal y1 ∧
    expectation E.design (generalizedTotal E.design false y0 f) = populationTotal y0 ∧
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 f) =
      ate (Fintype.card I) y1 y0) ∧
  (∀ g : I → ℝ,
    (∀ i, covariance E.design (fun w => indicator E.design true w i) (fun _ => g i) = 0) ∧
    expectation E.design (generalizedTotal E.design true y1 (fun _ => g)) = populationTotal y1 ∧
    expectation E.design (generalizedTotal E.design false y0 (fun _ => g)) = populationTotal y0 ∧
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 (fun _ => g)) =
      ate (Fintype.card I) y1 y0) ∧
  (∀ w, generalized E.design (Fintype.card I) y1 y0 f w =
    ht E.design (Fintype.card I) y1 y0 w -
      (htTotal E.design true (f w) w - htTotal E.design false (f w) w) / Fintype.card I)

/-- Exact affine formula, its balance criterion and witness, and generalized invariance. -/
def T23Statement : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (x z : I → ℝ) (f : (I → Bool) → I → ℝ) (b0 b1 : ℝ) (w : I → Bool),
    ht E.design (Fintype.card I) (fun i => b0+b1*x i) (fun i => b0+b1*z i) w =
      b0/(Fintype.card I : ℝ) *
        ((∑ i, indicator E.design true w i/marginal E.design true i) -
         (∑ i, indicator E.design false w i/marginal E.design false i)) +
      b1*ht E.design (Fintype.card I) x z w ∧
    (ht E.design (Fintype.card I) (fun i => b0+b1*x i) (fun i => b0+b1*z i) w =
        b1*ht E.design (Fintype.card I) x z w ↔
      b0=0 ∨ (∑ i, indicator E.design true w i/marginal E.design true i) =
        (∑ i, indicator E.design false w i/marginal E.design false i)) ∧
    generalized E.design (Fintype.card I) (fun i => b0+b1*x i) (fun i => b0+b1*z i)
      (fun v i => b0+b1*f v i) w = b1*generalized E.design (Fintype.card I) x z f w) ∧
  probabilityDesign singleAsymmetric ∧ positiveMarginals singleAsymmetric ∧
  0 < singleAsymmetric.weight 2 ∧
  ht singleAsymmetric 1 (fun _ => 1) (fun _ => 1) 2 = 3 ∧
  (-1 : ℚ)*ht singleAsymmetric 1 (fun _ => 0) (fun _ => 0) 2 = 0 ∧
  ht singleAsymmetric 1 (fun _ => 1) (fun _ => 1) 2 ≠
    (-1)*ht singleAsymmetric 1 (fun _ => 0) (fun _ => 0) 2

end
end SAP.P026b
