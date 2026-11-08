import Mathlib
import SAP.P026b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b
open Finset
open scoped BigOperators
noncomputable section

def T24Statement : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (x z : I → ℝ) (f : (I → Bool) → I → ℝ),
    (∀ w, generalized E.design (Fintype.card I) x z f w =
      ht E.design (Fintype.card I) (fun i => x i-f w i) (fun i => z i-f w i) w ∧
      generalized E.design (Fintype.card I) x z f w =
        residualContrast E.design (Fintype.card I) x z f w) ∧
    (∀ r : I → ℝ,
      variance E.design (generalized E.design (Fintype.card I) x z (fun _ => r)) =
        (armVarianceExpression E.design true (fun i => x i-r i) +
         armVarianceExpression E.design false (fun i => z i-r i) -
         2*splitCovarianceExpression E.design (fun i => x i-r i) (fun i => z i-r i)) /
          (Fintype.card I : ℝ)^2)) ∧
  (∀ (U C : Type) [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C),
    (∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d) →
    ∀ (x z : U → ℝ),
    (∀ a : Bool, variance E.clusterDesign
      (htTotal E.clusterDesign a (if a then E.totals x else E.totals z)) =
        armVarianceExpression E.clusterDesign a (if a then E.totals x else E.totals z)) ∧
    covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x))
      (htTotal E.clusterDesign false (E.totals z)) =
        (∑ i, ∑ j, (joint E.clusterDesign true false i j -
          marginal E.clusterDesign true i * marginal E.clusterDesign false j) *
          (E.totals x i/marginal E.clusterDesign true i) *
          (E.totals z j/marginal E.clusterDesign false j)) ∧
    covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x))
      (htTotal E.clusterDesign false (E.totals z)) =
        splitCovarianceExpression E.clusterDesign (E.totals x) (E.totals z) ∧
    covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x))
      (htTotal E.clusterDesign false (E.totals z)) =
        clusterCovarianceExpression E.clusterDesign (E.totals x) (E.totals z))

end
end SAP.P026b
