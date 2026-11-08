import AronowAudit.P005.Wave1.Gap.GP005B1b
import AronowAudit.P005.Wave1.Lib.FiniteDesignOrderTailC
import AronowAudit.P005.Wave1.Lib.QuadraticSamplingTailC

/-!
The frozen GP005B1b library already proves the unconditional arm estimate,
including the nonzero-trace quadratic-form bound and the allocation-uniform
first-moment estimate. Reuse that proof and check its exact held contract.
-/

namespace AronowAudit.P005.Wave1

noncomputable section
open Finset Filter

theorem tailC_arm_debiased_order (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P) (t : Arm) :
    stochasticO m (fun n S =>
      let A := armSet t S
      let y := if t = .treated then (P n).yT else (P n).yC
      armDebiased (P n) A y - (mean A y - dot (xMean (P n) A) (populationSlope (P n) y)))
      (fun n => Real.sqrt (kappa (P n)/n)) := by
  exact corrected_arm_debiased_order_proof d m P h t

example : type_of% @AronowAudit.P005.corrected_arm_debiased_order :=
  corrected_arm_debiased_order_proof

example : type_of% @AronowAudit.P005.corrected_arm_debiased_order :=
  tailC_arm_debiased_order

end
end AronowAudit.P005.Wave1
