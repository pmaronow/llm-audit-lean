import AronowAudit.P005.Wave1.Gap.GP005B1b
import AronowAudit.P005.Wave1.Lib.FiniteDesignOrderTailC
import AronowAudit.P005.Wave1.Lib.QuadraticSamplingTailC

/-!
The unconditional arm estimate follows from the quadratic-form bound
with nonzero trace and the allocation-uniform first-moment estimate.
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

end
end AronowAudit.P005.Wave1
