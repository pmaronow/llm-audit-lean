import AronowAudit.P029.Wave1.LateIdentity
import AronowAudit.P029.Wave1.Gap.GP029B3b

/-!
P029-T25 and P029-T27(b): LATE and the ICSW population limit.

The LATE identities follow from independent-arm identities, integration of the
almost-everywhere no-defier identities, and normalization by positive complier mass.
The ICSW limit follows from the six raw-moment limits and the estimated-score
substitution bound before taking the Wald ratio.
-/

namespace AronowAudit.P029.Wave1

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- P029-T25: the two ITT identities and the exact complier-effect Wald identity. -/
theorem late_identity_proof {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z) :
    mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = true} -
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = false} =
        mP μ {ω | (U ω).complier} ∧
    mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = true} -
      mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = false} =
        (∫ ω, if (U ω).complier then (U ω).tau else 0 ∂μ) ∧
    (∫ ω, if (U ω).complier then (U ω).tau else 0 ∂μ) =
      mP μ {ω | (U ω).complier} * mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} ∧
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} =
      mWald μ U Z (fun _ => 1) := by
  exact late_identity_paper_scope μ U Z hiv

/-- P029-T27(b): ICSW averages complier effects over the full covariate law. -/
theorem icsw_complier_effect_limit_proof {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ)
    (h : ICSWConditions μ U Z c m s)
    (hA3 : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ (Measure.map (fun ω => (U 0 ω).x) μ).support,
      ε < c x ∧ c x ≤ 1) :
    TendstoInMeasure μ (icswSequence U Z s) atTop (fun _ => ∫ ω, m (U 0 ω).x ∂μ) := by
  exact GP029B3b_icsw_limit h

end

end AronowAudit.P029.Wave1
