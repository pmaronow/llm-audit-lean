import AronowAudit.P029.Wave1.LateIdentityBlueprint
import AronowAudit.P029.Wave1.LateIdentity.N1
import AronowAudit.P029.Wave1.LateIdentity.N2
import AronowAudit.P029.Wave1.LateIdentity.N3
import AronowAudit.P029.Wave1.LateIdentity.N4
import AronowAudit.P029.Wave1.LateIdentity.N5

namespace AronowAudit.P029.Wave1

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

universe u v

noncomputable section

theorem late_identity_paper_scope {Ω : Type u} {X : Type v}
    [MeasurableSpace Ω] [MeasurableSpace X]
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
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} = mWald μ U Z (fun _ => 1) := by
  exact LateIdentity.assemble LateIdentity.n1_proof LateIdentity.n2_proof
    LateIdentity.n3_proof LateIdentity.n4_proof LateIdentity.n5_proof μ U Z hiv

end

end AronowAudit.P029.Wave1
