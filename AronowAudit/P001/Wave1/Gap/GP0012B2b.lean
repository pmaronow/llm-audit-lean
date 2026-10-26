import AronowAudit.P001.Wave1.PdaMeanNotIdentified

/-! The fixed joint law has two continuously differentiable CEF versions with different derivatives at its mean. -/

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance GP0012B2b_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

theorem pda_joint_cef_counterexample_proof : IsProbabilityMeasure gapJointLaw ∧
   HasJointPDF gapJointLaw (fun xy => gapPDF xy.1 * (if xy.2∈Set.Icc (-1 : ℝ) 1 then 1/2 else 0)) ∧
   mean gapJointLaw Prod.fst=0 ∧ IsCEF gapJointLaw Prod.fst Prod.snd (fun _ => 0) ∧
   IsCEF gapJointLaw Prod.fst Prod.snd pdaBump ∧
   ContDiff ℝ 1 pdaBump ∧ deriv pdaBump (mean gapJointLaw Prod.fst)=1 ∧
   deriv (fun _ : ℝ => (0 : ℝ)) (mean gapJointLaw Prod.fst)=0 := by
  rcases pda_at_mean_not_identified with
    ⟨hprob, hpdf, _hfst, _hsnd, _hindependent, _hbounded,
      hmean, _hgap, hzero, hsmooth, hslopes, _hrefute⟩
  have hbumpCEF : IsCEF gapJointLaw Prod.fst Prod.snd pdaBump := by
    simpa only [one_mul] using (hslopes (1 : ℝ)).1
  have hbumpDeriv : deriv pdaBump (mean gapJointLaw Prod.fst) = 1 := by
    simpa only [one_mul] using (hslopes (1 : ℝ)).2
  have hzeroDeriv :
      deriv (fun _ : ℝ => (0 : ℝ)) (mean gapJointLaw Prod.fst) = 0 := by
    simp only [deriv_const]
  exact ⟨hprob, hpdf, hmean, hzero, hbumpCEF, hsmooth, hbumpDeriv, hzeroDeriv⟩

end
end AronowAudit.P001.Wave1
