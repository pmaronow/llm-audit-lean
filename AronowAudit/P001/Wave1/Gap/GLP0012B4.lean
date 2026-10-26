import AronowAudit.P001.Wave1.PdaMeanNotIdentified

/-! # P001-T3: exact extrapolation witness

The witness has a fixed product law with bounded support, zero mean and CEF,
and a family of C¹ CEF extensions with arbitrary slopes at the covariate mean.
The bump vanishes wherever the covariate density is positive.
-/

namespace AronowAudit.P001.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableGLP0012B4 (p : Prop) : Decidable p := Classical.propDecidable p

/-- Every point with positive covariate density lies outside the open bump interval. -/
lemma pda_extrapolation_witness_bump_zero_on_support (x : ℝ) (hx : 0 < gapPDF x) :
    pdaBump x = 0 := by
  have hs := (PdaMeanNotIdentified.n1_proof.2.2.2.1 x hx).1
  simp [pdaBump, not_lt.mpr hs]

/-- The fixed-law PDA witness with arbitrary CEF slopes at the covariate mean. -/
theorem pda_extrapolation_witness_proof :
  IsProbabilityMeasure gapJointLaw ∧
  HasJointPDF gapJointLaw (fun xy => gapPDF xy.1 *
    (if xy.2 ∈ Set.Icc (-1 : ℝ) 1 then 1/2 else 0)) ∧
  gapJointLaw = (gapJointLaw.map Prod.fst).prod (gapJointLaw.map Prod.snd) ∧
  HasPDF (gapJointLaw.map Prod.fst) gapPDF ∧
  gapJointLaw.map Prod.snd = uniformLaw (-1) 1 ∧
  (∀ᵐ xy ∂gapJointLaw, xy.1 ∈ Set.Icc (-2 : ℝ) 2 ∧ xy.2 ∈ Set.Icc (-1 : ℝ) 1) ∧
  mean gapJointLaw Prod.fst = 0 ∧ gapPDF 0 = 0 ∧
  IsCEF gapJointLaw Prod.fst Prod.snd (fun _ => 0) ∧
  ContDiff ℝ 1 pdaBump ∧
  (∀ x, 0 < gapPDF x → pdaBump x = 0) ∧
  deriv (fun _ : ℝ => (0 : ℝ)) 0 = 0 ∧
  (∀ a : ℝ, IsCEF gapJointLaw Prod.fst Prod.snd (fun x => a*pdaBump x) ∧
    deriv (fun x => a*pdaBump x) (mean gapJointLaw Prod.fst) = a) := by
  obtain ⟨hprob, hjoint, hpdf, hsnd, hprod, hbounds, hmean, hgap,
    hcef, hC1, hfamily, _⟩ := pda_at_mean_not_identified
  exact ⟨hprob, hjoint, hprod, hpdf, hsnd, hbounds, hmean, hgap,
    hcef, hC1, pda_extrapolation_witness_bump_zero_on_support,
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).deriv, hfamily⟩

end
end AronowAudit.P001.Wave1
