import AronowAudit.P011.Wave1.PackageOLSBlueprint
import AronowAudit.P011.P011_BlockOLSCompletion

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PackageOLS

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne AronowAudit.P011.Wave1.CorollaryOne
  MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Matrix

noncomputable section

/-- The path mean-model theorem includes coordinate integrability. -/
theorem n2_proof : N2 := by
  intro k
  have hmean := (block_ols_representations.1 (2 : ℝ) (Or.inr rfl) (k + 1) (by omega)).1
  change MeanModel (pathModel 2 (k + 1)) (olsDesign k) olsCoef
  norm_num only at hmean
  exact hmean

end

end AronowAudit.P011.Wave1.PackageOLS
