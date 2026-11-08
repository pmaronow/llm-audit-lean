import SAP.P018b.Defs.WholeW3
import SAP.P018b.Bridge
import AronowAudit.P018.Wave1.Gap.GP0182B2b

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b.WH.W3

/-- Assemble the scaled probability-limit assertion under Standing alone.
The kernel adapter preserves the population projection,
fitted residuals, ordered-overlap sandwich, product sampling laws and
unconditional variance target by definition. No new mathematical leaves remain. -/
theorem T27_assembly : T27WholeStatement_W3 := by
  intro U _ k K hK
  exact AronowAudit.P018.Wave1.GP0182B2b_variance_consistency (Bridge.toKernel K) hK

end SAP.P018b.WH.W3
