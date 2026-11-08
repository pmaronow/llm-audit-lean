import SAP.P002a.Defs.WholeW4
import SAP.P002a.Bridge
import AronowAudit.P002.Wave1.Gap.DecisionLemma20

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W4

open SAP.P002a.Bridge

/-- The corrected canonical claim is exactly the scope of the existing four-limit
theorem. Copy the population fields through the definitionally equal bridge; no
new mathematical leaves are needed. -/
theorem T7_assembly : T7WholeStatement_W4 := by
  intro Ω _ μ _ sizes hsizes k P Z δ e A B r hk hδ he hA hB hr hP hpositive hZ sub hsub
  exact AronowAudit.P002.Wave1.corrected_lemma20_proof μ sizes hsizes k
    (fun n => toCovPopulation (P n)) Z δ e A B r hk hδ he hA hB hr hP hpositive hZ sub hsub

end SAP.P002a.WH.W4
