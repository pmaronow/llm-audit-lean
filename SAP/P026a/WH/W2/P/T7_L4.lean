import SAP.P026a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace SAP.P026a.WH.W2.P.T7_L4

theorem paper_mean_eq_audit : ∀ w b,
    SAP.P026a.paperTableTreatmentMean w b =
      AronowAudit.P026.tableTreatmentMean w b := by
  unfold SAP.P026a.paperTableTreatmentMean AronowAudit.P026.tableTreatmentMean
  decide +kernel

theorem paper_mean_certificate : ∀ w b,
    SAP.P026a.paperTableTreatmentMean w b =
      AronowAudit.P026.tableTreatmentMeanCertificate w b := by
  intro w b
  rw [paper_mean_eq_audit w b, AronowAudit.P026.table_treatment_mean_certificate]

end SAP.P026a.WH.W2.P.T7_L4

theorem SAP.P026a.WH.W2.T7_L4_proof : SAP.P026a.WH.W2.T7_L4 := by
  unfold SAP.P026a.WH.W2.T7_L4 SAP.P026a.w2ValidFit SAP.P026a.w2Gram
    SAP.P026a.w2Predict SAP.P026a.w2FeDesign SAP.P026a.w2FeBeta
    SAP.P026a.w2FeEstimate SAP.P026a.w2Treatment
  simp only [SAP.P026a.paperTableCenteredT,
    SAP.P026a.WH.W2.P.T7_L4.paper_mean_certificate]
  decide +kernel
