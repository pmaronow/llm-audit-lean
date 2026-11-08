import SAP.P026a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000

namespace SAP.P026a.WH.W1.P.T6_L4

lemma paper_fe_eq (w : Fin 6 × Fin 15) :
    SAP.P026a.paperFeEstimate w = AronowAudit.P026.feEstimate w := by
  rfl

lemma paper_fe_certificate (w : Fin 6 × Fin 15) :
    SAP.P026a.paperFeEstimate w = AronowAudit.P026.feCoefficientCertificate w := by
  rw [paper_fe_eq, AronowAudit.P026.fe_estimate_certificate]

lemma sharpened_moments :
    (-13987427/1000000000 : ℚ) < SAP.P026a.mean SAP.P026a.paperTableDesign SAP.P026a.paperFeEstimate ∧
    SAP.P026a.mean SAP.P026a.paperTableDesign SAP.P026a.paperFeEstimate < (-13987425/1000000000 : ℚ) ∧
    (77734705/1000000000 : ℚ) < SAP.P026a.designVariance SAP.P026a.paperTableDesign SAP.P026a.paperFeEstimate ∧
    SAP.P026a.designVariance SAP.P026a.paperTableDesign SAP.P026a.paperFeEstimate < (77734706/1000000000 : ℚ) := by
  unfold SAP.P026a.mean SAP.P026a.designVariance SAP.P026a.designCovariance
  simp only [SAP.P026a.paperTableDesign]
  simp_rw [paper_fe_certificate]
  decide +kernel

end SAP.P026a.WH.W1.P.T6_L4

theorem SAP.P026a.WH.W1.T6_L4_proof : SAP.P026a.WH.W1.T6_L4 := by
  unfold SAP.P026a.WH.W1.T6_L4
  exact SAP.P026a.WH.W1.P.T6_L4.sharpened_moments
