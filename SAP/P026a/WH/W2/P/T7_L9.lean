import SAP.P026a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.WH.W2.P.T7_L9

open Finset
open scoped BigOperators
noncomputable section

/-- The exact ninety within-block FE slopes, arranged by the first and second
block assignments. Repeated rows are retained to make the indexing explicit. -/
def slopeCache (w : W2Allocation) : ℚ :=
  (![![10/23, 10/23, 1/14, 1/14, 1/14, 17/28, 26/103, 26/103, 26/103, 26/103, 26/103, 26/103, -2/11, -2/11, -2/11],
     ![3/8, 3/8, 1/39, 1/39, 1/39, 7/13, 7/36, 7/36, 7/36, 7/36, 7/36, 7/36, -7/31, -7/31, -7/31],
     ![1/8, 1/8, -3/13, -3/13, -3/13, 11/39, -1/12, -1/12, -1/12, -1/12, -1/12, -1/12, -17/31, -17/31, -17/31],
     ![3/8, 3/8, 1/39, 1/39, 1/39, 7/13, 7/36, 7/36, 7/36, 7/36, 7/36, 7/36, -7/31, -7/31, -7/31],
     ![1/8, 1/8, -3/13, -3/13, -3/13, 11/39, -1/12, -1/12, -1/12, -1/12, -1/12, -1/12, -17/31, -17/31, -17/31],
     ![2/23, 2/23, -2/7, -2/7, -2/7, 1/4, -14/103, -14/103, -14/103, -14/103, -14/103, -14/103, -7/11, -7/11, -7/11]] : Fin 6 → Fin 15 → ℚ) w.1 w.2

theorem treatmentMean_cache (w : W2Allocation) (b : Bool) :
    paperTableTreatmentMean w b = AronowAudit.P026.tableTreatmentMeanCertificate w b := by
  have h := AronowAudit.P026.table_treatment_mean_certificate w b
  simpa [paperTableTreatmentMean, paperTableUnitDesign, paperTableDesign,
    paperTableCluster, AronowAudit.P026.tableTreatmentMean,
    AronowAudit.P026.tableUnitDesign, AronowAudit.P026.tableDesign,
    AronowAudit.P026.tableCluster, armIndicator, AronowAudit.P026.indicator,
    twoOfFourLaw, paperTwoOfSix, AronowAudit.P026.twoOfFour,
    AronowAudit.P026.twoOfSix] using h

theorem feEstimate_cache : ∀ w : W2Allocation, w2FeEstimate w = slopeCache w := by
  simp only [w2FeEstimate, paperTableCenteredT, paperTableCenteredY,
    treatmentMean_cache]
  decide +kernel

theorem feEstimate_eq_cache : w2FeEstimate = slopeCache := by
  funext w
  exact feEstimate_cache w

theorem fe_mean : mean paperTableDesign w2FeEstimate = -617206277/39696717060 := by
  rw [feEstimate_eq_cache]
  unfold mean paperTableDesign
  decide +kernel

theorem fe_variance : designVariance paperTableDesign w2FeEstimate =
    9703846625536373627/121217641949361157200 := by
  rw [feEstimate_eq_cache]
  unfold designVariance designCovariance mean paperTableDesign
  decide +kernel

end
end SAP.P026a.WH.W2.P.T7_L9

theorem SAP.P026a.WH.W2.T7_L9_proof : SAP.P026a.WH.W2.T7_L9 := by
  change SAP.P026a.w2ATECertificate SAP.P026a.w2FeEstimate
    (-16/1000) (283/1000) (283/1000) (80/1000)
  unfold SAP.P026a.w2ATECertificate SAP.P026a.roundsToThree SAP.P026a.sdRoundsToThree
  rw [SAP.P026a.WH.W2.P.T7_L9.fe_mean, SAP.P026a.WH.W2.P.T7_L9.fe_variance]
  norm_num
