import SAP.P054.Defs
import SAP.P054.Bridge
import AronowAudit.P054.P054_Reconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P054

theorem T1 : T1Statement := by
  intro N hN d w y hd hy hw hn
  have h :
      (∑ i, ratioResidual d w y i) = 0 ∧
      linearisationVariance d w y =
        (N : ℝ) / ((N : ℝ) - 1) * squaredWeightTerm d w y ∧
      (∀ c : ℝ, 0 < c → w = (fun _ => c) →
        squaredWeightTerm d w y = referenceVariance d w y) := by
    simpa only [linearisationVariance, squaredWeightTerm, referenceVariance,
      Bridge.groupCount_eq, Bridge.groupWeight_eq, Bridge.weightedProportion_eq,
      Bridge.ratioResidual_eq, mul_div_assoc] using
      (AronowAudit.P054.ratio_reconstruction hN d w y hd hy hw
        (by simpa only [Bridge.groupCount_eq] using hn))
  refine ⟨h.1, h.2.1, ?_⟩
  intro c hc heq
  have hequal := h.2.2 c hc heq
  exact ⟨hequal, h.2.1.trans (congrArg
    (fun x : ℝ => (N : ℝ) / ((N : ℝ) - 1) * x) hequal)⟩

theorem T2 : T2Statement := by
  intro N _hN d w y hd hy hw hn
  have h :
      weightedResidualSumSquares d w y =
        groupWeight d w * weightedProportion d w y * (1 - weightedProportion d w y) ∧
      classicalWlsVariance d w y =
        weightedProportion d w y * (1 - weightedProportion d w y) / (groupCount d - 1) ∧
      weightedProportion d w y * (1 - weightedProportion d w y) / (groupCount d - 1) =
        groupCount d / (groupCount d - 1) * referenceVariance d w y := by
    simpa only [classicalWlsVariance, weightedResidualSumSquares, referenceVariance,
      Bridge.groupCount_eq, Bridge.groupWeight_eq, Bridge.weightedProportion_eq] using
      (AronowAudit.P054.classical_intercept_wls d w y hd hy hw
        (by simpa only [Bridge.groupCount_eq] using hn))
  exact ⟨h.1, h.2.1, h.2.1.trans h.2.2⟩

end SAP.P054
