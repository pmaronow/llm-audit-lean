import SAP.P018a.Defs.WholeW1
import SAP.P018a.Bridge
import AronowAudit.P018.Wave1.Gap.GLP0181B1
import AronowAudit.P018.Wave1.Gap.GLP0181B3
import AronowAudit.P018.Wave1.Gap.GP0181B3
import AronowAudit.P018.Wave1.Gap.GLP0181B5
import AronowAudit.P018.Wave1.Gap.GLP0182B1
import AronowAudit.P018.Wave1.Gap.GP0182B1
import AronowAudit.P018.Wave1.Gap.GLP0182B2
import AronowAudit.P018.Wave1.Gap.GLP0182B3
import AronowAudit.P018.Wave1.Gap.GLP0182B4
import AronowAudit.P018.Wave1.Gap.GP0182B2
import AronowAudit.P018.Wave1.Gap.GP0181B1
import AronowAudit.P018.Wave1.Gap.GP0181B2
import AronowAudit.P018.Wave1.Gap.DecideC
import AronowAudit.P018.Wave1.Gap.TailBSignDegeneracy
import AronowAudit.P018.Wave1.WeightedConsistency


set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem existing_T9 : T9Statement := by
  exact ⟨AronowAudit.P018.Wave1.concentrated_weights_counterexample_proof,
    AronowAudit.P018.Wave1.concentrated_repetitions_counterexample_proof⟩

theorem existing_T10 : T10Statement := by
  refine ⟨?_, ?_, ?_, AronowAudit.P018.Wave1.concentrated_weights_counterexample_proof.1,
    AronowAudit.P018.Wave1.appendixB_counterexample_proof.1,
    AronowAudit.P018.Wave1.appendixB_counterexample_proof.2.1,
    AronowAudit.P018.Wave1.concentrated_weights_counterexample_proof.2.2.2.2⟩
  · intro U _ k R hR hCommon hT H hH hlim hMean
    exact AronowAudit.P018.Wave1.repeated_consistency_with_overlap_mean_control
      (Bridge.toRepeated R) hR hCommon hT H hH hlim hMean
  · intro U _ k K hK w a ha hWeights H hH hlim
    have hlimR : Tendsto (fun N : ℕ => recordWeightedH (singleRecord K)
        (fun d _ => w N d / a N)) atTop (𝓝 H) := by
      simpa only [Bridge.singleWeightedH] using hlim
    have h := AronowAudit.P018.Wave1.weighted_consistency_common_directed_kernel
      (Bridge.toRepeated (singleRecord K)) (Bridge.singleStanding K hK)
      (fun _ _ => (show (1 : ℕ) ≤ 2 by decide)) K.X K.Y (fun _ _ _ => false)
      (fun _ _ => (show Function.Injective (fun _ : Fin 1 => false) from
        fun _ _ _ => Subsingleton.elim _ _))
      (fun _ _ _ _ _ => ⟨rfl,rfl⟩) (fun N d _ => w N d) a ha
      (by obtain ⟨C,hC⟩ := hWeights; exact ⟨C,fun N d _ => hC N d⟩) H hH
      hlimR
    change inProbability (unitSampleLaw K) (fun N ω =>
      (N : ℝ) • recordWeightedVariance (singleRecord K) (fun d _ => w N d) ω -
        recordWeightedTarget (singleRecord K) (fun d _ => w N d)) at h
    simpa only [Bridge.singleWeightedVariance, Bridge.singleWeightedTarget] using h
  · intro U _ k N R w a ha _ ω _ _
    exact AronowAudit.P018.weighted_scale_invariance (Bridge.toRepeated R) w a ha ω

theorem existing_T11 : T11Statement := by
  exact ⟨AronowAudit.P018.Wave1.printed_targets_counterexample_proof,
    AronowAudit.P018.scalar_target_counterexample⟩

theorem existing_T13 : T13Statement := by
  have hFit := AronowAudit.P018.logistic_counterexample
  have hScore := AronowAudit.P018.logistic_witness_is_MLE.2.2
  have hDet : (AronowAudit.P018.logisticBread logitX 0).det = 35/4 := hFit.2.2.2.1
  have hIdentity := AronowAudit.P018.logistic_correction sixMembers
    (by decide) (by decide) logitX logitY 0 hFit.1 (by rw [hDet]; norm_num)
  refine ⟨hFit, AronowAudit.P018.logistic_numeric_certificate,
    AronowAudit.P018.logistic_covariances_positive, hScore, hIdentity.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hP : sandwich (logisticBread logitX 0)⁻¹
        (printedLogisticMeat sixMembers logitX logitR) = !![8/5,-2/5;-2/5,6/35] := hFit.2.2.2.2.1
    have hC : logisticVariance sixMembers logitX logitY 0 =
        !![38/25,-64/175;-64/175,192/1225] := hFit.2.2.2.2.2.1
    rw [hP,hC]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  · intro d
    fin_cases d <;> norm_num [expit,dot,logitY,logitR,Fin.sum_univ_succ]
  · norm_num [logisticBread,expit,dot,logitH,logitX,outer,Fin.sum_univ_succ,
      funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]
  · apply Matrix.inv_eq_left_inv
    have hB : logisticBread logitX 0 = logitH := by
      norm_num [logisticBread,expit,dot,logitH,logitX,outer,Fin.sum_univ_succ,
        funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]
    rw [hB]
    exact AronowAudit.P018.logistic_numeric_certificate.2.2.2.1
  · norm_num [sampleGram,logitX,outer,Fin.sum_univ_succ,Matrix.det_fin_two]
  · intro d
    fin_cases d <;> norm_num [sixMembers,logitR,Fin.sum_univ_succ]

theorem T8_existing_whole : T8WholeStatement := by
  constructor
  · intro U _ k K hK
    obtain ⟨hCLT,hTarget,hVariance,hPivot⟩ :=
      AronowAudit.P018.Wave1.inference_corrected_proof (Bridge.toKernel K) hK
    refine ⟨?_,hCLT,hTarget,hVariance,?_⟩
    · ext a b
      exact (AronowAudit.P018.Wave1.vc3_shared_integral (Bridge.toKernel K) hK a b).symm
    · intro c hc
      exact ⟨(hPivot c hc).1,(hPivot c hc).2, fun α hα =>
        AronowAudit.P018.Wave1.contrast_coverage_corrected_proof (Bridge.toKernel K) hK c hc α hα⟩
  · obtain ⟨h1,_,_,h4,_,h6,_,h8,h9,_⟩ :=
      AronowAudit.P018.Wave1.TailB_degenerate_inference_counterexample
    exact ⟨h1,h4,h6,h8,h9⟩

end SAP.P018a.WH.W1
