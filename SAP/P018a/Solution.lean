import SAP.P018a.WH.W1.Proofs.T13
import SAP.P018a.WH.W1.Proofs.T8
import SAP.P018a.WH.W1.Proofs.T9
import SAP.P018a.WH.W1.Proofs.T10
import SAP.P018a.WH.W1.Proofs.T11
import SAP.P018a.WH.W2.Proofs.T12
import SAP.P018a.WH.W2.Proofs.T1
import SAP.P018a.WH.W2.Proofs.T3
import SAP.P018a.WH.W2.Proofs.T7
import SAP.P018a.WH.W3.Proofs.T2
import SAP.P018a.Defs
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
namespace SAP.P018a
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem T1 : SAP.P018a.T1WholeStatement := SAP.P018a.WH.W2.T1_whole

theorem T2 : SAP.P018a.T2WholeStatement_W3 := SAP.P018a.WH.W3.T2_whole

theorem T3 : SAP.P018a.T3WholeStatement := SAP.P018a.WH.W2.T3_whole

theorem T4 : T4Statement := by
  refine ⟨fun K hK => AronowAudit.P018.Wave1.variance_consistency_corrected_proof
      (Bridge.toKernel K) hK,
    AronowAudit.P018.corrected_chebyshev, ?_⟩
  intro Ω _ μ _ Z hZ V hMean hVar c hc
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun N => AronowAudit.P018.corrected_chebyshev (μ N) (Z N) (hZ N) V c hc)
  simpa using tendsto_const_nhds.mul (hVar.add (hMean.pow 2))

theorem T5 : T5Statement := by
  exact ⟨AronowAudit.P018.two_role_counterexample,
    AronowAudit.P018.gls_variance_counterexample,
    AronowAudit.P018.Wave1.random_intercept_lower_bound_proof⟩

theorem T6 : T6Statement := by
  exact ⟨AronowAudit.P018.Wave1.benchmark_covariance_correction_proof,
    AronowAudit.P018.shared_random_effect_covariance,
    AronowAudit.P018.correct_gls_identity⟩

theorem T7 : SAP.P018a.T7WholeStatement := SAP.P018a.WH.W2.T7_whole

theorem T8 : SAP.P018a.T8WholeStatement := SAP.P018a.WH.W1.T8_whole

theorem T9 : SAP.P018a.T9WholeStatement := SAP.P018a.WH.W1.T9_whole

theorem T10 : SAP.P018a.T10WholeStatement := SAP.P018a.WH.W1.T10_whole

theorem T11 : SAP.P018a.T11WholeStatement := SAP.P018a.WH.W1.T11_whole

theorem T12 : SAP.P018a.T12WholeStatement := SAP.P018a.WH.W2.T12_whole

theorem T13 : SAP.P018a.T13WholeStatement := SAP.P018a.WH.W1.T13_whole

theorem T14 : T14Statement := by
  constructor
  · intro V E _ _ _ _ s hs hi k X Y β hY hH
    obtain ⟨hp,hi,hv,hf⟩ := AronowAudit.P018.logistic_correction s hs hi X Y β hY hH
    exact ⟨hp,hi,AronowAudit.P018.meat_symmetric s _,hv,hf⟩
  · have h := AronowAudit.P018.logistic_numeric_certificate
    have hP : printedLogisticMeat sixMembers logitX logitR = logitH := h.2.2.2.2.1
    have hC : meat sixMembers (fun d => score (logitX d) (logitR d)) =
        !![3/2,7/2;7/2,27/2] := h.2.2.2.2.2.1
    rw [hP, hC]
    intro he
    have he11 := congrArg (fun M : Mat 2 => M 1 1) he
    norm_num [logitH] at he11

end SAP.P018a
