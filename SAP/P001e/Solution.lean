import SAP.P001e.Defs
import SAP.P001e.Bridge
import SAP.P001e.Bridge.DoseIdentification
import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.Wave1.Gap.WP001dB3
import AronowAudit.P001.Wave1.Gap.GLP0014B4
import AronowAudit.P001.Wave1.Gap.GP0014B2b
import AronowAudit.P001.Wave1.Gap.GP0014B3
import SAP.P001e.WH.W1.Proofs.T77
import SAP.P001e.WH.W1.Proofs.T78
import SAP.P001e.WH.W1.Proofs.T79
import SAP.P001e.WH.W1.Proofs.T80
import SAP.P001e.WH.W1.Proofs.T83
import SAP.P001e.WH.W2.Proofs.T94
import SAP.P001e.WH.W2.Proofs.T85
import SAP.P001e.WH.W2.Proofs.T87
import SAP.P001e.WH.W2.Proofs.T89
import SAP.P001e.WH.W4.Proofs.T93

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e
universe u v w

theorem T77 : SAP.P001e.T77WholeStatement :=
  SAP.P001e.WH.W1.T77_whole

theorem T78 : SAP.P001e.T78WholeStatement :=
  SAP.P001e.WH.W1.T78_whole

theorem T79 : SAP.P001e.T79WholeStatement :=
  SAP.P001e.WH.W1.T79_whole

theorem T80 : SAP.P001e.T80WholeStatement :=
  SAP.P001e.WH.W1.T80_whole

theorem T81 : T81Statement := by
  rcases AronowAudit.P001.hot_deck_correct_donor_comparison with
    ⟨h1,h2,h3,h4,h5,h6,h7,h8,hm⟩
  have hc : hotDeckCompleted = ![2,2,3,10,12,3] := by
    funext i
    fin_cases i <;> norm_num [hotDeckCompleted, hotDeckDonor, hotDeckData]
  refine ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8⟩, ?_, hc, ?_⟩
  · norm_num [HotDeckDonors, UniqueNearest, respondents, exampleScores]
  · simpa only [hc] using hm

theorem T82 : T82Statement.{u,v} := by
  refine ⟨Bridge.T82Core_iff.mpr
    (@AronowAudit.P001.Wave1.binary_response_conditional_propensity_exists), ?_⟩
  intro q
  by_cases h : 0 < q
  · exact Or.inl h
  · exact Or.inr (by linarith)

theorem T83 : SAP.P001e.T83WholeStatement :=
  SAP.P001e.WH.W1.T83_whole

theorem T84 : T84Statement :=
  ⟨Bridge.T84Core_iff.mpr (@AronowAudit.P001.missing_ipw_logit_ml_counterexample), by norm_num⟩

theorem T85 : SAP.P001e.T85WholeStatement :=
  SAP.P001e.WH.W2.T85_whole

theorem T86 : T86Statement.{u,v} :=
  Bridge.T86Statement_iff.mpr (@AronowAudit.P001.response_weights_denominator_correction)

theorem T87 : SAP.P001e.T87WholeStatement :=
  SAP.P001e.WH.W2.T87_whole

theorem T88 : T88Statement.{u} :=
  Bridge.T88Statement_iff.mpr (@AronowAudit.P001.Wave1.ate_sharp_endpoint_estimation_ae_support)

theorem T89 : SAP.P001e.T89WholeStatement :=
  SAP.P001e.WH.W2.T89_whole

theorem T90 : T90Statement := by
  rcases Bridge.spike_witness with ⟨hlaw,hsp,hne⟩
  exact ⟨hlaw,hsp,by norm_num [spikeResponse],hne⟩

theorem T91 : SAP.P001e.T91IdentificationStatement.{u,v,w} :=
  ⟨Bridge.t91_positive_mass, Bridge.t91_continuous⟩

theorem T92 : T92Statement := by
  rcases Bridge.example_fit with ⟨hu,hfit⟩
  rcases Bridge.printed_numbers with ⟨hp,hb,hd,hn⟩
  have hf : fullImputation ![1,8,9,3,5,7]=6178/2437 := by
    norm_num [fullImputation, examplePrediction, exampleCoef, exampleX2, Fin.sum_univ_succ]
  refine ⟨hu,hfit,hp,hf,hd,?_⟩
  rw [hf, ← hb]
  exact hn

theorem T93 : SAP.P001e.T93WholeStatement_W4 :=
  SAP.P001e.WH.W4.T93_whole

theorem T94 : SAP.P001e.T94WholeStatement :=
  SAP.P001e.WH.W2.T94_whole

theorem T95 : T95Statement := by
  rcases AronowAudit.P001.matching_correct_donor_comparison with
    ⟨h1,h2,h3,h4,h5,h6,h7,h8,hm⟩
  have hc : matchingControl = ![5,5,0,5,0,0] := by
    funext i
    fin_cases i <;> norm_num [matchingControl, matchingDonor, exampleD, exampleY]
  have ht : matchingTreatment = ![2,2,3,10,2,3] := by
    funext i
    fin_cases i <;> norm_num [matchingTreatment, matchingDonor, exampleD, exampleY]
  refine ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8⟩, ?_, ?_, hc, ht, ?_, ?_, ?_⟩
  · norm_num [HotDeckDonors, UniqueNearest, respondents, exampleScores]
  · norm_num [MatchingDonors, UniqueNearest, nonrespondents, exampleScores]
  · rw [ht]; norm_num [Fin.sum_univ_succ]
  · rw [hc]; norm_num [Fin.sum_univ_succ]
  · simpa only [hc, ht] using hm

end SAP.P001e
