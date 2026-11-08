import SAP.P045a.WH.W1.Proofs.T1
import SAP.P045a.WH.W1.Proofs.T2
import SAP.P045a.WH.W1.Proofs.T3
import SAP.P045a.WH.W1.Proofs.T5
import SAP.P045a.WH.W1.Proofs.T7
import SAP.P045a.WH.W2.Proofs.T10
import SAP.P045a.WH.W2.Proofs.T12
import SAP.P045a.WH.W2.Proofs.T13
import SAP.P045a.WH.W2.Proofs.T15
import SAP.P045a.Defs
import SAP.P045a.Bridge
import AronowAudit.P045.P045_Spillover
import AronowAudit.P045.Wave1.Gap.GLP041P042P045P045B2
import AronowAudit.P041.Wave1.Gap.GP041P042P045B2
import AronowAudit.P045.Wave1.Gap.GLP041P042P045P045B1
import AronowAudit.P045.Wave1.Gap.FidP045

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a
open Bridge

theorem T1 : SAP.P045a.T1WholeStatement := SAP.P045a.WH.W1.T1_whole

theorem T2 : SAP.P045a.T2WholeStatement := SAP.P045a.WH.W1.T2_whole

theorem T3 : SAP.P045a.T3WholeStatement := SAP.P045a.WH.W1.T3_whole

theorem T4 : T4Statement := by
  exact ⟨@AronowAudit.P045.Wave1.direct_variance_correction_proof,
    @AronowAudit.P045.Wave1.singleton_drop_bias_proof,
    @AronowAudit.P045.Wave1.singleton_drop_dilated_bias_proof,
    AronowAudit.P045.toy_required_direct_variance_undefined⟩

theorem T5 : SAP.P045a.T5WholeStatement := SAP.P045a.WH.W1.T5_whole

theorem T6 : T6Statement := by
  refine ⟨?_,?_,?_⟩
  · intro n A z i
    exact AronowAudit.P045.full_neighborhood_events (network A) z i
  · intro Ω inst p E instE Y hp
    exact AronowAudit.P045.event_ht_conditional p.mass E Y
  · intro n hn p A Y hT hC pT pC
    exact AronowAudit.P045.full_neighborhood_ht_correction hn (design p) (network A) Y hT hC pT pC

theorem T7 : SAP.P045a.T7WholeStatement := SAP.P045a.WH.W1.T7_whole

theorem T8 : T8Statement := by
  refine ⟨AronowAudit.P045.nonmonotone_hajek_counterexample,
    AronowAudit.P045.deletion_domain_certificate,?_,?_⟩
  · intro d R hR
    obtain ⟨hd,hcells⟩ := AronowAudit.P045.deletion_domain_certificate d R hR
    have hp (i : Fin 10) : 0 < (measuredDegree R i : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hd i).1)
    have hc (i : Fin 10) : 0 < 9 - (measuredDegree R i : ℝ) := by
      have hb : (measuredDegree R i : ℝ) ≤ 6 := by exact_mod_cast (hd i).2
      linarith
    refine ⟨fun i => ⟨div_pos (hp i) (by norm_num), div_pos (hc i) (by norm_num)⟩,?_,?_⟩
    · intro t
      exact Finset.sum_pos (fun i _ => one_div_pos.mpr (hp i)) (hcells t).1
    · intro t
      exact Finset.sum_pos (fun i _ => one_div_pos.mpr (hc i)) (hcells t).2
  · have h := AronowAudit.P045.nonmonotone_hajek_counterexample.1
    norm_num [deletionMasks, Finset.card_powersetCard, show printedEdges.card = 20 from h, Nat.choose]

theorem T9 : T9Statement := by
  refine ⟨AronowAudit.P045.corrected_copy_symmetric,
    AronowAudit.P045.corrected_copy_monotone,?_,?_,AronowAudit.P045.hajek_bias_correction⟩
  · intro n T S hsub z i
    have h := AronowAudit.P045.deletion_exposure_inclusions (network T) (network S) hsub z i
    simp only [exposure_pred, decode_d11, decode_d10, decode_d01, decode_d00] at h
    exact h
  · intro n hn p T S hsub y h0 h1
    have h0' : ∀ i, 0 < AronowAudit.P045.exposureProb (design p).mass
        (AronowAudit.P045.exposure (network S).adj) i .d00 := by
      intro i
      rw [exposureProb_eq, decode_d00]
      exact h0 i
    have h1' : ∀ i, 0 < AronowAudit.P045.exposureProb (design p).mass
        (AronowAudit.P045.exposure (network S).adj) i .d01 := by
      intro i
      rw [exposureProb_eq, decode_d01]
      exact h1 i
    have h := AronowAudit.P045.missing_ties_ht_bias hn (design p) (network T) (network S)
      hsub (outcome y) h0' h1'
    dsimp only at h ⊢
    simp only [outcome, exposure_decode, htObserved_eq, exposure_pred,
      exposureProb_eq, decode_d11, decode_d10, decode_d01, decode_d00,
      AronowAudit.P045.effect, SAP.P045a.effect] at h
    exact h

theorem T10 : SAP.P045a.T10WholeStatement := SAP.P045a.WH.W2.T10_whole

theorem T11 : T11Statement := by
  exact @AronowAudit.P045.greedy_three_net_correction

theorem T12 : SAP.P045a.T12WholeStatement := SAP.P045a.WH.W2.T12_whole

theorem T13 : SAP.P045a.T13WholeStatement := SAP.P045a.WH.W2.T13_whole

theorem T14 : T14Statement := by
  exact ⟨AronowAudit.P045.pooling_counterexample,
    AronowAudit.P045.pooling_empty_subclass,
    AronowAudit.P045.pooling_population_counterexample⟩

theorem T15 : SAP.P045a.T15WholeStatement := SAP.P045a.WH.W2.T15_whole

theorem T16 : T16Statement := by
  unfold T16Statement
  have h := AronowAudit.P045.empty_cell_counterexample
  simp only [pairExposureProb_eq, pairCellNonempty_eq, exposure_pred,
    pairHT_dilated_fun, printedContrast_fun, project_forall,
    decode_d11, decode_d10, decode_d01, decode_d00] at h
  simp only [sap_forall]
  exact h

end SAP.P045a
