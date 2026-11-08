import SAP.P003b.Defs
import SAP.P003b.Bridge
import AronowAudit.P003.Wave1.Gap.GP0031B3
import AronowAudit.P003.Wave1.Gap.GP0031B3b
import AronowAudit.P003.Wave1.Gap.GP0032B2
import AronowAudit.P003.Wave1.Gap.GLP0032B7
import AronowAudit.P003.Wave1.Gap.GP0031B2
import AronowAudit.P003.Wave1.Gap.GLP0032B3
import AronowAudit.P003.Wave1.Gap.GLP0032B6
import AronowAudit.P003.Wave1.Gap.GLP0032B2
import AronowAudit.P003.Wave1.Gap.GP0032B1b
import AronowAudit.P003.Wave1.Gap.GLP0032B5
import AronowAudit.P003.Wave1.Gap.GLP0032B4
import AronowAudit.P003.Wave1.Gap.GLP0031B2
import AronowAudit.P003.Wave1.Gap.GP0031B1b
import SAP.P003b.WH.W1.Proofs.T18
import SAP.P003b.WH.W1.Proofs.T7
import SAP.P003b.WH.W1.Proofs.T32
import SAP.P003b.WH.W1.Proofs.T6
import SAP.P003b.WH.W2.Proofs.T36
import SAP.P003b.WH.W2.Proofs.T25
import SAP.P003b.WH.W2.Proofs.T19
import SAP.P003b.WH.W2.Proofs.T20
import SAP.P003b.WH.W2.Proofs.T30
import SAP.P003b.WH.W1.Proofs.T35

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P003b SAP.P003b.Bridge
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

 theorem SAP.P003b.T24 : T24Statement := by
  intro n w m hm hn
  have hf := AronowAudit.P003.corrected_sate w (by omega : 0 < n)
  have ht : (toCounts (tableCounts w)).total = 2*m := by
    simpa only [tableCounts_eq] using hf.1.trans hn
  have hmean := AronowAudit.P003.Wave1.balanced_mean_symmetry_proof (toCounts (tableCounts w)) m hm ht
  have htau : tau (tableCounts w) = tableTau w := hf.2.2.2.symm
  have hid : (∑ i, (bit (w i).1-bit (w i).2))/(m : ℝ) = 2*tableTau w := by
    unfold tableTau
    have hnR : (n : ℝ) = 2*(m : ℝ) := by exact_mod_cast hn
    rw [hnR]
    ring
  refine ⟨?_,?_,?_⟩
  · intro z hz
    have h := AronowAudit.P003.complement_estimator_identity w z m hm hn hz
    exact ⟨h.1,h.2.trans hid.symm,hid⟩
  · simpa only [designMean_eq,observed_eq,estimate_eq,tau_eq,htau] using hmean.1
  · simpa only [designProb_eq,observed_eq,estimate_eq,tau_eq,htau] using hmean.2

 theorem SAP.P003b.T25 : SAP.P003b.T25WholeStatement := SAP.P003b.WH.W2.T25_whole

 theorem SAP.P003b.T8 : T8Statement := by
  intro z hz
  exact ⟨AronowAudit.P003.Wave1.corrected_wald_row_proof z hz,
    AronowAudit.P003.Wave1.wald_median_and_hc0_proof z hz⟩

 theorem SAP.P003b.T19 : SAP.P003b.T19WholeStatement := SAP.P003b.WH.W2.T19_whole

 theorem SAP.P003b.T20 : SAP.P003b.T20WholeStatement := SAP.P003b.WH.W2.T20_whole

 theorem SAP.P003b.T26 : T26Statement := by
  have hcover := AronowAudit.P003.ConfidenceFollowup.badJointLaw_coverage
  rw [AronowAudit.P003.ConfidenceFollowup.badJointLaw_probability] at hcover
  have hc : designProb badPopulation 3 (fun q => tau badPopulation ∈
      missingInterval (109/500) (observed badPopulation q) (badMask q)) = 297/380 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat,badPopulation_eq,designProb_eq,badMask_eq,
      observed_eq,tau_eq,missingInterval_eq] using hcover
  refine ⟨rfl,by norm_num,by norm_num [badPopulation,Counts.total],by norm_num,by norm_num,
    by norm_num [tauQ,Counts.effect,Counts.total,badPopulation],?_,hc,by norm_num⟩
  intro q hq
  have hq' : toCounts q ∈ AronowAudit.P003.randomStates AronowAudit.P003.badPopulation 3 := by
    simpa only [badPopulation_eq,randomStates_eq,List.mem_map,to_inj,exists_eq_right] using hq
  have hd := bad_endpoints_native (toCounts q) hq'
  have hl := AronowAudit.P003.bad_mask_legal (toCounts q)
  refine ⟨?_,?_,?_⟩
  · simpa only [badMask_eq,badPopulation_eq,observed_eq,missingMasks_eq,List.mem_map,to_inj,exists_eq_right] using hl
  · simpa only [badPopulation_eq,observed_eq,badMask_eq,minusCompletion_eq,accepted_eq] using hd.1
  · simpa only [badPopulation_eq,observed_eq,badMask_eq,plusCompletion_eq,accepted_eq] using hd.2

 theorem SAP.P003b.T27 : T27Statement := by
  simpa only [T27Statement,printedExecution_eq,logTwo_eq] using AronowAudit.P003.ConfidenceFollowup.printed_search_claim_refuted

 theorem SAP.P003b.T30 : SAP.P003b.T30WholeStatement := SAP.P003b.WH.W2.T30_whole

 theorem SAP.P003b.T31 : T31Statement := by
  intro o α ho hα hne
  have h := AronowAudit.P003.Wave1.interval_length_bound_proof (toCounts o) α ho hα
    (by simpa only [accepted_eq] using hne)
  simpa only [upper_eq,lower_eq,total_eq] using h

 theorem SAP.P003b.T33 : T33Statement := by
  intro o v ho hn hmin hmax
  simpa only [pValue_any,from_to] using
    AronowAudit.P003.Wave1.balanced_pvalue_monotonicity_proof (toCounts o) (toCounts v) ho hn hmin hmax

 theorem SAP.P003b.T7 : SAP.P003b.T7WholeStatement := SAP.P003b.WH.W1.T7_whole

 theorem SAP.P003b.T32 : SAP.P003b.T32WholeStatement := SAP.P003b.WH.W1.T32_whole

 theorem SAP.P003b.T34 : T34Statement := by
  intro v m K α ε hm hn hsize hK hα hε
  have h :=
    AronowAudit.P003.Wave1.balanced_monte_coverage_proof (toCounts v) m K α ε hm hn hsize hK hα hε
  simp only [uniformProb_eq,canonicalObserved_eq,monteInterval_nativePool,monteInterval_eq,interval_eq,tau_eq,total_eq,logTwo_eq] at h ⊢
  convert h using 1 <;> rfl

 theorem SAP.P003b.T6 : SAP.P003b.T6WholeStatement := SAP.P003b.WH.W1.T6_whole

 theorem SAP.P003b.T35 : SAP.P003b.T35WholeStatement := SAP.P003b.WH.W1.T35_whole

 theorem SAP.P003b.T36 : SAP.P003b.T36WholeStatement := SAP.P003b.WH.W2.T36_whole

 theorem SAP.P003b.T18 : SAP.P003b.T18WholeStatement := SAP.P003b.WH.W1.T18_whole
