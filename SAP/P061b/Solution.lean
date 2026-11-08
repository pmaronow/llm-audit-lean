import SAP.P061b.Defs
import SAP.P061b.Bridge
import AronowAudit.P061.P061_Foundations
import AronowAudit.P061.P061_PaperDomains
import SAP.P061b.WH.W1.Proofs.T17
import SAP.P061b.WH.W1.Proofs.T19

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b
open Bridge
open scoped BigOperators Classical Topology

theorem T12 : T12Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω N D g y h hf d e hN hp hq
    have hd := AronowAudit.P061.sutva_design_free (toAudit D) g y h hf d e hN hp hq
    have he := AronowAudit.P061.sutva_design_free (toAudit D) g y h hf e d hN hq hp
    exact ⟨fun i => ⟨(hd.1 i).1, (he.1 i).1, (hd.1 i).2⟩, hd.2⟩
  · intro Ω N D D' g y hs d e hN hp hq
    exact AronowAudit.P061.sutva_design_invariance (toAudit D) (toAudit D') g y hs d e hN hp hq
  · intro Ω N D g y hs i d hp z hz
    exact AronowAudit.P061.sutva_epo_global (toAudit D) g y hs i d hp z hz
  · exact fun i z w h => h
  · intro D hp
    exact (AronowAudit.P061.household_sutva (toAudit D) hp).2
  · apply (AronowAudit.P061.household_sutva (toAudit bothOrNeither) _).2
    intro i
    fin_cases i <;>
      norm_num [AronowAudit.P061.pi, AronowAudit.P061.probability, toAudit,
        bothOrNeither, AronowAudit.P061.votingOutcome, tsum_fintype,
        Fintype.sum_prod_type, Fin.sum_univ_two]
  · apply (AronowAudit.P061.household_sutva (toAudit independentHousehold) _).2
    intro i
    fin_cases i <;>
      norm_num [AronowAudit.P061.pi, AronowAudit.P061.probability, toAudit,
        independentHousehold, AronowAudit.P061.votingOutcome, tsum_fintype,
        Fintype.sum_prod_type, Fin.sum_univ_two]

theorem T13 : T13Statement := by
  intro Ω N D g y
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hn
    refine ⟨?_, ?_, ?_⟩
    · intro i d hp z hz hg
      exact AronowAudit.P061.nurva_epo (toAudit D) g y hn i d hp z hz hg
    · intro i d e hp hq z w hz hw hg hk
      have hd := AronowAudit.P061.nurva_epo (toAudit D) g y hn i d hp z hz hg
      have he := AronowAudit.P061.nurva_epo (toAudit D) g y hn i e hq w hw hk
      exact congrArg₂ (· - ·) hd he
    · exact AronowAudit.P061.nurva_sutva_observational_equivalence (toAudit D) g y hn
  · exact AronowAudit.P061.sutva_implies_nurva (toAudit D) g y
  · intro y' he A
    exact AronowAudit.P061.observed_law_support (toAudit D) y y' he A
  · intro L
    constructor
    · rintro ⟨w, hw, hL⟩
      obtain ⟨w', hs, _, he⟩ :=
        AronowAudit.P061.nurva_sutva_observational_equivalence (toAudit D) g w hw
      exact ⟨w', hs, fun A => (he A).symm.trans (hL A)⟩
    · rintro ⟨w, hw, hL⟩
      exact ⟨w, AronowAudit.P061.sutva_implies_nurva (toAudit D) g w hw, hL⟩

theorem T14 : T14Statement := by
  obtain ⟨h1, h0, hm, hn, hs, hp, hu⟩ := AronowAudit.P061.household_tables
  refine ⟨h1, h0, hm, hn, hs, hp, hu, ?_⟩
  norm_num [ownAssignment, housemateAssignment, InSupport, oneTreated]

theorem T15 : T15Statement := by
  exact ⟨AronowAudit.P061.equilibrium_tables, AronowAudit.P061.hidden_version_tables⟩

theorem T16 : T16Statement := by
  intro Ω N D g y d hN hp hm
  have hd := (AronowAudit.P061.PaperDomains.ht_unbiased_T16_resolved
    (toAudit D) g y d hN hp hm).2
  refine ⟨hd.1, hd.2, ?_⟩
  intro e hq hm'
  have he := (AronowAudit.P061.PaperDomains.ht_unbiased_T16_resolved
    (toAudit D) g y e hN hq hm').2
  refine ⟨AronowAudit.P061.integrable_sub (toAudit D) hd.1 he.1, ?_⟩
  exact (AronowAudit.P061.expectation_sub (toAudit D) hd.1 he.1).trans
    (congrArg₂ (· - ·) hd.2 he.2)

theorem T17 : T17WholeStatement := SAP.P061b.WH.W1.T17_whole

theorem T18 : T18Statement := by
  intro Ω N D g y d e hN hp hn
  obtain ⟨hr, ht, hv, hc, hd⟩ :=
    AronowAudit.P061.nurva_exact_variances (toAudit D) g y d e hN hp hn
  refine ⟨hr, ht, ?_, hv, hc, hd, ?_, ?_⟩
  · exact hv.trans (indicator_sum D g y d).symm
  · intro i
    simp only [jointExposureProbability, exposureProbability, and_self]
  · intro hne i
    have he : ∀ z, ¬(g i z = d ∧ g i z = e) := fun z h => hne (h.1.symm.trans h.2)
    simp only [jointExposureProbability, eventProbability, he, ite_false, tsum_zero]

theorem T19 : T19WholeStatement := SAP.P061b.WH.W1.T19_whole

theorem T20 : T20Statement := by
  intro Ω N D g y F d hN hp hy hF hFd
  have hmain := AronowAudit.P061.PaperDomains.covariate_adjustment_T20
    (toAudit D) g y F d hN hp hy hF hFd
  refine ⟨hmain, ?_, ?_⟩
  · intro hi
    have hc := independent_prediction_calibrated D g F d hp hFd hi
    exact ⟨hc, hmain hc⟩
  · intro hi
    have hc := mean_independent_prediction_calibrated D g F d hp hi
    exact ⟨hc, hmain hc⟩

theorem T21 : T21Statement := by
  intro Ω D g y d b c hb hc hp hn h1 h2 hrate h3 ε hε
  have hr := (Filter.tendsto_add_atTop_iff_nat (f := fun N => b N / (N : ℝ)^2) 1).1 hrate
  have hi := (Filter.tendsto_add_atTop_iff_nat (f := fun N => b N * c N^2 / (N : ℝ)^2) 1).1 h3
  have h := AronowAudit.P061.ht_consistency (fun N => toAudit (D N)) g y d b c
    hb hc hp hn h1 h2 hr hi ε hε
  change Filter.Tendsto (fun N => AronowAudit.P061.probability (toAudit (D (N + 1))) (fun z =>
    |AronowAudit.P061.ht (toAudit (D (N + 1))) (g (N + 1)) (y (N + 1)) d z -
      AronowAudit.P061.aepo (toAudit (D (N + 1))) (g (N + 1)) (y (N + 1)) d| > ε)) _ _
  simpa only [Function.comp_def, sub_zero] using h.comp (Filter.tendsto_add_atTop_nat 1)

end SAP.P061b
