import SAP.P018b.WH.W3.Proofs.T27
import SAP.P018b.WH.W1.Proofs.T17
import SAP.P018b.WH.W1.Proofs.T18
import SAP.P018b.WH.W1.Proofs.T19
import SAP.P018b.WH.W1.Proofs.T20
import SAP.P018b.WH.W1.Proofs.T21
import SAP.P018b.WH.W2.Proofs.T22
import SAP.P018b.WH.W2.Proofs.T24
import SAP.P018b.Defs
import SAP.P018b.Bridge
import AronowAudit.P018.P018_Audit
import AronowAudit.P018.P018_PaperDomains
import AronowAudit.P018.Wave1.Gap.GLP0181B2
import AronowAudit.P018.Wave1.Gap.TailBRareLimits
import AronowAudit.P018.Wave1.Gap.GP0181B3
import AronowAudit.P018.Wave1.Gap.DecideC
import AronowAudit.P018.Wave1.PrintedLemma1
import AronowAudit.P018.Wave1.Gap.GLP0181B4
import AronowAudit.P018.Wave1.PrintedScalarCorollaries

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
open SAP.P018b SAP.P018b.Bridge

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Apply the exported factor-two identities and distribute the common bread. -/
theorem SAP.P018b.T15 : SAP.P018b.T15Statement := by
  constructor
  · intro V E _ _ _ _ s hs hi k T q P
    have h := AronowAudit.P018.ordered_index_general s hs hi T q
    have hm : (∑ i, orderedClusterMeat s T q i) - dyadMeat (fun d => ∑ t, q d t) -
        ((Fintype.card V : ℝ)-2) • individualMeat T q =
          meat s (fun d => ∑ t, q d t) + ((Fintype.card V : ℝ)-2) • individualMeat T q := h.2.2
    have hv := congrArg (sandwich P) hm
    simp only [sandwich, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul] at hv
    refine ⟨h.1, h.2.1, hm, hv, ?_⟩
    intro hn hne
    have hc : ((Fintype.card V : ℝ)-2) ≠ 0 := by
      have hn' : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
      linarith
    intro he
    have he' : sandwich P (meat s (fun d => ∑ t, q d t)) +
        ((Fintype.card V : ℝ)-2) • sandwich P (individualMeat T q) =
          sandwich P (meat s (fun d => ∑ t, q d t)) := hv.symm.trans he
    have hz : ((Fintype.card V : ℝ)-2) • sandwich P (individualMeat T q) = 0 :=
      add_left_cancel (he'.trans (add_zero _).symm)
    exact (smul_ne_zero hc hne) hz
  · have h : orderedSampleFacts := AronowAudit.P018.ordered_index_counterexample
    refine ⟨h, ?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · simpa only [individualMeat, dyadMeat, Fin.sum_univ_one] using h.1
    · have he := h.2.2.2.1
      simp only [orderedNonincidentMeat, Fin.sum_univ_two, Finset.sum_add_distrib, he]
      norm_num

theorem SAP.P018b.T16 : SAP.P018b.T16Statement := by
  intro V E _ _ _ _ s hs hi k T q P
  exact ⟨AronowAudit.P018.proposition2_corrected s hs hi T q P,
    AronowAudit.P018.appendixC_corrected_steps s hs hi T q⟩

theorem SAP.P018b.T17 : SAP.P018b.T17WholeStatement :=
  SAP.P018b.WH.W1.T17_whole

theorem SAP.P018b.T18 : SAP.P018b.T18WholeStatement :=
  SAP.P018b.WH.W1.T18_whole

theorem SAP.P018b.T19 : SAP.P018b.T19WholeStatement :=
  SAP.P018b.WH.W1.T19_whole

theorem SAP.P018b.T20 : SAP.P018b.T20WholeStatement :=
  SAP.P018b.WH.W1.T20_whole

theorem SAP.P018b.T21 : SAP.P018b.T21WholeStatement :=
  SAP.P018b.WH.W1.T21_whole

theorem SAP.P018b.T22 : SAP.P018b.T22WholeStatement :=
  SAP.P018b.WH.W2.T22_whole

theorem SAP.P018b.T23 : SAP.P018b.T23Statement := by
  exact ⟨@AronowAudit.P018.logistic_formula_correction,
    @AronowAudit.P018.logistic_summed_formulas, @AronowAudit.P018.generic_score_meat_psd⟩

theorem SAP.P018b.T24 : SAP.P018b.T24WholeStatement :=
  SAP.P018b.WH.W2.T24_whole

theorem SAP.P018b.T25 : SAP.P018b.T25Statement := by
  exact AronowAudit.P018.Wave1.benchmark_correspondence_printed_false

theorem SAP.P018b.T26 : SAP.P018b.T26Statement := by
  intro h
  apply AronowAudit.P018.Wave1.lemma1_printed_refuted
  intro U _ k K hK hrank
  exact h (fromKernel K) hK hrank

theorem SAP.P018b.T27 : SAP.P018b.T27WholeStatement_W3 :=
  SAP.P018b.WH.W3.T27_whole

theorem SAP.P018b.T28 : SAP.P018b.T28Statement := by
  exact AronowAudit.P018.Wave1.printed_corollaries_scalar_refuted
