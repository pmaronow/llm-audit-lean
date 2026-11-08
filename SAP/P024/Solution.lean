import SAP.P024.Defs
import SAP.P024.Bridge
import AronowAudit.P024.P024_Designs
import AronowAudit.P024.P024_IndependentCompletion
import AronowAudit.P024.Wave1.Gap.DecisionT7
import SAP.P024.WH.W1.Proofs.T5
import SAP.P024.WH.W1.Proofs.T6
import SAP.P024.WH.W1.Proofs.T7
import SAP.P024.WH.W1.Proofs.T8
import SAP.P024.WH.W2.Proofs.T6
import SAP.P024.WH.W3.Proofs.T8

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Filter SAP.P024 SAP.P024.Bridge
noncomputable section

theorem SAP.P024.T1 : SAP.P024.T1Statement := by
  rcases AronowAudit.P024.calendar_ht_counterexample with
    ⟨hp,hb0,hb1,hb2,hb3,hne,hx0,hx1,hx2,ht,he,hv⟩
  rcases AronowAudit.P024.calendar_null_counterexample with
    ⟨hd0,hd1,hd2,hp0,hp1,hp2,hvalid⟩
  refine ⟨hp,hb0,hb1,hb2,hb3,?_,hne,hx0,hx1,hx2,ht,he,hv,
    hd0,hd1,hd2,hp0,hp1,hp2,AronowAudit.P024.calendar_p_grid,hvalid,?_⟩
  · intro t
    fin_cases t <;> norm_num [calendarTreated, calendarBaseline]
  · exact AronowAudit.P024.randomized_timing_no_trend_counterexample.2.2.1

theorem SAP.P024.T2 : SAP.P024.T2Statement := by
  rcases AronowAudit.P024.raw_before_after_bias with ⟨he,hne,_,_⟩
  rcases AronowAudit.P024.raw_observed_effect_bias with ⟨hshift,he2,hne2⟩
  refine ⟨?_,?_,he,hne,hshift,he2,hne2⟩
  · intro I Ω _ _ d z y0 y1 hE
    exact AronowAudit.P024.timing_overlap_unbiased (toDesign d) z y0 y1 hE
  · intro Ω _ _ D α h0 h1
    exact AronowAudit.P024.randomization_test_valid D α h0 h1

theorem SAP.P024.T4 : SAP.P024.T4Statement := by
  rcases AronowAudit.P024.dominant_complete_limits with ⟨hratio,hvar⟩
  rcases AronowAudit.P024.dominant_six_checks with
    ⟨htrue,hfalse,h20,h10,h64,h62,_,_⟩
  rcases AronowAudit.P024.dominant_six_actual_checks with ⟨hsizes,hvar6,hmin,hatt⟩
  refine ⟨AronowAudit.P024.dominant_total_size,
    AronowAudit.P024.dominant_individual_outcomes,AronowAudit.P024.dominant_effect,?_,
    (fun k => AronowAudit.P024.uniform_subsets_independent (k+2)),
    AronowAudit.P024.nonempty_arm_probability,?_,
    AronowAudit.P024.dominant_conditional_unbiased,
    AronowAudit.P024.dominant_complete_distribution,hratio,hvar,
    AronowAudit.P024.dominant_max_weight,AronowAudit.P024.dominant_share_limit,
    htrue,hfalse,h20,h10,h64,h62,hsizes,hvar6,hmin,hatt⟩
  · intro k s hs0 hs1
    have he := AronowAudit.P024.dominant_exact_value k s hs0 hs1
    have hm : 1 ≤ (s.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs0)
    have hmK : (s.card : ℝ) ≤ (k+2 : ℝ)-1 := by
      have hc : s.card < k+2 := by
        simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hs1)
      have hcNat : s.card + 1 ≤ k+2 := hc
      have hcR' : (s.card : ℝ)+1 ≤ (k : ℝ)+2 := by exact_mod_cast hcNat
      linarith
    have hb := AronowAudit.P024.dominant_error_bound (k+2 : ℝ) s.card
      (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith) hm hmK
      (decide ((0 : Fin (k+2)) ∈ s))
    have he' : populationEstimator (dominantPopulation k) (fun _ => 0) s =
        dominantValue (k+2 : ℝ) s.card (decide ((0 : Fin (k+2)) ∈ s)) := by
      simp only [populationEstimator, hs0, hs1, or_self, ite_false]
      convert he using 1 <;> rfl
    exact ⟨he', he' ▸ hb.1, hb.2⟩
  · intro empty
    exact ⟨fun k => AronowAudit.P024.dominant_probability_lower_bound k (empty k),
      AronowAudit.P024.dominant_cluster_inconsistent empty⟩

theorem SAP.P024.T5 : SAP.P024.T5WholeStatement := SAP.P024.WH.W1.T5_whole

theorem SAP.P024.T6 : SAP.P024.T6WholeStatement_W2 := SAP.P024.WH.W2.T6_whole

theorem SAP.P024.T7 : SAP.P024.T7WholeStatement := SAP.P024.WH.W1.T7_whole

theorem SAP.P024.T8 : SAP.P024.T8WholeStatement_W3 := SAP.P024.WH.W3.T8_whole
