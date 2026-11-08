import SAP.P030.Defs
import SAP.P030.Bridge
import AronowAudit.P030.P030_Audit
import SAP.P030.WH.W1.Proofs.T2
import SAP.P030.WH.W1.Proofs.T5
import SAP.P030.WH.W1.Proofs.T8
import SAP.P030.WH.W1.Proofs.T14

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P030
open scoped BigOperators

theorem SAP.P030.T1 : SAP.P030.T1Statement := by
  classical
  rcases AronowAudit.P030.five_unit_counterexample with
    ⟨hE, hI, hN, hΩ, hF, hT, hV, hP, hS, hα⟩
  rcases AronowAudit.P030.five_rank_certificate with ⟨hR, hC, hD⟩
  refine ⟨by intros; rfl, hE, hI, hN, hΩ, ?_, hF, hT, Bridge.fiveOutcomes_value,
    AronowAudit.P030.five_distances.1, AronowAudit.P030.five_distances.2,
    hR, hC, hD, AronowAudit.P030.five_correlations, ?_, hP, hS, by norm_num, hα⟩
  · intro a
    have hp : uniformProbability fiveΩ (fun z => z = fiveAssignment a) = 1/(fiveΩ.card : ℝ) :=
      AronowAudit.P030.uniform_point_probability _ _ (by simp [fiveΩ])
    have hn : fiveΩ.card = 2 := hN
    rw [hp, hn]; norm_num
  · intro a
    exact ⟨(hV a).1, (hV a).2.1, Bridge.five_treated_nonempty a⟩

theorem SAP.P030.T2 : SAP.P030.T2WholeStatement := SAP.P030.WH.W1.T2_whole

theorem SAP.P030.T3 : SAP.P030.T3Statement := by
  refine ⟨?_, SAP.P030.T1⟩
  intro A μ f
  let ν := Bridge.toLaw μ
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hi : upperTail μ f x = 1 - lowerTail μ f x + probability μ (fun z => f z = x) :=
      AronowAudit.P030.tail_identity ν f x
    have hn : 0 ≤ probability μ (fun z => f z = x) := AronowAudit.P030.probability_nonneg ν _
    exact ⟨hi, by linarith⟩
  · intro u hu _
    exact ⟨AronowAudit.P030.lower_tail_valid ν f u hu, AronowAudit.P030.upper_tail_valid ν f u hu⟩
  · intro α h0 h1
    have hl : probability μ (fun z => lowerTail μ f (f z) ≤ α/2) ≤ α/2 :=
      AronowAudit.P030.lower_tail_valid ν f (α/2) (by linarith)
    have hu : probability μ (fun z => upperTail μ f (f z) ≤ α/2) ≤ α/2 :=
      AronowAudit.P030.upper_tail_valid ν f (α/2) (by linarith)
    have hs : probability μ (fun z => correctedReject α (lowerTail μ f (f z)) (upperTail μ f (f z))) ≤
        probability μ (fun z => lowerTail μ f (f z) ≤ α/2 ∨ upperTail μ f (f z) ≤ α/2) :=
      AronowAudit.P030.probability_mono ν _ _
        (fun _ _ h => h.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le))
    have hb := hs.trans (AronowAudit.P030.probability_union_le ν _ _)
    have hUpper : ∀ x : ℝ, upperTail μ f x < α/2 → 1-α/2 < lowerTail μ f x := by
      intro x hx
      have hi : upperTail μ f x = 1 - lowerTail μ f x + probability μ (fun z => f z = x) :=
        AronowAudit.P030.tail_identity ν f x
      have hn : 0 ≤ probability μ (fun z => f z = x) := AronowAudit.P030.probability_nonneg ν _
      linarith
    exact ⟨hb, by linarith, AronowAudit.P030.corrected_two_tailed_valid ν f α h0 h1,
      hUpper,
      fun x => AronowAudit.P030.corrected_reject_subset_printed ν f α x,
      fun pL pU => AronowAudit.P030.twoTailP_event pL pU α h0 h1,
      AronowAudit.P030.conventional_two_tailed_valid ν f α h0 h1⟩

theorem SAP.P030.T4 : SAP.P030.T4Statement := by
  change ¬ SAP.P030.PrintedTwoTailedExactness
  rw [← Bridge.PrintedTwoTailedExactness_eq]
  exact AronowAudit.P030.printed_two_tailed_claim_false

theorem SAP.P030.T5 : SAP.P030.T5WholeStatement := SAP.P030.WH.W1.T5_whole

theorem SAP.P030.T6 : SAP.P030.T6Statement := by
  refine ⟨?_, Bridge.outcomeNullNonconstant⟩
  intro N Ω S obs hobs Y g
  exact AronowAudit.P030.corrected_outcome_null Ω S obs hobs Y g

theorem SAP.P030.T7 : SAP.P030.T7Statement := by
  intro N Ω S obs _
  refine ⟨AronowAudit.P030.conditional_preserves_treatments Ω S obs,
    fun Y h => AronowAudit.P030.no_interference_fixed Ω S obs Y h,
    fun Y h => AronowAudit.P030.fixed_dependence_implies_interference Ω S obs Y h, ?_,
    fun Y h => AronowAudit.P030.no_effects_implies_no_interference Ω Y h⟩
  intro c τ
  have h := AronowAudit.P030.direct_effects_no_interference Ω c τ
  exact ⟨h, AronowAudit.P030.no_interference_fixed Ω S obs _ h⟩

theorem SAP.P030.T8 : SAP.P030.T8WholeStatement := SAP.P030.WH.W1.T8_whole

theorem SAP.P030.T9 : SAP.P030.T9Statement := by
  refine ⟨?_, Bridge.weakMonotoneExample, Bridge.tableNumerics⟩
  intro n hn a b ha hb
  exact AronowAudit.P030.corrected_spearman hn a b ha hb

theorem SAP.P030.T10 : SAP.P030.T10Statement := by
  refine ⟨?_, ?_, AronowAudit.P030.inverse_square_decay,
    AronowAudit.P030.inverse_square_not_exponential,
    AronowAudit.P030.inverse_square_unbounded, AronowAudit.P030.exponential_finite_at_zero⟩
  · intro N d z i hself
    exact AronowAudit.P030.inverse_square_self_term_undefined d z i hself
  · intro N d hd
    exact ⟨AronowAudit.P030.inverse_square_sums_defined d hd, by intros; rfl, by intros; rfl⟩

theorem SAP.P030.T11 : SAP.P030.T11Statement := by
  refine ⟨?_, AronowAudit.P030.sample_count_arithmetic,
    AronowAudit.P030.sample_count_reconciliations⟩
  intro A inst U F C T hU hFC hFT hCT
  exact ⟨AronowAudit.P030.sample_partition_count U F C T hU hFC hFT hCT,
    AronowAudit.P030.printed_sample_counts_inconsistent U F C T hU hFC hFT hCT⟩

theorem SAP.P030.T12 : SAP.P030.T12Statement := by
  intro N Ω S a hΩ Y g hnull
  exact AronowAudit.P030.one_tailed_randomization_valid Ω S a hΩ Y g hnull

theorem SAP.P030.T13 : SAP.P030.T13Statement := by
  classical
  intro N M hN hM i neighbors hself
  refine ⟨AronowAudit.P030.complete_nonempty N M hM, ?_, ?_,
    AronowAudit.P030.proximal_exposure_expectations N M hN hM i neighbors hself⟩
  · intro h
    exact AronowAudit.P030.conditioned_complete_nonempty N M hN hM i true (fun _ => h) (by simp)
  · intro h
    exact AronowAudit.P030.conditioned_complete_nonempty N M hN hM i false (by simp) (fun _ => h)

theorem SAP.P030.T14 : SAP.P030.T14WholeStatement := SAP.P030.WH.W1.T14_whole

theorem SAP.P030.T15 : SAP.P030.T15Statement := by
  exact ⟨AronowAudit.P030.half_controls_square, AronowAudit.P030.half_controls_maximizers⟩
