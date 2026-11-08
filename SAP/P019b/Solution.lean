import SAP.P019b.Defs
import SAP.P019b.Bridge
import AronowAudit.P019.Wave1.Gap.GP019B1
import AronowAudit.P019.Wave1.Gap.GP019B2b
import AronowAudit.P019.Wave1.Gap.GLP019B2
import AronowAudit.P019.Wave1.Gap.GP019B3b
import SAP.P019b.WH.W1.Proofs.T22
import SAP.P019b.WH.W1.Proofs.T12
import SAP.P019b.WH.W1.Proofs.T13
import SAP.P019b.WH.W1.Proofs.T17
import SAP.P019b.WH.W1.Proofs.T21

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019b

open Bridge Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

theorem T12 : T12WholeStatement := SAP.P019b.WH.W1.T12_whole

theorem T13 : T13WholeStatement := SAP.P019b.WH.W1.T13_whole

theorem T14 : T14Statement := by
  intro Ω _ S R Q hY hX h2 hi hz0 hz1 hq0 hq1
  have hzFalse : 0 < S.law.prob (fun ω => S.Z ω = false) := by
    have he : S.law.prob (fun ω => S.Z ω = false) =
        1 - S.law.prob (fun ω => S.Z ω = true) :=
      AronowAudit.P019.prob_false (toLaw S.law) S.Z
    rw [he]
    exact sub_pos.mpr hz1
  have hqFalse : 0 < S.law.prob (fun ω => Q ω = false) := by
    have he : S.law.prob (fun ω => Q ω = false) =
        1 - S.law.prob (fun ω => Q ω = true) :=
      AronowAudit.P019.prob_false (toLaw S.law) Q
    rw [he]
    exact sub_pos.mpr hq1
  have h := AronowAudit.P019.cnn_interpretation (toStudy S) R Q hY hX h2 hi
    hzFalse.ne' hz0.ne' hqFalse.ne' hq0.ne'
  dsimp only at h ⊢
  rcases h with ⟨hm, ht, hd, hc, hmu, hl, he, heq, hb, hdelta⟩
  have hp (z : Bool) : (toStudy S).law.prob ((toStudy S).cell z false) ≠ 0 := by
    rw [AronowAudit.P019.cell_probability (toStudy S) ht]
    apply mul_ne_zero
    · cases z
      · exact hzFalse.ne'
      · exact hz0.ne'
    · change S.law.prob (fun ω => S.Y ω = false) ≠ 0
      simpa only [hY] using hqFalse.ne'
  have hcond : S.listMean true false - S.listMean false false =
      S.law.ce (fun ω => bitVal (S.X ω)) (fun ω => S.Y ω = false) := by
    change (toStudy S).listMean true false - (toStudy S).listMean false false =
      (toStudy S).law.ce (fun ω => AronowAudit.P019.bitVal ((toStudy S).X ω))
        (fun ω => (toStudy S).Y ω = false)
    rw [AronowAudit.P019.list_mean_identified (toStudy S) h2 ht true false (hp true),
      AronowAudit.P019.list_mean_identified (toStudy S) h2 ht false false (hp false)]
    simp [AronowAudit.P019.bitVal]
  have hmean : S.law.mean (fun ω => bitVal (S.Y ω)) =
      S.law.prob (fun ω => Q ω = true) := by
    have he := AronowAudit.P019.mean_bit (toLaw S.law) S.Y
    change S.law.mean (fun ω => bitVal (S.Y ω)) =
      S.law.prob (fun ω => S.Y ω = true) at he
    simpa only [hY] using he
  change S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = true) -
      S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = false) =
    S.law.prob (fun ω => Q ω = true) +
      S.law.prob (fun ω => R ω = true ∧ Q ω = false) at hl
  refine ⟨hm, h2, ht, hcond, hcond.symm.trans hd, hc, hmu, hl, hmean, he, ?_,
    heq, ?_, hb, hdelta⟩
  · rw [hl]; ring
  · rw [hl]; constructor <;> intro h <;> linarith

theorem T15 : T15Statement := by
  constructor
  · intro n p1 p2 α hn hp10 hp11 hp20 hp21 hs ha0 ha1
    have h := AronowAudit.P019.Wave1.two_sided_power_corrected_proof
      n p1 p2 α hn hp10 hp11 hp20 hp21 hs ha0 ha1
    have hv := AronowAudit.P019.pooled_variance_difference p1 p2
    dsimp only at h ⊢
    exact ⟨h.1, hv.1, sub_nonneg.mpr hv.2, h.2⟩
  · dsimp only
    let c := normalQuantile (1-(1/20 : ℝ)/2)
    have h := AronowAudit.P019.Wave1.two_sided_power_corrected_proof
      50 (1/2) (1/2) (1/20) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [AronowAudit.P019.planningS])
      (by norm_num) (by norm_num)
    change 0 < c ∧
      twoSidedPlanningPower 50 (1/2) (1/2) c =
        favoredTail 50 (1/2) (1/2) c + oppositeTail 50 (1/2) (1/2) c ∧ _ at h
    have hB : oppositeTail 50 (1/2) (1/2) c = 1/40 := by
      calc
        oppositeTail 50 (1/2) (1/2) c = (1/20 : ℝ)/2 := h.2.2.2.2.2.1.mpr rfl
        _ = 1/40 := by norm_num
    have hAB : favoredTail 50 (1/2) (1/2) c = oppositeTail 50 (1/2) (1/2) c := by
      simp only [favoredTail, oppositeTail, sub_self, abs_zero, mul_zero, zero_sub]
    have hS : planningS (1/2) (1/2) = 1/2 := by norm_num [planningS]
    have hV : planningV (1/2) (1/2) = 1/2 := by norm_num [planningV]
    have hA : favoredTail 50 (1/2) (1/2) c = normalCDF (-c) := by
      unfold favoredTail
      rw [hS, hV]
      congr 1
      simp only [sub_self, abs_zero, mul_zero, zero_sub]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1/2))]
    refine ⟨hS, hV, by norm_num, hA, hA.symm.trans (hAB.trans hB), hB, ?_⟩
    rw [h.2.1, hAB, hB]
    norm_num

theorem T16 : T16Statement := by
  intro ρ h0 h1
  exact AronowAudit.P019.ceiling_as_printed ρ h0 h1

theorem T17 : T17WholeStatement := SAP.P019b.WH.W1.T17_whole

theorem T18 : T18Statement := by
  intro Ω _ S hs c1 c0
  exact AronowAudit.P019.Wave1.proposition_one_variance_limit_proof (toStudy S) hs c1 c0

theorem T19 : T19Statement := by
  intro Ω _ S hs c1 c0 cV
  exact ⟨AronowAudit.P019.asymptotic_variance_positive (toStudy S) hs,
    AronowAudit.P019.Wave1.combined_asymptotic_inference_proof (toStudy S) hs c1 c0 cV⟩

theorem T20 : T20Statement := by
  intro Ω _ S hs c1 c0 d1 d0
  exact AronowAudit.P019.Wave1.proposition_two_efficiency_proof (toStudy S) hs c1 c0 d1 d0

theorem T21 : T21WholeStatement := SAP.P019b.WH.W1.T21_whole

theorem T22 : T22WholeStatement := SAP.P019b.WH.W1.T22_whole

end
end SAP.P019b
