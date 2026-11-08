import SAP.P025a.Defs
import SAP.P025a.T8Proof
import SAP.P025a.Bridge
import AronowAudit.P025.P025_Interval
import AronowAudit.P025.P025_PrintedRefutations
import AronowAudit.P025.Wave1.Gap.FidP025
import SAP.P025a.WH.W1.Proofs.T10
import SAP.P025a.WH.W1.Proofs.T11
import SAP.P025a.WH.W1.Proofs.T1
import SAP.P025a.WH.W1.Proofs.T2
import SAP.P025a.WH.W1.Proofs.T3
import SAP.P025a.WH.W2.Proofs.T4
import SAP.P025a.WH.W2.Proofs.T5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a
noncomputable section
open scoped BigOperators

 theorem T1 : SAP.P025a.T1WholeStatement := SAP.P025a.WH.W1.T1_whole

 theorem T2 : SAP.P025a.T2WholeStatement := SAP.P025a.WH.W1.T2_whole

 theorem T3 : SAP.P025a.T3WholeStatement := SAP.P025a.WH.W1.T3_whole

 theorem T4 : SAP.P025a.T4WholeStatement := SAP.P025a.WH.W2.T4_whole

 theorem T5 : SAP.P025a.T5WholeStatement := SAP.P025a.WH.W2.T5_whole

 theorem T6 : T6Statement := by
  have hroot (pG pE γ : ℝ) (hE : 0 < pE) (hEG : pE < pG) (hG : pG < 1)
      (hγ : 1 ≤ γ) :
      ((binaryInterval pG γ) ∩ (binaryInterval pE γ)).Nonempty ↔
        Real.sqrt (sampleOddsRatio pG pE) ≤ γ := by
    have h := AronowAudit.P025.overlap_criterion pG pE γ hE hEG hG hγ
    exact h.1.trans (h.2.trans (Real.sqrt_le_left (by linarith)).symm)
  refine ⟨?_,AronowAudit.P025.overlap_threshold_numbers,?_,?_,?_,
    @AronowAudit.P025.equal_estimates_product,?_,?_,?_,?_,?_⟩
  · intro pG pE γ hE hEG hG hγ
    have h := AronowAudit.P025.overlap_criterion pG pE γ hE hEG hG hγ
    exact ⟨h.1,h.2,hroot pG pE γ hE hEG hG hγ⟩
  · intro γ hγ
    constructor
    · have h := hroot (917/1000) (503/1000) γ (by norm_num) (by norm_num) (by norm_num) hγ
      simpa only [show sampleOddsRatio (917/1000) (503/1000) = 455749/41749
        by norm_num [sampleOddsRatio]] using h
    · have h := hroot (44/48) (291/579) γ (by norm_num) (by norm_num) (by norm_num) hγ
      simpa only [show sampleOddsRatio (44/48) (291/579) = 1056/97
        by norm_num [sampleOddsRatio]] using h
  · have h (pG pE γ : ℝ) (hE : 0 < pE) (hEG : pE < pG) (hG : pG < 1) (hγ : 1 ≤ γ) :=
      (AronowAudit.P025.overlap_criterion pG pE γ hE hEG hG hγ).1.trans
        (AronowAudit.P025.overlap_criterion pG pE γ hE hEG hG hγ).2
    refine ⟨?_,?_,?_,?_⟩
    · exact (h (917/1000) (503/1000) 3 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).not.mpr (by norm_num [AronowAudit.P025.sampleOddsRatio])
    · exact (h (917/1000) (503/1000) 4 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).mpr (by norm_num [AronowAudit.P025.sampleOddsRatio])
    · exact (h (44/48) (291/579) 3 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).not.mpr (by norm_num [AronowAudit.P025.sampleOddsRatio])
    · exact (h (44/48) (291/579) 4 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).mpr (by norm_num [AronowAudit.P025.sampleOddsRatio])
  · intro p a b hp hp1 ha hb
    dsimp only
    have hf := AronowAudit.P025.reweighted_formula p a b hp hp1 ha hb
    refine ⟨hf,?_⟩
    rw [show reweightedPrevalence p a b = p*b/(p*b+(1-p)*a) from hf]
    have hd : 0 < p*b+(1-p)*a := by positivity
    have he : 1 - p*b/(p*b+(1-p)*a) = ((1-p)*a)/(p*b+(1-p)*a) := by
      field_simp; ring
    rw [he]
    field_simp
  · intro pG pE g₁ g₀ e₁ e₀ γ hE hEG hG hg₁ hg₀ he₁ he₀ heq hcapG hcapE
    exact AronowAudit.P025.common_cap_product _ _ _ γ (div_pos hg₁ hg₀)
      (div_pos he₀ he₁) hcapG hcapE
      ((AronowAudit.P025.equal_estimates_product pG pE g₁ g₀ e₁ e₀
        hE hEG hG hg₁ hg₀ he₁ he₀).1 heq)
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)

 theorem T7 : T7Statement := by
  exact ⟨AronowAudit.P025.printed_proposition_one_refuted,
    @AronowAudit.P025.printed_proposition_one_upper⟩

 theorem T8 : T8Statement := by
  exact SAP.P025a.T8_luna_assembly

 theorem T9 : T9Statement := by
  intro J hJ y mass hy hmass α β hα hab _
  have hβ : 0 < β := hα.trans_le hab
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k _
    exact AronowAudit.P025.lower_partition_original_box y mass α β hα hab k
  · intro k hk
    exact AronowAudit.P025.corrected_lower_display_at_cut hJ y mass hy hmass α β hα hab k hk
  · intro k hk2 hkJ
    have h := AronowAudit.P025.printed_partition_discrepancy hJ y mass hmass
      (β/α) (div_pos hβ hα) k hk2 hkJ
    have he : lowerValue y mass (β/α) k =
        lowerNumerator y mass (β/α) k / lowerDenominator mass (β/α) k := by
      simpa only [← Bridge.ratio_eq, Bridge.threshold_lower, lowerValue,
        lowerNumerator, lowerDenominator, one_mul] using AronowAudit.P025.threshold_partition y mass (β/α) 1 k
    refine ⟨h.1,?_⟩
    rw [← he]
    simpa only [← Bridge.lowerValue_eq, lowerNumerator, lowerDenominator] using h.2.1
  · simp [printedLowerExpression]
  · simp [printedLowerExpression]

 theorem T10 : SAP.P025a.T10WholeStatement := SAP.P025a.WH.W1.T10_whole

 theorem T11 : SAP.P025a.T11WholeStatement := SAP.P025a.WH.W1.T11_whole

end
end SAP.P025a
