import SAP.P036.Defs
import SAP.P036.Bridge
import AronowAudit.P036.P036_Unadjusted

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped BigOperators

namespace SAP.P036

theorem T1 : T1Statement := by
  unfold T1Statement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω _ μ _ k peer X β₀ β₁ γ Y ε hpeer hX he hxγ hmodel hzero
    simpa only [Bridge.regressorSigma_eq, Bridge.linearPredictor_eq] using
      (AronowAudit.P036.corrected_model_conditional_mean μ peer hpeer X hX
        β₀ β₁ γ Y ε he hxγ hmodel hzero)
  · intro Ω _ μ _ peer β₀ β₁ Y ε hpeer he hmodel hzero hp₀ hp₁
    simpa only [Bridge.conditionalArmMean_eq] using
      (AronowAudit.P036.unadjusted_conditional_means μ peer hpeer β₀ β₁ Y ε
        he hmodel hzero hp₀ hp₁)
  · intro ι _ _ s Y h₁ h₀
    have hmin (b : ℝ × ℝ) :
        (∀ c : ℝ × ℝ, rss s Y b.1 b.2 ≤ rss s Y c.1 c.2) ↔
          b = olsCoefficients s Y := by
      simpa only [Bridge.rss_eq, Bridge.olsCoefficients_eq] using
        (AronowAudit.P036.ols_unique_minimizer s Y h₁ h₀ b)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simpa only [Bridge.peers_eq] using (AronowAudit.P036.peers_binary (s : Set ι) i)
    · simpa only [Bridge.peers_eq] using (AronowAudit.P036.sum_peers s)
    · refine ⟨olsCoefficients s Y, (hmin _).mpr rfl, ?_⟩
      intro b hb
      exact (hmin b).mp hb
    · intro b
      exact hmin b
  · intro ι _ _ s Y k₁ k₀ hn₁ hn₀ _hbin hk₁ hk₀
    simp only [olsCoefficients, armMean, tableCoefficients, hn₁, hn₀, hk₁, hk₀,
      Nat.cast_ofNat]
  · simpa only [Bridge.tableCoefficients_eq] using AronowAudit.P036.table_any_coefficients
  · simpa only [Bridge.tableCoefficients_eq] using AronowAudit.P036.table_interest_coefficients
  · simpa only [Bridge.roundsToThree_eq, Bridge.tableCoefficients_eq] using
      AronowAudit.P036.table_coefficient_rounding

theorem T2 : T2Statement := by
  unfold T2Statement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ι _ _ s Y h₁ h₀
    have hp₁ : 0 < s.card := by omega
    have hp₀ : 0 < sᶜ.card := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b
      simpa only [Bridge.gram_eq] using (AronowAudit.P036.gram_entries s a b)
    · intro a b
      simpa only [Bridge.gramInverse_eq, Bridge.gram_eq] using
        (AronowAudit.P036.gram_inverse s hp₁ hp₀ a b)
    · change (regressionCoefficient s Y 0, regressionCoefficient s Y 1) = olsCoefficients s Y
      simpa only [Bridge.regressionCoefficient_eq, Bridge.olsCoefficients_eq] using
        (AronowAudit.P036.matrix_ols_coefficients s Y)
    · intro i
      simpa only [Bridge.leverage_eq] using (AronowAudit.P036.leverage_by_arm s i)
    · simpa only [Bridge.hc2Variance_eq, Bridge.olsResidual_eq] using
        (AronowAudit.P036.hc2_arm_formula s Y)
    · change hc2Variance s Y = neymanEstimate s Y
      simpa only [Bridge.hc2Variance_eq, Bridge.neymanEstimate_eq] using
        (AronowAudit.P036.hc2_eq_neyman s Y h₁ h₀)
  · intro ι _ _ n₁ n₀ h₁ h₀ hN Y₁ Y₀
    have hm := AronowAudit.P036.complete_randomization_moments n₁ n₀ h₁ h₀ hN Y₁ Y₀
    have he := AronowAudit.P036.expected_hc2_variance n₁ n₀ h₁ h₀ hN Y₁ Y₀
    have hc := AronowAudit.P036.corrected_hc2_conservativeness n₁ n₀ h₁ h₀ hN Y₁ Y₀
    have hn : 0 ≤ AronowAudit.P036.populationVariance (AronowAudit.P036.unitEffect Y₁ Y₀) /
        (Fintype.card ι : ℝ) := by
      rw [← hc.1]
      exact sub_nonneg.mpr hc.2.1
    dsimp only
    simp only [Bridge.designExpectation_eq, Bridge.estimatedEffect_eq,
      Bridge.populationMean_eq, Bridge.designVariance_eq, Bridge.populationVariance_eq,
      Bridge.unitEffect_eq, Bridge.observedOutcome_eq, Bridge.sampleVariance_eq,
      Bridge.hc2Variance_eq]
    exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, he, hc.1, hn, hc.2.1, hc.2.2⟩
  · intro ι s Y hs k hbin hk
    simpa only [Bridge.sampleVariance_eq] using
      (AronowAudit.P036.binary_sample_variance s Y hs k hbin hk)
  · intro ι _ _ s Y k₁ k₀ hn₁ hn₀ hbin hk₁ hk₀
    simpa only [Bridge.hc2Variance_eq, Bridge.tableHC2_eq] using
      (AronowAudit.P036.table_from_binary_counts s Y k₁ k₀ hn₁ hn₀ hbin hk₁ hk₀).2
  · simpa only [Bridge.tableHC2_eq] using AronowAudit.P036.table_any_hc2
  · simpa only [Bridge.tableHC2_eq] using AronowAudit.P036.table_interest_hc2
  · simpa only [Bridge.roundsToThree_eq, Bridge.tableHC2_eq] using
      AronowAudit.P036.table_hc2_se_rounding

end SAP.P036
