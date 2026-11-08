import SAP.P042.Defs
import SAP.P042.Bridge
import AronowAudit.P042.P042_Turnout
import AronowAudit.P041.Wave1.Gap.GP041P042P045B2
import AronowAudit.P042.Wave1.Gap.GLP041P042P045P042B1
import AronowAudit.P042.Wave1.PrintedPoolingVariance
import AronowAudit.P042.Wave1.PrintedComparisonVariance
import SAP.P042.WH.W1.Proofs.T1
import SAP.P042.WH.W1.Proofs.T3
import SAP.P042.WH.W2.Proofs.T6

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P042 SAP.P042.Bridge Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

theorem SAP.P042.T1 : SAP.P042.T1WholeStatement :=
  SAP.P042.WH.W1.T1_whole

theorem SAP.P042.T2 : SAP.P042.T2Statement := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω _ μ _ J a D hD
    have hd (j : Fin J) : covariance (D j) (D j) μ = variance (D j) μ :=
      covariance_self (hD j).aemeasurable
    refine ⟨AronowAudit.P042.pooled_mean μ a D hD,
      AronowAudit.P042.pooled_variance μ a D hD, ?_⟩
    simpa only [covarianceForm_eq, offDiagonal_eq, hd] using
      AronowAudit.P042.covariance_form_decomposition a
        (fun j k => covariance (D j) (D k) μ) (fun j k => covariance_comm (D j) (D k))
  · intro Ω _ μ _ J hJ D hD hv
    letI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
    let v := fun j => variance (D j) μ
    have hw := AronowAudit.P042.precision_weights v hv
    have hc := AronowAudit.P042.corrected_precision_variance μ hJ D hD hv
    dsimp only
    refine ⟨hw.1, hw.2.1, hw.2.2, AronowAudit.P042.precision_diagonal v hv,
      hc.1, hc.2, ?_, ?_, ?_, ?_⟩
    · exact AronowAudit.P042.uncorrelated_precision_variance μ hJ D hD hv
    · exact AronowAudit.P042.positive_covariance_inflation μ hJ D hD hv
    · intro z
      exact congrArg (fun t : ℝ => z * Real.sqrt t)
        (AronowAudit.P042.pooled_variance μ (normalizedWeight v) D hD)
    · intro z hz
      have hcancel :
          (z * Real.sqrt (variance (pooled (normalizedWeight v) D) μ) =
            z * Real.sqrt ((totalWeight v)⁻¹)) ↔
          Real.sqrt (variance (pooled (normalizedWeight v) D) μ) =
            Real.sqrt ((totalWeight v)⁻¹) :=
        ⟨mul_left_cancel₀ (ne_of_gt hz), congrArg (fun t : ℝ => z*t)⟩
      exact hcancel.trans ((Real.sqrt_inj (variance_nonneg _ μ)
        (inv_nonneg.mpr hw.1.le)).trans hc.2)
  · intro Ω _ μ _ A B C hA hB hC hAB hAC hBC
    exact AronowAudit.P042.shared_control_covariance μ A B C hA hB hC hAB hAC hBC
  · intro Ω _ μ _ n0 n1 n2 hn0 hn1 hn2 X hX hind sigmaSq hs hvar
    exact AronowAudit.P042.independent_arm_shared_control μ hn0 hn1 hn2 X hX hind
      sigmaSq hs hvar
  · intro Ω _ μ _ J a s D hD ha hs hvs
    refine ⟨?_, AronowAudit.P042.pooled_variance_upper_bound μ a s D hD ha hs hvs, ?_⟩
    · intro j k
      exact AronowAudit.P042.covariance_abs_bound μ (D j) (D k)
        (hD j) (hD k) (s j) (s k) (hs j) (hs k) (hvs j) (hvs k)
    · intro Z hZ hm hv hc
      exact AronowAudit.P042.pooled_rank_one_equality μ a s D Z hD hZ hm hv hc
  · intro Ω _ μ _ ι _ _ N A hN hA hdis D hD hv
    have hpool (w : ι → ℝ) : MemLp (pooled w D) 2 μ := by
      convert memLp_finsetSum' Finset.univ (fun j _ => (hD j).const_mul (w j)) using 1
      funext ω
      simp [pooled, Finset.sum_apply]
    exact ⟨AronowAudit.P042.pooled_difference_covariance μ N A hN hA hdis D hD hv,
      AronowAudit.P042.difference_variance μ _ _ (hpool _) (hpool _)⟩
  · intro Ω _ μ _ J hJ D hD hv e a c12 c13 c23 ha hb
    exact AronowAudit.P042.three_contrast_block μ hJ D hD hv e a c12 c13 c23 ha hb
  · intro N hN n hn hsizes Y
    exact ⟨AronowAudit.P042.Wave1.P042B1_support_nonempty n hsizes,
      AronowAudit.P042.Wave1.finite_population_shared_control_proof hN n hn hsizes Y⟩

theorem SAP.P042.T3 : SAP.P042.T3WholeStatement :=
  SAP.P042.WH.W1.T3_whole

theorem SAP.P042.T4 : SAP.P042.T4Statement := by
  exact ⟨robo_fixed_exact, AronowAudit.P042.robo_fixed_rounding,
    AronowAudit.P042.robo_fixed_interval, AronowAudit.P042.robo_fixed_positive,
    robo_stochastic_variance, robo_random_exact, robo_random_rounding⟩

theorem SAP.P042.T5 : SAP.P042.T5Statement := by
  exact ⟨AronowAudit.P042.Wave1.printed_pooling_variance_refuted,
    AronowAudit.P042.Wave1.printed_comparison_variance_refuted⟩

theorem SAP.P042.T6 : SAP.P042.T6WholeStatement_W2 :=
  SAP.P042.WH.W2.T6_whole
