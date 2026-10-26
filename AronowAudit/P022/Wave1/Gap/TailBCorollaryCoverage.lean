import AronowAudit.P022.Wave1.Gap.TailBCorollaryArray
import AronowAudit.P061.P061_Foundations
import AronowAudit.P053.P053_NormalQuantiles

/-! Exact Corollary 1 and the literal random-threshold coverage limit. -/
namespace AronowAudit.P022.Wave1
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
noncomputable section

/-- The atomic-law inference library uses precisely the same uniform permutations. -/
theorem tb13_uniform_expectation (d : Design) (f : Assignment d → ℝ) :
    AronowAudit.P061.expectation (AronowAudit.P061.uniformDesign (Assignment d)) f =
      designExpectation d f := by
  simp only [AronowAudit.P061.expectation, AronowAudit.P061.uniformDesign,
    tsum_fintype, ← Finset.mul_sum, designExpectation,
    Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm]
  rw [Finset.sum_mul]

theorem tb13_uniform_probability (d : Design) (E : Assignment d → Prop) :
    AronowAudit.P061.probability (AronowAudit.P061.uniformDesign (Assignment d)) E =
      designProbability d E := by
  classical
  unfold AronowAudit.P061.probability designProbability designExpectation
  rw [tsum_fintype, Fintype.expect_eq_sum_div_card, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro π _
  by_cases he : E π <;> simp [he, AronowAudit.P061.uniformDesign, one_div]

/-- Closed distance tails imply the atomic library's strict-tail convention. -/
theorem tb13_to_in_probability (S : ExperimentSequence)
    (Y : (q : ℕ) → Assignment (S.design q) → ℝ) (a : ℝ)
    (hY : TailB_DesignTendsto S.design Y a) :
    AronowAudit.P061.ConvergesInProbability
      (fun q => AronowAudit.P061.uniformDesign (Assignment (S.design q))) Y a := by
  intro ε hε
  simp only [tb13_uniform_probability]
  apply squeeze_zero (fun _ => Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (fun q => TailB_designProbability_mono _ _ _ (fun π hπ => ?_)) (hY ε hε)
  simpa only [Real.dist_eq] using hπ.le

/-- Studentization needs no pointwise positivity of the random variance estimates. -/
theorem tb13_studentized_clt (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (h3 : BoundedThirdMoments S)
    (hns : NonsingularLaw H) :
    weakStandardNormal S (fun q π =>
      (estimatedEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) π -
        averageEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)) /
          Real.sqrt (gamma H θ ρ * estimatedVariance (S.design q)
            (rowOutcomes S true q) (rowOutcomes S false q) .H π)) := by
  have hUI := tb13_square_integrability S h3
  have hs := tb13_limiting_variance_pos S H θ ρ h hUI hns
  have hsb := tb13_true_le_bound S H θ ρ h hUI
  have hb := lt_of_lt_of_le hs hsb
  have hg : gamma H θ ρ * limitingBound H θ ρ .H = limitingTrueVariance H θ ρ := by
    exact div_mul_cancel₀ _ hb.ne'
  let V q := trueVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)
  let W q π := estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H π
  let Y q π := Real.sqrt (gamma H θ ρ * (((S.design q).N : ℝ)*W q π)) /
    Real.sqrt (((S.design q).N : ℝ)*V q)
  have hv := tb13_true_variance_limit S H θ ρ h hUI
  have hw := (TailB_estimated_bound_limit S H θ ρ h hUI .H).comp
    (fun x => gamma H θ ρ*x) (by fun_prop)
  rw [hg] at hw
  have hY : TailB_DesignTendsto S.design Y 1 := by
    have ht := (hw.prod (TailB_DesignTendsto.deterministic S.design hv)).comp
      (fun p : ℝ × ℝ => Real.sqrt p.1/Real.sqrt p.2)
      (Real.continuous_sqrt.continuousAt.comp continuousAt_fst |>.div
        (Real.continuous_sqrt.continuousAt.comp continuousAt_snd) (Real.sqrt_pos.mpr hs).ne')
    simpa only [div_self (Real.sqrt_pos.mpr hs).ne'] using ht
  have hz : AronowAudit.P061.WeakConverges
      (fun q => AronowAudit.P061.uniformDesign (Assignment (S.design q)))
      (fun q π => (estimatedEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) π-
        averageEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q))/Real.sqrt (V q))
      (gaussianReal 0 1) := by
    simpa only [AronowAudit.P061.WeakConverges, weakStandardNormal, tb13_uniform_expectation, V]
      using tb13_actual_variance_clt S H θ ρ h h3 hns
  have hdiv := AronowAudit.P061.weakConverges_div_consistent
    (fun q => AronowAudit.P061.uniformDesign (Assignment (S.design q))) _ Y
      (gaussianReal 0 1) hz (tb13_to_in_probability S Y 1 hY)
  intro f
  have ht := hdiv f
  simp only [tb13_uniform_expectation] at ht
  apply ht.congr'
  filter_upwards [hv.eventually_const_lt hs] with q hq
  have hV : 0 < V q := pos_of_mul_pos_right hq (Nat.cast_nonneg _)
  have hN : 0 < Real.sqrt ((S.design q).N : ℝ) := Real.sqrt_pos.mpr
    (Nat.cast_pos.mpr (NeZero.pos _))
  congr 1
  funext π
  congr 1
  dsimp [Y]
  rw [show gamma H θ ρ * (((S.design q).N : ℝ)*W q π) =
    ((S.design q).N : ℝ)*(gamma H θ ρ*W q π) by ring,
    Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _),
    mul_div_mul_left _ _ hN.ne', div_div_div_cancel_right₀ (Real.sqrt_pos.mpr hV).ne']

/-- Arbitrary central standard-normal interval mass in the target's CDF notation. -/
theorem tb13_normal_mass (x : ℝ) (hx : 0 ≤ x) :
    (gaussianReal 0 1 (Icc (-x) x)).toReal = 2*normalCDF x-1 := by
  letI tb13_normal_null : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hc : ContinuousWithinAt (cdf (gaussianReal 0 1)) (Iic (-x)) (-x) :=
    (AronowAudit.P053.NormalCompletion.cdf_continuousAt (gaussianReal 0 1) (-x)).continuousWithinAt
  have hn : 0 ≤ cdf (gaussianReal 0 1) x-cdf (gaussianReal 0 1) (-x) :=
    sub_nonneg.mpr (monotone_cdf (μ := gaussianReal 0 1) (by linarith))
  have he : gaussianReal 0 1 (Icc (-x) x) = ENNReal.ofReal
      (cdf (gaussianReal 0 1) x-cdf (gaussianReal 0 1) (-x)) := by
    calc
      _ = (cdf (gaussianReal 0 1)).measure (Icc (-x) x) := by rw [measure_cdf]
      _ = _ := by rw [StieltjesFunction.measure_Icc, hc.leftLim_eq]
  rw [he, ENNReal.toReal_ofReal hn, AronowAudit.P053.NormalCompletion.normal_cdf_neg]
  change cdf (gaussianReal 0 1) x-(1-cdf (gaussianReal 0 1) x) = _
  rw [cdf_eq_real]
  change normalCDF x-(1-normalCDF x) = 2*normalCDF x-1
  ring


/-- Random-threshold coverage under the actual uniform permutation laws. -/
theorem tb13_coverage_limit (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (h3 : BoundedThirdMoments S)
    (hns : NonsingularLaw H) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun q => designProbability (S.design q) (fun π =>
      |estimatedEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) π -
        averageEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)| ≤
          normalCritical α * Real.sqrt (estimatedVariance (S.design q)
            (rowOutcomes S true q) (rowOutcomes S false q) .H π))) atTop
      (𝓝 (2*normalCDF (normalCritical α/Real.sqrt (gamma H θ ρ))-1)) := by
  have hUI := tb13_square_integrability S h3
  have hs := tb13_limiting_variance_pos S H θ ρ h hUI hns
  have hsb := tb13_true_le_bound S H θ ρ h hUI
  have hb := lt_of_lt_of_le hs hsb
  have hg : 0 < gamma H θ ρ := div_pos hs hb
  have hgm : gamma H θ ρ * limitingBound H θ ρ .H = limitingTrueVariance H θ ρ :=
    div_mul_cancel₀ _ hb.ne'
  let W q π := estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H π
  let scale q π := Real.sqrt (gamma H θ ρ*W q π)
  let s q := Real.sqrt (limitingTrueVariance H θ ρ)/Real.sqrt (S.design q).N
  have hN (q : ℕ) : 0 < Real.sqrt ((S.design q).N : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos _))
  have hscale : TailB_DesignTendsto S.design (fun q π => scale q π/s q) 1 := by
    have hw := (TailB_estimated_bound_limit S H θ ρ h hUI .H).comp
      (fun x => Real.sqrt (gamma H θ ρ*x)/Real.sqrt (limitingTrueVariance H θ ρ))
      (by fun_prop)
    rw [hgm, div_self (Real.sqrt_pos.mpr hs).ne'] at hw
    convert hw using 1
    funext q π
    dsimp [scale, s, W]
    rw [show gamma H θ ρ * (((S.design q).N : ℝ)*estimatedVariance (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q) .H π) =
        ((S.design q).N : ℝ)*(gamma H θ ρ*estimatedVariance (S.design q)
          (rowOutcomes S true q) (rowOutcomes S false q) .H π) by ring,
      Real.sqrt_mul (Nat.cast_nonneg _)]
    field_simp
  have hz : 0 < normalCritical α := AronowAudit.P053.NormalCompletion.normalCritical_pos α hα hα1
  have hq : 0 < normalCritical α/Real.sqrt (gamma H θ ρ) :=
    div_pos hz (Real.sqrt_pos.mpr hg)
  letI tb13_coverage_normal_null : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have ht := AronowAudit.P061.weakConverges_scaled_interval
    (fun q => AronowAudit.P061.uniformDesign (Assignment (S.design q)))
    (fun q π => estimatedEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) π-
      averageEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q))
    scale s (gaussianReal 0 1) (fun q => div_pos (Real.sqrt_pos.mpr hs) (hN q))
    (tb13_to_in_probability S _ 1 hscale)
    (by simpa only [AronowAudit.P061.WeakConverges, weakStandardNormal, tb13_uniform_expectation, scale, W]
      using tb13_studentized_clt S H θ ρ h h3 hns)
    (normalCritical α/Real.sqrt (gamma H θ ρ)) hq
    (measure_singleton _) (measure_singleton _)
  rw [tb13_normal_mass _ hq.le] at ht
  simp only [tb13_uniform_probability] at ht
  convert ht using 1
  funext q
  congr 1
  funext π
  congr 1
  dsimp [scale, W]
  rw [Real.sqrt_mul hg.le]
  field_simp

/-- The critical-value CDF identity gives the printed conservative inequality. -/
theorem tb13_coverage_lower (H : JointLaw) (θ ρ : ℝ)
    (hg : 0 < gamma H θ ρ) (hg1 : gamma H θ ρ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    1-α ≤ 2*normalCDF (normalCritical α/Real.sqrt (gamma H θ ρ))-1 := by
  have hz : 0 < normalCritical α := AronowAudit.P053.NormalCompletion.normalCritical_pos α hα hα1
  have hc : normalCDF (normalCritical α) = 1-α/2 :=
    AronowAudit.P053.NormalCompletion.normalCritical_cdf α hα hα1
  have hs : Real.sqrt (gamma H θ ρ) ≤ 1 := (Real.sqrt_le_one).mpr hg1
  have hq : normalCritical α ≤ normalCritical α/Real.sqrt (gamma H θ ρ) := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hg)).mpr
    nlinarith
  have hm := monotone_cdf (μ := gaussianReal 0 1) hq
  simp only [cdf_eq_real, measureReal_def] at hm
  change normalCDF (normalCritical α) ≤ normalCDF (normalCritical α/Real.sqrt (gamma H θ ρ)) at hm
  linarith

/-- P022-T17: Corollary 1 and the conservative coverage limit. -/
theorem TailB_corollary1_and_coverage : (∀ (S : ExperimentSequence)
      (H : JointLaw)
      (θ ρ : ℝ)
      (h : Conditions123 S H θ ρ)
      (h3 : BoundedThirdMoments S)
      (hns : NonsingularLaw H),
      0 < gamma H θ ρ ∧ gamma H θ ρ ≤ 1 ∧
    Tendsto (fun q => ((S.design q).N : ℝ) * trueVariance (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q)) atTop (𝓝 (limitingTrueVariance H θ ρ)) ∧
    weakStandardNormal S (fun q π =>
      (estimatedEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) π -
        averageEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)) /
          Real.sqrt (gamma H θ ρ * estimatedVariance (S.design q)
            (rowOutcomes S true q) (rowOutcomes S false q) .H π)) ∧
    (∀ α, 0 < α → α < 1 →
      Tendsto (fun q => designProbability (S.design q) (fun π =>
        |estimatedEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) π -
          averageEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)| ≤
            normalCritical α * Real.sqrt (estimatedVariance (S.design q)
              (rowOutcomes S true q) (rowOutcomes S false q) .H π))) atTop
        (𝓝 (2 * normalCDF (normalCritical α / Real.sqrt (gamma H θ ρ)) - 1)) ∧
      1 - α ≤ 2 * normalCDF (normalCritical α / Real.sqrt (gamma H θ ρ)) - 1)) := by
  intro S H θ ρ h h3 hns
  have hUI := tb13_square_integrability S h3
  have hs := tb13_limiting_variance_pos S H θ ρ h hUI hns
  have hsb := tb13_true_le_bound S H θ ρ h hUI
  have hb := lt_of_lt_of_le hs hsb
  have hg : 0 < gamma H θ ρ := div_pos hs hb
  have hg1 : gamma H θ ρ ≤ 1 := (div_le_one hb).mpr hsb
  exact ⟨hg, hg1, tb13_true_variance_limit S H θ ρ h hUI,
    tb13_studentized_clt S H θ ρ h h3 hns, fun α hα hα1 =>
      ⟨tb13_coverage_limit S H θ ρ h h3 hns α hα hα1,
        tb13_coverage_lower H θ ρ hg hg1 α hα hα1⟩⟩

end
end AronowAudit.P022.Wave1
