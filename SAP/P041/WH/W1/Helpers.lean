import SAP.P041.Defs.WholeW1
import SAP.P041.Bridge
import AronowAudit.P053.P053_NormalQuantiles
import AronowAudit.P040.P040_Regression

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1
open Matrix
open scoped BigOperators

theorem t7_existing : T7Statement := by
  refine ⟨Bridge.citation_ols_exact_fit, Bridge.citation_gram_inverse_is_inverse,
    Bridge.citation_hc1_exact_variance, Bridge.corrected_citation_standard_error, ?_⟩
  ext i
  fin_cases i <;> norm_num [citationGramInverse, citationCellDesign, dotProduct, Fin.sum_univ_succ]

theorem t8_existing : T8Statement := by
  exact ⟨Bridge.corrected_star_wald_bounds, Bridge.corrected_normal_star_tiers_proof,
    Bridge.nested_significance_reading⟩

theorem t11_existing : T11Statement := by
  exact ⟨Bridge.printed_former_normal_p_enclosures_proof, Bridge.former_subgroup_nondetections⟩

theorem t2_existing : T2Statement := by
  exact ⟨Bridge.corrected_former_nondetection, Bridge.corrected_former_imprecision,
    Bridge.former_wald_endpoint_enclosures, Bridge.corrected_between_relative_effects,
    Bridge.corrected_normal_p_approximations_proof, Bridge.observed_early_contrasts,
    Bridge.smaller_contrast_does_not_exclude_common_bias⟩

theorem t12_existing : T12Statement := by
  exact ⟨Bridge.printed_percentages_arithmetic_and_direction,
    Bridge.printed_directional_percentages_refuted⟩

/-- Strict monotonicity of the genuine CDF identifies any certified critical
point with the strict p-value cutoff, including boundary equality. -/
theorem normal_lt_critical (α c z : ℝ) (hc : NormalCriticalW1 α c) :
    normalTwoSided z < α ↔ c < |z| := by
  have he : 2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-c) = α := by
    simpa only [normalTwoSided, abs_of_pos hc.1] using hc.2.1
  have hm := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
  constructor
  · intro h
    have hh : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-|z|) <
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-c) := by
      unfold normalTwoSided at h
      linarith
    have := hm.lt_iff_lt.mp hh
    linarith
  · intro h
    have hh := hm (show -|z| < -c by linarith)
    unfold normalTwoSided
    linarith

theorem normal_tier_equivalences (c₁ c₅ c₁₀ : ℝ)
    (h₁ : NormalCriticalW1 0.01 c₁) (h₅ : NormalCriticalW1 0.05 c₅)
    (h₁₀ : NormalCriticalW1 0.10 c₁₀) : NormalTierEquivalencesW1 c₁ c₅ c₁₀ := by
  intro z
  have e₁ := normal_lt_critical 0.01 c₁ z h₁
  have e₅ := normal_lt_critical 0.05 c₅ z h₅
  have e₁₀ := normal_lt_critical 0.10 c₁₀ z h₁₀
  by_cases a : normalTwoSided z < 0.01
  · have b : normalTwoSided z < 0.05 := by linarith
    have c : normalTwoSided z < 0.10 := by linarith
    simp only [significanceTier, if_pos a]
    have za := e₁.mp a
    have zb := e₅.mp b
    have zc := e₁₀.mp c
    constructor
    · exact ⟨fun _ => za, fun _ => trivial⟩
    constructor
    · simp only [show (3 : ℕ) ≠ 2 by decide, false_iff, not_and_or, not_lt, not_le]
      exact Or.inr za
    constructor
    · simp only [show (3 : ℕ) ≠ 1 by decide, false_iff, not_and_or, not_lt, not_le]
      exact Or.inr zb
    · simp only [show (3 : ℕ) ≠ 0 by decide, false_iff, not_le]
      exact zc
  · by_cases b : normalTwoSided z < 0.05
    · have c : normalTwoSided z < 0.10 := by linarith
      have za : |z| ≤ c₁ := le_of_not_gt (fun h => a (e₁.mpr h))
      have zb := e₅.mp b
      have zc := e₁₀.mp c
      simp only [significanceTier, if_neg a, if_pos b]
      constructor
      · simp only [show (2 : ℕ) ≠ 3 by decide, false_iff, not_lt]; exact za
      constructor
      · exact ⟨fun _ => ⟨zb,za⟩, fun _ => trivial⟩
      constructor
      · simp only [show (2 : ℕ) ≠ 1 by decide, false_iff, not_and_or, not_lt, not_le]
        exact Or.inr zb
      · simp only [show (2 : ℕ) ≠ 0 by decide, false_iff, not_le]; exact zc
    · by_cases c : normalTwoSided z < 0.10
      · have za : |z| ≤ c₁ := le_of_not_gt (fun h => a (e₁.mpr h))
        have zb : |z| ≤ c₅ := le_of_not_gt (fun h => b (e₅.mpr h))
        have zc := e₁₀.mp c
        simp only [significanceTier, if_neg a, if_neg b, if_pos c]
        constructor
        · simp only [show (1 : ℕ) ≠ 3 by decide, false_iff, not_lt]; exact za
        constructor
        · simp only [show (1 : ℕ) ≠ 2 by decide, false_iff, not_and_or, not_lt, not_le]
          exact Or.inl zb
        constructor
        · exact ⟨fun _ => ⟨zc,zb⟩, fun _ => trivial⟩
        · simp only [show (1 : ℕ) ≠ 0 by decide, false_iff, not_le]; exact zc
      · have za : |z| ≤ c₁ := le_of_not_gt (fun h => a (e₁.mpr h))
        have zb : |z| ≤ c₅ := le_of_not_gt (fun h => b (e₅.mpr h))
        have zc : |z| ≤ c₁₀ := le_of_not_gt (fun h => c (e₁₀.mpr h))
        simp only [significanceTier, if_neg a, if_neg b, if_neg c]
        constructor
        · simp only [show (0 : ℕ) ≠ 3 by decide, false_iff, not_lt]; exact za
        constructor
        · simp only [show (0 : ℕ) ≠ 2 by decide, false_iff, not_and_or, not_lt, not_le]
          exact Or.inl zb
        constructor
        · simp only [show (0 : ℕ) ≠ 1 by decide, false_iff, not_and_or, not_lt, not_le]
          exact Or.inl zc
        · exact ⟨fun _ => zc, fun _ => trivial⟩

theorem complement_all (n k : ℕ) (j₀ : Fin k) (X : Matrix (Fin n) (Fin k) ℝ)
    (S : Fin n → ℝ) (hX : IsUnit (X.transpose * X).det) (h₁ : ∀ i, X i j₀ = 1) :
    olsCoefficients X (1-S) = Pi.single j₀ 1 - olsCoefficients X S ∧
    olsResidual X (1-S) = -olsResidual X S ∧
    robustMeat X (olsResidual X (1-S)) = robustMeat X (olsResidual X S) ∧
    (k < n → hc1Covariance X (1-S) = hc1Covariance X S ∧
      ∀ j, Real.sqrt (hc1Covariance X (1-S) j j) = Real.sqrt (hc1Covariance X S j j)) := by
  have he : X *ᵥ Pi.single j₀ (1 : ℝ) = 1 := by
    ext i
    simpa using h₁ i
  obtain ⟨hr,hm,hc⟩ := Bridge.ols_complement_residuals_and_covariance X (Pi.single j₀ 1) S hX he
  exact ⟨Bridge.ols_complement_coefficients X (Pi.single j₀ 1) S hX he,
    hr, hm, fun _ => ⟨hc, fun j => by rw [hc]⟩⟩

theorem indicator_updates (r : Option ℝ) (h : ℝ) :
    (if (∃ t : ℝ, r = some t ∧ t ≤ h) then (0 : ℝ) else 1) = survivalIndicator r h ∧
    (if (∃ t : ℝ, r = some t ∧ t ≤ h) then (1 : ℝ) else 0) = removalIndicator r h := by
  cases r with
  | none => simp [survivalIndicator, removalIndicator]
  | some t =>
    by_cases hth : t ≤ h
    · simp [survivalIndicator, removalIndicator, hth, not_lt.mpr hth]
    · simp [survivalIndicator, removalIndicator, hth, lt_of_not_ge hth]

theorem s11_table : ∀ (m : Fin 3) (h : Fin 4),
    armSurvivalDifference ((![150,100,75] : Fin 3 → ℝ) m)
      ((![150,100,76] : Fin 3 → ℝ) m)
      (S11TreatedSurvivorsW1 m h) (S11ControlSurvivorsW1 m h) = S11SurvivalTableW1 m h ∧
    S11SurvivalTableW1 m h ≠ 0 ∧
    withinPrintedPrecision (S11SurvivalTableW1 m h) (S11PrintedTableW1 m h) ∧
    ¬ withinPrintedPrecision (-S11SurvivalTableW1 m h) (S11PrintedTableW1 m h) := by
  intro m h
  fin_cases m <;> fin_cases h <;>
    norm_num [armSurvivalDifference, S11TreatedSurvivorsW1, S11ControlSurvivorsW1,
      S11SurvivalTableW1, S11PrintedTableW1, withinPrintedPrecision]

/-- The full six-hour vectors follow from the derived design facts and two
small exact matrix multiplications. -/
theorem six_hour_vectors (hP : PositiveDesignFactsW1)
    (n : ℕ) (study : Fin n → Fin 3) (treated : Fin n → Bool) (Y : Fin n → ℝ)
    (hb : BalancedCellsW1 study treated) (ht : ArmTotalW1 treated true Y = 105)
    (hc : ArmTotalW1 treated false Y = 88) (h₂ : StudyTotalW1 study 1 Y = 91)
    (h₄ : StudyTotalW1 study 2 Y = 65) :
    (PositiveRowsW1 study treated).transpose *ᵥ Y = ![193,105,91,65] ∧
    (PositiveRowsW1 study treated).transpose *ᵥ (1-Y) = ![107,45,9,35] ∧
    olsCoefficients (PositiveRowsW1 study treated) Y = ![47/150,17/150,27/50,7/25] ∧
    olsCoefficients (PositiveRowsW1 study treated) (1-Y) = ![103/150,-17/150,-27/50,-7/25] := by
  let X := PositiveRowsW1 study treated
  obtain ⟨_,hG,hU,hY,_⟩ := hP n study treated Y hb
  have hY' : X.transpose *ᵥ Y = ![193,105,91,65] := by
    simpa only [ht,hc,h₂,h₄,show (105:ℝ)+88 = 193 by norm_num] using hY
  have hU' : IsUnit positiveStudyGram.det := by rwa [hG] at hU
  have hcert : positiveStudyGram *ᵥ ![47/150,17/150,27/50,7/25] = ![193,105,91,65] := by
    ext j
    fin_cases j <;> norm_num [positiveStudyGram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hfit : olsCoefficients X Y = ![47/150,17/150,27/50,7/25] := by
    unfold olsCoefficients
    rw [hY', hG, ← hcert, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU', Matrix.one_mulVec]
  have hfitR : olsCoefficients X (1-Y) = ![103/150,-17/150,-27/50,-7/25] := by
    have ha := (complement_all n 4 0 X Y hU (fun i => by simp [X, PositiveRowsW1])).1
    rw [ha, hfit]
    ext j
    fin_cases j <;> norm_num [Pi.single_apply]
  have hRY := Bridge.ols_normal_equations X (1-Y) hU
  rw [hG,hfitR] at hRY
  have hrCert : positiveStudyGram *ᵥ ![103/150,-17/150,-27/50,-7/25] = ![107,45,9,35] := by
    ext j
    fin_cases j <;> norm_num [positiveStudyGram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  exact ⟨hY', hRY.symm.trans hrCert, hfit, hfitR⟩

theorem slope_with_complement (n k : ℕ) (j₀ j : Fin k) (hj : j ≠ j₀)
    (X : Matrix (Fin n) (Fin k) ℝ) (Y : Fin n → ℝ) (b v : ℝ)
    (hX : IsUnit (X.transpose * X).det) (h₁ : ∀ i, X i j₀ = 1)
    (hβ : olsCoefficients X Y j = b)
    (hr : b ≠ 0 ∧ withinPrintedPrecision b v ∧ ¬ withinPrintedPrecision (-b) v) :
    SurvivalAndRemovalSlopeW1 X Y j b v := by
  have hc := congrFun (complement_all n k j₀ X Y hX h₁).1 j
  have he : olsCoefficients X (1-Y) j = -b := by
    simpa [Pi.single_apply, hj, hβ] using hc
  exact ⟨hβ,he,hr⟩

theorem s11_regressions (hP : PositiveDesignFactsW1) (hC : CitedDesignFactsW1)
    (hF : FormerDesignFactsW1) : S11RegressionFactsW1 := by
  refine ⟨?_,?_,?_⟩
  · intro n study treated Y h hb ht hc
    obtain ⟨_,_,hU,_,hβ⟩ := hP n study treated Y hb
    have hβ' : olsCoefficients (PositiveRowsW1 study treated) Y 1 = S11SurvivalTableW1 0 h := by
      rw [hβ,ht,hc]
      exact (s11_table 0 h).1
    exact slope_with_complement n 4 0 1 (by decide) _ Y _ _ hU
      (fun i => by simp [PositiveRowsW1]) hβ' (s11_table 0 h).2
  · intro n study treated Y h hb ht hc
    obtain ⟨_,_,hU,_,hβ⟩ := hC n study treated Y hb
    have hβ' : olsCoefficients (CitedRowsW1 study treated) Y 1 = S11SurvivalTableW1 1 h := by
      rw [hβ,ht,hc]
      exact (s11_table 1 h).1
    exact slope_with_complement n 3 0 1 (by decide) _ Y _ _ hU
      (fun i => by simp [CitedRowsW1]) hβ' (s11_table 1 h).2
  · intro n treated Y h h75 h76 ht hc
    obtain ⟨_,_,hU,_,hβ⟩ := hF n treated Y h75 h76
    have hβ' : olsCoefficients (FormerRowsW1 treated) Y 1 = S11SurvivalTableW1 2 h := by
      rw [hβ,ht,hc]
      exact (s11_table 2 h).1
    exact slope_with_complement n 2 0 1 (by decide) _ Y _ _ hU
      (fun i => by simp [FormerRowsW1]) hβ' (s11_table 2 h).2

end SAP.P041.WH.W1
