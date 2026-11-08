import SAP.P039.Bridge.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.Bridge
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

/-- The exported exact fits give the corrected cells by coefficient projection and rational rounding. -/
theorem corrected_table_cells : CorrectedTableCellsStatement := by
  have ha := AronowAudit.P039.table_A1_exact_fit
  have hb := AronowAudit.P039.table_A2_exact_fit
  have hc := AronowAudit.P039.table_A3_exact_fit
  have ua := AronowAudit.P039.table_A1_unique_minimizer
  have ub := AronowAudit.P039.table_A2_unique_minimizer
  have uc := AronowAudit.P039.table_A3_unique_minimizer
  have ra := AronowAudit.P039.table_A1_coefficient_rounding
  have rb := AronowAudit.P039.table_A2_coefficient_rounding
  have rc := AronowAudit.P039.table_A3_coefficient_rounding
  have sa := AronowAudit.P039.table_A1_standard_error_rounding
  have qa : ols tableA1 tableTwoOutcome 1 =
      7146187962914975000000/1117667657915636289559 := by
    exact congrFun ha.2.2.2.1 1
  have qb : ols tableA2 tableTwoOutcome 1 =
      315309901567374756223272228924480076940000000/49481205176565031631955325062456554157036059 := by
    exact congrFun hb.2.2.2.1 1
  have qc : ols tableA3 tableTwoOutcome 1 =
      560959205595590684404193874010188762669512981839878401170000000/
        87848341864933029922153613743599975715147930782629447955391927 := by
    exact congrFun hc.2.2.2.1 1
  have sb : (0.955 : ℝ) ≤ Real.sqrt (olsSESquared tableA2 tableTwoOutcome 1) ∧
      Real.sqrt (olsSESquared tableA2 tableTwoOutcome 1) < (0.965 : ℝ) := by
    rw [olsSESquared_eq, tableA2_eq, tableTwoOutcome_eq, hb.2.2.2.2.2.2]
    constructor
    · apply (Real.le_sqrt (by norm_num) (by norm_num)).2
      norm_num
    · apply (Real.sqrt_lt' (by norm_num)).2
      norm_num
  have sc : (1.005 : ℝ) ≤ Real.sqrt (olsSESquared tableA3 tableTwoOutcome 1) ∧
      Real.sqrt (olsSESquared tableA3 tableTwoOutcome 1) < (1.015 : ℝ) := by
    rw [olsSESquared_eq, tableA3_eq, tableTwoOutcome_eq, hc.2.2.2.2.2.2]
    constructor
    · apply (Real.le_sqrt (by norm_num) (by norm_num)).2
      norm_num
    · apply (Real.sqrt_lt' (by norm_num)).2
      norm_num
  exact ⟨⟨AronowAudit.P039.coefficientsA1, ua.1, ua.2⟩,
    ⟨AronowAudit.P039.coefficientsA2, ub.1, ub.2⟩,
    ⟨AronowAudit.P039.coefficientsA3, uc.1, uc.2⟩,
    qa, ra.1, ra.2, ha.2.2.2.2.2.2, sa.1, sa.2.1, sa.2.2.1, sa.2.2.2,
    qb, rb.1, rb.2, sb.1, sb.2, qc, rc.1, rc.2,
    (by change (0.95 : ℝ) ≤ Real.sqrt (olsSESquared tableA3 tableTwoOutcome 1); linarith [sc.1]),
    (by change Real.sqrt (olsSESquared tableA3 tableTwoOutcome 1) < (1.05 : ℝ); linarith [sc.2]),
    sc.1, sc.2⟩

/-- Arithmetic substitution into the exported nested-fit bound. -/
lemma rounded_bound (se₁ se₂ s₁ s₂ : ℝ)
    (hse₂u : se₂ ≤ 0.965) (hs₁ : 0 ≤ s₁) (hs₁u : s₁ ≤ 4.625)
    (hs₂ : 4.695 ≤ s₂) (hbound : se₁ ≤ se₂*s₁/s₂) : se₁ ≤ 7141/7512 := by
  have hp : 0 < s₂ := by linarith
  calc
    se₁ ≤ se₂*s₁/s₂ := hbound
    _ ≤ (0.965 : ℝ)*4.625/s₂ :=
      div_le_div_of_nonneg_right (mul_le_mul hse₂u hs₁u hs₁ (by norm_num)) hp.le
    _ ≤ (0.965 : ℝ)*4.625/4.695 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs₂
    _ = 7141/7512 := AronowAudit.P039.printed_standard_error_exact_gap.1

/-- Transport the nested regressor geometry before any outcome is chosen. -/
theorem nested_geometry : NestedStandardErrorsStatement := by
  exact @AronowAudit.P039.PaperDomains.nested_standard_error_bound

/-- Apply the numerical bound to actual nested OLS fits with positive residual SSEs. -/
theorem printed_cells_bound : PrintedCellsBoundStatement := by
  intro Z₁ Z₂ q y hspan h₁ h₂ hp₁ hp₂ hse₂ hs₁ hs₂
  have h := nested_geometry Z₁ Z₂ q hspan h₁ h₂ (by decide) (by decide)
  dsimp only at h
  obtain ⟨_, _, _, _, _, _, _, hout⟩ := h
  have hb := (hout y hp₁ hp₂).2.2.2
  apply rounded_bound _ _ _ _ hse₂ (Real.sqrt_nonneg _) hs₁ hs₂
  norm_num [olsResidualStandardError] at hb ⊢
  exact hb

/-- Assemble the nested-fit result, printed-cell contradiction and the corrected coefficients and SEs. -/
theorem T7_correspondence : T7Statement := by
  exact ⟨nested_geometry,
    @AronowAudit.P039.printed_nested_standard_errors_impossible,
    AronowAudit.P039.printed_standard_error_exact_gap,
    printed_cells_bound,
    corrected_table_cells⟩

end SAP.P039.Bridge
