import SAP.P030.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P030.Bridge
open scoped BigOperators
noncomputable section

/-- Assemble the already exported design and conditional point-mass certificates. -/
theorem tableDesign : TableDesign := by
  rcases AronowAudit.P030.ten_design with ⟨hN, hC, hΩ, hE, hT⟩
  exact ⟨hN, hC, hΩ, hE, hT, AronowAudit.P030.ten_assignment_probabilities⟩

/-- Each table assignment treats an explicitly identified variant unit. -/
theorem table_treated_nonempty (r : Fin 6) :
    (Finset.univ.filter
      (fun j => tenS j = false ∧ tenAssignment (tableTreatment r) j = true)).Nonempty := by
  classical
  refine ⟨tableTreatment r, ?_⟩
  have hs : tenS (tableTreatment r) = false := by
    fin_cases r <;> norm_num [tenS, tableTreatment]
  simp [hs, tenAssignment]

/-- Transport the exact table computations, without adding any rank calculations. -/
theorem tableNumerics : TableNumerics := by
  exact ⟨AronowAudit.P030.table_y_vector, AronowAudit.P030.table_distances,
    AronowAudit.P030.table_correlations.1, table_treated_nonempty,
    AronowAudit.P030.table_correlations.2.1, AronowAudit.P030.table_correlations.2.2,
    AronowAudit.P030.table_value_order, AronowAudit.P030.worked_table_result.2.1,
    AronowAudit.P030.table_rounding⟩

theorem weakMonotoneExample : WeakMonotoneExample :=
  AronowAudit.P030.weak_monotonicity_counterexample

/-- Replace the two table entries by the definitionally identical actual statistics. -/
theorem outcomeNullNonconstant : OutcomeNullNonconstant := by
  rcases AronowAudit.P030.statistic_invariance_counterexample with
    ⟨hE, hI, hF, h0, h3, hne, _⟩
  exact ⟨hE, hI, AronowAudit.P030.ten_design.2.2.1, hF, h0, h3, tableNumerics, hne⟩

theorem fiveOutcomes_value : fiveOutcomes = ![0,1,2] := by
  funext i
  fin_cases i <;> rfl

/-- These witnesses avoid the empty-set branch of the nearest-distance definition. -/
theorem five_treated_nonempty (a : Fin 2) :
    (Finset.univ.filter (fun j => fiveS j = false ∧ fiveAssignment a j = true)).Nonempty := by
  classical
  fin_cases a
  · exact ⟨3, by norm_num [fiveS, fiveAssignment]⟩
  · exact ⟨4, by norm_num [fiveS, fiveAssignment]⟩

/-- Existing positive-variance theorem applied to two unequal explicit entries. -/
theorem ordering_variances :
    0 < rankSquares (![1,2,1,1] : Fin 4 → ℝ) ∧
    0 < rankSquares (![0,2,1,1] : Fin 4 → ℝ) := by
  exact ⟨AronowAudit.P030.nonconstant_rank_variance _ ⟨0, 1, by norm_num⟩,
    AronowAudit.P030.nonconstant_rank_variance _ ⟨0, 1, by norm_num⟩⟩

end
end SAP.P030.Bridge
