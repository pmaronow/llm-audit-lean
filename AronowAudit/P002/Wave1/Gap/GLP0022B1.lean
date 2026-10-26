import AronowAudit.P002.Wave1.PrintedTheorem2

/-!
P002-T4: the quantitative sharpness counterexample for adjusted coverage.

The finite-design sampling calculation puts the square inside the expectation:
`E[(bar x)^2] = f_m Q` and
`E[(overline{x^2} - Q)^2] = f_m (R - Q^2)`.
-/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Population normal equations center the residuals; the half-moment bound
then forces both residual schedules to vanish. -/
theorem T4SC_residuals_vanish : PrintedTheorem2.ResidualsVanish :=
  PrintedTheorem2.n2_proof PrintedTheorem2.n1_proof

/-- Exact arm fits with equal population intercepts accept the LATE whenever
both observed arm Gram matrices are nonsingular. -/
theorem T4SC_full_rank_acceptance : PrintedTheorem2.FullRankAcceptance :=
  PrintedTheorem2.n3_proof PrintedTheorem2.n1_proof

/-- The two corrected sampling second moments give the factor 258 per arm. -/
theorem T4SC_single_arm_failure : PrintedTheorem2.SingleArmFailure :=
  PrintedTheorem2.n6_proof PrintedTheorem2.n4_proof
    PrintedTheorem2.n5_proof PrintedTheorem2.n11_proof

/-- Allocation bounds and a union bound give the factor 1548; small designs
are covered by the elementary probability upper bound. -/
theorem T4SC_class_failure : PrintedTheorem2.ClassFailure :=
  PrintedTheorem2.n7_proof PrintedTheorem2.n11_proof T4SC_single_arm_failure

/-- The full-rank acceptance event yields the class-wide finite coverage bound. -/
theorem T4SC_coverage_lower_bound : PrintedTheorem2.CoverageLowerBound :=
  PrintedTheorem2.n8_proof PrintedTheorem2.n11_proof T4SC_residuals_vanish
    T4SC_full_rank_acceptance T4SC_class_failure

/-- The specified centered grid supplies a model in every beta fiber. -/
theorem T4SC_grid_in_class : PrintedTheorem2.GridInClass :=
  PrintedTheorem2.n9_proof

/-- The nested infimum is squeezed between the finite coverage bound and one. -/
theorem T4SC_infimum_limit_one : PrintedTheorem2.InfimumLimitOne :=
  PrintedTheorem2.n10_proof PrintedTheorem2.n11_proof
    T4SC_coverage_lower_bound T4SC_grid_in_class

theorem theorem2_sharpness_counterexample_proof (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (∀ n, 2 ≤ n → ∀ β, Xi (degenerateCovModel n β) 0 (1/4) 4 (1/2) (1/4) ∧
      late (degenerateCovModel n β).pop = β) ∧
    (∀ n, 2 ≤ n → ∀ P : CovPopulation n 1, Xi P 0 (1/4) 4 (1/2) (1/4) →
      max 0 (1-1548/((n : ℝ)-1)) ≤ adjustedCoverage P (late P.pop) α) ∧
    Tendsto (fun n => infCoverageXi n 1 0 (1/4) 4 (1/2) (1/4) α) atTop (nhds 1) ∧
    ¬Tendsto (fun n => infCoverageXi n 1 0 (1/4) 4 (1/2) (1/4) α) atTop
      (nhds (ENNReal.ofReal (1-α))) := by
  have hlim := T4SC_infimum_limit_one α
  refine ⟨T4SC_grid_in_class, ?_, hlim, ?_⟩
  · intro n hn P hP
    exact T4SC_coverage_lower_bound n P α hn hP
  · intro hbad
    have heq := tendsto_nhds_unique hlim hbad
    have hlt : ENNReal.ofReal (1-α) < 1 :=
      ENNReal.ofReal_lt_one.mpr (by linarith [hα.1])
    exact (ne_of_lt hlt) heq.symm

end
end AronowAudit.P002.Wave1
