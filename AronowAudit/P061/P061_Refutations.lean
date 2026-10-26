import AronowAudit.P061.P061_PrintedClaims

/-! Refutations of the two false printed general assertions.
The actual design retains every feasible real assignment, has positive exposure
probabilities, and has a nonsummable targeted signed response. -/
namespace AronowAudit.P061.Refutations
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

theorem divergent_exposure_one_positive :
    IndividualPositivity realGeometricDesign divergentExposure 1 := by
  refine ⟨1/2,by norm_num,?_⟩
  intro i
  fin_cases i
  change 1/2 ≤ pi realGeometricDesign divergentExposure 0 1
  rw [missing_moment_counterexample.1]

theorem divergent_exposure_zero_positive :
    IndividualPositivity realGeometricDesign divergentExposure 0 := by
  refine ⟨1/2,by norm_num,?_⟩
  intro i
  fin_cases i
  change 1/2 ≤ pi realGeometricDesign divergentExposure 0 0
  rw [missing_moment_counterexample.2.1]

theorem printed_well_defined_claim_refuted : ¬PrintedClaims.printed_well_defined_claim := by
  intro h
  have ht := h realGeometricDesign divergentExposure divergentOutcome 1 0
    (by norm_num) divergent_exposure_one_positive divergent_exposure_zero_positive
  exact missing_moment_counterexample.2.2.2.1
    (integrable_summable realGeometricDesign (ht.1 0))

theorem printed_general_ht_unbiased_refuted : ¬PrintedClaims.printed_general_ht_unbiased := by
  intro h
  have ht := h realGeometricDesign divergentExposure divergentOutcome 1 0
    (by norm_num) divergent_exposure_one_positive divergent_exposure_zero_positive
  exact missing_moment_counterexample.2.2.2.2 ht.1

end
end AronowAudit.P061.Refutations
