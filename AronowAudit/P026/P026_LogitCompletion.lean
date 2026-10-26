import AronowAudit.P026.P026_LogitApproximation
import AronowAudit.P026.P026_LogitFiniteMoments
/-! Complete actual-table logistic theorem: unique MLEs, certified coefficients,
exact means, variances over all 90 allocations and certified standard-deviation bounds. -/
namespace AronowAudit.P026.LogitCompletion
noncomputable section
theorem logit_table_corrected_completed :
    (∃! β, logitMaximizer false β) ∧ (∃! β, logitMaximizer true β) ∧
    |(logitCoefficients true).1-(-11201076/10000000)| ≤ 5/10000000 ∧
    |(logitCoefficients true).2-(5657586/10000000)| ≤ 5/10000000 ∧
    |(logitCoefficients false).1-(10843223/10000000)| ≤ 5/10000000 ∧
    |(logitCoefficients false).2-(2280259/10000000)| ≤ 5/10000000 ∧
    expectation realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual)=0 ∧
    (247090/1000000 : ℝ) ≤ Real.sqrt (variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual)) ∧
    Real.sqrt (variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual)) ≤ 247093/1000000 ∧
    (605/10000 : ℝ) ≤ variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual) ∧
    variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual) < 615/10000 ∧
    expectation realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual) =
      variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual) ∧
    (125/10000 : ℝ) ≤ Real.sqrt (variance realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual)) ∧
    Real.sqrt (variance realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual)) < 135/10000 := by
  obtain ⟨hca,hcb,hcc,hcd⟩:=logit_quoted_coefficient_bounds
  obtain ⟨hmean,hunbiased⟩:=logit_exact_moments
  obtain ⟨hslo,hshi,hvlo,hvhi,hvslo,hvshi⟩:=
    LogitFiniteMoments.logit_numeric_moment_bounds tableLogitResidual
      actual_residual_bound actual_residual_approximation
  exact ⟨logit_maximizer_unique false,logit_maximizer_unique true,
    hca,hcb,hcc,hcd,hmean,hslo,hshi,hvlo,hvhi,hunbiased,hvslo,hvshi⟩

end
end AronowAudit.P026.LogitCompletion
namespace AronowAudit.P026
theorem logit_table_corrected :
    (∃! β, logitMaximizer false β) ∧ (∃! β, logitMaximizer true β) ∧
    |(logitCoefficients true).1-(-11201076/10000000)| ≤ 5/10000000 ∧
    |(logitCoefficients true).2-(5657586/10000000)| ≤ 5/10000000 ∧
    |(logitCoefficients false).1-(10843223/10000000)| ≤ 5/10000000 ∧
    |(logitCoefficients false).2-(2280259/10000000)| ≤ 5/10000000 ∧
    expectation realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual)=0 ∧
    (247090/1000000 : ℝ) ≤ Real.sqrt (variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual)) ∧
    Real.sqrt (variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual)) ≤ 247093/1000000 ∧
    (605/10000 : ℝ) ≤ variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual) ∧
    variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual) < 615/10000 ∧
    expectation realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual) =
      variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual) ∧
    (125/10000 : ℝ) ≤ Real.sqrt (variance realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual)) ∧
    Real.sqrt (variance realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual)) < 135/10000 := by
  exact LogitCompletion.logit_table_corrected_completed

end AronowAudit.P026
