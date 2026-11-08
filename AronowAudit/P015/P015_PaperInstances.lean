import AronowAudit.P015.P015_PaperDomains
namespace AronowAudit.P015.PaperInstances
open MeasureTheory Matrix Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000

def bernoulliReference : Measure ℝ := Measure.dirac 0+Measure.dirac 1
def softplus (η : ℝ) : ℝ := Real.log (1+Real.exp η)

/-- A nondegenerate normalized Bernoulli canonical family, for the fresh
probability-family premises in the scope repairs. -/
theorem bernoulli_canonical_family :
    CanonicalFamily bernoulliReference softplus 1 (fun _=>0) Set.univ {0,1} := by
  refine ⟨by norm_num,isOpen_univ,by measurability,?_,?_⟩
  · simp [bernoulliReference,Measure.add_apply]
  · intro η _
    have hpos : 0<1+Real.exp η := by positivity
    refine ⟨?_,?_⟩
    · exact (integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))
    · rw [bernoulliReference,integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp))]
      simp only [integral_dirac,canonicalLogLikelihood,zero_mul,one_mul,div_one,add_zero,
        zero_sub,softplus,Real.exp_neg,Real.exp_sub,Real.exp_log hpos,Real.exp_zero]
      field_simp

/-- The new scalar score wrapper is instantiated on an actual binary
response in this valid family, rather than on an arbitrary log function. -/
theorem canonical_score_application :
    HasDerivAt (canonicalLogLikelihood softplus 1 1 0)
      (1-deriv softplus 0) 0 := by
  simpa only [div_one] using PaperSpecializations.canonical_score_derivative_calculus bernoulliReference
    softplus 1 (fun _=>0) Set.univ {0,1} bernoulli_canonical_family
    1 0 (deriv softplus 0) (by simp) (Set.mem_univ _) (by
      apply DifferentiableAt.hasDerivAt
      exact ((differentiableAt_const (1:ℝ)).add Real.differentiableAt_exp).log (by norm_num))

#print axioms bernoulli_canonical_family
#print axioms canonical_score_application
end
end AronowAudit.P015.PaperInstances
