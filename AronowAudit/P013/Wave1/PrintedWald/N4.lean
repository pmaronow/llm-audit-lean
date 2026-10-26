import AronowAudit.P013.Wave1.PrintedWaldBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Under an independent product design, the variance of a sum of coordinate
functions is the sum of their coordinate variances. The proof first shows that
distinct coordinates have zero covariance. -/
theorem n4_proof : N4 := by
  classical
  intro Ω _ P R g
  have hcov (i j : Fin R) :
      covariance (replicateDesign P R) (fun zs => g i (zs i)) (fun zs => g j (zs j)) =
        if i = j then variance P (g i) else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [if_pos rfl, ite_true, variance, covariance,
        replicate_marginal P R i (fun a => g i a * g i a),
        replicate_marginal P R i (g i)]
    · rw [if_neg hij, covariance,
        replicate_pair_marginal P R i j hij (g i) (g j),
        replicate_marginal P R i (g i), replicate_marginal P R j (g j)]
      ring
  change covariance (replicateDesign P R) (fun zs => ∑ r, g r (zs r))
    (fun zs => ∑ r, g r (zs r)) = ∑ r, variance P (g r)
  rw [covariance_sum_sum]
  simp_rw [hcov]
  simp

end

end AronowAudit.P013.Wave1.PrintedWald
