import AronowAudit.P029.Wave1.PackageWeightedFit.N2
import AronowAudit.P029.Wave1.PackageWeightedFit.N3
import AronowAudit.P029.Wave1.PackageWeightedFit.N4

/-!
# P029-T23: an explicit nested Bernoulli counterexample

The package's inside-log objective has an exact minimizer that does not minimize
the observation-weighted objective over the same nested Bernoulli parameter space.
-/

namespace AronowAudit.P029.Wave1

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

theorem nested_bernoulli_package_weighted_fit_counterexample :
    ∃ q : AronowAudit.P029.Wave1.PackageWeightedFit.Theta,
      q.val = AronowAudit.P029.packageCells ∧
      AronowAudit.P029.IsMinimizer
        (fun t : AronowAudit.P029.Wave1.PackageWeightedFit.Theta =>
          AronowAudit.P029.packageObjective
            (AronowAudit.P029.Wave1.PackageWeightedFit.lik t)
            AronowAudit.P029.Wave1.PackageWeightedFit.obsW) q ∧
      ¬ AronowAudit.P029.IsMinimizer
        (fun t : AronowAudit.P029.Wave1.PackageWeightedFit.Theta =>
          AronowAudit.P029.weightedObjective
            (AronowAudit.P029.Wave1.PackageWeightedFit.lik t)
            AronowAudit.P029.Wave1.PackageWeightedFit.obsW) q := by
  obtain ⟨q, hq⟩ := PackageWeightedFit.n4_proof
  exact ⟨q, hq, PackageWeightedFit.n2_proof q hq, PackageWeightedFit.n3_proof q hq⟩

end

end AronowAudit.P029.Wave1
