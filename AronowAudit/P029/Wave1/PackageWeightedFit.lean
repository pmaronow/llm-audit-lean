import AronowAudit.P029.Wave1.PackageWeightedFitBlueprint
import AronowAudit.P029.Wave1.PackageWeightedFit.N1
import AronowAudit.P029.Wave1.PackageWeightedFit.N2
import AronowAudit.P029.Wave1.PackageWeightedFit.N3
import AronowAudit.P029.Wave1.PackageWeightedFit.N4

namespace AronowAudit.P029.Wave1

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

theorem printed_package_weighted_fit_refuted :
    ¬ (∀ {I Θ : Type} [Fintype I] (L : Θ → I → ℝ) (w : I → ℝ),
      (∀ θ i, 0 < L θ i) → (∀ i, 0 < w i) → ∀ θ : Θ,
        IsMinimizer (fun t => packageObjective (L t) w) θ →
        IsMinimizer (fun t => weightedObjective (L t) w) θ) :=
  PackageWeightedFit.assemble PackageWeightedFit.n1_proof PackageWeightedFit.n2_proof
    PackageWeightedFit.n3_proof PackageWeightedFit.n4_proof

example : AronowAudit.P029.Wave1.PackageWeightedFit.Target :=
  printed_package_weighted_fit_refuted

end

end AronowAudit.P029.Wave1
