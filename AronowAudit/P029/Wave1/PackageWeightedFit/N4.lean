import AronowAudit.P029.Wave1.PackageWeightedFitBlueprint

/-!
The package's unweighted cell optimum is a feasible parameter
(ordered interior receipt probabilities). Feasibility is the first conjunct of
`AronowAudit.P029.two_sided_weight_counterexample`.
-/

namespace AronowAudit.P029.Wave1.PackageWeightedFit

open AronowAudit.P029

theorem n4_proof : N4 := ⟨⟨packageCells, two_sided_weight_counterexample.1⟩, rfl⟩

end AronowAudit.P029.Wave1.PackageWeightedFit
