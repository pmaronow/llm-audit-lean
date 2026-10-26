import AronowAudit.P018.Wave1.WeightedConsistencyBlueprint
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem g1_proof : G1.{u} := by
  intro U _ μ _ N i j hij
  have hi : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
      (Measure.pi (fun _ : Fin N => μ)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h := (hi.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  simpa only [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) j).map_eq] using h

end
end AronowAudit.P018.Wave1.WeightedConsistency
