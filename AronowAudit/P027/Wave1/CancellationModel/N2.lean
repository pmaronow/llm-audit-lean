import AronowAudit.P027.Wave1.CancellationModelBlueprint

/-! Node N2 of the record-11 blueprint (trivial; written by the blueprint architect):
the coordinates of a finite product of `N(0, σ2)` laws satisfy `GaussianNoise`. -/

namespace AronowAudit.P027.Wave1.CancellationModel

open MeasureTheory ProbabilityTheory

theorem n2_proof : N2 := by
  intro K _ σ2
  exact ⟨fun k => ⟨(measurable_pi_apply k).aemeasurable, (measurePreserving_eval _ k).map_eq⟩,
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)⟩

end AronowAudit.P027.Wave1.CancellationModel
