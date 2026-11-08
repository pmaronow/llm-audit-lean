import AronowAudit.P027.Wave1.CancellationLimitBlueprint
import Mathlib.Probability.Independence.InfinitePi

/-! Node N9 of the record-10 blueprint (trivial; written by the blueprint architect):
coordinates of the countable product of `N(0, σ2)` laws taken along an injective index
map satisfy `GaussianNoise`. -/

namespace AronowAudit.P027.Wave1.CancellationLimit

open MeasureTheory ProbabilityTheory

theorem n9_proof : N9 := by
  intro K f hf σ2
  exact ⟨fun k => ⟨(measurable_pi_apply (f k)).aemeasurable, Measure.infinitePi_map_eval _ (f k)⟩,
    (iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)).precomp hf⟩

end AronowAudit.P027.Wave1.CancellationLimit
