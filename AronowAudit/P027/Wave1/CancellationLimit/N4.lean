import AronowAudit.P027.Wave1.CancellationLimitBlueprint
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! For nonnegative functions the L¹ norm is their integral. -/

namespace AronowAudit.P027.Wave1.CancellationLimit

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable

theorem n4_proof : N4 := by
  intro Ξ _ μ T hnonneg hint hmean
  have hnorm (n : ℕ) : eLpNorm (T n) 1 μ = ENNReal.ofReal (∫ ξ, T n ξ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hint n).aestronglyMeasurable,
      ofReal_integral_eq_lintegral_ofReal (hint n) (Eventually.of_forall (hnonneg n))]
    apply lintegral_congr
    intro ξ
    exact Real.enorm_eq_ofReal (hnonneg n ξ)
  have hnorm_limit : Tendsto (fun n => ENNReal.ofReal (∫ ξ, T n ξ ∂μ))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hmean
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
  simpa only [Pi.sub_def, sub_zero, hnorm] using hnorm_limit

end
end AronowAudit.P027.Wave1.CancellationLimit
