import AronowAudit.P027.Wave1.GaussianMomentsBlueprint
import Mathlib.Probability.Independence.Integration

/-! Independent integrable mean-zero real random variables have an integrable
product with integral zero. -/

namespace AronowAudit.P027.Wave1.GaussianMoments

open MeasureTheory ProbabilityTheory

theorem n2_proof : N2 := fun _ _ _ _ hXY hX hY hX0 _ =>
  ⟨hXY.integrable_mul hX hY, by
    rw [hXY.integral_fun_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable,
      hX0, zero_mul]⟩

end AronowAudit.P027.Wave1.GaussianMoments
