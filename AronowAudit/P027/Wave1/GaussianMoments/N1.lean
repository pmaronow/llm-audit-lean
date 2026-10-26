import AronowAudit.P027.Wave1.GaussianMomentsBlueprint
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space

/-! Transfer the first two Gaussian moments through the coordinate's law map. -/

namespace AronowAudit.P027.Wave1.GaussianMoments

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable

theorem n1_proof : N1 := by
  intro Ξ _ μ _ X v hX hlaw
  have hLp : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) :=
    memLp_id_gaussianReal (μ := 0) (v := v) 2
  have hid : Integrable (id : ℝ → ℝ) (gaussianReal 0 v) :=
    hLp.integrable (by norm_num)
  have hsq : Integrable (fun x : ℝ => x * x) (gaussianReal 0 v) := by
    simpa only [id_eq, pow_two] using hLp.integrable_sq
  have hsecond : (∫ x : ℝ, x * x ∂gaussianReal 0 v) = (v : ℝ) := by
    have hv : (∫ x : ℝ, x^2 ∂gaussianReal 0 v) -
        (∫ x : ℝ, x ∂gaussianReal 0 v)^2 =
        ProbabilityTheory.variance (id : ℝ → ℝ) (gaussianReal 0 v) :=
      (variance_eq_sub hLp).symm
    rw [integral_id_gaussianReal, variance_id_gaussianReal] at hv
    simpa only [pow_two, zero_mul, sub_zero] using hv
  have hid_map : Integrable (id : ℝ → ℝ) (μ.map X) := by
    rw [hlaw]
    exact hid
  have hsq_map : Integrable (fun x : ℝ => x * x) (μ.map X) := by
    rw [hlaw]
    exact hsq
  have hXint : Integrable X μ := by
    simpa only [Function.comp_def, id_eq] using
      (integrable_map_measure aestronglyMeasurable_id hX).mp hid_map
  have hXXint : Integrable (fun ξ => X ξ * X ξ) μ := by
    exact (integrable_map_measure hsq_map.aestronglyMeasurable hX).mp hsq_map
  have hXmean : (∫ ξ, X ξ ∂μ) = 0 := by
    calc
      (∫ ξ, X ξ ∂μ) = ∫ x : ℝ, x ∂μ.map X :=
        (integral_map hX aestronglyMeasurable_id).symm
      _ = 0 := by rw [hlaw, integral_id_gaussianReal]
  have hXXmean : (∫ ξ, X ξ * X ξ ∂μ) = (v : ℝ) := by
    calc
      (∫ ξ, X ξ * X ξ ∂μ) = ∫ x : ℝ, x * x ∂μ.map X :=
        (integral_map hX hsq_map.aestronglyMeasurable).symm
      _ = (v : ℝ) := by rw [hlaw]; exact hsecond
  exact ⟨⟨hXint, hXmean⟩, ⟨hXXint, hXXmean⟩⟩

end
end AronowAudit.P027.Wave1.GaussianMoments
