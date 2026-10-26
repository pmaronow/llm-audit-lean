import AronowAudit.P042.Wave1.SixAtomicBlueprint

/-!
Transfer of the exact rational finite moments to the six-voter probability law.
-/

set_option autoImplicit false

namespace AronowAudit.P042.Wave1.SixAtomic

open AronowAudit.P042 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

theorem n2_proof : N2 := by
  intro h1
  letI : IsProbabilityMeasure sixMeasure := h1.1
  have hL2 : ∀ j, MemLp (sixD j) 2 sixMeasure := by
    intro j
    exact MemLp.of_discrete

  -- SixΩ is definitionally the product type used by sixAllocations.
  -- The cast of a rational mean is the integral of the pointwise cast.
  have hmean (X : SixΩ → ℚ) :
      (∫ a, (X a : ℝ) ∂sixMeasure) =
        (rationalMean sixAllocations X : ℝ) := by
    rw [h1.2]
    norm_num [rationalMean, six_design.1, Rat.cast_div]
    exact (Rat.cast_sum sixAllocations X).symm

  -- Apply the same integral bridge to the rational centered square.
  have hvariance (X : SixΩ → ℚ) :
      variance (fun a => (X a : ℝ)) sixMeasure =
        (rationalVariance sixAllocations X : ℝ) := by
    have hXmeas : Measurable (fun a : SixΩ => (X a : ℝ)) :=
      Measurable.of_discrete
    rw [variance_eq_integral hXmeas.aemeasurable, hmean X]
    calc
      _ = ∫ a : SixΩ, (((X a - rationalMean sixAllocations X) ^ 2 : ℚ) : ℝ)
          ∂sixMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun a => by push_cast; rfl)
      _ = _ := hmean (fun a => (X a - rationalMean sixAllocations X) ^ 2)

  -- Likewise for the rational centered product; covariance is its integral.
  have hcovariance (X Y : SixΩ → ℚ) :
      covariance (fun a => (X a : ℝ)) (fun a => (Y a : ℝ)) sixMeasure =
        (rationalCovariance sixAllocations X Y : ℝ) := by
    rw [covariance, hmean X, hmean Y]
    calc
      _ = ∫ a : SixΩ,
          (((X a - rationalMean sixAllocations X) *
            (Y a - rationalMean sixAllocations Y) : ℚ) : ℝ) ∂sixMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun a => by push_cast; rfl)
      _ = _ := hmean (fun a =>
        (X a - rationalMean sixAllocations X) *
          (Y a - rationalMean sixAllocations Y))

  obtain ⟨_, _, hv0, hv1, hcov01, _, _⟩ := six_moments
  refine ⟨hL2, ?_, ?_, ?_⟩
  · change variance (fun a : SixΩ => (sixD1 a : ℝ)) sixMeasure = 3 / 10
    rw [hvariance sixD1]
    norm_num [hv0]
  · change variance (fun a : SixΩ => (sixD2 a : ℝ)) sixMeasure = 3 / 10
    rw [hvariance sixD2]
    norm_num [hv1]
  · change covariance (fun a : SixΩ => (sixD1 a : ℝ))
        (fun a : SixΩ => (sixD2 a : ℝ)) sixMeasure = 3 / 20
    rw [hcovariance sixD1 sixD2]
    norm_num [hcov01]

end

end AronowAudit.P042.Wave1.SixAtomic
