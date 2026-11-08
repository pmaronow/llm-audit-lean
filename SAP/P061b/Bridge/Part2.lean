import SAP.P061b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b.Bridge
open scoped BigOperators Classical

/-- The indicator mean is its exposure probability, an instance of the existing event identity. -/
theorem indicator_mean {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Schedule Ω N) (i : Fin N) (d : ℝ) :
    designMean D (exposureIndicator g i d) = exposureProbability D g i d := by
  change AronowAudit.P061.expectation (toAudit D) (fun z => if g i z = d then 1 else 0) =
    AronowAudit.P061.pi (toAudit D) g i d
  simpa only [AronowAudit.P061.pi, one_mul] using
    AronowAudit.P061.expectation_event (toAudit D) (fun z => g i z = d) 1

/-- This is the exported centered-indicator identity after substituting the indicator means. -/
theorem indicator_covariance {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Schedule Ω N) (i j : Fin N) (d e : ℝ) :
    designCovariance D (exposureIndicator g i d) (exposureIndicator g j e) =
      jointExposureProbability D g i j d e - exposureProbability D g i d *
        exposureProbability D g j e := by
  unfold designCovariance
  rw [indicator_mean, indicator_mean]
  exact AronowAudit.P061.centered_cross_expectation (toAudit D) g i j d e

/-- Only substitution into a finite sum and scalar algebra separate the two printed forms. -/
theorem indicator_sum {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) : indicatorVarianceSum D g y d = covarianceSum D g y d d := by
  unfold indicatorVarianceSum covarianceSum
  simp_rw [indicator_covariance]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem independent_prediction_calibrated {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g F : Schedule Ω N) (d : ℝ) (hp : ∀ i, 0 < exposureProbability D g i d)
    (hFd : ExposureMoment D g F d)
    (hi : ∀ i, EventIndependent D (exposureIndicator g i d) (F i)) :
    PredictionCalibrated D g F d := by
  intro i
  have he : ∀ z, exposureIndicator g i d z = 1 ↔ g i z = d := by
    intro z
    simp [exposureIndicator]
  have hp' : 0 < AronowAudit.P061.probability (toAudit D) (fun z => g i z = d) := hp i
  have hFd' : AronowAudit.P061.Integrable (toAudit D)
      (fun z => if g i z = d then F i z else 0) := hFd i
  have h := AronowAudit.P061.independent_event_expectation (toAudit D)
    (exposureIndicator g i d) (F i) (fun a => a = 1) (fun a => a)
    (by simpa only [he] using hp') (hi i) (by simpa only [he] using hFd')
  have hm : designMean D (fun z => if g i z = d then F i z else 0) =
      exposureProbability D g i d * designMean D (F i) := by
    change AronowAudit.P061.expectation (toAudit D) (fun z => if g i z = d then F i z else 0) =
      AronowAudit.P061.probability (toAudit D) (fun z => g i z = d) *
        AronowAudit.P061.expectation (toAudit D) (F i)
    simpa only [he] using h.2
  change AronowAudit.P061.expectation (toAudit D) (fun z =>
    (if g i z = d then F i z else 0) / exposureProbability D g i d) = _
  rw [AronowAudit.P061.expectation_div_algebra]
  change designMean D (fun z => if g i z = d then F i z else 0) /
    exposureProbability D g i d = _
  rw [hm]
  exact mul_div_cancel_left₀ _ (hp i).ne'

theorem mean_independent_prediction_calibrated {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g F : Schedule Ω N) (d : ℝ) (hp : ∀ i, 0 < exposureProbability D g i d)
    (hi : ∀ i, MeanIndependent D (F i) (exposureIndicator g i d)) :
    PredictionCalibrated D g F d := by
  intro i
  have he : ∀ z, exposureIndicator g i d z = 1 ↔ g i z = d := by
    intro z
    simp [exposureIndicator]
  have hp' : 0 < eventProbability D (fun z => g i z = d) := hp i
  have hm := hi i 1 (by simpa only [he] using hp')
  change AronowAudit.P061.expectation (toAudit D) (fun z =>
    (if g i z = d then F i z else 0) / exposureProbability D g i d) = _
  rw [AronowAudit.P061.expectation_div_algebra]
  change designMean D (fun z => if g i z = d then F i z else 0) /
    eventProbability D (fun z => g i z = d) = _
  simpa only [he] using hm

end SAP.P061b.Bridge
