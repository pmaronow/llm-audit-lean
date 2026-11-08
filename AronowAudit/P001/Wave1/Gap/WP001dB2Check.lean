import AronowAudit.P001.Wave1.Gap.WP001dB2

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
namespace AronowAudit.P001.Wave1

example : ∀ {K τ : ℕ} (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
  (κ : Measure ℝ) [SFinite κ]
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (Θ : Set (Fin τ → ℝ)) (θ tstar : Fin τ → ℝ) (hθ : θ ∈ Θ) (ht : tstar ∈ Θ)
  (hg : ∀ t ∈ Θ, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hgn : ∀ t ∈ Θ, ∀ y x, 0 ≤ g y x t)
  (hnorm : ∀ t ∈ Θ, ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ) = 1)
  (hunique : ∀ t ∈ Θ,
    averageKLExt νX κ (fun y x => g y x θ) g tstar ≤
      averageKLExt νX κ (fun y x => g y x θ) g t ∧
    (averageKLExt νX κ (fun y x => g y x θ) g t =
      averageKLExt νX κ (fun y x => g y x θ) g tstar → t = tstar)),
  averageKLExt νX κ (fun y x => g y x θ) g θ = 0 ∧
  tstar = θ ∧
  (∀ t ∈ Θ, averageKLExt νX κ (fun y x => g y x θ) g t = 0 ↔ t = θ) :=
  AronowAudit.P001.Wave1.normalized_true_model_unique_kl_target

end AronowAudit.P001.Wave1
