import AronowAudit.P001.Wave1.Gap.GP0014B1

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGLP0014B3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-- P001-T8: apply the proved finite-density and Fubini adapter to the
measurable joint observation map. Its density argument works over the
finite model law and retains the stated `SFinite` reference measure. -/
theorem averaged_kl_entropy_loglikelihood_proof {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
  (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
  (κ : Measure ℝ) [SFinite κ] (f : ℝ → (Fin K → ℝ) → ℝ)
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ)
  (hf : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
  (hg : Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hfn : ∀ y x, 0 ≤ f y x) (hgn : ∀ y x, 0 ≤ g y x t)
  (hfnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (f y x) ∂κ)=1)
  (hgnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ)=1)
  (htrue : μ.map (fun ω => (X ω,Y ω)) =
    (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
  (hdom : ∀ᵐ xy ∂(νX.prod κ), 0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 t)
  (hent : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
    f xy.2 xy.1*Real.log (f xy.2 xy.1)) (νX.prod κ))
  (hcross : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
    f xy.2 xy.1*Real.log (g xy.2 xy.1 t)) (νX.prod κ)) :
  averageKLExt νX κ f g t ≠ ∞ ∧
  (averageKLExt νX κ f g t).toReal =
    (∫ x, ∫ y, f y x*Real.log (f y x) ∂κ ∂νX) - expectedLogLikelihood μ X Y g t ∧
  averageKL νX κ f g t = (averageKLExt νX κ f g t).toReal := by
  exact averaged_kl_entropy_adapter μ X Y (hX.prodMk hY) νX κ f g t
    hf hg hfn hgn hfnorm hgnorm htrue hdom hent hcross

end
end AronowAudit.P001.Wave1
