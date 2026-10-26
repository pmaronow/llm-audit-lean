import AronowAudit.P027.Wave1.UniformStart

/-! P027-T2: the uniform-start bridge together with the samplewise corrections. -/

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory
attribute [local instance] Classical.propDecidable

theorem periodic_correction_values_with_uniform_start :
    (∀ (r m : ℕ) (hr : 0 < r), 0 < m →
      let K := (Σ _ : Fin r × Fin 2, Fin m)
      let L : ℝ := 12 * (r : ℝ)
      let left : K → ℝ := fun k =>
        ∑ a : K, if phaseIndex a < phaseIndex k then phaseSize a else 0
      let s : ℝ → K → Bool := fun u k => decide
        (∃ j : Fin m, left k ≤ u + (j : ℝ) * L ∧
          u + (j : ℝ) * L < left k + phaseSize k)
      let ν : Measure ℝ :=
        (ENNReal.ofReal L)⁻¹ • (volume.restrict (Set.Ico (0 : ℝ) L))
      IsProbabilityMeasure ν ∧
      (∀ k : K, left k = phaseStartLeft k.1 + L * (k.2 : ℝ)) ∧
      (∀ u : ℝ, u ∈ Set.Ico (0 : ℝ) L →
        ∃! g : Fin r × Fin 2,
          u ∈ Set.Ico (phaseStartLeft g)
            (phaseStartLeft g + (if g.2 = 0 then 2 else 10))) ∧
      (∀ (g : Fin r × Fin 2) (u : ℝ),
        u ∈ Set.Ico (phaseStartLeft g)
          (phaseStartLeft g + (if g.2 = 0 then 2 else 10)) →
        s u = (phaseOriginal r m hr).selected g) ∧
      (∀ g : Fin r × Fin 2,
        ν (Set.Ico (phaseStartLeft g)
          (phaseStartLeft g + (if g.2 = 0 then 2 else 10))) =
            ENNReal.ofReal (phaseProb r g)) ∧
      (∀ F : (K → Bool) → ℝ,
        Integrable (fun u => F (s u)) ν ∧
        (∫ u, F (s u) ∂ν) =
          expect (phaseOriginal r m hr)
            (fun g => F ((phaseOriginal r m hr).selected g)))) ∧
    (∀ (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (g : Fin r × Fin 2),
    quadraticCorrection (phaseOriginal r m hr) z g =
      ((m:ℝ)*(2*r)-m)*groupSquares (fun _ => m) z g/phaseProb r g ∧
    quadraticCorrection (phaseGrouped r hr) (groupTotal (fun _ => m) z) g =
      (2*r-1)*(groupTotal (fun _ => m) z g)^2/phaseProb r g) := by
  exact ⟨AronowAudit.P027.Wave1.periodic_uniform_start_bridge,
    AronowAudit.P027.phase_correction_values⟩

end
end AronowAudit.P027.Wave1
