import AronowAudit.P027.Wave1.UniformStartBlueprint
import AronowAudit.P027.Wave1.UniformStart.N1
import AronowAudit.P027.Wave1.UniformStart.N2
import AronowAudit.P027.Wave1.UniformStart.N3
import AronowAudit.P027.Wave1.UniformStart.N4
import AronowAudit.P027.Wave1.UniformStart.N5

/-! The continuous uniform-start selection law agrees with the finite phase law. -/

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory
attribute [local instance] Classical.propDecidable

theorem periodic_uniform_start_bridge :
    ∀ (r m : ℕ) (hr : 0 < r), 0 < m →
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
            (fun g => F ((phaseOriginal r m hr).selected g))) := by
  exact UniformStart.assemble UniformStart.n1_proof UniformStart.n2_proof
    UniformStart.n3_proof UniformStart.n4_proof UniformStart.n5_proof

end
end AronowAudit.P027.Wave1
