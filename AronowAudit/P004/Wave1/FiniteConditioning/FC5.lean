import AronowAudit.P004.Wave1.FiniteConditioning.FC2

namespace AronowAudit.P004.Wave1.FiniteConditioning

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Positive cylinder weights preserve pointwise absolute bounds. -/
theorem fc5_proof : FC5 := by
  classical
  intro N p hp J U M hU z
  have hden : 0 < ∏ j ∈ J, coin (p j) (z j) := conditioning_mass_pos p hp J z
  have hmono (V W : Assignment N → ℝ) (hVW : ∀ w, V w ≤ W w) :
      conditionOn p J V z ≤ conditionOn p J W z := by
    unfold conditionOn
    apply div_le_div_of_nonneg_right _ hden.le
    apply expect_mono p hp
    intro w
    by_cases hw : ∀ j ∈ J, w j = z j
    · simp only [if_pos hw]
      exact hVW w
    · simp only [if_neg hw, le_refl]
  have hlo : conditionOn p J (fun _ => -M) z ≤ conditionOn p J U z :=
    hmono (fun _ => -M) U (fun w => (abs_le.mp (hU w)).1)
  have hhi : conditionOn p J U z ≤ conditionOn p J (fun _ => M) z :=
    hmono U (fun _ => M) (fun w => (abs_le.mp (hU w)).2)
  rw [(fc2_proof p hp J).1 (-M) z] at hlo
  rw [(fc2_proof p hp J).1 M z] at hhi
  exact abs_le.mpr ⟨hlo, hhi⟩

end
end AronowAudit.P004.Wave1.FiniteConditioning
