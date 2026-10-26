import AronowAudit.P013.Wave1.PrintedWaldBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Events agreeing on E have probabilities differing by at most P(Eᶜ). -/
theorem n13_proof : N13 := by
  classical
  intro Ω _ P X Vhat target V b z E hV hb hz hhat
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hagree : ∀ ω, E ω →
      (0 ≤ Vhat ω ∧ |X ω - target| ≤ z * Real.sqrt (Vhat ω) ↔
        |(X ω - target) / Real.sqrt V| ≤ z * Real.sqrt b) := by
    intro ω hE
    rw [hhat ω hE]
    constructor
    · rintro ⟨_, hcov⟩
      rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
      simpa only [Real.sqrt_mul hb V, mul_assoc] using hcov
    · intro hcov
      refine ⟨mul_nonneg hb hV.le, ?_⟩
      rw [abs_div, abs_of_pos hs, div_le_iff₀ hs] at hcov
      simpa only [Real.sqrt_mul hb V, mul_assoc] using hcov
  unfold probability
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : E ω
  · have heq := hagree ω hE
    by_cases hA : 0 ≤ Vhat ω ∧ |X ω - target| ≤ z * Real.sqrt (Vhat ω)
    · have hB := heq.mp hA
      simp [hA, hB, hE]
    · have hB : ¬ |(X ω - target) / Real.sqrt V| ≤ z * Real.sqrt b :=
        fun hB => hA (heq.mpr hB)
      simp [hA, hB, hE]
  · by_cases hA : 0 ≤ Vhat ω ∧ |X ω - target| ≤ z * Real.sqrt (Vhat ω) <;>
      by_cases hB : |(X ω - target) / Real.sqrt V| ≤ z * Real.sqrt b <;>
      simp [hA, hB, hE, abs_of_pos (P.positive ω), (P.positive ω).le]

end

end AronowAudit.P013.Wave1.PrintedWald
