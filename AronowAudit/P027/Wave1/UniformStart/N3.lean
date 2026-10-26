import AronowAudit.P027.Wave1.UniformStart.N2

/-! A translated systematic point can hit only its own block and phase. -/

namespace AronowAudit.P027.Wave1.UniformStart

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n3_proof : N3 := by
  intro r g h u hu j j'
  have hr : 0 < r := Nat.zero_lt_of_lt g.1.isLt
  have hL : (0 : ℝ) < 12 * (r : ℝ) := by
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    positivity
  have hub : 0 ≤ u ∧ u < 12 * (r : ℝ) := (n2_proof r).1 g hu
  obtain ⟨ha, hend⟩ := phaseInterval_endpoint_bounds h
  constructor
  · intro hhit
    have hblock :
        (12 * (r : ℝ)) * (j : ℝ) ≤ u + (j' : ℝ) * (12 * (r : ℝ)) ∧
        u + (j' : ℝ) * (12 * (r : ℝ)) <
          (12 * (r : ℝ)) * ((j : ℝ) + 1) := by
      constructor <;> nlinarith [hhit.1, hhit.2]
    have hjeq : j' = j := by
      apply le_antisymm
      · by_contra hnot
        have hn : j + 1 ≤ j' := by omega
        have hc : (j : ℝ) + 1 ≤ (j' : ℝ) := by exact_mod_cast hn
        have hmul := mul_le_mul_of_nonneg_left hc hL.le
        nlinarith [hub.1, hblock.2]
      · by_contra hnot
        have hn : j' + 1 ≤ j := by omega
        have hc : (j' : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hn
        have hmul := mul_le_mul_of_nonneg_left hc hL.le
        nlinarith [hub.2, hblock.1]
    subst j'
    have huh : u ∈ phaseInterval h := by
      change phaseStartLeft h ≤ u ∧
        u < phaseStartLeft h + (if h.2 = 0 then 2 else 10)
      constructor <;> nlinarith [hhit.1, hhit.2]
    obtain ⟨g₀, hg₀, huniq⟩ := (n2_proof r).2 u hub
    exact ⟨rfl, (huniq h huh).trans (huniq g hu).symm⟩
  · rintro ⟨hj, hh⟩
    subst j'
    subst h
    change phaseStartLeft g ≤ u ∧
      u < phaseStartLeft g + (if g.2 = 0 then 2 else 10) at hu
    constructor <;> nlinarith [hu.1, hu.2]

end
end AronowAudit.P027.Wave1.UniformStart
