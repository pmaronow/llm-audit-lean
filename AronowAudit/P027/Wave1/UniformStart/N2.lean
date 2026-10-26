import AronowAudit.P027.Wave1.UniformStartBlueprint
import Mathlib.Algebra.Order.Floor.Semiring

/-! The first-block phase intervals, including their half-open boundaries. -/

namespace AronowAudit.P027.Wave1.UniformStart

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Endpoint bounds also used in the block-localisation proof. -/
theorem phaseInterval_endpoint_bounds {r : ℕ} (g : Fin r × Fin 2) :
    0 ≤ phaseStartLeft g ∧
      phaseStartLeft g + (if g.2 = 0 then 2 else 10) ≤ 12 * (r : ℝ) := by
  have hi0 : (0 : ℝ) ≤ (g.1 : ℝ) := by positivity
  have hir : (g.1 : ℝ) + 1 ≤ (r : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt g.1.isLt)
  unfold phaseStartLeft
  split_ifs <;> constructor <;> linarith

private theorem phaseInterval_block_bounds {r : ℕ} (g : Fin r × Fin 2)
    (u : ℝ) (hu : u ∈ phaseInterval g) :
    12 * (g.1 : ℝ) ≤ u ∧ u < 12 * ((g.1 : ℝ) + 1) := by
  by_cases hb : g.2 = 0
  · simp only [phaseInterval, phaseStartLeft, hb, ite_true, add_zero, Set.mem_Ico] at hu
    constructor <;> linarith [hu.1, hu.2]
  · simp only [phaseInterval, phaseStartLeft, hb, ite_false, Set.mem_Ico] at hu
    constructor <;> linarith [hu.1, hu.2]

private theorem phaseInterval_unique {r : ℕ} (g h : Fin r × Fin 2)
    (u : ℝ) (hg : u ∈ phaseInterval g) (hh : u ∈ phaseInterval h) : h = g := by
  obtain ⟨hgl, hgu⟩ := phaseInterval_block_bounds g u hg
  obtain ⟨hhl, hhu⟩ := phaseInterval_block_bounds h u hh
  have hival : h.1.val = g.1.val := by
    apply le_antisymm
    · by_contra hnot
      have hn : g.1.val + 1 ≤ h.1.val := by omega
      have hc : (g.1 : ℝ) + 1 ≤ (h.1 : ℝ) := by exact_mod_cast hn
      linarith
    · by_contra hnot
      have hn : h.1.val + 1 ≤ g.1.val := by omega
      have hc : (h.1 : ℝ) + 1 ≤ (g.1 : ℝ) := by exact_mod_cast hn
      linarith
  have hi : h.1 = g.1 := Fin.ext hival
  rcases g with ⟨i, b⟩
  rcases h with ⟨i', b'⟩
  change i' = i at hi
  subst i'
  have hb : b' = b := by
    fin_cases b <;> fin_cases b' <;> try rfl
    all_goals
      exfalso
      norm_num [phaseInterval, phaseStartLeft] at hg hh
      linarith [hg.1, hg.2, hh.1, hh.2]
  exact Prod.ext rfl hb

theorem n2_proof : N2 := by
  intro r
  constructor
  · intro g u hu
    obtain ⟨ha, hb⟩ := phaseInterval_endpoint_bounds g
    change phaseStartLeft g ≤ u ∧
      u < phaseStartLeft g + (if g.2 = 0 then 2 else 10) at hu
    exact ⟨le_trans ha hu.1, lt_of_lt_of_le hu.2 hb⟩
  · intro u hu
    have hu0 : 0 ≤ u := hu.1
    have huL : u < 12 * (r : ℝ) := hu.2
    have hdiv0 : 0 ≤ u / 12 := div_nonneg hu0 (by norm_num)
    have hfloor : ⌊u / 12⌋₊ < r := by
      apply (Nat.floor_lt hdiv0).2
      linarith
    let i : Fin r := ⟨⌊u / 12⌋₊, hfloor⟩
    have hil : 12 * (i : ℝ) ≤ u := by
      have hf : (⌊u / 12⌋₊ : ℝ) ≤ u / 12 := Nat.floor_le hdiv0
      change 12 * (⌊u / 12⌋₊ : ℝ) ≤ u
      linarith
    have hiu : u < 12 * ((i : ℝ) + 1) := by
      have hf : u / 12 < (⌊u / 12⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (u / 12)
      change u < 12 * ((⌊u / 12⌋₊ : ℝ) + 1)
      linarith
    by_cases hlow : u < 12 * (i : ℝ) + 2
    · have hg : u ∈ phaseInterval (i, (0 : Fin 2)) := by
        simpa [phaseInterval, phaseStartLeft] using (show
          12 * (i : ℝ) ≤ u ∧ u < 12 * (i : ℝ) + 2 from ⟨hil, hlow⟩)
      exact ⟨(i, 0), hg, fun h hh => phaseInterval_unique (i, 0) h u hg hh⟩
    · have hg : u ∈ phaseInterval (i, (1 : Fin 2)) := by
        have hl : 12 * (i : ℝ) + 2 ≤ u := le_of_not_gt hlow
        have hh : u < (12 * (i : ℝ) + 2) + 10 := by linarith
        simpa [phaseInterval, phaseStartLeft] using (show
          12 * (i : ℝ) + 2 ≤ u ∧ u < (12 * (i : ℝ) + 2) + 10 from ⟨hl, hh⟩)
      exact ⟨(i, 1), hg, fun h hh => phaseInterval_unique (i, 1) h u hg hh⟩

end
end AronowAudit.P027.Wave1.UniformStart
