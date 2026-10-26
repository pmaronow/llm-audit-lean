import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint

/-!
# P002-T27: main p. 14 Lemma 1 for the paper's AR functions

The coefficient-level Lemma 1 assumes that one common observed dataset generates the
observed and simulated AR coefficients (`DataGeneratedCoefficients`), Assumptions 6/7
hold for all of them (`ARRegular`), and no two globally distinct simulated AR functions
meet in the open interval. All four printed conclusions are included, including both
one-sided unbounded intervals.

The coefficient objects supply continuity and nonnegativity.
-/

namespace AronowAudit.P002.Wave1.QuantileIndexInterval
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Lemma 1 for the data-generated AR coefficients. -/
def Target : Prop :=
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → DataGeneratedCoefficients Qf Qg →
    ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    ∀ (l u : EReal), l < u →
    (∀ β ∈ openInterval l u, ¬ crossing (fun m => arFunction (Qg m)) β) →
    let g := fun m => arFunction (Qg m)
    (∀ x ∈ openInterval l u, ∀ y ∈ openInterval l u,
      mcIndices g α x = mcIndices g α y) ∧
    (∀ x ∈ openInterval l u, ∀ a b : ℝ,
      l = (a : EReal) → u = (b : EReal) →
      mcIndices g α x ⊆ mcIndices g α a ∧
      mcIndices g α x ⊆ mcIndices g α b) ∧
    (∀ x ∈ openInterval l u, ∀ b : ℝ, l = ⊥ → u = (b : EReal) →
      mcIndices g α x ⊆ mcIndices g α b) ∧
    (∀ x ∈ openInterval l u, ∀ a : ℝ, u = ⊤ → l = (a : EReal) →
      mcIndices g α x ⊆ mcIndices g α a)

/-- Continuity of the critical value, single-curve interior constancy and closure
extension imply the interval conclusions. -/
theorem assemble (h2 : AlgorithmSupport.N2) (h3 : AlgorithmSupport.N3)
    (h4 : AlgorithmSupport.N4) : Target := by
  intro M Qf Qg α hM hα _hdata _hQf hQg l u hlu hcross
  have hreg := arFamily_regular Qg hQg
  set g : Fin M → ℝ → ℝ := fun m => arFunction (Qg m) with hg
  have hc : ∀ s, Continuous (g s) := hreg.1
  have hn : ∀ s β, 0 ≤ g s β := hreg.2.1
  -- every index valid at an interior point is valid on the whole open interval
  have hint : ∀ x ∈ openInterval l u, ∀ m ∈ mcIndices g α x,
      ∀ y ∈ openInterval l u, m ∈ mcIndices g α y := by
    intro x hx m hm
    refine h3 M g α m l u x hM hα hc hn hx ?_ hm
    intro s hs β hβ heq
    exact hcross β hβ ⟨s, m, hs, heq⟩
  -- and on the whole closed interval
  have hcl : ∀ x ∈ openInterval l u, ∀ m ∈ mcIndices g α x,
      ∀ β ∈ closedInterval l u, m ∈ mcIndices g α β := by
    intro x hx m hm
    exact h4 M g α m l u hc (h2 M g α hM hα hc) hlu (hint x hx m hm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    ext m
    exact ⟨fun hm => hint x hx m hm y hy, fun hm => hint y hy m hm x hx⟩
  · intro x hx a b hl hu
    constructor
    · intro m hm
      exact hcl x hx m hm a ⟨le_of_eq hl, hl ▸ hlu.le⟩
    · intro m hm
      exact hcl x hx m hm b ⟨hu ▸ hlu.le, le_of_eq hu.symm⟩
  · intro x hx b _ hu m hm
    exact hcl x hx m hm b ⟨hu ▸ hlu.le, le_of_eq hu.symm⟩
  · intro x hx a _ hl m hm
    exact hcl x hx m hm a ⟨le_of_eq hl, hl ▸ hlu.le⟩

end
end AronowAudit.P002.Wave1.QuantileIndexInterval
