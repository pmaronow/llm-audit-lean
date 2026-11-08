import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022
open scoped BigOperators

/-- Closed three-decimal display bins, including both possible ties. -/
def DisplaysAs (value printed : ℝ) : Prop :=
  value ∈ Set.Icc (printed - (1 / 2000 : ℝ)) (printed + (1 / 2000 : ℝ))

/-- All three parts of the corrected Table 1 calculation (p. 857). -/
def T11Statement : Prop :=
  (∀ Va VH z L U LH UH : ℝ,
    0 < Va → 0 < VH → 0 < z →
    DisplaysAs L (-1555 / 1000) → DisplaysAs U (192 / 1000) →
    DisplaysAs LH (-1528 / 1000) → DisplaysAs UH (165 / 1000) →
    (U - L) / 2 = z * Real.sqrt Va →
    (UH - LH) / 2 = z * Real.sqrt VH →
    ((873 / 1000 : ℝ) ≤ (U - L) / 2 ∧ (U - L) / 2 ≤ 874 / 1000 ∧
     (846 / 1000 : ℝ) ≤ (UH - LH) / 2 ∧ (UH - LH) / 2 ≤ 847 / 1000 ∧
     100 * (1 - VH / Va) ≤ 100 * (1 - (423 / 437 : ℝ) ^ 2) ∧
     100 * (1 - (423 / 437 : ℝ) ^ 2) = 1204000 / 190969 ∧
     100 * (1 - VH / Va) < 13 / 2) ∧
    (DisplaysAs Va (199 / 1000) → DisplaysAs VH (186 / 1000) →
      (2400 / 397 : ℝ) ≤ 100 * (1 - VH / Va) ∧
      100 * (1 - VH / Va) ≤ 1204000 / 190969 ∧
      (11 / 2 : ℝ) < 100 * (1 - VH / Va) ∧
      100 * (1 - VH / Va) < 13 / 2)) ∧
  (100 * (1 - (186 / 1000 : ℝ) / (199 / 1000)) = (1300 / 199 : ℝ))

noncomputable def halfWidth (L U : ℝ) : ℝ := (U - L) / 2

noncomputable def reductionPercent (Va VH : ℝ) : ℝ := 100 * (1 - VH / Va)

end SAP.P022
