import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

/-- Quarterly growth is indexed by quarter number; only quarters 1 through 16 are used. -/
abbrev QuarterGrowth := ℕ → ℝ

noncomputable def incomeNumerator (decay : ℝ) (h : QuarterGrowth) : ℝ :=
  (1 / 3 : ℝ) * h 16 + ∑ k ∈ Finset.range 14, decay ^ (k + 1) * h (15 - k)

noncomputable def incomeDenominator (decay : ℝ) : ℝ :=
  (1 / 3 : ℝ) + ∑ k ∈ Finset.range 14, decay ^ (k + 1)

noncomputable def incomeGrowth (decay : ℝ) (h : QuarterGrowth) : ℝ :=
  incomeNumerator decay h / incomeDenominator decay

noncomputable def describedNumerator (decay : ℝ) (h : QuarterGrowth) : ℝ :=
  (1 / 3 : ℝ) * h 16 + ∑ k ∈ Finset.range 15, decay ^ (k + 1) * h (15 - k)

noncomputable def describedDenominator (decay : ℝ) : ℝ :=
  (1 / 3 : ℝ) + ∑ k ∈ Finset.range 15, decay ^ (k + 1)

noncomputable def describedGrowth (decay : ℝ) (h : QuarterGrowth) : ℝ :=
  describedNumerator decay h / describedDenominator decay

noncomputable def firstQuarterOnly : QuarterGrowth := fun q => if q = 1 then 1 else 0

/-- The sixteen-quarter description differs from the implemented predictor, with both exact witnesses. -/
def T1Statement : Prop :=
  (∀ decay : ℝ, 0 ≤ decay →
    0 < incomeDenominator decay ∧ 0 < describedDenominator decay ∧
    (∀ h h' : QuarterGrowth,
      (∀ q, 2 ≤ q → q ≤ 16 → h q = h' q) →
      incomeNumerator decay h = incomeNumerator decay h' ∧
      incomeGrowth decay h = incomeGrowth decay h') ∧
    (∀ h : QuarterGrowth,
      describedNumerator decay h - incomeNumerator decay h = decay^15 * h 1) ∧
    describedDenominator decay - incomeDenominator decay = decay^15) ∧
  (0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧
    firstQuarterOnly 1 = 1 ∧ (∀ q, 2 ≤ q → q ≤ 16 → firstQuarterOnly q = 0) ∧
    incomeNumerator (1 / 2) firstQuarterOnly = 0 ∧
    incomeGrowth (1 / 2) firstQuarterOnly = 0 ∧
    describedNumerator (1 / 2) firstQuarterOnly = (1 / 32768 : ℝ) ∧
    describedDenominator (1 / 2) = (131069 / 98304 : ℝ) ∧
    describedGrowth (1 / 2) firstQuarterOnly = (3 / 131069 : ℝ) ∧
    0 < describedGrowth (1 / 2) firstQuarterOnly ∧
    describedGrowth (1 / 2) firstQuarterOnly ≠ incomeGrowth (1 / 2) firstQuarterOnly) ∧
  (0 < (9 / 10 : ℝ) ∧ (9 / 10 : ℝ) < 1 ∧
    incomeNumerator (9 / 10) firstQuarterOnly = 0 ∧
    incomeGrowth (9 / 10) firstQuarterOnly = 0 ∧
    describedNumerator (9 / 10) firstQuarterOnly = (205891132094649 / 10 ^ 15 : ℝ) ∧
    describedDenominator (9 / 10) = (22440939433444477 / (3 * 10 ^ 15) : ℝ) ∧
    describedGrowth (9 / 10) firstQuarterOnly = (617673396283947 / 22440939433444477 : ℝ) ∧
    0 < describedGrowth (9 / 10) firstQuarterOnly ∧
    describedGrowth (9 / 10) firstQuarterOnly ≠ incomeGrowth (9 / 10) firstQuarterOnly) ∧
  ((1/2 : ℝ)^15 = 1/32768 ∧
    (1/3 : ℝ) + 32767/32768 = 131069/98304 ∧
    (9/10 : ℝ)^15 = 205891132094649/10^15)

/-- The corrected Q2--16 predictor, its relation to Q1--16, and both endpoint cases.
The earlier-quarter sum is written in reverse order: q = 15-k, for 0 ≤ k < 14. -/
def T2Statement : Prop :=
  (∀ (decay : ℝ) (h : QuarterGrowth), 0 ≤ decay →
    (1/3 : ℝ) ≤ incomeDenominator decay ∧
    0 < incomeDenominator decay ∧ 0 < describedDenominator decay ∧
    (∀ h' : QuarterGrowth,
      (∀ q, 2 ≤ q → q ≤ 16 → h q = h' q) →
      incomeNumerator decay h = incomeNumerator decay h' ∧
      incomeGrowth decay h = incomeGrowth decay h') ∧
    describedNumerator decay h = incomeNumerator decay h + decay^15 * h 1 ∧
    describedDenominator decay = incomeDenominator decay + decay^15 ∧
    describedGrowth decay h - incomeGrowth decay h =
      decay^15 * (h 1 - incomeGrowth decay h) / describedDenominator decay ∧
    (describedGrowth decay h = incomeGrowth decay h ↔
      decay = 0 ∨ h 1 = incomeGrowth decay h)) ∧
  (∀ h : QuarterGrowth,
    incomeDenominator 0 = (1 / 3 : ℝ) ∧ incomeGrowth 0 h = h 16 ∧
    incomeDenominator 1 = (43 / 3 : ℝ) ∧
    incomeGrowth 1 h = (3 / 43 : ℝ) *
      ((1 / 3 : ℝ) * h 16 + ∑ k ∈ Finset.range 14, h (15 - k)) ∧
    (0 : ℝ) ^ 0 = 1 ∧ (∀ k : ℕ, (1 : ℝ) ^ k = 1) ∧
    (∀ k : ℕ, 1 ≤ k → (0 : ℝ) ^ k = 0))

end SAP.P039
