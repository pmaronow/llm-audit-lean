import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P038

/-- The `m` Tuesdays on either side of election day, excluding week zero. -/
def referenceWeeks (m : ℕ) : Finset ℤ :=
  (Finset.Icc (-(m : ℤ)) (m : ℤ)).erase 0

/-- Strictly outside the dashed lines at the election-day RR and its reciprocal. -/
def moreExtreme (electionRR referenceRR : ℝ) : Prop :=
  referenceRR < min electionRR (1 / electionRR) ∨
    max electionRR (1 / electionRR) < referenceRR

/-- Reference weeks whose RRs satisfy the caption's strict outside rule. -/
noncomputable def tailWeeks (R : ℝ) (r : ℤ → ℝ) (m : ℕ) : Finset ℤ := by
  classical
  exact (referenceWeeks m).filter (fun w => moreExtreme R (r w))

/-- The number of outside reference points in the window. -/
noncomputable def tailCount (R : ℝ) (r : ℤ → ℝ) (m : ℕ) : ℕ :=
  (tailWeeks R r m).card

/-- The proportion of the `2m` reference points outside the dashed lines.
The statement uses this quantity only at the positive windows 12 and 25. -/
noncomputable def empiricalP (R : ℝ) (r : ℤ → ℝ) (m : ℕ) : ℝ :=
  (tailCount R r m : ℝ) / (2 * (m : ℝ))

/-- The target's two-decimal rounding bin, closed below and open above. -/
def roundsTo (x v : ℝ) : Prop := v - 1 / 200 ≤ x ∧ x < v + 1 / 200

/-- The alternative convention that counts election day as one extra tail point. -/
noncomputable def electionDayAdjustedP (R : ℝ) (r : ℤ → ℝ) (m : ℕ) : ℝ :=
  ((tailCount R r m + 1 : ℕ) : ℝ) / (2 * (m : ℝ) + 1)

/-- P038-T1: all four mathematical clauses of the corrected footnote-2 claim.
The tail count and the particular figure-tail set remain hypotheses. -/
def T1Statement : Prop :=
  (∀ (R : ℝ) (r : ℤ → ℝ), 0 < R →
    (∀ w ∈ referenceWeeks 25, 0 < r w) → tailCount R r 25 = 2 →
    empiricalP R r 25 = 2 / 50 ∧
    empiricalP R r 25 = 1 / 25 ∧
    empiricalP R r 25 = 4 / 100 ∧
    6 / 100 - empiricalP R r 25 = 1 / 50) ∧
  (∀ k : ℤ, 0 ≤ k → k ≤ 50 →
    ((k : ℝ) / 50 = 6 / 100 ↔ k = 3) ∧
    (roundsTo ((k : ℝ) / 50) (6 / 100) ↔ k = 3) ∧
    (roundsTo ((k : ℝ) / 50) (4 / 100) ↔ k = 2) ∧
    ((k : ℝ) / 50 = 4 / 100 ↔ k = 2)) ∧
  (∀ (R : ℝ) (r : ℤ → ℝ), 0 < R →
    (∀ w ∈ referenceWeeks 100, 0 < r w) →
    (empiricalP R r 25 = 6 / 100 ↔ tailCount R r 25 = 3) ∧
    (roundsTo (empiricalP R r 25) (6 / 100) ↔ tailCount R r 25 = 3) ∧
    (roundsTo (empiricalP R r 25) (4 / 100) ↔ tailCount R r 25 = 2) ∧
    (empiricalP R r 25 = 4 / 100 ↔ tailCount R r 25 = 2) ∧
    (∀ m n : ℕ, 1 ≤ m → m ≤ n → n ≤ 100 →
      tailCount R r m ≤ tailCount R r n) ∧
    (tailWeeks R r 25 = {-14, 7} →
      tailCount R r 12 = 1 ∧ tailCount R r 25 = 2 ∧
      empiricalP R r 12 = 1 / 24 ∧
      (35 / 1000 : ℝ) ≤ empiricalP R r 12 ∧
      empiricalP R r 12 < 45 / 1000 ∧
      roundsTo (empiricalP R r 12) (4 / 100) ∧
      empiricalP R r 25 = 4 / 100 ∧
      ¬ roundsTo (empiricalP R r 25) (6 / 100) ∧
      electionDayAdjustedP R r 25 = 3 / 51 ∧
      electionDayAdjustedP R r 25 = 1 / 17 ∧
      (55 / 1000 : ℝ) ≤ electionDayAdjustedP R r 25 ∧
      electionDayAdjustedP R r 25 < 65 / 1000 ∧
      roundsTo (electionDayAdjustedP R r 25) (6 / 100) ∧
      electionDayAdjustedP R r 12 = 2 / 25 ∧
      electionDayAdjustedP R r 12 = 8 / 100 ∧
      ¬ roundsTo (electionDayAdjustedP R r 12) (4 / 100) ∧
      ¬ (roundsTo (empiricalP R r 12) (4 / 100) ∧
          roundsTo (empiricalP R r 25) (6 / 100)) ∧
      ¬ (roundsTo (electionDayAdjustedP R r 12) (4 / 100) ∧
          roundsTo (electionDayAdjustedP R r 25) (6 / 100))))

end SAP.P038
