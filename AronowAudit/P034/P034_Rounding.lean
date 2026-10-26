import Mathlib

namespace AronowAudit.P034

/-! P034-T5: exact arithmetic for Table OA3 (online Appendix p. 11).
All 39 category cells are included. Counts represent response slots, not
participants. No statistical statement about the survey is asserted. -/

/-- “N”, the three counts in each category of Table OA3, Appendix p. 11,
in printed row order; columns are no information, information, and total.
Rows 3 and 9 (zero based) are character evaluation and other policies. -/
def oa3Counts : Fin 13 → Fin 3 → ℕ := ![
  ![818, 777, 1595], ![477, 475, 952], ![281, 309, 590],
  ![266, 268, 534], ![259, 240, 499], ![258, 240, 498],
  ![224, 252, 476], ![219, 214, 433], ![49, 19, 68],
  ![24, 25, 49], ![9, 39, 48], ![9, 15, 24], ![5, 4, 9]]

/-- “Total”, the counts at the foot of Table OA3, Appendix p. 11:
`2,898 | 2,877 | 5,775`. -/
def oa3Totals : Fin 3 → ℕ := ![2898, 2877, 5775]

/-- The corrected category percentages in tenths of a percent, in the same
order as `oa3Counts`. From Table OA3, Appendix p. 11, with the two Total
cells repaired: character evaluation `9.2%`, other policies `0.8%`.
Every other cell retains its printed value. -/
def oa3Tenths : Fin 13 → Fin 3 → ℕ := ![
  ![282, 270, 276], ![165, 165, 165], ![97, 107, 102],
  ![92, 93, 92], ![89, 83, 86], ![89, 83, 86],
  ![77, 88, 82], ![76, 74, 75], ![17, 7, 12],
  ![8, 9, 8], ![3, 14, 8], ![3, 5, 4], ![2, 1, 2]]

/-- “Each percentage ... is 100 times the count ... divided by ... column
total” (P034-T5, Table OA3, p. 11). -/
def oa3Percentage (i : Fin 13) (j : Fin 3) : ℚ :=
  100 * (oa3Counts i j : ℚ) / (oa3Totals j : ℚ)

/-- “r-1/20 ≤ x < r+1/20” (P034-T5 rounding convention). The reported
value is `n/10`, so it is explicitly a one-decimal percentage. -/
def roundsToTenth (x : ℚ) (n : ℕ) : Prop :=
  (n : ℚ)/10 - 1/20 ≤ x ∧ x < (n : ℚ)/10 + 1/20

/-- P034-T5(i)-(iv): exact repaired ratios and rounding intervals, the two
printed values fail the same rule, all 39 repaired percentages round
correctly, all 13 row totals add up, and all three columns sum to their
printed totals. Table OA3, online Appendix p. 11. -/
theorem corrected_oa3_table :
    266+268 = (534 : ℕ) ∧ 24+25 = (49 : ℕ) ∧ 2898+2877 = (5775 : ℕ) ∧
    oa3Percentage 3 2 = 712/77 ∧
    (915/100 : ℚ) ≤ 712/77 ∧ (712/77 : ℚ) < 925/100 ∧
    roundsToTenth (oa3Percentage 3 2) 92 ∧
    ¬ roundsToTenth (oa3Percentage 3 2) 93 ∧
    oa3Percentage 9 2 = 28/33 ∧
    (75/100 : ℚ) ≤ 28/33 ∧ (28/33 : ℚ) < 85/100 ∧
    roundsToTenth (oa3Percentage 9 2) 8 ∧
    ¬ roundsToTenth (oa3Percentage 9 2) 9 ∧
    (∀ i j, roundsToTenth (oa3Percentage i j) (oa3Tenths i j)) ∧
    (∀ i, oa3Counts i 0 + oa3Counts i 1 = oa3Counts i 2) ∧
    (∀ j, ∑ i, oa3Counts i j = oa3Totals j) ∧
    (5775 : ℕ) = 3 * 1925 := by
  simp only [roundsToTenth]
  decide +kernel

end AronowAudit.P034

