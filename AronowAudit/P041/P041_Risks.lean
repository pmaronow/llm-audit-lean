import Mathlib.Tactic
import Mathlib.Basic.Real.Basic

noncomputable section
namespace AronowAudit.P041

/-!
P041-E001 / P041-N006: exact arithmetic behind the percentages in the abstract
(printed p. 1/8) and the citation paragraph (pp. 4/8-5/8).
The counts are inputs from the deposited data, not counts printed in the
article. No theorem here certifies the underlying data.
-/

/-- "x% more likely ... than" (abstract, p. 1/8; citation paragraph, p. 5/8),
read directionally with the comparison group as reference. The article gives
no formula; this is the reading fixed in targets P041-T3 and P041-T4. -/
def relativeIncrease (pA pB : ℝ) : ℝ := 100 * (pA / pB - 1)

/-- The deposited do-file, lines 33, 38, 43: "abs(a-b)/((a+b)/2)*100".
This symmetric percentage difference produced the printed 36, 29 and 64. -/
def symmetricDifference (a b : ℝ) : ℝ := 100 * |a - b| / ((a + b) / 2)

/-- Whole-number rounding convention in targets, standing assumption S7:
"k - 1/2 ≤ x < k + 1/2". -/
def roundsWhole (x : ℝ) (k : ℤ) : Prop := (k:ℝ) - 1 / 2 ≤ x ∧ x < (k:ℝ) + 1 / 2

/-- Target P041-T3(i)-(iii): the three relative increases are 575/13,
100/3 and 375/4; the printed integers fail to round them, while 44, 33 and
94 round them correctly. The symmetric differences round to 36, 29 and 64. -/
theorem risk_percentages_counterexample :
    relativeIncrease (75/150) (52/150) = 575/13 ∧
    relativeIncrease (92/150) (69/150) = 100/3 ∧
    relativeIncrease (62/100) (32/100) = 375/4 ∧
    (575/13 : ℝ) - 36 = 107/13 ∧ (107/13 : ℝ) > 1/2 ∧
    (100/3 : ℝ) - 29 = 13/3 ∧ (13/3 : ℝ) > 1/2 ∧
    (375/4 : ℝ) - 64 = 119/4 ∧ (119/4 : ℝ) > 1/2 ∧
    ¬ roundsWhole (relativeIncrease (75/150) (52/150)) 36 ∧
    ¬ roundsWhole (relativeIncrease (92/150) (69/150)) 29 ∧
    ¬ roundsWhole (relativeIncrease (62/100) (32/100)) 64 ∧
    roundsWhole (relativeIncrease (75/150) (52/150)) 44 ∧
    roundsWhole (relativeIncrease (92/150) (69/150)) 33 ∧
    roundsWhole (relativeIncrease (62/100) (32/100)) 94 ∧
    symmetricDifference 75 52 = 4600/127 ∧
    symmetricDifference 92 69 = 200/7 ∧
    symmetricDifference 62 32 = 3000/47 ∧
    roundsWhole (symmetricDifference 75 52) 36 ∧
    roundsWhole (symmetricDifference 92 69) 29 ∧
    roundsWhole (symmetricDifference 62 32) 64 := by
  norm_num [relativeIncrease, symmetricDifference, roundsWhole]

/-- Target P041-T3(iv): for a > b > 0, the symmetric difference understates
the directional relative increase by 100(a-b)^2/(b(a+b)), a strictly positive
quantity. -/
theorem symmetric_understates_relative (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    relativeIncrease a b - symmetricDifference a b =
      100 * (a-b)^2 / (b*(a+b)) ∧
    0 < relativeIncrease a b - symmetricDifference a b := by
  have ha : 0 < a := lt_trans hb hab
  have hs : a + b ≠ 0 := ne_of_gt (by linarith)
  have he : relativeIncrease a b - symmetricDifference a b =
      100 * (a-b)^2 / (b*(a+b)) := by
    unfold relativeIncrease symmetricDifference
    rw [abs_of_pos (sub_pos.mpr hab)]
    field_simp
    <;> ring
  refine ⟨he, ?_⟩
  rw [he]
  positivity

/-- Target P041-T3(iv): the exact gaps in the three printed comparisons. -/
theorem risk_measure_gaps :
    relativeIncrease 75 52 - symmetricDifference 75 52 = 13225/1651 ∧
    relativeIncrease 92 69 - symmetricDifference 92 69 = 100/21 ∧
    relativeIncrease 62 32 - symmetricDifference 62 32 = 5625/188 := by
  norm_num [relativeIncrease, symmetricDifference]

/-- Target P041-T4, the corrected percentages, abstract p. 1/8 and citation
paragraph p. 5/8: 44%, 33%, 94%, or 44.23%, 33.33%, 93.75%. The alternative
12-hour count of 76 is explicitly conditional on a timestamp repair; it gives
46% (46.15%). Relabelling the measure as symmetric permits the old numbers. -/
theorem corrected_risk_percentages :
    relativeIncrease (75/150) (52/150) = 575/13 ∧
    roundsWhole (relativeIncrease (75/150) (52/150)) 44 ∧
    |relativeIncrease (75/150) (52/150) - 44.23| ≤ 0.005 ∧
    relativeIncrease (92/150) (69/150) = 100/3 ∧
    roundsWhole (relativeIncrease (92/150) (69/150)) 33 ∧
    |relativeIncrease (92/150) (69/150) - 33.33| ≤ 0.005 ∧
    relativeIncrease (62/100) (32/100) = 375/4 ∧
    relativeIncrease (62/100) (32/100) = 93.75 ∧
    roundsWhole (relativeIncrease (62/100) (32/100)) 94 ∧
    relativeIncrease (76/150) (52/150) = 600/13 ∧
    roundsWhole (relativeIncrease (76/150) (52/150)) 46 ∧
    |relativeIncrease (76/150) (52/150) - 46.15| ≤ 0.005 ∧
    symmetricDifference 75 52 = 4600/127 ∧
    symmetricDifference 92 69 = 200/7 ∧
    symmetricDifference 62 32 = 3000/47 ∧
    roundsWhole (symmetricDifference 75 52) 36 ∧
    roundsWhole (symmetricDifference 92 69) 29 ∧
    roundsWhole (symmetricDifference 62 32) 64 := by
  norm_num [relativeIncrease, symmetricDifference, roundsWhole]

/-- Target P041-T12(P1),(P3), the true arithmetic and direction in the printed
abstract and citation paragraph. This does not validate their directional labels. -/
theorem printed_percentages_arithmetic_and_direction :
    symmetricDifference 75 52 = 4600/127 ∧
    symmetricDifference 92 69 = 200/7 ∧
    symmetricDifference 62 32 = 3000/47 ∧
    roundsWhole (symmetricDifference 75 52) 36 ∧
    roundsWhole (symmetricDifference 92 69) 29 ∧
    roundsWhole (symmetricDifference 62 32) 64 ∧
    (52/150 : ℝ) < 75/150 ∧ (69/150 : ℝ) < 92/150 ∧
    (32/100 : ℝ) < 62/100 := by
  norm_num [symmetricDifference, roundsWhole]

/- Target P041-T12(P2), as printed: "36% more likely ... 29% more likely"
(abstract, p. 1/8) and "64% more likely" (pp. 4/8-5/8). These percentages are
false under the directional reading, as risk_percentages_counterexample proves. -/


end AronowAudit.P041

