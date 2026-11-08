import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- Mathematical content packaged for P041-T3. -/
def T3Statement : Prop :=
  (relativeIncrease (75/150) (52/150) = 575/13 ∧
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
    roundsWhole (symmetricDifference 62 32) 64) ∧
  (∀ (a b : ℝ) (hb : 0 < b) (hab : b < a),
    relativeIncrease a b - symmetricDifference a b =
      100 * (a-b)^2 / (b*(a+b)) ∧
    0 < relativeIncrease a b - symmetricDifference a b) ∧
  (relativeIncrease 75 52 - symmetricDifference 75 52 = 13225/1651 ∧
    relativeIncrease 92 69 - symmetricDifference 92 69 = 100/21 ∧
    relativeIncrease 62 32 - symmetricDifference 62 32 = 5625/188)

end SAP.P041
