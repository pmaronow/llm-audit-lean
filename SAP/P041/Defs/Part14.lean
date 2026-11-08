import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- Mathematical content packaged for P041-T12. -/
def T12Statement : Prop :=
  (symmetricDifference 75 52 = 4600/127 ∧
    symmetricDifference 92 69 = 200/7 ∧
    symmetricDifference 62 32 = 3000/47 ∧
    roundsWhole (symmetricDifference 75 52) 36 ∧
    roundsWhole (symmetricDifference 92 69) 29 ∧
    roundsWhole (symmetricDifference 62 32) 64 ∧
    (52/150 : ℝ) < 75/150 ∧ (69/150 : ℝ) < 92/150 ∧
    (32/100 : ℝ) < 62/100) ∧
  (¬ (roundsWhole (relativeIncrease (75/150) (52/150)) 36 ∧
    roundsWhole (relativeIncrease (92/150) (69/150)) 29 ∧
    roundsWhole (relativeIncrease (62/100) (32/100)) 64))

end SAP.P041
