import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- Mathematical content packaged for P041-T4. -/
def T4Statement : Prop :=
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
    roundsWhole (symmetricDifference 62 32) 64

end SAP.P041
