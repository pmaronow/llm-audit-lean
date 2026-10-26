import AronowAudit.P004.Wave1.AreaSumBlueprint

/-! P004-T5: the finite table `areaWitnessTable` realizes exactly the
case-B shares `binShare`. -/

namespace AronowAudit.P004.Wave1.AreaSum
open AronowAudit.P004

theorem a9_proof : A9 := by
  intro j i z
  simp only [areaWitnessTable]
  generalize z i = a
  fin_cases j <;> cases a <;>
    norm_num [finiteAverage, areaWitnessMass, areaWitnessOutcome, binShare, Fin.sum_univ_succ]

end AronowAudit.P004.Wave1.AreaSum
