import AronowAudit.P001.Wave1.CompleteDescriptionBlueprint

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.CompleteDescription

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n2_proof : N2 := by
  classical
  -- Expand the four-atom measure before taking real parts. All arithmetic here is
  -- in ENNReal until the final simplification of toReal.
  have happly (S : Set (Fin 4)) :
      electorateLaw S =
        ENNReal.ofReal (3/8 : ℝ) * (if (0 : Fin 4) ∈ S then 1 else 0) +
        ENNReal.ofReal (1/8 : ℝ) * (if (1 : Fin 4) ∈ S then 1 else 0) +
        ENNReal.ofReal (1/8 : ℝ) * (if (2 : Fin 4) ∈ S then 1 else 0) +
        ENNReal.ofReal (3/8 : ℝ) * (if (3 : Fin 4) ∈ S then 1 else 0) := by
    simp [electorateLaw, finiteLawMeasure, Fin.sum_univ_succ,
      Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
      Set.indicator, binaryJoint, add_assoc]
  refine ⟨⟨?_⟩, ?_, ?_, ?_⟩
  · rw [happly]
    norm_num
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  · rw [happly]
    norm_num [potentialPair, voteRule, electorateU, electorateD]
  · rw [happly]
    norm_num [potentialPair, voteRule, electorateU, electorateD]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  · rw [happly]
    norm_num [electorateD]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
    norm_num

end

end AronowAudit.P001.Wave1.CompleteDescription
