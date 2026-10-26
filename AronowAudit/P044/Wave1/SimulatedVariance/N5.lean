import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- Identify the design support and push each exposure indicator through the design. -/
theorem n5_proof : N5 := by
  classical
  intro h1 h2 h4
  change Function.Injective cliqueAssignments at h1
  change (∀ (i : Fin 12) (a : Exposure),
    exposureCount cliqueF i a = cliqueFullCount a) at h2
  rcases h4 with ⟨_hnonneg, _htotal, havg⟩
  have hmass (t : Fin 66) : cliqueMass (cliqueAssignments t) = (1 / 66 : ℝ) := by
    unfold cliqueMass
    simp only [h1.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hzero (z : Assignment 12) (hz : z ∉ Set.range cliqueAssignments) :
      cliqueMass z = 0 := by
    unfold cliqueMass
    apply Finset.sum_eq_zero
    intro r _
    have hne : cliqueAssignments r ≠ z := by
      intro hr
      exact hz ⟨r, hr⟩
    exact if_neg hne
  have hpos (z : Assignment 12) :
      0 < cliqueMass z ↔ z ∈ Set.range cliqueAssignments := by
    constructor
    · intro hz
      by_contra hout
      rw [hzero z hout] at hz
      exact (lt_irrefl (0 : ℝ)) hz
    · rintro ⟨r, rfl⟩
      rw [hmass]
      norm_num
  have hsupport :
      Finset.univ.filter (fun z => 0 < cliqueMass z) =
        Finset.univ.image cliqueAssignments := by
    ext z
    simp [hpos, Set.mem_range]
  have hf (r : Fin 66) (i : Fin 12) :
      exposure cliqueAdj (cliqueAssignments r) i = cliqueF r i :=
    (congrFun (congrFun cliqueF_is_exposure r) i).symm
  have hmarginal (i : Fin 12) (a : Exposure) :
      marginal cliqueMass (fun z => exposure cliqueAdj z) i a =
        (exposureCount cliqueF i a : ℝ) / 66 := by
    calc
      marginal cliqueMass (fun z => exposure cliqueAdj z) i a =
          ∑ z, cliqueMass z *
            (if exposure cliqueAdj z i = a then (1 : ℝ) else 0) := by
        unfold marginal
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> simp
      _ = (∑ r : Fin 66,
          if exposure cliqueAdj (cliqueAssignments r) i = a then (1 : ℝ) else 0) / 66 :=
        havg (fun z => if exposure cliqueAdj z i = a then (1 : ℝ) else 0)
      _ = (exposureCount cliqueF i a : ℝ) / 66 := by
        simp_rw [hf]
        simp only [exposureCount, ← Finset.sum_filter, Finset.sum_const,
          nsmul_eq_mul, mul_one]
  change SupportMarginals
  constructor
  · calc
      (Finset.univ.filter (fun z => 0 < cliqueMass z)).card =
          (Finset.univ.image cliqueAssignments).card := congrArg Finset.card hsupport
      _ = (Finset.univ : Finset (Fin 66)).card :=
        Finset.card_image_of_injective _ h1
      _ = 66 := by simp only [Finset.card_univ, Fintype.card_fin]
  · intro i
    constructor
    · rw [hmarginal, h2 i .d01]
      norm_num [cliqueFullCount]
    · rw [hmarginal, h2 i .d00]
      norm_num [cliqueFullCount]

end

end AronowAudit.P044.Wave1.SimulatedVariance
