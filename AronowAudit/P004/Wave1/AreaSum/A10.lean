import AronowAudit.P004.Wave1.AreaSumBlueprint
import AronowAudit.P004.Wave1.AreaSum.A2
import AronowAudit.P004.Wave1.AreaSum.A3
import AronowAudit.P004.Wave1.AreaSum.A5
import AronowAudit.P004.Wave1.AreaSum.A7
import AronowAudit.P004.Wave1.AreaSum.A8

/-! Aggregate the six actual spatial integrals by the proved area-partition identity. -/

namespace AronowAudit.P004.Wave1.AreaSum

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem a10_proof : A10 := by
  intro i z
  have hunion : region areaBinaryPopulation i 6 =
      ⋃ j : Fin 6, region areaBinaryPopulation i (j : ℝ) := by
    rw [a2_proof.2 i, (a3_proof (areaBinaryCenter i)).1]
    exact Set.iUnion_congr fun j => (a2_proof.1 i j).symm
  have hdis : Pairwise (fun j k : Fin 6 =>
      Disjoint (region areaBinaryPopulation i (j : ℝ))
        (region areaBinaryPopulation i (k : ℝ))) := by
    intro j k hjk
    rw [a2_proof.1 i j, a2_proof.1 i k]
    exact (a3_proof (areaBinaryCenter i)).2 hjk
  have hmeas (j : Fin 6) : MeasurableSet (region areaBinaryPopulation i (j : ℝ)) :=
    (a7_proof.1 j i).1
  have hmass (j : Fin 6) :
      0 < volume (region areaBinaryPopulation i (j : ℝ)) ∧
        volume (region areaBinaryPopulation i (j : ℝ)) < ⊤ :=
    ⟨(a7_proof.1 j i).2.1, (a7_proof.1 j i).2.2.1⟩
  have hint (j : Fin 6) : IntegrableOn (fun x => areaBinaryPopulation.outcome x z)
      (region areaBinaryPopulation i (j : ℝ)) volume :=
    (a7_proof.1 j i).2.2.2 z
  have hpartition := AronowAudit.P004.area_partition_identity
    (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (fun j : Fin 6 => region areaBinaryPopulation i (j : ℝ))
    (fun x => areaBinaryPopulation.outcome x z) (by norm_num) hmeas hdis hmass hint
  have htotal : (∑ j : Fin 6, (volume (region areaBinaryPopulation i (j : ℝ))).toReal) =
      36 * Real.pi := by
    simp_rw [volumes a2_proof a5_proof]
    norm_num [Fin.sum_univ_succ] <;> ring
  calc
    circleAverage areaBinaryPopulation 6 i z =
        ∑ j : Fin 6, (volume (region areaBinaryPopulation i (j : ℝ))).toReal /
          (∑ k : Fin 6, (volume (region areaBinaryPopulation i (k : ℝ))).toReal) *
            circleAverage areaBinaryPopulation (j : ℝ) i z := by
      change (∫ x in region areaBinaryPopulation i 6,
        areaBinaryPopulation.outcome x z ∂volume) /
          (volume (region areaBinaryPopulation i 6)).toReal = _
      rw [hunion]
      exact hpartition
    _ = ∑ j : Fin 6, (2 * (j : ℝ) + 1) / 36 * binShare j (z i) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [htotal, volumes a2_proof a5_proof i j, a8_proof]
      field_simp [Real.pi_ne_zero] <;> ring

end
end AronowAudit.P004.Wave1.AreaSum
