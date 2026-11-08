import SAP.P014.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open MeasureTheory

namespace SAP.P014.WH.W1.P.T2_L2

end SAP.P014.WH.W1.P.T2_L2

theorem SAP.P014.WH.W1.T2_L2_proof : SAP.P014.WH.W1.T2_L2 := by
  classical
  intro Ω mΩ N μ hμ Z hZ f
  let ν : Measure (SAP.P014.TreatmentVector N) := μ.map Z
  have hνf : Integrable f ν := Integrable.of_finite
  have hcomp : Integrable (fun ω => f (Z ω)) μ := by
    exact (integrable_map_measure hνf.aestronglyMeasurable hZ.aemeasurable).mp hνf
  refine ⟨hcomp, ?_⟩
  calc
    (∫ ω, f (Z ω) ∂μ) = ∫ z, f z ∂ν :=
      (integral_map hZ.aemeasurable hνf.aestronglyMeasurable).symm
    _ = ∑ z : SAP.P014.TreatmentVector N,
        eventProbability μ (fun ω => Z ω = z) * f z := by
      rw [integral_fintype hνf]
      simp_rw [smul_eq_mul]
      apply Finset.sum_congr rfl
      intro z hz
      have hmass : ν.real {z} = eventProbability μ (fun ω => Z ω = z) := by
        rw [Measure.real_def, Measure.map_apply hZ (MeasurableSet.singleton z)]
        rw [SAP.P014.eventProbability]
        congr 1
      rw [hmass]
    _ = ∑ z ∈ (Finset.univ.filter (fun z : SAP.P014.TreatmentVector N =>
          0 < eventProbability μ (fun ω => Z ω = z))),
          eventProbability μ (fun ω => Z ω = z) * f z := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hp : 0 < eventProbability μ (fun ω => Z ω = z)
      · simp [hp]
      · have hnonneg : 0 ≤ eventProbability μ (fun ω => Z ω = z) := by
          unfold SAP.P014.eventProbability
          exact ENNReal.toReal_nonneg
        have hz0 : eventProbability μ (fun ω => Z ω = z) = 0 :=
          le_antisymm (le_of_not_gt hp) hnonneg
        simp [hz0]
    _ = SAP.P014.expectation (SAP.P014.assignmentLaw μ Z) f := by
      rfl
