import AronowAudit.P029.Wave1.FiniteMeasureBlueprint

namespace AronowAudit.P029.Wave1.FiniteMeasure

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- The finite IV assumptions transfer with every measurability and integrability conjunct. -/
theorem n3_proof : N3 := by
  classical
  intro hN1 hN2 L X _ _ _ _ _ p U Z hIV
  rcases hIV with ⟨hp, hZ0, hZ1, hIndep, hDefier, hFirst⟩
  obtain ⟨hprob, hIntegral, hP, hCE⟩ := hN1 p hp
  letI : IsProbabilityMeasure (atomicMeasure p) := hprob
  have hIndep' :
      IndepFun Z (fun i => ((U i).x, (U i).d0, (U i).d1, (U i).y0, (U i).y1))
        (atomicMeasure p) := by
    exact (hN2 p hp
      (fun i => ((U i).x, (U i).d0, (U i).d1, (U i).y0, (U i).y1)) Z hIndep).symm
  have hZmass : mP (atomicMeasure p) {i | Z i = true} =
      fP p (fun i => Z i = true) := by
    simpa only [Set.mem_setOf_eq] using hP {i | Z i = true}
  have hDefierReal : mP (atomicMeasure p) {i | (U i).defier} = 0 := by
    rw [hP]
    simpa only [Set.mem_setOf_eq] using hDefier
  have hDefierMass : (atomicMeasure p) {i | (U i).defier} = 0 := by
    calc
      (atomicMeasure p) {i | (U i).defier} =
          ENNReal.ofReal (mP (atomicMeasure p) {i | (U i).defier}) := by
        symm
        exact ENNReal.ofReal_toReal (measure_ne_top _ _)
      _ = 0 := by rw [hDefierReal, ENNReal.ofReal_zero]
  unfold IVAssumptions
  refine ⟨Measurable.of_discrete, Measurable.of_discrete, Measurable.of_discrete,
    Measurable.of_discrete, Measurable.of_discrete, Measurable.of_discrete,
    (hIntegral (fun i => (U i).y0)).1, (hIntegral (fun i => (U i).y1)).1,
    hIndep', ?_, ?_, hDefierMass, ?_⟩
  · rw [hZmass]
    exact hZ0
  · rw [hZmass]
    exact hZ1
  · simpa only [hCE, Set.mem_setOf_eq] using hFirst

end

end AronowAudit.P029.Wave1.FiniteMeasure
