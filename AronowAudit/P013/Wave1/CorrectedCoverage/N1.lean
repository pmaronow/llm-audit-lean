import AronowAudit.P013.Wave1.CorrectedCoverageBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.CorrectedCoverage

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- The finite atomic design law has total mass one and the prescribed event masses. -/
theorem n1_proof : N1 := by
  classical
  intro Ω _ _ _ P
  have hmass (A : Ω → Prop) :
      designMeasure P {z | A z} =
        ∑ z, if A z then ENNReal.ofReal (P.weight z) else 0 := by
    unfold designMeasure
    rw [MeasureTheory.Measure.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro z _
    rw [MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.dirac_apply' z ((Set.toFinite {z | A z}).measurableSet)]
    by_cases hz : A z <;> simp [Set.indicator, smul_eq_mul, hz]
  have htotal : designMeasure P Set.univ = 1 := by
    calc
      designMeasure P Set.univ = ∑ z, ENNReal.ofReal (P.weight z) := by
        simpa using hmass (fun _ => True)
      _ = ENNReal.ofReal (∑ z, P.weight z) :=
        (ENNReal.ofReal_sum_of_nonneg (fun z _ => (P.positive z).le)).symm
      _ = 1 := by rw [P.total]; norm_num
  refine ⟨⟨htotal⟩, ?_⟩
  intro A
  have hfinite : ∀ z ∈ (Finset.univ : Finset Ω),
      (if A z then ENNReal.ofReal (P.weight z) else 0) ≠ ⊤ := by
    intro z _
    by_cases hz : A z <;> simp [hz]
  change (designMeasure P {z | A z}).toReal = probability P A
  rw [hmass A, ENNReal.toReal_sum hfinite]
  unfold probability
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : A z <;> simp [hz, ENNReal.toReal_ofReal (P.positive z).le]

end

end AronowAudit.P013.Wave1.CorrectedCoverage
