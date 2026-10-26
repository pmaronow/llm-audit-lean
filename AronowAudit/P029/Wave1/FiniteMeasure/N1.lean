import AronowAudit.P029.Wave1.FiniteMeasureBlueprint

namespace AronowAudit.P029.Wave1.FiniteMeasure

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- Finite atomic laws reproduce the finite probability and expectation operations. -/
theorem n1_proof : N1 := by
  classical
  intro L _ _ _ p hp
  have hPnonneg (E : L → Prop) : 0 ≤ fP p E := by
    unfold fP
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact hp.1 i
    · exact le_rfl
  have hmass (B : Set L) :
      (atomicMeasure p) B = ENNReal.ofReal (fP p (fun i => i ∈ B)) := by
    have hB : MeasurableSet B := MeasurableSet.of_discrete
    unfold atomicMeasure
    rw [Measure.finsetSum_apply]
    calc
      (∑ i, (ENNReal.ofReal (p i) • Measure.dirac i) B) =
          ∑ i, ENNReal.ofReal (if i ∈ B then p i else 0) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' i hB]
        by_cases hi : i ∈ B <;> simp [Set.indicator, hi]
      _ = ENNReal.ofReal (fP p (fun i => i ∈ B)) := by
        unfold fP
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro i _
        split_ifs
        · exact hp.1 i
        · exact le_rfl
  have hprob : IsProbabilityMeasure (atomicMeasure p) := by
    constructor
    simpa only [fP, Set.mem_univ, if_true, hp.2, ENNReal.ofReal_one] using
      hmass (Set.univ : Set L)
  letI : IsProbabilityMeasure (atomicMeasure p) := hprob
  have hIntegral (v : L → ℝ) :
      (∫ i, v i ∂(atomicMeasure p)) = fE p v := by
    unfold atomicMeasure
    rw [integral_finsetSum_measure]
    · unfold fE
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [integral_smul_measure, integral_dirac, smul_eq_mul,
        ENNReal.toReal_ofReal (hp.1 i)]
    · intro i _
      exact (integrable_dirac (by simp)).smul_measure (by simp)
  have hMassReal (B : Set L) :
      mP (atomicMeasure p) B = fP p (fun i => i ∈ B) := by
    rw [mP, hmass B, ENNReal.toReal_ofReal (hPnonneg _)]
  refine ⟨hprob, ?_, hMassReal, ?_⟩
  · intro v
    exact ⟨Integrable.of_finite, hIntegral v⟩
  · intro v B
    have hB : MeasurableSet B := MeasurableSet.of_discrete
    unfold mCE fCE
    rw [hMassReal B,
      ← integral_indicator (μ := atomicMeasure p) (f := v) hB,
      hIntegral (B.indicator v)]
    rfl

end

end AronowAudit.P029.Wave1.FiniteMeasure
