import AronowAudit.P029.Wave1.FiniteMeasureBlueprint

namespace AronowAudit.P029.Wave1.FiniteMeasure

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- Normalizing a positive-mass restriction gives exactly the conditional atomic law. -/
theorem n4_proof : N4 := by
  classical
  intro L Y _ _ _ p hp X x hx
  have hvalid : ValidLaw (condLaw p X x) := by
    constructor
    · intro i
      unfold condLaw
      split_ifs
      · exact div_nonneg (hp.1 i) hx.le
      · exact le_rfl
    · calc
        (∑ i, condLaw p X x i) =
            ∑ i, (if X i = x then p i else 0) / fP p (fun j => X j = x) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          by_cases hi : X i = x <;> simp [condLaw, hi]
        _ = fP p (fun i => X i = x) / fP p (fun i => X i = x) := by
          exact (Finset.sum_div Finset.univ (fun i => if X i = x then p i else 0)
            (fP p (fun i => X i = x))).symm
        _ = 1 := div_self (ne_of_gt hx)
  have hsingle (q : L → ℝ) (i : L) :
      (atomicMeasure q) {i} = ENNReal.ofReal (q i) := by
    unfold atomicMeasure
    rw [Measure.finsetSum_apply]
    calc
      (∑ j, (ENNReal.ofReal (q j) • Measure.dirac j) {i}) =
          ∑ j, if j = i then ENNReal.ofReal (q j) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply' j (measurableSet_singleton i)]
        by_cases hji : j = i <;> simp [Set.indicator, hji]
      _ = ENNReal.ofReal (q i) := by simp
  refine ⟨hvalid, ?_⟩
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (measurableSet_singleton i)]
  by_cases hi : X i = x
  · have hinter : ({i} ∩ {j | X j = x} : Set L) = {i} := by
      ext j
      by_cases hji : j = i <;> simp [hji, hi]
    rw [hinter, hsingle p i, hsingle (condLaw p X x) i]
    change ENNReal.ofReal ((fP p (fun j => X j = x))⁻¹) * ENNReal.ofReal (p i) =
      ENNReal.ofReal (if X i = x then p i / fP p (fun j => X j = x) else 0)
    rw [if_pos hi, ← ENNReal.ofReal_mul (inv_nonneg.mpr hx.le)]
    congr 1
    exact (div_eq_inv_mul _ _).symm
  · have hinter : ({i} ∩ {j | X j = x} : Set L) = ∅ := by
      ext j
      by_cases hji : j = i <;> simp [hji, hi]
    rw [hinter, measure_empty, mul_zero, hsingle (condLaw p X x) i]
    simp only [condLaw, if_neg hi, ENNReal.ofReal_zero]

end

end AronowAudit.P029.Wave1.FiniteMeasure
