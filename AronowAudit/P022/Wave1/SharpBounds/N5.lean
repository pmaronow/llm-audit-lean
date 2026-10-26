import AronowAudit.P022.Wave1.SharpBoundsBlueprint
import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem integral_unitLaw {N : ℕ} [NeZero N] (f : Fin N → ℝ) :
    (∫ i, f i ∂(unitLaw N : Measure (Fin N))) = finiteMean f := by
  simp [unitLaw, PMF.integral_eq_sum, PMF.uniformOfFintype_apply, finiteMean,
    Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm, ← Finset.sum_mul]

local instance instDecidableN5 (p : Prop) : Decidable p := Classical.propDecidable p

theorem measure_unitLaw {N : ℕ} [NeZero N] (s : Set (Fin N)) :
    ((unitLaw N : Measure (Fin N)) s).toReal =
      finiteMean (fun i => if i ∈ s then (1 : ℝ) else 0) := by
  classical
  change (unitLaw N : Measure (Fin N)).real s = _
  rw [← integral_indicator_one ((Set.toFinite s).measurableSet), integral_unitLaw]
  apply Finset.expect_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [Set.indicator_apply, hi]

theorem integral_pairLaw {N : ℕ} [NeZero N] (z1 z0 : Fin N → ℝ)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g) :
    (∫ p, g p ∂(pairLaw z1 z0 : Measure (ℝ × ℝ))) =
      finiteMean (fun i => g (z1 i, z0 i)) := by
  rw [pairLaw, ProbabilityMeasure.toMeasure_map,
    integral_map_of_stronglyMeasurable (measurable_of_finite _) hg.stronglyMeasurable,
    integral_unitLaw]

theorem measure_pairLaw {N : ℕ} [NeZero N] (z1 z0 : Fin N → ℝ)
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
    ((pairLaw z1 z0 : Measure (ℝ × ℝ)) s).toReal =
      finiteMean (fun i => if (z1 i, z0 i) ∈ s then (1 : ℝ) else 0) := by
  rw [pairLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_of_finite _) hs, measure_unitLaw]
  apply Finset.expect_congr rfl
  intro i _
  by_cases hi : (z1 i, z0 i) ∈ s <;> simp [Set.mem_preimage, hi]

theorem n5_proof : N5 := by
  intro N _ z1 z0
  refine ⟨integral_pairLaw z1 z0, ?_, ?_, ?_⟩
  · intro x
    constructor
    · simpa [lawCDF, empiricalCDF] using measure_pairLaw z1 z0 {p | p.1 ≤ x}
        (measurableSet_le measurable_fst measurable_const)
    · simpa [lawCDF, empiricalCDF] using measure_pairLaw z1 z0 {p | p.2 ≤ x}
        (measurableSet_le measurable_snd measurable_const)
  · intro c e
    have ht := measure_pairLaw z1 z0 {p | c ≤ p.1 ∧ e ≤ p.2}
      ((measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_const measurable_snd))
    refine ht.trans ?_
    apply Finset.expect_congr rfl
    intro i _
    by_cases hi : c ≤ z1 i ∧ e ≤ z0 i <;> simp [hi]
  · have h1 : lawMean (pairLaw z1 z0) true = finiteMean z1 := by
      simpa [lawMean] using integral_pairLaw z1 z0 Prod.fst measurable_fst
    have h0 : lawMean (pairLaw z1 z0) false = finiteMean z0 := by
      simpa [lawMean] using integral_pairLaw z1 z0 Prod.snd measurable_snd
    unfold lawCovariance
    rw [h1, h0]
    exact integral_pairLaw z1 z0 _ ((measurable_fst.sub_const _).mul (measurable_snd.sub_const _))

end
end AronowAudit.P022.Wave1.SharpBounds
