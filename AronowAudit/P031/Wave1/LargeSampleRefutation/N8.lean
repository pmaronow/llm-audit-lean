import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fintype.BigOperators

/-! Restriction to the first `m` coordinates has the uniform law on
`Fin m → Fin 2`. The equality of the finite product and uniform laws is
checked on singletons; it includes `m = 0`. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n8_proof : N8 := by
  intro m x
  let μ₂ : Measure (Fin 2) := (PMF.uniformOfFintype (Fin 2)).toMeasure
  let R : (ℕ → Fin 2) → (Fin m → Fin 2) := fun ω j => ω j.val
  let A : Set (Fin m → Fin 2) :=
    {v | (Real.sqrt m)⁻¹ * ∑ j, sgn2 (v j) ≤ x}
  have hR : Measurable R := by
    dsimp only [R]
    fun_prop
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have hRlaw : coinMeasure.map R = Measure.pi (fun _ : Fin m => μ₂) := by
    change (Measure.infinitePi (fun _ : ℕ => μ₂)).map R = _
    simpa only [R, Measure.infinitePi_eq_pi] using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : ℕ => μ₂) (f := fun j : Fin m => j.val) Fin.val_injective)
  have hμ₂ (d : Fin 2) : μ₂ {d} = (2 : ENNReal)⁻¹ := by
    dsimp only [μ₂]
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    norm_num only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  have hfinite : Measure.pi (fun _ : Fin m => μ₂) =
      (PMF.uniformOfFintype (Fin m → Fin 2)).toMeasure := by
    apply Measure.ext_of_singleton
    intro v
    rw [Measure.pi_singleton,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [hμ₂, PMF.uniformOfFintype_apply, ENNReal.inv_pow]

  have hsum (ω : ℕ → Fin 2) :
      (∑ j : Fin m, sgn2 (R ω j)) = ∑ j ∈ Finset.range m, sgn2 (ω j) := by
    exact Fin.sum_univ_eq_sum_range (fun j => sgn2 (ω j)) m
  have hevent :
      {ω : ℕ → Fin 2 |
        (Real.sqrt m)⁻¹ * ∑ j ∈ Finset.range m, sgn2 (ω j) ≤ x} = R ⁻¹' A := by
    ext ω
    change ((Real.sqrt m)⁻¹ * ∑ j ∈ Finset.range m, sgn2 (ω j) ≤ x) ↔
      ((Real.sqrt m)⁻¹ * ∑ j : Fin m, sgn2 (R ω j) ≤ x)
    rw [hsum]
  change (coinMeasure
    {ω : ℕ → Fin 2 |
      (Real.sqrt m)⁻¹ * ∑ j ∈ Finset.range m, sgn2 (ω j) ≤ x}).toReal = _
  rw [hevent, ← Measure.map_apply hR hA, hRlaw, hfinite,
    PMF.toMeasure_uniformOfFintype_apply A hA]
  simp only [A, Fintype.card_subtype, Fintype.card_fun, Fintype.card_fin,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, Set.mem_ofPred_eq, Nat.cast_pow, Nat.cast_ofNat]

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
