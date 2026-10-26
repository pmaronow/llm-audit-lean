import AronowAudit.P027.Wave1.UniformStartBlueprint
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! A finite step function on a conull partition, with no measurability
assumption on its values outside that partition. -/

namespace AronowAudit.P027.Wave1.UniformStart

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n5_proof : N5 := by
  intro X ι _ _ ν _ S hS I hI _hsub hpart f c hconst
  let φ : ι → X → ℝ := fun i => (I i).indicator (fun _ => c i)
  let p : X → ℝ := fun u => ∑ i, φ i u
  have hφ : ∀ i, Integrable (φ i) ν := by
    intro i
    exact (integrable_const (c i)).indicator (hI i)
  have hp : Integrable p ν := by
    exact integrable_finsetSum Finset.univ (fun i _ => hφ i)
  have haeS : ∀ᵐ u ∂ν, u ∈ S := mem_ae_iff.mpr hS
  have hfp : f =ᵐ[ν] p := by
    filter_upwards [haeS] with u hu
    obtain ⟨i, hi, huniq⟩ := hpart u hu
    have hsingle : p u = φ i u := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        have hjnot : u ∉ I j := by
          intro hj
          exact hji (huniq j hj)
        exact Set.indicator_of_notMem hjnot (fun _ => c j)
      · intro hinot
        exact False.elim (hinot (Finset.mem_univ i))
    rw [hsingle]
    change f u = (I i).indicator (fun _ => c i) u
    rw [Set.indicator_of_mem hi]
    exact hconst i u hi
  refine ⟨hp.congr hfp.symm, ?_⟩
  calc
    (∫ u, f u ∂ν) = ∫ u, p u ∂ν := integral_congr_ae hfp
    _ = ∑ i, ∫ u, φ i u ∂ν :=
      integral_finsetSum Finset.univ (fun i _ => hφ i)
    _ = ∑ i, (ν (I i)).toReal * c i := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [φ]
      simpa only [measureReal_def, smul_eq_mul] using
        (integral_indicator_const (μ := ν) (c i) (hI i))

end
end AronowAudit.P027.Wave1.UniformStart
