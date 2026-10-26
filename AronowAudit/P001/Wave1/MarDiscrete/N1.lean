import AronowAudit.P001.Wave1.MarDiscreteBlueprint
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

universe u v

namespace AronowAudit.P001.Wave1.MarDiscrete

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n1_proof : N1.{u, v} := by
  intro Ω E _ _ _ _ μ _ X hX m hMi
  let C : E → Set Ω := fun x => {ω | X ω = x}
  have hC : ∀ x, MeasurableSet (C x) := fun x => hX (measurableSet_singleton x)
  have hdisj : Pairwise (fun x y => Disjoint (C x) (C y)) := by
    intro x y hxy
    apply Set.disjoint_left.mpr
    intro ω hx hy
    change X ω = x at hx
    change X ω = y at hy
    exact hxy (hx.symm.trans hy)
  have hcover : (⋃ x, C x) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨X ω, rfl⟩
  have hcell : ∀ x : E, (∫ ω in C x, (m ∘ X) ω ∂μ) = m x * prob μ (C x) := by
    intro x
    calc
      (∫ ω in C x, (m ∘ X) ω ∂μ) = ∫ _ in C x, m x ∂μ := by
        apply setIntegral_congr_fun (hC x)
        intro ω hω
        change X ω = x at hω
        simp only [Function.comp_apply, hω]
      _ = m x * prob μ (C x) := by
        rw [setIntegral_const, smul_eq_mul]
        exact mul_comm _ _
  have hsum : HasSum (fun x : E => m x * prob μ {ω | X ω = x}) (mean μ (m ∘ X)) := by
    simpa only [hcell, hcover, Measure.restrict_univ, mean] using
      (hasSum_integral_iUnion hC hdisj hMi.integrableOn)
  exact ⟨hsum.summable, hsum.tsum_eq.symm⟩

end

end AronowAudit.P001.Wave1.MarDiscrete
