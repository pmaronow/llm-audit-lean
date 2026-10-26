import AronowAudit.P001.Wave1.PolynomialBlpBlueprint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
Finite-dimensional least squares, without an independence assumption on the generators.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.PolynomialBlp

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

theorem n3_proof : N3.{u} := by
  classical
  intro H _ _ d v y
  let K : Submodule ℝ H := Submodule.span ℝ (Set.range v)
  letI : FiniteDimensional ℝ K :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  letI : CompleteSpace K := FiniteDimensional.complete ℝ K
  have hy : K.starProjection y ∈ Submodule.span ℝ (Set.range v) :=
    K.starProjection_apply_mem y
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
  refine ⟨b, ?_⟩
  intro c
  have hc : (∑ i, c i • v i) ∈ K :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c, rfl⟩
  have hbounded : BddBelow (Set.range (fun z : K => ‖y - (z : H)‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact norm_nonneg _
  calc
    ‖y - ∑ i, b i • v i‖ = ‖y - K.starProjection y‖ := by rw [hb]
    _ = ⨅ z : K, ‖y - (z : H)‖ := Submodule.starProjection_minimal y
    _ ≤ ‖y - ∑ i, c i • v i‖ :=
      ciInf_le hbounded (⟨∑ i, c i • v i, hc⟩ : K)

end

end AronowAudit.P001.Wave1.PolynomialBlp
