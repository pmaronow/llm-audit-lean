import AronowAudit.P002.Wave1.E61EigenvalueBlueprint
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Exp

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

universe u

/-- Expand the product by the chosen subset, and combine the two exponential products. -/
theorem n3_proof : N3 := by
  intro N p θ a
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro B _
  have hsum : (∑ i ∈ B, a i) + (∑ i ∈ Bᶜ, a i) = ∑ i, a i :=
    Finset.sum_add_sum_compl B a
  have hfirst : (∏ i ∈ B, p * Real.exp (θ * (a i * (1 - p)))) =
      p ^ B.card * Real.exp (∑ i ∈ B, θ * (a i * (1 - p))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Real.exp_sum]
  have hsecond : (∏ i ∈ Bᶜ, (1 - p) * Real.exp (-(θ * (a i * p)))) =
      (1 - p) ^ (N - B.card) * Real.exp (∑ i ∈ Bᶜ, -(θ * (a i * p))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Real.exp_sum]
    simp only [Finset.card_compl, Fintype.card_fin]
  have hexponent :
      (∑ i ∈ B, θ * (a i * (1 - p))) + (∑ i ∈ Bᶜ, -(θ * (a i * p))) =
        θ * ((∑ i ∈ B, a i) - p * ∑ i, a i) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_neg_distrib]
    rw [← hsum]
    ring
  rw [hfirst, hsecond]
  calc
    p ^ B.card * (1 - p) ^ (N - B.card) *
        Real.exp (θ * ((∑ i ∈ B, a i) - p * ∑ i, a i)) =
        p ^ B.card * (1 - p) ^ (N - B.card) *
          (Real.exp (∑ i ∈ B, θ * (a i * (1 - p))) *
            Real.exp (∑ i ∈ Bᶜ, -(θ * (a i * p)))) := by
      rw [← Real.exp_add, hexponent]
    _ = _ := by ring

end
end AronowAudit.P002.Wave1.E61Eigenvalue
