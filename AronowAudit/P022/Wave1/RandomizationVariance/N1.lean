import AronowAudit.P022.Wave1.RandomizationVarianceBlueprint
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.PermutationMarginals

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.RandomizationVariance
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators
noncomputable section

theorem n1_proof : N1 := by
  intro N a b s t
  constructor
  · intro h
    subst t
    exact permutation_eval_mean (by have := s.isLt; omega) (fun i => a i * b i) s
  · intro hst
    have hN : 2 ≤ N := by
      have := Fintype.one_lt_card_iff_nontrivial.mpr (show Nontrivial (Fin N) from ⟨⟨s, t, hst⟩⟩)
      have hgt : 1 < N := by simpa using this
      omega
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (N : ℝ) ≠ 0 := by linarith
    have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
    have h := StatLean.HypothesisTesting.avg_perm_apply_pair hst (fun i j => a i * b j)
    simp only [Fintype.card_fin] at h
    have hprod : (∑ p ∈ (univ : Finset (Fin N)) ×ˢ univ, a p.1 * b p.2) =
        (∑ i, a i) * (∑ i, b i) := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
    rw [← Finset.diag_union_offDiag (univ : Finset (Fin N)),
      Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag] at hprod
    have hoff : (∑ p ∈ (univ : Finset (Fin N)).offDiag, a p.1 * b p.2) =
        (∑ i, a i) * (∑ i, b i) - ∑ i, a i * b i := by linarith
    rw [hoff] at h
    simp only [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
    rw [div_eq_inv_mul, h]
    field_simp
    <;> ring

end
end AronowAudit.P022.Wave1.RandomizationVariance
