import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint

namespace AronowAudit.P031.Wave1.FootnoteThreeProbability
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- Finite Cauchy--Schwarz for the actual uniform fixed-count design. -/
theorem n2_proof : N2 := by
  classical
  intro N M f hMN
  let S := (Finset.univ : Finset (Fin N)).powersetCard M
  have hcNat : 0 < S.card := by
    dsimp only [S]
    simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using
      (Nat.choose_pos hMN)
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hcNat
  have hCS : (∑ s ∈ S, |f s|) ^ 2 ≤ (S.card : ℝ) * ∑ s ∈ S, f s ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] using
      (Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun s => |f s|))
  apply Real.le_sqrt_of_sq_le
  change ((∑ s ∈ S, |f s|) / (S.card : ℝ)) ^ 2 ≤
    (∑ s ∈ S, f s ^ 2) / (S.card : ℝ)
  calc
    _ = (∑ s ∈ S, |f s|) ^ 2 / (S.card : ℝ) ^ 2 := by rw [div_pow]
    _ ≤ ((S.card : ℝ) * ∑ s ∈ S, f s ^ 2) / (S.card : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hCS (sq_nonneg _)
    _ = _ := by field_simp [hc.ne'] <;> ring

end
end AronowAudit.P031.Wave1.FootnoteThreeProbability
