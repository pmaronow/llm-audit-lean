import AronowAudit.P022.Wave1.SharpBoundsBlueprint

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem n4_proof : N4 := by
  intro N _ F c h
  have hN : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  let a : ℕ → ℝ := fun k => (k : ℝ) / N
  let b : ℕ → ℝ := fun k => if hk : k < N then c ⟨k, hk⟩ else 0
  have hab (k : ℕ) : a k ≤ a (k + 1) := by
    dsimp [a]
    apply div_le_div_of_nonneg_right _ hN.le
    exact_mod_cast Nat.le_succ k
  have heq (k : ℕ) (hk : k < N) : Set.EqOn F (fun _ => c ⟨k, hk⟩)
      (Set.uIoo (a k) (a (k + 1))) := by
    rw [Set.uIoo_of_le (hab k)]
    intro u hu
    apply h ⟨k, hk⟩ u hu.1
    simpa [a, Nat.cast_add, Nat.cast_one] using hu.2
  have hint (k : ℕ) (hk : k < N) : IntervalIntegrable F volume (a k) (a (k + 1)) :=
    intervalIntegrable_const.congr_uIoo (heq k hk).symm
  have hi (k : ℕ) (hk : k < N) :
      (∫ u in a k..a (k + 1), F u) = b k / N := by
    rw [intervalIntegral.integral_congr_uIoo (heq k hk), intervalIntegral.integral_const]
    simp only [b, dif_pos hk, smul_eq_mul]
    dsimp [a]
    push_cast
    ring
  calc
    (∫ u in (0 : ℝ)..1, F u) = ∑ k ∈ range N, ∫ u in a k..a (k + 1), F u := by
      simpa [a, ne_of_gt hN] using
        (intervalIntegral.sum_integral_adjacent_intervals hint).symm
    _ = ∑ k ∈ range N, b k / N := by
      exact sum_congr rfl (fun k hk => hi k (mem_range.mp hk))
    _ = finiteMean c := by
      rw [← Finset.sum_div]
      unfold finiteMean
      rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
      congr 1
      rw [← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro i _
      simp [b, i.isLt]

end
end AronowAudit.P022.Wave1.SharpBounds
