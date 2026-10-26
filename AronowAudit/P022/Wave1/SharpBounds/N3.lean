import AronowAudit.P022.Wave1.SharpBoundsBlueprint

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

private theorem quantile_cell {N : ℕ} (y : Fin N → ℝ) (j : Fin N) (u : ℝ)
    (hl : (j : ℝ) / N < u) (hu : u < ((j : ℝ) + 1) / N) :
    empiricalQuantile y u = sortedValues y j := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := j.isLt; omega)
  have hlow := (div_lt_iff₀ hN).mp hl
  have hupp := (lt_div_iff₀ hN).mp hu
  have hc : Nat.ceil ((N : ℝ) * u) = j.val + 1 := by
    apply (Nat.ceil_eq_iff (by omega : j.val + 1 ≠ 0)).2
    push_cast
    constructor <;> nlinarith
  simp [empiricalQuantile, hc, orderStatistic, sortedValues]

theorem n3_proof : N3 := by
  intro N y j u hl hu
  refine ⟨quantile_cell y j u hl hu, quantile_cell y j.rev (1 - u) ?_ ?_⟩
  · have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := j.isLt; omega)
    apply (div_lt_iff₀ hN).2
    have hj : (j.rev : ℝ) = (N : ℝ) - 1 - j := by
      rw [Fin.val_rev, Nat.cast_sub (show j.val + 1 ≤ N by have := j.isLt; omega)]
      push_cast
      ring
    rw [hj]
    have := (lt_div_iff₀ hN).mp hu
    nlinarith
  · have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := j.isLt; omega)
    apply (lt_div_iff₀ hN).2
    have hj : (j.rev : ℝ) = (N : ℝ) - 1 - j := by
      rw [Fin.val_rev, Nat.cast_sub (show j.val + 1 ≤ N by have := j.isLt; omega)]
      push_cast
      ring
    rw [hj]
    have := (div_lt_iff₀ hN).mp hl
    nlinarith

end
end AronowAudit.P022.Wave1.SharpBounds
