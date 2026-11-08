import SAP.P001e.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical

namespace SAP.P001e.WH.W1.P.T78_L1

private theorem residualSS_shift {n K : ℕ}
    (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
    (b : Fin (K+1) → ℝ) (hX : ∀ i, X i 0 = 1) (t : ℝ) :
    residualSS X Y (b + Pi.single 0 t) =
      residualSS X Y b - 2 * t * (∑ i, (Y i - X.mulVec b i)) + (n : ℝ) * t^2 := by
  unfold residualSS
  have hres : ∀ i, Y i - X.mulVec (b + Pi.single 0 t) i =
      (Y i - X.mulVec b i) - t := by
    intro i
    rw [Matrix.mulVec_add, Matrix.mulVec_single]
    simp [hX i]
    ring
  simp_rw [hres]
  calc
    (∑ i, ((Y i - X.mulVec b i) - t)^2) =
        ∑ i, ((Y i - X.mulVec b i)^2 - 2 * t * (Y i - X.mulVec b i) + t^2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, (Y i - X.mulVec b i)^2) -
          (∑ i, 2 * t * (Y i - X.mulVec b i)) + (∑ _i : Fin n, t^2) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ i, (Y i - X.mulVec b i)^2) -
          2 * t * (∑ i, (Y i - X.mulVec b i)) + (n : ℝ) * t^2 := by
          rw [← Finset.mul_sum]
          simp

end SAP.P001e.WH.W1.P.T78_L1

theorem SAP.P001e.WH.W1.T78_L1_proof : SAP.P001e.WH.W1.T78_L1 := by
  intro n K hn X Y b hX hmin
  let S : ℝ := ∑ i, (Y i - X.mulVec b i)
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hshift := SAP.P001e.WH.W1.P.T78_L1.residualSS_shift X Y b hX (S / (n : ℝ))
  have hmin' := hmin (b + Pi.single 0 (S / (n : ℝ)))
  rw [hshift] at hmin'
  have hs : (∑ i, (Y i - X.mulVec b i)) = S := rfl
  rw [hs] at hmin'
  have hquad : S^2 / (n : ℝ) ≤ 0 := by
    have hrewrite : -2 * (S / (n : ℝ)) * S + (n : ℝ) * (S / (n : ℝ))^2 =
        -(S^2 / (n : ℝ)) := by
      field_simp [ne_of_gt hnR]
      ring
    nlinarith [hmin', hrewrite]
  have hquad_nonneg : 0 ≤ S^2 / (n : ℝ) :=
    div_nonneg (sq_nonneg S) (le_of_lt hnR)
  have hquad_zero : S^2 / (n : ℝ) = 0 := le_antisymm hquad hquad_nonneg
  have hSsq : S^2 = 0 := by
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    rcases (div_eq_zero_iff).mp hquad_zero with h | h
    · exact h
    · exact False.elim (hn_ne h)
  nlinarith [hSsq]
