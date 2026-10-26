import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint

/-!
Exact moments of the enumerated hypercube.  These are finite sums,
so the cancellation argument does not require a probability space.
-/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

private theorem n2_sgn_sq (d : Fin 2) : sgn2 d ^ 2 = 1 := by
  fin_cases d <;> norm_num [sgn2]

private theorem n2_sgn_swap (d : Fin 2) :
    sgn2 (Equiv.swap (0 : Fin 2) 1 d) = -sgn2 d := by
  fin_cases d <;> norm_num [sgn2]

/-- Change just the `j`th digit.  Its inverse is the same digit change. -/
private def n2_flip {k : ℕ} (j : Fin k) :
    (Fin k → Fin 2) ≃ (Fin k → Fin 2) where
  toFun v := Function.update v j (Equiv.swap (0 : Fin 2) 1 (v j))
  invFun v := Function.update v j (Equiv.swap (0 : Fin 2) 1 (v j))
  left_inv v := by
    funext a
    by_cases ha : a = j
    · subst a
      simp only [Function.update_self, Equiv.swap_apply_self]
    · simp only [Function.update_of_ne ha]
  right_inv v := by
    funext a
    by_cases ha : a = j
    · subst a
      simp only [Function.update_self, Equiv.swap_apply_self]
    · simp only [Function.update_of_ne ha]

private theorem n2_coordinate_sum (k : ℕ) (j : Fin k) :
    (∑ v : Fin k → Fin 2, sgn2 (v j)) = 0 := by
  have hneg : (∑ v : Fin k → Fin 2, sgn2 (v j)) =
      -(∑ v : Fin k → Fin 2, sgn2 (v j)) := by
    calc
      _ = ∑ v : Fin k → Fin 2, sgn2 (n2_flip j v j) :=
        ((n2_flip j).sum_comp (fun v => sgn2 (v j))).symm
      _ = ∑ v : Fin k → Fin 2, -sgn2 (v j) := by
        apply Finset.sum_congr rfl
        intro v _
        change sgn2 (Function.update v j (Equiv.swap (0 : Fin 2) 1 (v j)) j) = _
        rw [Function.update_self, n2_sgn_swap]
      _ = _ := by rw [Finset.sum_neg_distrib]
  linarith

private theorem n2_coordinate_product_sum (k : ℕ) (j l : Fin k) :
    (∑ v : Fin k → Fin 2, sgn2 (v j) * sgn2 (v l)) =
      if j = l then (2 : ℝ) ^ k else 0 := by
  by_cases hjl : j = l
  · subst l
    rw [if_pos rfl]
    simp_rw [← pow_two, n2_sgn_sq]
    simp [Fintype.card_fun]
  · rw [if_neg hjl]
    have hneg : (∑ v : Fin k → Fin 2, sgn2 (v j) * sgn2 (v l)) =
        -(∑ v : Fin k → Fin 2, sgn2 (v j) * sgn2 (v l)) := by
      calc
        _ = ∑ v : Fin k → Fin 2,
            sgn2 (n2_flip j v j) * sgn2 (n2_flip j v l) :=
          ((n2_flip j).sum_comp (fun v => sgn2 (v j) * sgn2 (v l))).symm
        _ = ∑ v : Fin k → Fin 2, -(sgn2 (v j) * sgn2 (v l)) := by
          apply Finset.sum_congr rfl
          intro v _
          change sgn2 (Function.update v j (Equiv.swap (0 : Fin 2) 1 (v j)) j) *
            sgn2 (Function.update v j (Equiv.swap (0 : Fin 2) 1 (v j)) l) = _
          rw [Function.update_self, Function.update_of_ne (Ne.symm hjl), n2_sgn_swap]
          ring
        _ = _ := by rw [Finset.sum_neg_distrib]
    linarith

private theorem n2_sum_sign_sums (k : ℕ) :
    (∑ v : Fin k → Fin 2, ∑ j, sgn2 (v j)) = 0 := by
  rw [Finset.sum_comm]
  simp only [n2_coordinate_sum, Finset.sum_const_zero]

private theorem n2_sum_sign_sums_sq (k : ℕ) :
    (∑ v : Fin k → Fin 2, (∑ j, sgn2 (v j)) ^ 2) =
      (k : ℝ) * (2 : ℝ) ^ k := by
  calc
    _ = ∑ v : Fin k → Fin 2, ∑ j : Fin k, ∑ l : Fin k,
        sgn2 (v j) * sgn2 (v l) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ j : Fin k, ∑ l : Fin k, ∑ v : Fin k → Fin 2,
        sgn2 (v j) * sgn2 (v l) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j : Fin k, ∑ l : Fin k,
        if j = l then (2 : ℝ) ^ k else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      exact n2_coordinate_product_sum k j l
    _ = (k : ℝ) * (2 : ℝ) ^ k := by simp

/-- Transport through the binary enumeration. -/
private theorem n2_sum_digits (n : ℕ) (f : (Fin (hcK n) → Fin 2) → ℝ) :
    (∑ i : Fin (hcN n), f (hcDigits n i)) = ∑ v, f v := by
  change (∑ i : Fin (2 ^ hcK n),
    f ((finFunctionFinEquiv (m := 2) (n := hcK n)).symm i)) = _
  exact (finFunctionFinEquiv (m := 2) (n := hcK n)).symm.sum_comp f

theorem n2_proof : N2 := by
  intro n
  have hscale : (hcK n : ℝ) = (2 * ((n : ℝ) + 1)) ^ 2 := by
    simp only [hcK, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat]
    ring
  have hden : 2 * ((n : ℝ) + 1) ≠ 0 := by positivity
  constructor
  · change (∑ i : Fin (hcN n),
      (∑ j, sgn2 (hcDigits n i j)) / (2 * ((n : ℝ) + 1))) = 0
    rw [← Finset.sum_div,
      n2_sum_digits n (fun v => ∑ j, sgn2 (v j)), n2_sum_sign_sums]
    simp
  · change (∑ i : Fin (hcN n),
      ((∑ j, sgn2 (hcDigits n i j)) / (2 * ((n : ℝ) + 1))) ^ 2) = _
    simp_rw [div_pow]
    rw [← Finset.sum_div,
      n2_sum_digits n (fun v => (∑ j, sgn2 (v j)) ^ 2),
      n2_sum_sign_sums_sq, hscale]
    simp only [hcN, Nat.cast_pow, Nat.cast_ofNat]
    field_simp [hden] <;> ring

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
