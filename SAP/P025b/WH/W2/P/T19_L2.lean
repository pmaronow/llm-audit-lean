import SAP.P025b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

theorem SAP.P025b.WH.W2.T19_L2_proof : SAP.P025b.WH.W2.T19_L2 := by
  intro n hn y hy hnonconstant
  let first : Fin n := ⟨0, hn⟩
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  push Not at hnonconstant
  obtain ⟨j, hj⟩ := hnonconstant
  have hfirstj : y first ≤ y j := by
    apply hy
    exact Fin.le_iff_val_le_val.mpr (Nat.zero_le j.val)
  have hjstrict : y first < y j := lt_of_le_of_ne hfirstj (Ne.symm hj)
  have hsum : (∑ _i : Fin n, y first) < ∑ i : Fin n, y i := by
    apply Finset.sum_lt_sum
    · intro i hi
      apply hy
      exact Fin.le_iff_val_le_val.mpr (Nat.zero_le i.val)
    · exact ⟨j, Finset.mem_univ _, hjstrict⟩
  have hsum' : (n : ℝ) * y first < ∑ i : Fin n, y i := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] using hsum
  change y first < (∑ i : Fin n, y i) / (n : ℝ)
  apply (lt_div_iff₀ hnR).2
  nlinarith [hsum']
