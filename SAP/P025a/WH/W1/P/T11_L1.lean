import SAP.P025a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

theorem SAP.P025a.WH.W1.T11_L1_proof : SAP.P025a.WH.W1.T11_L1 := by
  intro n γ k hk
  classical
  by_cases hkn : k = n
  · subst k
    simp [SAP.P025a.upperWeights, Finset.sum_const]
  · have hknlt : k < n := by omega
    let q : Fin n := ⟨k, hknlt⟩
    have hprefix : Finset.univ.filter (fun i : Fin n => i.val < k) = Finset.Iio q := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      change (i : ℕ) < k ↔ i < q
      rw [← Fin.val_fin_lt]
    have htail : Finset.univ.filter (fun i : Fin n => ¬ i.val < k) = Finset.Ici q := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
      rw [Fin.le_iff_val_le_val]
      simp only [q]
      omega
    calc
      (∑ i : Fin n, SAP.P025a.upperWeights γ k i) =
          (∑ i ∈ Finset.Iio q, (1 : ℝ)) + ∑ i ∈ Finset.Ici q, γ := by
        simp only [SAP.P025a.upperWeights]
        rw [Finset.sum_ite, hprefix, htail]
      _ = (k : ℝ) + γ * ((n - k : ℕ) : ℝ) := by
        simp [q, Nat.cast_sub hk]
        ring
