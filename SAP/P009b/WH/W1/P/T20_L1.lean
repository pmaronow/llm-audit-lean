import SAP.P009b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P009b.WH.W1.P.T20_L1

private theorem binary_nonneg {n : ℕ} (J : Fin n → Fin n → ℝ)
    (hJ : ∀ i j, J i j = 0 ∨ J i j = 1) (i j : Fin n) : 0 ≤ J i j := by
  rcases hJ i j with h | h
  · rw [h]
  · rw [h]
    norm_num

end SAP.P009b.WH.W1.P.T20_L1

theorem SAP.P009b.WH.W1.T20_L1_proof : SAP.P009b.WH.W1.T20_L1 := by
  intro n J hJ ρ
  have hprod : ∀ i j ℓ, 0 ≤ J ℓ i * J (ρ ℓ) j := by
    intro i j ℓ
    exact mul_nonneg
      (SAP.P009b.WH.W1.P.T20_L1.binary_nonneg J hJ ℓ i)
      (SAP.P009b.WH.W1.P.T20_L1.binary_nonneg J hJ (ρ ℓ) j)
  refine ⟨?_, ?_⟩
  · intro i j
    by_cases hd : ∃ ℓ, J ℓ i = 1 ∧ J ℓ j = 1
    · simp [SAP.P009b.wholeArrayE,
        SAP.P009b.wholeArrayD, hd]
    · have hD : SAP.P009b.wholeArrayD J i j = 0 := by
        simp [SAP.P009b.wholeArrayD, hd]
      by_cases hw : ∃ ℓ, J ℓ i = 1 ∧ J (ρ ℓ) j = 1
      · obtain ⟨ℓ, hi, hj⟩ := hw
        have hw' : ∃ k, J k i = 1 ∧ J (ρ k) j = 1 := ⟨ℓ, hi, hj⟩
        have hs := Finset.single_le_sum
          (f := fun k => (1 - SAP.P009b.wholeArrayD J i j) * J k i * J (ρ k) j)
          (fun k _ => by
            rw [hD]
            simp only [sub_zero, one_mul]
            exact hprod i j k)
          (Finset.mem_univ ℓ)
        calc
          SAP.P009b.wholeArrayE J ρ i j = 1 := by
            simp [SAP.P009b.wholeArrayE, hD, hw']
          _ ≤ ∑ k, (1 - SAP.P009b.wholeArrayD J i j) * J k i * J (ρ k) j := by
            simpa [hD, hi, hj] using hs
      · have hsum : 0 ≤ ∑ ℓ, (1 - SAP.P009b.wholeArrayD J i j) *
            J ℓ i * J (ρ ℓ) j :=
          Finset.sum_nonneg (fun ℓ _ => by
            rw [hD]
            simp only [sub_zero, one_mul]
            exact hprod i j ℓ)
        simpa [SAP.P009b.wholeArrayE, hD, hw] using hsum
  · intro i j
    by_cases hd : ∃ ℓ, J ℓ i = 1 ∧ J ℓ j = 1
    · have hsum : 0 ≤ ∑ ℓ, J ℓ i * J (ρ ℓ) j :=
        Finset.sum_nonneg (fun ℓ _ => hprod i j ℓ)
      simpa [SAP.P009b.wholeArrayD, hd] using hsum
    · simp [SAP.P009b.wholeArrayD, hd]
