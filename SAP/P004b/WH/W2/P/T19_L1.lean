import SAP.P004b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T19_L1

open scoped BigOperators

private theorem sum_range_pairs (f : ℕ → ℝ) (m : ℕ)
    (hpair : ∀ k, k < m → f (2*k) + f (2*k+1) = 0) :
    (∑ n ∈ Finset.range (2*m), f n) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1) = 2*m+2 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ]
    rw [ih (fun k hk => hpair k (by omega))]
    linarith [hpair m (by omega)]

private theorem cancelling_pair (m k : ℕ) (hk : k < m)
    (z : SAP.P004b.Assignment (2*m+1)) :
    SAP.P004b.cancellingArray m ⟨2*k+1, by omega⟩ z +
      SAP.P004b.cancellingArray m ⟨2*k+2, by omega⟩ z = 0 := by
  have hs₁ : SAP.P004b.cancellingSource m ⟨2*k+1, by omega⟩ = ⟨k+1, by omega⟩ := by
    apply Fin.ext
    simp [SAP.P004b.cancellingSource]
    omega
  have hs₂ : SAP.P004b.cancellingSource m ⟨2*k+2, by omega⟩ = ⟨k+1, by omega⟩ := by
    apply Fin.ext
    simp [SAP.P004b.cancellingSource]
    omega
  have hodd : (2*k+1) % 2 = 1 := by omega
  have heven : (2*k+2) % 2 = 0 := by omega
  simp [SAP.P004b.cancellingArray, hs₁, hs₂, hodd, heven]

end SAP.P004b.WH.W2.P.T19_L1

theorem SAP.P004b.WH.W2.T19_L1_proof : SAP.P004b.WH.W2.T19_L1 := by
  intro m z
  rw [Fin.sum_univ_succ]
  have htail :
      (∑ i : Fin (2*m), SAP.P004b.cancellingArray m i.succ z) = 0 := by
    let f : ℕ → ℝ := fun n => SAP.P004b.cancellingArray m
      ⟨min (n+1) (2*m), by
        have hmin := Nat.min_le_right (n+1) (2*m)
        omega⟩ z
    have hf (n : ℕ) (hn : n < 2*m) :
        f n = SAP.P004b.cancellingArray m ⟨n+1, by omega⟩ z := by
      have hmin : min (n+1) (2*m) = n+1 := Nat.min_eq_left (by omega)
      simp [f, hmin]
    have hconvert :
        (∑ n ∈ Finset.range (2*m), f n) =
          (∑ i : Fin (2*m), SAP.P004b.cancellingArray m i.succ z) := by
      rw [← Fin.sum_univ_eq_sum_range f (2*m)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hf i.val (by omega)]
      rfl
    have hpairs : ∀ k, k < m → f (2*k) + f (2*k+1) = 0 := by
      intro k hk
      rw [hf (2*k) (by omega), hf (2*k+1) (by omega)]
      exact SAP.P004b.WH.W2.P.T19_L1.cancelling_pair m k hk z
    rw [← hconvert]
    exact SAP.P004b.WH.W2.P.T19_L1.sum_range_pairs f m hpairs
  rw [htail]
  simp [SAP.P004b.cancellingArray, SAP.P004b.cancellingSource,
    SAP.P004b.bit]
