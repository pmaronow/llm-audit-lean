import SAP.P025b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b.WH.W2.P.T19_L1

open scoped BigOperators

theorem denominator_formula {n : ℕ} (l b : ℝ) (k : ℕ) (hk : k ≤ n) :
    (∑ i : Fin n, if i.val < k then l else b) =
      l * (k : ℝ) + b * ((n : ℝ) - (k : ℝ)) := by
  induction k with
  | zero =>
      simp [Fintype.card_fin] <;> ring
  | succ k ih =>
      have hk' : k ≤ n := by omega
      let q : Fin n := ⟨k, by omega⟩
      have hprev := ih hk'
      have hup := AronowAudit.P025.threshold_den_update
        (fun _ : Fin n => (1 : ℝ)) l b q
      have hstep :
          (∑ i : Fin n, if i.val < k + 1 then l else b) =
            (∑ i : Fin n, if i.val < k then l else b) + (l - b) := by
        simpa [AronowAudit.P025.threshold, q, Fin.le_iff_val_le_val,
          Fin.lt_def] using hup
      rw [hstep, hprev]
      simp only [Nat.cast_succ]
      ring

end SAP.P025b.WH.W2.P.T19_L1

theorem SAP.P025b.WH.W2.T19_L1_proof : SAP.P025b.WH.W2.T19_L1 := by
  classical
  intro n y l b k hk
  constructor
  · calc
      (∑ i : Fin n, (if i.val < k then l else b) * y i) =
          ∑ i : Fin n, if i.val < k then l * y i else b * y i := by
            simp only [ite_mul]
      _ = (∑ i with i.val < k, l * y i) +
            (∑ i with ¬ i.val < k, b * y i) := by
              exact Finset.sum_ite _ _
      _ = l * t19Prefix y k + b * t19Tail y k := by
            simp only [not_lt]
            simp only [t19Prefix, t19Tail]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
  · exact SAP.P025b.WH.W2.P.T19_L1.denominator_formula l b k hk
