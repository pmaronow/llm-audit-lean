import SAP.P026b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b.WH.W1.P.T21_L1

end SAP.P026b.WH.W1.P.T21_L1

set_option maxHeartbeats 1000000

theorem SAP.P026b.WH.W1.T21_L1_proof : SAP.P026b.WH.W1.T21_L1 := by
  classical
  intro Ω I hΩ hI hIdec D N M m hN hm hmM hmarg x z w
  have hM : 0 < M := lt_trans hm hmM
  have hd : 0 < M - m := Nat.sub_pos_of_lt hmM
  have h1 (w : Ω) :
      htTotal D true x w = observedArmSum D true x z w / ((m : ℝ) / M) := by
    unfold htTotal observedArmSum
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hmarg i).1]
    exact congrArg (fun v : ℝ => v / ((m : ℝ) / M))
      (AronowAudit.P026.observed_mask (Bridge.toDesign D) true x z w i).symm
  have h0 (w : Ω) :
      htTotal D false z w = observedArmSum D false x z w / (((M - m : ℕ) : ℝ) / M) := by
    unfold htTotal observedArmSum
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hmarg i).2]
    exact congrArg (fun v : ℝ => v / (((M - m : ℕ) : ℝ) / M))
      (AronowAudit.P026.observed_mask (Bridge.toDesign D) false x z w i).symm
  calc
    ht D N x z w =
        (M : ℝ) / N *
          (observedArmSum D true x z w / m -
            observedArmSum D false x z w / (M - m : ℕ)) := by
      unfold ht
      rw [h1 w, h0 w]
      field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hN),
        Nat.cast_ne_zero.mpr (ne_of_gt hM),
        Nat.cast_ne_zero.mpr (ne_of_gt hm),
        Nat.cast_ne_zero.mpr (ne_of_gt hd)] <;> ring
    _ = T21ClusterContrast D N M m x z w := rfl
