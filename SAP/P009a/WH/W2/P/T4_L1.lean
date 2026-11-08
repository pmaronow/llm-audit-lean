import SAP.P009a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009a.WH.W2.P.T4_L1

open scoped BigOperators Classical

noncomputable section

theorem proof : SAP.P009a.WH.W2.T4_L1 := by
  intro Ω hΩ P X k p q hk hp horder hbound
  classical
  cases q with
  | none =>
      simp only [SAP.P009a.OrderBound] at hbound
      have hterm (ω : Ω) :
          P.mass ω * Real.rpow |X ω| p ≤ P.mass ω * Real.rpow k p := by
        by_cases hm : P.mass ω = 0
        · simp [hm]
        · have hmpos : 0 < P.mass ω := by
            have : ¬ P.mass ω ≤ 0 := by
              intro hle
              exact hm (le_antisymm hle (P.nonneg ω))
            exact lt_of_not_ge this
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg (X ω)) (hbound ω hmpos) hp.le)
            (P.nonneg ω)
      calc
        expectation P (fun ω => Real.rpow |X ω| p) =
            ∑ ω, P.mass ω * Real.rpow |X ω| p := rfl
        _ ≤ ∑ ω, P.mass ω * Real.rpow k p :=
            Finset.sum_le_sum (fun ω _ => hterm ω)
        _ = Real.rpow k p := by
            rw [← Finset.sum_mul, P.total]
            simp
  | some r =>
      have hpq : p ≤ r := WithTop.coe_le_coe.mp horder
      have hqpos : 0 < r := hp.trans_le hpq
      have hθ0 : 0 ≤ p/r := div_nonneg hp.le hqpos.le
      have hθ1 : p/r ≤ 1 := (div_le_one hqpos).2 hpq
      have hmoment :
          expectation P (fun ω => Real.rpow |X ω| r) ≤ Real.rpow k r := by
        simp only [SAP.P009a.OrderBound] at hbound
        change expectation P (fun ω => Real.rpow |X ω| r) ≤ Real.rpow k r at hbound
        exact hbound
      have hid (ω : Ω) :
          ((|X ω| : ℝ) ^ r) ^ (p/r) = |X ω| ^ p := by
        have he : r*(p/r) = p := by field_simp [ne_of_gt hqpos]
        simpa only [he] using
          (Real.rpow_mul (abs_nonneg (X ω)) r (p/r)).symm
      have hJ := (Real.concaveOn_rpow hθ0 hθ1).le_map_sum
        (t := Finset.univ) (w := P.mass)
        (p := fun ω => Real.rpow |X ω| r)
        (fun ω _ => P.nonneg ω) P.total
        (fun ω _ => Real.rpow_nonneg (abs_nonneg (X ω)) r)
      have hinterp :
          expectation P (fun ω => Real.rpow |X ω| p) ≤
            Real.rpow (expectation P (fun ω => Real.rpow |X ω| r)) (p/r) := by
        simpa only [Real.rpow_eq_pow, smul_eq_mul, hid,
          SAP.P009a.expectation] using hJ
      have hmoment_nonneg :
          0 ≤ expectation P (fun ω => Real.rpow |X ω| r) := by
        unfold SAP.P009a.expectation
        apply Finset.sum_nonneg
        intro ω _
        exact mul_nonneg (P.nonneg ω)
          (Real.rpow_nonneg (abs_nonneg (X ω)) r)
      have hscale :
          Real.rpow (Real.rpow k r) (p/r) = Real.rpow k p := by
        have he : r*(p/r) = p := by field_simp [ne_of_gt hqpos]
        change (k ^ r) ^ (p/r) = k ^ p
        simpa only [he] using (Real.rpow_mul (le_of_lt hk) r (p/r)).symm
      exact hinterp.trans
        ((Real.rpow_le_rpow hmoment_nonneg hmoment hθ0).trans_eq hscale)

end
end SAP.P009a.WH.W2.P.T4_L1

theorem SAP.P009a.WH.W2.T4_L1_proof : SAP.P009a.WH.W2.T4_L1 :=
  SAP.P009a.WH.W2.P.T4_L1.proof
