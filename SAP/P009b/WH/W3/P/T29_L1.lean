import SAP.P009b.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009b.WH.W3.P.T29_L1

end SAP.P009b.WH.W3.P.T29_L1

theorem SAP.P009b.WH.W3.T29_L1_proof : SAP.P009b.WH.W3.T29_L1 := by
  intro Ω _ P X m q hm hq hmq
  have htheta0 : 0 ≤ m/q := div_nonneg hm hq.le
  have htheta1 : m/q ≤ 1 := (div_le_one hq).2 hmq
  have hid (ω : Ω) : (|X ω| ^ q) ^ (m/q) = Real.rpow |X ω| m := by
    rw [← Real.rpow_mul (abs_nonneg (X ω))]
    congr 1
    field_simp
  have hJ := (Real.concaveOn_rpow htheta0 htheta1).le_map_sum
    (t := Finset.univ) (w := P.mass) (p := fun ω => Real.rpow |X ω| q)
    (fun ω _ => P.nonneg ω) P.total
    (fun ω _ => Real.rpow_nonneg (abs_nonneg (X ω)) q)
  simpa only [Real.rpow_eq_pow, smul_eq_mul, hid, mean] using hJ
