import SAP.P003b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P003b SAP.P003b.Bridge

theorem SAP.P003b.WH.W1.T18_L1_proof : SAP.P003b.WH.W1.T18_L1 := by
  intro ε hε tests htests
  obtain ⟨C, hC, hK⟩ := AronowAudit.P003.recommended_k_log_bound ε hε
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Asymptotics.IsBigO.of_bound (4*C/Real.log 2)
  filter_upwards [htests, hK] with n ht hn
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlogTwo : 0 ≤ logTwo n := by
    unfold logTwo
    exact div_nonneg hlog h2.le
  have hK' : (recommendedK ε n : ℝ) ≤ C*Real.log n := by
    simpa only [recommendedK_eq] using hn
  have hleft : 0 ≤ (tests n : ℝ)*recommendedK ε n := by positivity
  have hright : 0 ≤ (n : ℝ)*(Real.log n)^2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright]
  calc
    (tests n : ℝ)*recommendedK ε n ≤
        (4*(n : ℝ)*logTwo n)*(recommendedK ε n : ℝ) := by
      exact mul_le_mul_of_nonneg_right ht (by positivity)
    _ ≤ (4*(n : ℝ)*logTwo n)*(C*Real.log n) :=
      mul_le_mul_of_nonneg_left hK' (by positivity)
    _ = (4*C/Real.log 2)*((n : ℝ)*(Real.log n)^2) := by
      unfold logTwo
      ring
