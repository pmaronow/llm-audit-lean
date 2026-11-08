import SAP.P003b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem SAP.P003b.WH.W1.T18_L2_proof : SAP.P003b.WH.W1.T18_L2 := by
  intro ε hε
  have hnR : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hnR
  apply Asymptotics.IsBigO.of_bound (ε ^ 2)
  filter_upwards [hlog.eventually (Filter.eventually_ge_atTop ε)] with n hlogn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    by_contra hnot
    have hle : (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hz : (n : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg n)
    have hn0 : n = 0 := by exact_mod_cast hz
    subst n
    simp at hlogn
    linarith
  have hl : 0 ≤ Real.log (n : ℝ) := le_trans hε.le hlogn
  have harg : (n : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) / ε :=
    (le_div_iff₀ hε).2 (mul_le_mul_of_nonneg_left hlogn hnpos.le)
  have hlogarg : Real.log (n : ℝ) ≤
      Real.log ((n : ℝ) * Real.log (n : ℝ) / ε) :=
    Real.log_le_log hnpos harg
  have hprod : (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 2 ≤
      (n : ℝ) ^ 2 * Real.log (n : ℝ) *
        Real.log ((n : ℝ) * Real.log (n : ℝ) / ε) := by
    calc
      _ = ((n : ℝ) ^ 2 * Real.log (n : ℝ)) * Real.log (n : ℝ) := by ring
      _ ≤ ((n : ℝ) ^ 2 * Real.log (n : ℝ)) *
          Real.log ((n : ℝ) * Real.log (n : ℝ) / ε) :=
        mul_le_mul_of_nonneg_left hlogarg (mul_nonneg (sq_nonneg _) hl)
  have hscale : (n : ℝ) ^ 2 * Real.log (n : ℝ) *
      Real.log ((n : ℝ) * Real.log (n : ℝ) / ε) =
      ε ^ 2 * ((n : ℝ) ^ 2 * Real.log (n : ℝ) / ε ^ 2 *
        Real.log ((n : ℝ) * Real.log (n : ℝ) / ε)) := by
    field_simp [ne_of_gt hε]
    <;> ring
  have hf_nonneg : 0 ≤ (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 2 := by positivity
  have hq : 0 ≤ Real.log ((n : ℝ) * Real.log (n : ℝ) / ε) :=
    le_trans hl hlogarg
  have hpre : 0 ≤ (n : ℝ) ^ 2 * Real.log (n : ℝ) / ε ^ 2 := by positivity
  have hg_nonneg : 0 ≤ (n : ℝ) ^ 2 * Real.log (n : ℝ) / ε ^ 2 *
      Real.log ((n : ℝ) * Real.log (n : ℝ) / ε) := mul_nonneg hpre hq
  rw [Real.norm_eq_abs, abs_of_nonneg hf_nonneg,
    Real.norm_eq_abs, abs_of_nonneg hg_nonneg]
  exact hprod.trans_eq hscale
