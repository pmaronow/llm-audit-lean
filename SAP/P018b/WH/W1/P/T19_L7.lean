import SAP.P018b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P018b.WH.W1.P.T19_L7

lemma wholeRareDelta_bounds (m : ℕ) :
    0 < wholeRareDelta (m + 1) ∧ wholeRareDelta (m + 1) ≤ 1 := by
  change 0 < AronowAudit.P018.rareDelta (m + 1) ∧
    AronowAudit.P018.rareDelta (m + 1) ≤ 1
  exact ⟨AronowAudit.P018.Wave1.TailB_rare_delta_pos (m + 1) (by omega),
    AronowAudit.P018.Wave1.TailB_rare_delta_le_one (m + 1) (by omega)⟩

lemma rareFactor_bounds (m : ℕ) :
    0 ≤ 1 - 1 / (m + 1 : ℝ) ∧ 1 - 1 / (m + 1 : ℝ) ≤ 1 := by
  have hden : (1 : ℝ) ≤ (m + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
  have hpos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
  have hfrac : 1 / (m + 1 : ℝ) ≤ 1 := (div_le_one hpos).2 hden
  have hfrac0 : 0 ≤ 1 / (m + 1 : ℝ) := by positivity
  constructor <;> linarith

lemma rarePower_eq (m : ℕ) :
    (2 : ℝ) ^ (-3 * (m + 1 : ℤ)) = (1 / 8 : ℝ) ^ (m + 1) := by
  rw [show -3 * (m + 1 : ℤ) = (-3 : ℤ) * ((m + 1 : ℕ) : ℤ) by norm_cast]
  rw [_root_.zpow_mul]
  norm_num
  norm_cast

lemma wholeRareHterm_nonneg (m : ℕ) : 0 ≤ wholeRareHterm m := by
  unfold wholeRareHterm
  positivity

lemma wholeRareHterm_le_geom (m : ℕ) : wholeRareHterm m ≤ (1 / 8 : ℝ) ^ m := by
  let x : ℝ := 1 - 1 / (m + 1 : ℝ)
  let d : ℝ := wholeRareDelta (m + 1)
  have hx : 0 ≤ x ∧ x ≤ 1 := by
    simpa [x] using rareFactor_bounds m
  have hd : 0 ≤ d ∧ d ≤ 1 := by
    simpa [d] using (wholeRareDelta_bounds m).imp (fun h => h.le) id
  have hx2 : x ^ 2 ≤ 1 := by
    have hp : 0 ≤ (1 - x) * (1 + x) :=
      mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.1])
    nlinarith
  have hd2 : d ^ 2 ≤ 1 := by
    have hp : 0 ≤ (1 - d) * (1 + d) :=
      mul_nonneg (sub_nonneg.mpr hd.2) (by linarith [hd.1])
    nlinarith
  have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hd2_nonneg : 0 ≤ d ^ 2 := sq_nonneg d
  have hfac : x ^ 2 * d ^ 2 ≤ 1 := by
    calc
      x ^ 2 * d ^ 2 ≤ 1 * 1 :=
        mul_le_mul hx2 hd2 hd2_nonneg (by norm_num)
      _ = 1 := by norm_num
  have hfac_nonneg : 0 ≤ x ^ 2 * d ^ 2 := mul_nonneg hx2_nonneg hd2_nonneg
  have hq_nonneg : 0 ≤ (1 / 8 : ℝ) ^ (m + 1) := by positivity
  have hq_le : (1 / 8 : ℝ) ≤ 1 := by norm_num
  have hpow_le : (1 / 8 : ℝ) ^ (m + 1) ≤ (1 / 8 : ℝ) ^ m := by
    rw [pow_succ]
    calc
      (1 / 8 : ℝ) ^ m * (1 / 8 : ℝ) ≤ (1 / 8 : ℝ) ^ m * 1 :=
        mul_le_mul_of_nonneg_left hq_le (by positivity)
      _ = (1 / 8 : ℝ) ^ m := by ring
  change (2 : ℝ) ^ (-3 * (m + 1 : ℤ)) *
      (1 - 1 / (m + 1 : ℝ)) ^ 2 * (wholeRareDelta (m + 1)) ^ 2 ≤
      (1 / 8 : ℝ) ^ m
  rw [rarePower_eq m]
  change (1 / 8 : ℝ) ^ (m + 1) * x ^ 2 * d ^ 2 ≤ (1 / 8 : ℝ) ^ m
  calc
    (1 / 8 : ℝ) ^ (m + 1) * x ^ 2 * d ^ 2 =
        (1 / 8 : ℝ) ^ (m + 1) * (x ^ 2 * d ^ 2) := by ring
    _ ≤ (1 / 8 : ℝ) ^ (m + 1) * 1 :=
      mul_le_mul_of_nonneg_left hfac hq_nonneg
    _ = (1 / 8 : ℝ) ^ (m + 1) := by ring
    _ ≤ (1 / 8 : ℝ) ^ m := hpow_le

end SAP.P018b.WH.W1.P.T19_L7

theorem SAP.P018b.WH.W1.T19_L7_proof : SAP.P018b.WH.W1.T19_L7 := by
  apply Summable.of_nonneg_of_le
    SAP.P018b.WH.W1.P.T19_L7.wholeRareHterm_nonneg
    SAP.P018b.WH.W1.P.T19_L7.wholeRareHterm_le_geom
  exact summable_geometric_of_norm_lt_one (by norm_num)

