import AronowAudit.P004.Wave1.AreaSumBlueprint

namespace AronowAudit.P004.Wave1.AreaSum

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Distance to the closed unit disk, with an explicit radial nearest point. -/
theorem a1_proof : A1 := by
  intro c x
  classical
  by_cases hx : dist x c ≤ 1
  · rw [Metric.infDist_zero_of_mem (Metric.mem_closedBall.mpr hx),
      max_eq_right (sub_nonpos.mpr hx)]
  · have hρ : 1 < dist x c := lt_of_not_ge hx
    have hρpos : 0 < dist x c := lt_trans zero_lt_one hρ
    have hρne : dist x c ≠ 0 := ne_of_gt hρpos
    let y := c + (dist x c)⁻¹ • (x - c)
    have hyc : dist y c = 1 := by
      rw [dist_eq_norm]
      have hsub : y - c = (dist x c)⁻¹ • (x - c) := by dsimp [y]; abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρpos),
        ← dist_eq_norm, inv_mul_cancel₀ hρne]
    have hcoef : 0 ≤ 1 - (dist x c)⁻¹ := by
      have : (dist x c)⁻¹ ≤ 1 := (inv_le_one₀ hρpos).mpr hρ.le
      linarith
    have hxy : dist x y = dist x c - 1 := by
      rw [dist_eq_norm]
      have hsub : x - y = (1 - (dist x c)⁻¹) • (x - c) := by
        dsimp [y]
        rw [sub_smul, one_smul]
        abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef, ← dist_eq_norm]
      rw [sub_mul, one_mul, inv_mul_cancel₀ hρne]
    rw [max_eq_left (by linarith : 0 ≤ dist x c - 1)]
    apply le_antisymm
    · calc
        Metric.infDist x (Metric.closedBall c 1) ≤ dist x y :=
          Metric.infDist_le_dist_of_mem (Metric.mem_closedBall.mpr hyc.le)
        _ = dist x c - 1 := hxy
    · apply (Metric.le_infDist ⟨c, Metric.mem_closedBall_self (by norm_num)⟩).mpr
      intro z hz
      have hz' : dist z c ≤ 1 := Metric.mem_closedBall.mp hz
      have ht : dist x c ≤ dist x z + dist z c := dist_triangle x z c
      linarith

end
end AronowAudit.P004.Wave1.AreaSum
