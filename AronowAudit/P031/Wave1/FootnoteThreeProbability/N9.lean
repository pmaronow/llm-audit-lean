import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint

namespace AronowAudit.P031.Wave1.FootnoteThreeProbability
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- A positive deterministic denominator can be bounded away from zero
on all sufficiently late rows. -/
theorem n9_proof : N9 := by
  classical
  intro hEC P X D U D0 hX hD hD0 ε hε
  have hD00 : D0 ≠ 0 := hD0.ne'
  have hDhalf : ∀ᶠ n in atTop, D0 / 2 < D (P n) :=
    Filter.Tendsto.eventually_const_lt (half_lt_self hD0) hD
  have hInv : Tendsto (fun n => (D (P n))⁻¹) atTop (nhds D0⁻¹) := hD.inv₀ hD00
  have hDet : Tendsto (fun n => U / D (P n) - U / D0) atTop (nhds (0 : ℝ)) := by
    have ht := (hInv.const_mul U).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => U * D0⁻¹) atTop (nhds (U * D0⁻¹)))
    simpa only [div_eq_mul_inv, sub_self] using ht
  have hSmall : ∀ᶠ n in atTop, |U / D (P n) - U / D0| < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero] using
      (Metric.tendsto_nhds.mp hDet (ε / 2) (by positivity))
  let δ : ℝ := ε * D0 / 4
  have hδ : 0 < δ := div_pos (mul_pos hε hD0) (by norm_num)
  have hThreshold : (2 / D0) * δ = ε / 2 := by
    dsimp only [δ]
    field_simp [hD00] <;> ring
  have hUpper : Tendsto (fun n => eventProbability (P n) (fun s => δ < |X (P n) s - U|))
      atTop (nhds (0 : ℝ)) := hX δ hδ
  have hEvent : ∀ᶠ n in atTop,
      eventProbability (P n) (fun s => ε < |X (P n) s / D (P n) - U / D0|) ≤
      eventProbability (P n) (fun s => δ < |X (P n) s - U|) := by
    filter_upwards [hDhalf, hSmall] with n hDn hDetn
    have hDn0 : 0 < D (P n) := lt_trans (half_pos hD0) hDn
    have hRecip : 1 / D (P n) ≤ 2 / D0 := by
      calc
        _ ≤ 1 / (D0 / 2) := one_div_le_one_div_of_le (half_pos hD0) hDn.le
        _ = _ := by field_simp [hD00] <;> ring
    apply (hEC (P n)).2.1
    intro s _ hlarge
    by_contra hnot
    have hxsmall : |X (P n) s - U| ≤ δ := le_of_not_gt hnot
    have hdiv : |(X (P n) s - U) / D (P n)| ≤ (2 / D0) * δ := by
      calc
        _ = (1 / D (P n)) * |X (P n) s - U| := by
          rw [abs_div, abs_of_pos hDn0]
          ring
        _ ≤ (2 / D0) * |X (P n) s - U| :=
          mul_le_mul_of_nonneg_right hRecip (abs_nonneg _)
        _ ≤ (2 / D0) * δ :=
          mul_le_mul_of_nonneg_left hxsmall (div_nonneg (by norm_num) hD0.le)
    have htri : |X (P n) s / D (P n) - U / D0| ≤
        |(X (P n) s - U) / D (P n)| + |U / D (P n) - U / D0| := by
      calc
        _ = |(X (P n) s - U) / D (P n) + (U / D (P n) - U / D0)| := by
          congr 1 <;> ring
        _ ≤ _ := abs_add_le _ _
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
  · exact Filter.Eventually.of_forall (fun n => (hEC (P n)).1 _)
  · exact hEvent

end
end AronowAudit.P031.Wave1.FootnoteThreeProbability
