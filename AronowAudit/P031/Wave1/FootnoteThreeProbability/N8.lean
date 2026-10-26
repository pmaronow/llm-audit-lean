import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint

namespace AronowAudit.P031.Wave1.FootnoteThreeProbability
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- An error event for the weighted sum is eventually contained in a union
of two error events at one fixed positive threshold. -/
theorem n8_proof : N8 := by
  classical
  intro hEC P F G H e1 e0 a b h hF hG hH he1 he0 ε hε
  let L : ℝ := |a| + |b| + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hFclose : ∀ᶠ n in atTop, |F (P n) - a| < 1 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hF 1 (by norm_num))
  have hGclose : ∀ᶠ n in atTop, |G (P n) - b| < 1 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hG 1 (by norm_num))
  have hFbound : ∀ᶠ n in atTop, |F (P n)| ≤ L := by
    filter_upwards [hFclose] with n hn
    have ht : |F (P n)| ≤ |F (P n) - a| + |a| := by
      simpa only [sub_add_cancel] using (abs_add_le (F (P n) - a) a)
    dsimp only [L]
    linarith [abs_nonneg b]
  have hGbound : ∀ᶠ n in atTop, |G (P n)| ≤ L := by
    filter_upwards [hGclose] with n hn
    have ht : |G (P n)| ≤ |G (P n) - b| + |b| := by
      simpa only [sub_add_cancel] using (abs_add_le (G (P n) - b) b)
    dsimp only [L]
    linarith [abs_nonneg a]
  have hHsmall : ∀ᶠ n in atTop, |H (P n) - h| < ε / 3 := by
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp hH (ε / 3) (by positivity))
  let δ : ℝ := ε / (3 * L)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hL)
  have hLδ : L * δ = ε / 3 := by
    dsimp only [δ]
    field_simp [hL.ne'] <;> ring
  have hE1 : Tendsto (fun n => eventProbability (P n) (fun s => δ < |e1 (P n) s|))
      atTop (nhds (0 : ℝ)) := by
    simpa only [sub_zero] using (he1 δ hδ)
  have hE0 : Tendsto (fun n => eventProbability (P n) (fun s => δ < |e0 (P n) s|))
      atTop (nhds (0 : ℝ)) := by
    simpa only [sub_zero] using (he0 δ hδ)
  have hUpper : Tendsto (fun n =>
      eventProbability (P n) (fun s => δ < |e1 (P n) s|) +
      eventProbability (P n) (fun s => δ < |e0 (P n) s|)) atTop (nhds (0 : ℝ)) := by
    simpa only [add_zero] using hE1.add hE0
  have hEvent : ∀ᶠ n in atTop,
      eventProbability (P n) (fun s =>
        ε < |F (P n) * e1 (P n) s + G (P n) * e0 (P n) s + H (P n) - h|) ≤
      eventProbability (P n) (fun s => δ < |e1 (P n) s|) +
      eventProbability (P n) (fun s => δ < |e0 (P n) s|) := by
    filter_upwards [hFbound, hGbound, hHsmall] with n hFn hGn hHn
    calc
      _ ≤ eventProbability (P n)
          (fun s => δ < |e1 (P n) s| ∨ δ < |e0 (P n) s|) := by
        apply (hEC (P n)).2.1
        intro s _ hlarge
        by_contra hnot
        have he1small : |e1 (P n) s| ≤ δ :=
          le_of_not_gt (fun he => hnot (Or.inl he))
        have he0small : |e0 (P n) s| ≤ δ :=
          le_of_not_gt (fun he => hnot (Or.inr he))
        have ht : |F (P n) * e1 (P n) s| ≤ L * δ := by
          rw [abs_mul]
          calc
            _ ≤ L * |e1 (P n) s| := mul_le_mul_of_nonneg_right hFn (abs_nonneg _)
            _ ≤ L * δ := mul_le_mul_of_nonneg_left he1small hL.le
        have hc : |G (P n) * e0 (P n) s| ≤ L * δ := by
          rw [abs_mul]
          calc
            _ ≤ L * |e0 (P n) s| := mul_le_mul_of_nonneg_right hGn (abs_nonneg _)
            _ ≤ L * δ := mul_le_mul_of_nonneg_left he0small hL.le
        have htri :
            |F (P n) * e1 (P n) s + G (P n) * e0 (P n) s + H (P n) - h| ≤
            |F (P n) * e1 (P n) s| + |G (P n) * e0 (P n) s| + |H (P n) - h| := by
          calc
            _ = |(F (P n) * e1 (P n) s + G (P n) * e0 (P n) s) + (H (P n) - h)| := by
              congr 1 <;> ring
            _ ≤ |F (P n) * e1 (P n) s + G (P n) * e0 (P n) s| + |H (P n) - h| :=
              abs_add_le _ _
            _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
        linarith
      _ ≤ _ := (hEC (P n)).2.2.1 _ _
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
  · exact Filter.Eventually.of_forall (fun n => (hEC (P n)).1 _)
  · exact hEvent

end
end AronowAudit.P031.Wave1.FootnoteThreeProbability
