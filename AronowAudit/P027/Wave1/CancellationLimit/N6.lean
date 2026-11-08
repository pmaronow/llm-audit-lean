import AronowAudit.P027.Wave1.CancellationLimitBlueprint

/-! Event containment for the generic perturbation estimate. No finiteness or
measurability of the functions is needed. -/

namespace AronowAudit.P027.Wave1.CancellationLimit

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable

theorem n6_proof : N6 := by
  intro Ξ _ μ B S T M _hSnonneg hTnonneg hestimate hS hT
  rw [tendstoInMeasure_iff_dist]
  intro δ hδ
  let C : ℝ := |M| + 1
  let t : ℝ := δ / (4 * C)
  let d : ℝ := 1 + 1 / t
  let u : ℝ := δ / (4 * d)
  have hC : 0 < C := by dsimp [C]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have htC : t * C = δ / 4 := by
    dsimp [t]
    field_simp [hC.ne'] <;> ring
  have hdu : d * u = δ / 4 := by
    dsimp [u]
    field_simp [hd.ne'] <;> ring
  have hSbound : ∀ᶠ n in atTop, S n ≤ C := by
    filter_upwards [(Metric.tendsto_nhds.mp hS) 1 zero_lt_one] with n hn
    have habs : |S n - M| < 1 := by simpa only [Real.dist_eq] using hn
    have hupper : S n - M < 1 := (abs_lt.mp habs).2
    change S n ≤ |M| + 1
    linarith [le_abs_self M]
  have hSclose : ∀ᶠ n in atTop, |S n - M| < δ / 2 := by
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp hS) (δ / 2) (by linarith)
  have hdom : ∀ᶠ n in atTop,
      μ {ξ | δ ≤ dist (B n ξ) (-M)} ≤ μ {ξ | u ≤ dist (T n ξ) 0} := by
    filter_upwards [hSbound, hSclose] with n hn hn'
    apply measure_mono
    intro ξ hξ
    change δ ≤ dist (B n ξ) (-M) at hξ
    change u ≤ dist (T n ξ) 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hTnonneg n ξ)]
    by_contra hnot
    have hTu : T n ξ < u := lt_of_not_ge hnot
    have hsmall : d * T n ξ < δ / 4 := by
      calc
        d * T n ξ < d * u := mul_lt_mul_of_pos_left hTu hd
        _ = δ / 4 := hdu
    have hBS : |B n ξ + S n| < δ / 2 := by
      calc
        |B n ξ + S n| ≤ t * S n + d * T n ξ := hestimate t ht n ξ
        _ ≤ t * C + d * T n ξ :=
          add_le_add (mul_le_mul_of_nonneg_left hn ht.le) le_rfl
        _ < δ / 2 := by rw [htC]; linarith
    have htriangle : |B n ξ + M| ≤ |B n ξ + S n| + |S n - M| := by
      calc
        |B n ξ + M| = |(B n ξ + S n) - (S n - M)| := by congr 1 <;> ring
        _ ≤ |B n ξ + S n| + |S n - M| := abs_sub _ _
    have hlarge : δ ≤ |B n ξ + M| := by
      simpa only [Real.dist_eq, sub_neg_eq_add] using hξ
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendstoInMeasure_iff_dist.mp hT) u hu)
    (Eventually.of_forall (fun _ => zero_le)) hdom

end
end AronowAudit.P027.Wave1.CancellationLimit
