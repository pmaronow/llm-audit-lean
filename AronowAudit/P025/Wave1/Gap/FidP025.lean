import AronowAudit.P025.P025_Interval

namespace AronowAudit.P025.Wave1
noncomputable section
open scoped BigOperators

/-- Every value between the endpoint ratios is attained at a feasible point
with an explicit parameter on the supplied segment, including its endpoints. -/
theorem ratio_segment_attains_certificate {ι : Type*} [Fintype ι] [Nonempty ι]
    (y a : ι → ℝ) (ha : ∀ i, 0 < a i) (γ : ℝ) (u v : ι → ℝ)
    (hu : normBox γ u) (hv : normBox γ v) (z : ℝ)
    (hz : ratio y a u ≤ z ∧ z ≤ ratio y a v) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
      normBox γ (fun i => (1 - t) * u i + t * v i) ∧
      ratio y a (fun i => (1 - t) * u i + t * v i) = z := by
  let w : ℝ → ι → ℝ := fun t i => (1 - t) * u i + t * v i
  have hw (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : normBox γ (w t) := by
    intro i
    have h1 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hu i).1)
    have h2 := mul_nonneg ht.1 (sub_nonneg.mpr (hv i).1)
    have h3 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hu i).2)
    have h4 := mul_nonneg ht.1 (sub_nonneg.mpr (hv i).2)
    dsimp [w]
    constructor <;> nlinarith
  let f : ℝ → ℝ := fun t => ratio y a (w t)
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div
    · change ContinuousOn (fun t => ∑ i, a i * ((1 - t) * u i + t * v i) * y i) _
      fun_prop
    · change ContinuousOn (fun t => ∑ i, a i * ((1 - t) * u i + t * v i)) _
      fun_prop
    · intro t ht
      exact (denominator_pos a (w t) ha (fun i => by linarith [(hw t ht i).1])).ne'
  have hf0 : f 0 = ratio y a u := by simp [f, w]
  have hf1 : f 1 = ratio y a v := by simp [f, w]
  have hz' : z ∈ Set.Icc (f 0) (f 1) := by simpa [hf0, hf1] using hz
  obtain ⟨t, ht, htz⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hf hz'
  exact ⟨t, ht, hw t ht, htz⟩

/-- The increment identity includes γ = 1; equality of the stationary and
outcome-test index sets is asserted under the additional strict bound. -/
theorem gamma_stationarity_certificate {n : ℕ} (hn : 0 < n)
    (y a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (γ : ℝ) (hγ : 1 ≤ γ) :
    (∀ k : Fin n,
      upperValue y a γ (k.val + 1) - upperValue y a γ k.val =
        (1 - γ) * a k * (y k - upperValue y a γ k.val) /
          (∑ i, a i * upperWeights γ (k.val + 1) i)) ∧
    (1 < γ →
      {k : Fin n | upperValue y a γ k.val ≥ upperValue y a γ (k.val + 1)} =
        {k : Fin n | upperValue y a γ k.val ≤ y k}) := by
  constructor
  · intro k
    exact threshold_increment hn a y ha 1 γ zero_lt_one
      (lt_of_lt_of_le zero_lt_one hγ) k
  · intro hstrict
    exact (strict_gamma_stationarity hn y a ha γ hstrict).2

end
end AronowAudit.P025.Wave1
