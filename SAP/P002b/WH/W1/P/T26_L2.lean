import SAP.P002b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b.WH.W1.P.T26_L2

open SAP.P002b

theorem positive_variance_order (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (absStudent a u ≤ absStudent b v) ↔ a ^ 2 * v - b ^ 2 * u ≤ 0 := by
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hv0 : v ≠ 0 := ne_of_gt hv
  rw [absStudent, if_neg hu0, absStudent, if_neg hv0]
  rw [ENNReal.ofReal_le_ofReal_iff (div_nonneg (abs_nonneg b) (Real.sqrt_nonneg v))]
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hu) (Real.sqrt_pos.mpr hv)]
  have hleft : 0 ≤ |a| * Real.sqrt v := mul_nonneg (abs_nonneg a) (Real.sqrt_nonneg v)
  have hright : 0 ≤ |b| * Real.sqrt u := mul_nonneg (abs_nonneg b) (Real.sqrt_nonneg u)
  rw [← sq_le_sq₀ hleft hright]
  rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hv.le, sq_abs, Real.sq_sqrt hu.le]
  simpa only [sub_nonpos]

theorem ofReal_abs_div_le_zero_iff (a u : ℝ) (hu : 0 < u) :
    ENNReal.ofReal (|a| / Real.sqrt u) ≤ 0 ↔ a = 0 := by
  rw [← ENNReal.ofReal_zero, ENNReal.ofReal_le_ofReal_iff (le_rfl : 0 ≤ (0 : ℝ))]
  constructor
  · intro h
    have hn : 0 ≤ |a| / Real.sqrt u := div_nonneg (abs_nonneg a) (Real.sqrt_nonneg u)
    have hz : |a| / Real.sqrt u = 0 := le_antisymm h hn
    have hs : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
    have habs : |a| = 0 := by
      rcases (div_eq_zero_iff.mp hz) with h | h
      · exact h
      · exact False.elim (hs h)
    exact abs_eq_zero.mp habs
  · intro h
    simp [h]

theorem student_order_stable (a a' u u' b b' v v' : ℝ)
    (hu : 0 ≤ u) (hu' : 0 ≤ u') (hv : 0 ≤ v) (hv' : 0 ≤ v')
    (ha0 : a = 0 ↔ a' = 0) (hu0 : u = 0 ↔ u' = 0)
    (hb0 : b = 0 ↔ b' = 0) (hv0 : v = 0 ↔ v' = 0)
    (hc : a ^ 2 * v - b ^ 2 * u ≤ 0 ↔ a' ^ 2 * v' - b' ^ 2 * u' ≤ 0) :
    (absStudent a u ≤ absStudent b v) ↔ (absStudent a' u' ≤ absStudent b' v') := by
  by_cases huZ : u = 0
  · have hu'Z : u' = 0 := hu0.mp huZ
    by_cases hvZ : v = 0
    · have hv'Z : v' = 0 := hv0.mp hvZ
      simp [absStudent, huZ, hu'Z, hvZ, hv'Z, ha0, hb0]
    · have hvPos : 0 < v := lt_of_le_of_ne hv (Ne.symm hvZ)
      have hv'Ne : v' ≠ 0 := fun h => hvZ (hv0.mpr h)
      have hv'Pos : 0 < v' := lt_of_le_of_ne hv' (Ne.symm hv'Ne)
      have hleft : (absStudent a u ≤ absStudent b v) ↔ a = 0 := by
        constructor
        · intro h
          by_contra ha
          have htop : absStudent a u = ⊤ := by simp [absStudent, huZ, ha]
          have hfinite : absStudent b v ≠ ⊤ := by simp [absStudent, hvZ]
          rw [htop] at h
          exact hfinite (top_le_iff.mp h)
        · intro ha
          simp [absStudent, huZ, hvZ, ha]
      have hright : (absStudent a' u' ≤ absStudent b' v') ↔ a' = 0 := by
        constructor
        · intro h
          by_contra ha
          have htop : absStudent a' u' = ⊤ := by simp [absStudent, hu'Z, ha]
          have hfinite : absStudent b' v' ≠ ⊤ := by simp [absStudent, hv'Ne]
          rw [htop] at h
          exact hfinite (top_le_iff.mp h)
        · intro ha
          simp [absStudent, hu'Z, hv'Ne, ha]
      exact hleft.trans (ha0.trans hright.symm)
  · have huPos : 0 < u := lt_of_le_of_ne hu (Ne.symm huZ)
    have hu'Ne : u' ≠ 0 := fun h => huZ (hu0.mpr h)
    have hu'Pos : 0 < u' := lt_of_le_of_ne hu' (Ne.symm hu'Ne)
    by_cases hvZ : v = 0
    · have hv'Z : v' = 0 := hv0.mp hvZ
      by_cases hbZ : b = 0
      · have hb'Z : b' = 0 := hb0.mp hbZ
        have hleft : (absStudent a u ≤ absStudent b v) ↔ a = 0 := by
          simp [absStudent, huZ, hvZ, hbZ,
            SAP.P002b.WH.W1.P.T26_L2.ofReal_abs_div_le_zero_iff a u huPos]
        have hright : (absStudent a' u' ≤ absStudent b' v') ↔ a' = 0 := by
          simp [absStudent, hu'Ne, hv'Z, hb'Z,
            SAP.P002b.WH.W1.P.T26_L2.ofReal_abs_div_le_zero_iff a' u' hu'Pos]
        exact hleft.trans (ha0.trans hright.symm)
      · have hb'Ne : b' ≠ 0 := fun h => hbZ (hb0.mpr h)
        simp [absStudent, huZ, hu'Ne, hvZ, hv'Z, hbZ, hb'Ne]
    · have hvPos : 0 < v := lt_of_le_of_ne hv (Ne.symm hvZ)
      have hv'Ne : v' ≠ 0 := fun h => hvZ (hv0.mpr h)
      have hv'Pos : 0 < v' := lt_of_le_of_ne hv' (Ne.symm hv'Ne)
      exact (positive_variance_order a b u v huPos hvPos).trans
        (hc.trans (positive_variance_order a' b' u' v' hu'Pos hv'Pos).symm)

theorem eval_le_zero_iff_of_sign (p : Polynomial ℝ) (x y : ℝ)
    (hs : (Polynomial.eval x p < 0 ↔ Polynomial.eval y p < 0) ∧
      (Polynomial.eval x p = 0 ↔ Polynomial.eval y p = 0)) :
    (Polynomial.eval x p ≤ 0 ↔ Polynomial.eval y p ≤ 0) := by
  constructor
  · intro h
    rcases (le_iff_lt_or_eq.mp h) with hlt | heq
    · exact le_of_lt (hs.1.mp hlt)
    · exact le_of_eq (hs.2.mp heq)
  · intro h
    rcases (le_iff_lt_or_eq.mp h) with hlt | heq
    · exact le_of_lt (hs.1.mpr hlt)
    · exact le_of_eq (hs.2.mpr heq)

end SAP.P002b.WH.W1.P.T26_L2

theorem SAP.P002b.WH.W1.T26_L2_proof : SAP.P002b.WH.W1.T26_L2 := by
  intro hL1 ι inst t v hv
  let family : ((ι ⊕ ι) ⊕ (ι × ι)) → Polynomial ℝ := fun k =>
    match k with
    | Sum.inl (Sum.inl i) => t i
    | Sum.inl (Sum.inr i) => v i
    | Sum.inr (i, j) => (t i) ^ 2 * (v j) - (t j) ^ 2 * (v i)
  obtain ⟨cuts, hcuts⟩ := hL1 _ family
  refine ⟨cuts, ?_⟩
  intro x y hxy i j
  have ht := hcuts x y hxy (Sum.inl (Sum.inl i))
  have hvv := hcuts x y hxy (Sum.inl (Sum.inr i))
  have htb := hcuts x y hxy (Sum.inl (Sum.inl j))
  have hvb := hcuts x y hxy (Sum.inl (Sum.inr j))
  have hcross := hcuts x y hxy (Sum.inr (i, j))
  have ht0 : Polynomial.eval x (t i) = 0 ↔ Polynomial.eval y (t i) = 0 := by
    simpa [family] using ht.2
  have hv0 : Polynomial.eval x (v i) = 0 ↔ Polynomial.eval y (v i) = 0 := by
    simpa [family] using hvv.2
  have hb0 : Polynomial.eval x (t j) = 0 ↔ Polynomial.eval y (t j) = 0 := by
    simpa [family] using htb.2
  have hvb0 : Polynomial.eval x (v j) = 0 ↔ Polynomial.eval y (v j) = 0 := by
    simpa [family] using hvb.2
  have hc0 : (Polynomial.eval x (family (Sum.inr (i, j))) ≤ 0 ↔
      Polynomial.eval y (family (Sum.inr (i, j))) ≤ 0) :=
    SAP.P002b.WH.W1.P.T26_L2.eval_le_zero_iff_of_sign _ _ _ hcross
  have hc :
      (Polynomial.eval x (t i) ^ 2 * Polynomial.eval x (v j) -
          Polynomial.eval x (t j) ^ 2 * Polynomial.eval x (v i) ≤ 0) ↔
      (Polynomial.eval y (t i) ^ 2 * Polynomial.eval y (v j) -
          Polynomial.eval y (t j) ^ 2 * Polynomial.eval y (v i) ≤ 0) := by
    simpa [family, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow] using hc0
  exact SAP.P002b.WH.W1.P.T26_L2.student_order_stable
    (Polynomial.eval x (t i)) (Polynomial.eval y (t i))
    (Polynomial.eval x (v i)) (Polynomial.eval y (v i))
    (Polynomial.eval x (t j)) (Polynomial.eval y (t j))
    (Polynomial.eval x (v j)) (Polynomial.eval y (v j))
    (hv i x) (hv i y) (hv j x) (hv j y) ht0 hv0 hb0 hvb0 hc
