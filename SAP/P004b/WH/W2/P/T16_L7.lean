import SAP.P004b.WH.W2.Leaves
import AronowAudit.P004.Wave1.Gap.GP0041B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T16_L7

open scoped Classical
noncomputable section

private theorem thin_sep_eq_witness (n : ℕ) (hn : 0 < n) (k : Fin n) :
    planeSeparation (thinPolygon n 0)
      (thinPolygon n ⟨k.val + 1, by omega⟩) =
        dist (planePoint 1 (min (2 * (k : ℝ) / (n : ℝ)) 1))
          (planePoint 2 (2 * (k : ℝ) / (n : ℝ))) := by
  let i : Fin (n + 1) := ⟨k.val + 1, by omega⟩
  let a : ℝ := 2 * (k : ℝ) / (n : ℝ)
  let g : ℝ := max 0 (a - 1)
  let p : EuclideanSpace ℝ (Fin 2) := planePoint 1 (min a 1)
  let q : EuclideanSpace ℝ (Fin 2) := planePoint 2 a
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi0 : i ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i] at hv
  have hiR : (i : ℝ) - 1 = (k : ℝ) := by simp [i]
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha2 : a < 2 := by
    dsimp [a]
    have hkR : (k : ℝ) < (n : ℝ) := by exact_mod_cast k.isLt
    apply (div_lt_iff₀ hnR).2
    nlinarith
  have hupper : a ≤ (2 * ((i : ℝ) - 1) + 1) / (n : ℝ) := by
    rw [hiR]
    dsimp [a]
    apply (div_le_div_iff_of_pos_right hnR).2
    linarith
  have hupper' : a ≤ (2 * (k : ℝ) + 1) / (n : ℝ) := by
    have hupper'' := hupper
    rw [hiR] at hupper''
    simpa [a] using hupper''
  have hp : p ∈ thinPolygon n 0 := by
    change (0 ≤ (1 : ℝ) ∧ 1 ≤ 1 ∧ 0 ≤ min a 1 ∧ min a 1 ≤ 1)
    exact ⟨by norm_num, by norm_num, le_min ha0 (by norm_num), min_le_right _ _⟩
  have hq : q ∈ thinPolygon n i := by
    simp only [thinPolygon, if_neg hi0, rectangle, Set.mem_setOf_eq]
    change (2 : ℝ) ≤ 2 ∧ 2 ≤ 2 + (n : ℝ) ∧
      (2 * ((i : ℝ) - 1) / (n : ℝ)) ≤ a ∧
      a ≤ (2 * ((i : ℝ) - 1) + 1) / (n : ℝ)
    rw [hiR]
    dsimp [a]
    exact ⟨le_rfl, by linarith, le_rfl, by simpa [a] using hupper'⟩
  have hpoint : ∀ x ∈ thinPolygon n 0, ∀ y ∈ thinPolygon n i,
      dist p q ≤ dist x y := by
    intro x hx y hy
    have hx' : 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 := by
      simpa [thinPolygon, rectangle] using hx
    have hy' : (2 : ℝ) ≤ y 0 ∧ y 0 ≤ 2 + (n : ℝ) ∧
        (2 * ((i : ℝ) - 1) / (n : ℝ)) ≤ y 1 ∧
        y 1 ≤ (2 * ((i : ℝ) - 1) + 1) / (n : ℝ) := by
      simpa [thinPolygon, hi0, rectangle] using hy
    have hylo : a ≤ y 1 := by
      rw [hiR] at hy'
      dsimp [a]
      exact hy'.2.2.1
    have hxcoord : 1 ≤ y 0 - x 0 := by linarith
    have hxsq : 1 ≤ (x 0 - y 0) ^ 2 := by
      nlinarith [sq_nonneg (y 0 - x 0 - 1)]
    have hysq : g ^ 2 ≤ (x 1 - y 1) ^ 2 := by
      by_cases ha : a ≤ 1
      · have hg : g = 0 := by
          dsimp [g]
          rw [max_eq_left (sub_nonpos.mpr ha)]
        rw [hg]
        nlinarith [sq_nonneg (x 1 - y 1)]
      · have ha' : 1 ≤ a := le_of_not_ge ha
        have hg : g = a - 1 := by
          dsimp [g]
          rw [max_eq_right (sub_nonneg.mpr ha')]
        have hgap : 0 ≤ y 1 - x 1 - (a - 1) := by
          linarith [hylo, hx'.2.2.2]
        rw [hg]
        nlinarith [mul_nonneg hgap (show 0 ≤ y 1 - x 1 + (a - 1) by linarith)]
    have hsq : (dist x y) ^ 2 ≥ (dist p q) ^ 2 := by
      rw [AronowAudit.P004.Wave1.spacing_dist_sq, AronowAudit.P004.Wave1.spacing_dist_sq]
      have hpsq : (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = 1 + g ^ 2 := by
        change (1 - 2 : ℝ) ^ 2 + (min a 1 - a) ^ 2 = 1 + g ^ 2
        by_cases ha : a ≤ 1
        · have hg : g = 0 := by
            dsimp [g]
            rw [max_eq_left (sub_nonpos.mpr ha)]
          rw [min_eq_left ha, hg]
          norm_num
        · have ha' : 1 ≤ a := le_of_not_ge ha
          have hg : g = a - 1 := by
            dsimp [g]
            rw [max_eq_right (sub_nonneg.mpr ha')]
          rw [min_eq_right ha', hg]
          norm_num
          ring
      have hxq : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 ≥ 1 + g ^ 2 := by linarith
      linarith
    by_contra hnot
    have hlt : dist x y < dist p q := lt_of_not_ge hnot
    have hsum : 0 < dist p q + dist x y := by
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_lt (dist_nonneg) hlt) (dist_nonneg)
    have hprod : 0 < (dist p q - dist x y) * (dist p q + dist x y) :=
      mul_pos (sub_pos.mpr hlt) hsum
    nlinarith
  have hSnonempty : ∃ r : ℝ,
      r ∈ {r | ∃ x ∈ thinPolygon n 0, ∃ y ∈ thinPolygon n i, dist x y = r} := by
    exact ⟨dist p q, p, hp, q, hq, rfl⟩
  have hlow : ∀ r ∈ {r : ℝ | ∃ x ∈ thinPolygon n 0, ∃ y ∈ thinPolygon n i,
      dist x y = r}, dist p q ≤ r := by
    rintro r ⟨x, hx, y, hy, rfl⟩
    exact hpoint x hx y hy
  change sInf {r : ℝ | ∃ x ∈ thinPolygon n 0, ∃ y ∈ thinPolygon n i,
      dist x y = r} = dist p q
  exact le_antisymm
    (csInf_le ⟨dist p q, hlow⟩ ⟨p, hp, q, hq, rfl⟩)
    (le_csInf hSnonempty hlow)

private theorem leaf_proof : SAP.P004b.WH.W2.T16_L7 := by
  intro n hn k
  let a : ℝ := 2 * (k : ℝ) / (n : ℝ)
  let g : ℝ := max 0 (a - 1)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hkR : (k : ℝ) < (n : ℝ) := by exact_mod_cast k.isLt
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha2 : a < 2 := by
    dsimp [a]
    apply (div_lt_iff₀ hnR).2
    nlinarith
  have hg0 : 0 ≤ g := le_max_left _ _
  have hg1 : g < 1 := by
    by_cases ha : a ≤ 1
    · dsimp [g]
      rw [max_eq_left (sub_nonpos.mpr ha)]
      norm_num
    · have ha' : 1 ≤ a := le_of_not_ge ha
      dsimp [g]
      rw [max_eq_right (sub_nonneg.mpr ha')]
      linarith
  have hsep := thin_sep_eq_witness n hn k
  have hdsq :
      (dist (planePoint 1 (min (2 * (k : ℝ) / (n : ℝ)) 1))
        (planePoint 2 (2 * (k : ℝ) / (n : ℝ)))) ^ 2 =
        1 + g ^ 2 := by
    change (dist (planePoint 1 (min a 1)) (planePoint 2 a)) ^ 2 = 1 + g ^ 2
    rw [AronowAudit.P004.Wave1.spacing_dist_sq]
    by_cases ha : a ≤ 1
    · have hg : g = 0 := by
        dsimp [g]
        rw [max_eq_left (sub_nonpos.mpr ha)]
      rw [hg, min_eq_left ha]
      simp [planePoint]
      ring
    · have ha' : 1 ≤ a := le_of_not_ge ha
      have hg : g = a - 1 := by
        dsimp [g]
        rw [max_eq_right (sub_nonneg.mpr ha')]
      rw [hg, min_eq_right ha']
      simp [planePoint]
      ring
  constructor
  · rw [hsep]
    exact dist_nonneg
  constructor
  · rw [hsep, hdsq]
  · rw [hsep, hdsq]
    have hprod : 0 < (1 - g) * (1 + g) :=
      mul_pos (sub_pos.mpr hg1) (by linarith)
    nlinarith

end
end SAP.P004b.WH.W2.P.T16_L7

theorem SAP.P004b.WH.W2.T16_L7_proof : SAP.P004b.WH.W2.T16_L7 := by
  exact SAP.P004b.WH.W2.P.T16_L7.leaf_proof
