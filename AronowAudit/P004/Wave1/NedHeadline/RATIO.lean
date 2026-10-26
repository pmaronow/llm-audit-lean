import AronowAudit.P004.Wave1.NedHeadlineBlueprint

universe u

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

theorem ratio_proof : RATIO := by
  intro N p R z hN hp hg1 hg0
  let B1 := (∑ i, bit (z i) * (R i z - barMu (fun _ => p) R true)) / (N * p)
  let B0 := (∑ i, (1 - bit (z i)) * (R i z - barMu (fun _ => p) R false)) /
    (N * (1 - p))
  let C1 := armCount z true / (N * p)
  let C0 := armCount z false / (N * (1 - p))
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 < 1 - p := sub_pos.mpr hp.2
  have hc1 : (1 / 2 : ℝ) ≤ C1 := by
    have h := (abs_le.mp hg1).1
    change -(1 / 2 : ℝ) ≤ C1 - 1 at h
    linarith
  have hc0 : (1 / 2 : ℝ) ≤ C0 := by
    have h := (abs_le.mp hg0).1
    change -(1 / 2 : ℝ) ≤ C0 - 1 at h
    linarith
  have hc1pos : 0 < C1 := lt_of_lt_of_le (by norm_num) hc1
  have hc0pos : 0 < C0 := lt_of_lt_of_le (by norm_num) hc0
  have hcount1 : 0 < armCount z true := by
    have h := (div_pos_iff).mp hc1pos
    rcases h with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (mul_pos hn hp.1).le) h.2)
  have hcount0 : 0 < armCount z false := by
    have h := (div_pos_iff).mp hc0pos
    rcases h with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (mul_pos hn hq).le) h.2)
  have hid := hajek_ratio_identity p R z hN hp hcount1 hcount0
  change hajek R z - ame (fun _ => p) R = B1 / C1 - B0 / C0 ∧
    linearHajek (fun _ => p) R z - ame (fun _ => p) R = B1 - B0 at hid
  have hrem : linearHajek (fun _ => p) R z - hajek R z =
      B1 * (C1 - 1) / C1 - B0 * (C0 - 1) / C0 := by
    have he : linearHajek (fun _ => p) R z - hajek R z =
        (B1 - B0) - (B1 / C1 - B0 / C0) := by linarith [hid.1, hid.2]
    rw [he]
    field_simp [hc1pos.ne', hc0pos.ne'] <;> ring
  have hbound (B C : ℝ) (hC : (1 / 2 : ℝ) ≤ C) :
      |B * (C - 1) / C| ≤ 2 * (|B| * |C - 1|) := by
    have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
    rw [abs_div, abs_mul, abs_of_pos hCpos, div_le_iff₀ hCpos]
    have hprod : 0 ≤ |B| * |C - 1| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hC hprod
    nlinarith [hmul]
  change |linearHajek (fun _ => p) R z - hajek R z| ≤
    2 * (|B1| * |C1 - 1| + |B0| * |C0 - 1|)
  rw [hrem]
  calc
    _ ≤ |B1 * (C1 - 1) / C1| + |B0 * (C0 - 1) / C0| := abs_sub _ _
    _ ≤ 2 * (|B1| * |C1 - 1|) + 2 * (|B0| * |C0 - 1|) :=
      add_le_add (hbound B1 C1 hc1) (hbound B0 C0 hc0)
    _ = _ := by ring

end
end AronowAudit.P004.Wave1.NedHeadline
