import AronowAudit.P004.Wave1.AreaSumBlueprint

namespace AronowAudit.P004.Wave1.AreaSum

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem a3_proof : A3 := by
  classical
  intro c
  have hupper (j : Fin 6) {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ bin c j) :
      dist x c ≤ (j : ℝ) + 1 := by
    by_cases hj : j.val = 0
    · have hj0 : j = 0 := Fin.ext hj
      subst j
      simpa [bin] using hx
    · exact (show (j : ℝ) < dist x c ∧ dist x c ≤ (j : ℝ) + 1 from
        by simpa only [bin, if_neg hj, Set.mem_setOf_eq] using hx).2
  have hlower (j : Fin 6) (hj : j.val ≠ 0) {x : EuclideanSpace ℝ (Fin 2)}
      (hx : x ∈ bin c j) : (j : ℝ) < dist x c := by
    exact (show (j : ℝ) < dist x c ∧ dist x c ≤ (j : ℝ) + 1 from
      by simpa only [bin, if_neg hj, Set.mem_setOf_eq] using hx).1
  have hdisj (j k : Fin 6) (hjk : j < k) : Disjoint (bin c j) (bin c k) := by
    apply Set.disjoint_left.mpr
    intro x hxj hxk
    have hk : k.val ≠ 0 := by omega
    have hgap : (j : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (show j.val + 1 ≤ k.val by omega)
    have hu := hupper j hxj
    have hl := hlower k hk hxk
    linarith
  constructor
  · ext x
    rw [Metric.mem_closedBall, Set.mem_iUnion]
    constructor
    · intro hx
      by_cases h0 : dist x c ≤ 1
      · exact ⟨0, by simpa [bin] using h0⟩
      by_cases h1 : dist x c ≤ 2
      · exact ⟨1, by norm_num [bin]; exact ⟨by linarith, h1⟩⟩
      by_cases h2 : dist x c ≤ 3
      · exact ⟨2, by norm_num [bin]; exact ⟨by linarith, h2⟩⟩
      by_cases h3 : dist x c ≤ 4
      · exact ⟨3, by norm_num [bin]; exact ⟨by linarith, h3⟩⟩
      by_cases h4 : dist x c ≤ 5
      · exact ⟨4, by norm_num [bin]; exact ⟨by linarith, h4⟩⟩
      · exact ⟨5, by norm_num [bin]; exact ⟨by linarith, hx⟩⟩
    · rintro ⟨j, hj⟩
      have hu := hupper j hj
      have hjle : (j : ℝ) ≤ 5 := by
        exact_mod_cast (show j.val ≤ 5 by omega)
      linarith
  · intro j k hjk
    rcases lt_or_gt_of_ne hjk with hlt | hlt
    · exact hdisj j k hlt
    · exact (hdisj k j hlt).symm

end
end AronowAudit.P004.Wave1.AreaSum
