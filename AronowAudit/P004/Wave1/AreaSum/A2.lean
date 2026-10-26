import AronowAudit.P004.Wave1.AreaSum.A1

namespace AronowAudit.P004.Wave1.AreaSum

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem a2_proof : A2 := by
  classical
  have hzero (r : ℝ) : max (r - 1) 0 = 0 ↔ r ≤ 1 := by
    constructor
    · intro h
      have := le_max_left (r - 1) 0
      rw [h] at this
      linarith
    · intro h
      exact max_eq_right (by linarith)
  have houter (r d : ℝ) (hd : 1 ≤ d) :
      d - 1 < max (r - 1) 0 ∧ max (r - 1) 0 ≤ d ↔ d < r ∧ r ≤ d + 1 := by
    by_cases hr : r ≤ 1
    · rw [max_eq_right (by linarith : r - 1 ≤ 0)]
      constructor <;> intro h <;> exfalso <;> linarith [h.1]
    · rw [max_eq_left (by linarith : 0 ≤ r - 1)]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hwhole (r : ℝ) : 0 ≤ max (r - 1) 0 ∧ max (r - 1) 0 ≤ 5 ↔ r ≤ 6 := by
    constructor
    · rintro ⟨-, h⟩
      have hlower : r - 1 ≤ max (r - 1) 0 := le_max_left _ _
      linarith
    · intro h
      exact ⟨le_max_right _ _, max_le (by linarith) (by norm_num)⟩
  constructor
  · intro i j
    by_cases hj : j.val = 0
    · ext x
      have hx : x ∈ region areaBinaryPopulation i ((j : ℕ) : ℝ) ↔
          max (dist x (areaBinaryCenter i) - 1) 0 ∈
            ((if ((j : ℕ) : ℝ) = 0 then ({0} : Set ℝ) else if ((j : ℕ) : ℝ) = 6 then Set.Icc 0 5
              else Set.Ioc (((j : ℕ) : ℝ) - 1) ((j : ℕ) : ℝ)) : Set ℝ) := by
        show Metric.infDist x (Metric.closedBall (areaBinaryCenter i) 1) ∈
            ((if ((j : ℕ) : ℝ) = 0 then ({0} : Set ℝ) else if ((j : ℕ) : ℝ) = 6 then Set.Icc 0 5
              else Set.Ioc (((j : ℕ) : ℝ) - 1) ((j : ℕ) : ℝ)) : Set ℝ) ↔ _
        rw [a1_proof]
      rw [hx]
      simp only [hj, Nat.cast_zero, ↓reduceIte, Set.mem_singleton_iff, bin,
        Metric.mem_closedBall]
      exact hzero (dist x (areaBinaryCenter i))
    · have hjpos : 1 ≤ j.val := by omega
      have hjr : 1 ≤ (j : ℝ) := by exact_mod_cast hjpos
      have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      have hj6 : (j : ℝ) ≠ 6 := by
        have hjlt : (j : ℝ) < 6 := by exact_mod_cast j.isLt
        linarith
      ext x
      change (Metric.infDist x (Metric.closedBall (areaBinaryCenter i) 1) ∈
        (if (j : ℝ) = 0 then {0} else if (j : ℝ) = 6 then Set.Icc 0 5
          else Set.Ioc ((j : ℝ) - 1) j)) ↔ x ∈ bin (areaBinaryCenter i) j
      rw [a1_proof]
      simpa only [if_neg hj0, if_neg hj6, Set.mem_Ioc, bin, if_neg hj,
        Set.mem_setOf_eq] using houter (dist x (areaBinaryCenter i)) j hjr
  · intro i
    ext x
    change (Metric.infDist x (Metric.closedBall (areaBinaryCenter i) 1) ∈
      (if (6 : ℝ) = 0 then {0} else if (6 : ℝ) = 6 then Set.Icc 0 5
        else Set.Ioc (6 - 1) 6)) ↔ dist x (areaBinaryCenter i) ≤ 6
    rw [a1_proof]
    simp only [if_neg (by norm_num : (6 : ℝ) ≠ 0), ↓reduceIte, Set.mem_Icc]
    exact hwhole (dist x (areaBinaryCenter i))

end
end AronowAudit.P004.Wave1.AreaSum
