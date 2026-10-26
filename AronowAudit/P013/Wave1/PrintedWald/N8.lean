import AronowAudit.P013.Wave1.PrintedWaldBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Both potential outcomes at a unit have square one. -/
theorem wOutcome_sq (n : ℕ) (i : Fin (n + 1)) (d : Fin 2) :
    (wPop n).outcome i d ^ 2 = 1 := by
  change (if i.val % 2 = 0 then (1 : ℝ) else -1) ^ 2 = 1
  split_ifs <;> norm_num

/-- Distinct units using one coordinate have opposite parity and opposite outcomes. -/
theorem wOutcome_mul_same_pair (n : ℕ) (i j : Fin (n + 1)) (d e : Fin 2)
    (hpair : i.val / 2 = j.val / 2) (hne : i ≠ j) :
    (wPop n).outcome i d * (wPop n).outcome j e = -1 := by
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  change (if i.val % 2 = 0 then (1 : ℝ) else -1) *
    (if j.val % 2 = 0 then (1 : ℝ) else -1) = -1
  by_cases hi : i.val % 2 = 0
  · have hj : j.val % 2 ≠ 0 := by omega
    simp [hi, hj]
  · have hj : j.val % 2 = 0 := by omega
    simp [hi, hj]

/-- Every distinct-unit joint at the even sizes is strictly positive. -/
theorem wDistinct_joint_pos (h7 : N7) (k : ℕ) (i j : Fin (2 * k + 3 + 1))
    (d e : Fin 2) (hne : i ≠ j) :
    0 < jointPi (wPop (2 * k + 3)) i j d e := by
  obtain ⟨he0, he1⟩ := pairEpsilon_even_bounds k
  rw [h7 k i j d e hne]
  split_ifs <;> linarith

/-- The two different exposures cannot both occur at the same unit. -/
theorem wJoint_self_cross_zero (n : ℕ) (i : Fin (n + 1)) :
    jointPi (wPop n) i i 1 0 = 0 := by
  have hzero : (fun z => indicator (wPop n).exposure i 1 z *
      indicator (wPop n).exposure i 0 z) = (fun _ => (0 : ℝ)) := by
    funext z
    by_cases hi : (wPop n).exposure z i = 1
    · have hi0 : (wPop n).exposure z i ≠ 0 := by rw [hi]; decide
      simp [indicator, hi, hi0]
    · simp [indicator, hi]
  unfold jointPi
  rw [hzero, expectation_const]

/-- On the split event every off-diagonal same-exposure pair term is zero. -/
theorem wSameExposure_pairTerm_zero (h1 : N1) (h7 : N7) (k : ℕ)
    (z : Fin (wSupport (2 * k + 3))) (hz : wSplit (2 * k + 3) z)
    (i j : Fin (2 * k + 3 + 1)) (d : Fin 2) (hne : i ≠ j) :
    pairTerm (wPop (2 * k + 3)) i j d d z = 0 := by
  classical
  by_cases hpair : i.val / 2 = j.val / 2
  · have hsplit := hz i j hpair hne
    have hmask : indicator (wPop (2 * k + 3)).exposure i d z *
        indicator (wPop (2 * k + 3)).exposure j d z = 0 := by
      by_cases hi : (wPop (2 * k + 3)).exposure z i = d
      · have hj : (wPop (2 * k + 3)).exposure z j ≠ d :=
          fun hj => hsplit (hi.trans hj.symm)
        simp [indicator, hi, hj]
      · simp [indicator, hi]
    unfold pairTerm
    rw [hmask]
    simp
  · have hjoint : jointPi (wPop (2 * k + 3)) i j d d = 1 / 4 := by
      rw [h7 k i j d d hne, if_neg hpair]
    unfold pairTerm
    rw [hjoint, h1 (2 * k + 3) i d, h1 (2 * k + 3) j d]
    norm_num

/-- Expression (7) consists only of its diagonal on the all-split event. -/
theorem n8_proof : N8 := by
  classical
  intro h1 h7 k z hz d
  have hoff : (∑ i, ∑ j ∈ univ.erase i,
      pairTerm (wPop (2 * k + 3)) i j d d z) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j hj
    exact wSameExposure_pairTerm_zero h1 h7 k z hz i j d (mem_erase.mp hj).1.symm
  unfold varianceHT
  rw [hoff, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [h1 (2 * k + 3) i d, div_pow, wOutcome_sq]
  ring

end

end AronowAudit.P013.Wave1.PrintedWald
