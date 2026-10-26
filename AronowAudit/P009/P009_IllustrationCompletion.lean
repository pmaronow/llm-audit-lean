import AronowAudit.P009.P009_OneSourceCompletion

/-! Exact finite-law computations for the six-unit illustration. -/
namespace AronowAudit.P009.IllustrationConfidence
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem cons_at_one {n : ℕ} (b : Bool) (z : Assignment (n+1)) :
    (Fin.cons (α := fun _ : Fin (n+2) => Bool) b z) (1 : Fin (n+2)) = z 0 := by rfl
theorem cons_at_four {n : ℕ} (b : Bool) (z : Assignment (n+4)) :
    (Fin.cons (α := fun _ : Fin (n+5) => Bool) b z) (4 : Fin (n+5)) = z 3 := by rfl
theorem cons_at_five {n : ℕ} (b : Bool) (z : Assignment (n+5)) :
    (Fin.cons (α := fun _ : Fin (n+6) => Bool) b z) (5 : Fin (n+6)) = z 4 := by rfl

theorem illustration_davg : dAvg illustrationExperiment = 3 := by
  have h := OneSourceCompletion.source_davg (n := 6) (by omega) 4
    (by constructor <;> omega) (fun i => if i = 0 then -1/4 else 1)
  change (6 : ℝ) * dAvg illustrationExperiment = _ at h
  norm_num at h
  linarith

theorem illustration_B1 : B1 illustrationExperiment = 1/6 := by
  have h := (OneSourceCompletion.corrected_one_source_spillover_completed
    (n := 6) (by omega) 4 (by constructor <;> omega)
    (fun i => if i = 0 then -1/4 else 1)).2.2
  change B1 illustrationExperiment = _ at h
  norm_num at h
  exact h

theorem illustration_msq : msq illustrationExperiment = 1 := by
  norm_num [msq, effect, potential, illustrationExperiment, fairExperiment,
    oneSourceOutcome, mean, fairLaw, Fin.sum_univ_succ, sum_cube_succ,
    sum_cube_zero, Fintype.sum_bool, bit, Function.update]

theorem illustration_marginal (i : Fin 6) (b : Bool) :
    marginal illustrationExperiment i b = 1/2 :=
  SparseCompletion.fair_marginal _ _ i b

theorem illustration_vBER_mean :
    mean illustrationExperiment.design (vBER illustrationExperiment) = 229/144 := by
  unfold vBER
  simp only [illustration_marginal]
  norm_num [illustrationExperiment, fairExperiment, oneSourceOutcome, mean,
    fairLaw, Fin.sum_univ_succ, sum_cube_succ, sum_cube_zero, Fintype.sum_bool, bit,
    cons_at_one, cons_at_two, cons_at_three, cons_at_four, cons_at_five]

theorem illustration_ht_mean : mean illustrationExperiment.design (ht illustrationExperiment) = 1 := by
  unfold ht muHat
  simp only [illustration_marginal]
  norm_num [illustrationExperiment, fairExperiment, oneSourceOutcome, mean,
    fairLaw, Fin.sum_univ_succ, sum_cube_succ, sum_cube_zero, Fintype.sum_bool, bit,
    cons_at_one, cons_at_two, cons_at_three, cons_at_four, cons_at_five]

theorem illustration_ht_variance :
    var illustrationExperiment.design (ht illustrationExperiment) = 241/144 := by
  rw [variance_second_moment, illustration_ht_mean]
  unfold ht muHat
  simp only [illustration_marginal]
  norm_num [illustrationExperiment, fairExperiment, oneSourceOutcome, mean,
    fairLaw, Fin.sum_univ_succ, sum_cube_succ, sum_cube_zero, Fintype.sum_bool, bit,
    cons_at_one, cons_at_two, cons_at_three, cons_at_four, cons_at_five]

theorem ccov_second_moment {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (A : Ω → Prop) (X Y : Ω → ℝ) (hp : prob P A ≠ 0) :
    ccov P A X Y = cmean P A (fun z => X z * Y z) - cmean P A X * cmean P A Y := by
  have hsub (F G : Ω → ℝ) :
      cmean P A (fun z => F z - G z) = cmean P A F - cmean P A G := by
    unfold cmean
    rw [← sub_div, ← mean_sub]
    congr 2
    funext z
    split_ifs <;> ring
  have hmul (c : ℝ) (F : Ω → ℝ) :
      cmean P A (fun z => c * F z) = c * cmean P A F := by
    unfold cmean
    rw [← mul_div_assoc, ← mean_const_mul]
    congr 2
    funext z
    split_ifs <;> ring
  have hc (c : ℝ) : cmean P A (fun _ => c) = c := by
    unfold cmean
    have hh : mean P (fun z => if A z then c else 0) = c * prob P A := by
      change mean P (fun z => if A z then c else 0) =
        c * mean P (fun z => if A z then 1 else 0)
      rw [← mean_const_mul]
      congr 1
      funext z
      split_ifs <;> ring
    rw [hh, mul_div_cancel_right₀ _ hp]
  unfold ccov
  have he : (fun z => (X z - cmean P A X) * (Y z - cmean P A Y)) =
      (fun z => (X z * Y z - cmean P A Y * X z) -
        (cmean P A X * Y z - cmean P A X * cmean P A Y)) := by
    funext z
    ring
  rw [he, hsub, hsub, hsub, hmul, hmul, hc]
  ring

theorem illustration_pair_prob (i j : Fin 6) (hij : i ≠ j) (a b : Bool) :
    prob illustrationExperiment.design (fun z => z i = a ∧ z j = b) = 1/4 := by
  fin_cases i <;> fin_cases j <;> cases a <;> cases b
  all_goals first
    | exact False.elim (hij rfl)
    | norm_num [prob, mean, illustrationExperiment, fairExperiment, fairLaw,
        sum_cube_succ, sum_cube_zero, Fintype.sum_bool,
        cons_at_one, cons_at_two, cons_at_three, cons_at_four, cons_at_five]

theorem illustration_ccov (i j : Fin 6) (hij : i ≠ j) (a b : Bool) :
    ccov illustrationExperiment.design (fun z => z i = a ∧ z j = b)
      (illustrationExperiment.outcome i) (illustrationExperiment.outcome j) =
      if 0 < i.val ∧ i.val < 4 ∧ 0 < j.val ∧ j.val < 4 then bit a * bit b else 0 := by
  rw [ccov_second_moment _ _ _ _ (by rw [illustration_pair_prob i j hij a b]; norm_num)]
  fin_cases i <;> fin_cases j <;> cases a <;> cases b
  all_goals first
    | exact False.elim (hij rfl)
    | norm_num [cmean, prob, mean, illustrationExperiment, fairExperiment,
        oneSourceOutcome, fairLaw, sum_cube_succ, sum_cube_zero, Fintype.sum_bool,
        cons_at_one, cons_at_two, cons_at_three, cons_at_four, cons_at_five, bit]

theorem illustration_B2 : B2 illustrationExperiment = 1/3 := by
  unfold B2
  rw [illustration_davg]
  have hpair (i j : Fin 6) :
      (if j = i then 0 else ∑ a : Bool, ∑ b : Bool,
        (1 - 2 * bit a) * (1 - 2 * bit b) *
          ccov illustrationExperiment.design (fun z => z i = a ∧ z j = b)
            (illustrationExperiment.outcome i) (illustrationExperiment.outcome j)) =
      if i ≠ j ∧ 0 < i.val ∧ i.val < 4 ∧ 0 < j.val ∧ j.val < 4 then (1 : ℝ) else 0 := by
    by_cases hij : i = j
    · subst j; simp
    · simp only [Ne.symm hij, ite_false, illustration_ccov i j hij]
      split_ifs <;> norm_num [Fintype.sum_bool, bit] <;> tauto
  simp_rw [hpair]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

theorem one_source_pair_count_counterexample :
    Bernoulli illustrationExperiment ∧ dAvg illustrationExperiment = 3 ∧
    msq illustrationExperiment = 1 ∧ B1 illustrationExperiment = 1/6 ∧
    B2 illustrationExperiment = 1/3 ∧ (1/3:ℝ) ≠ (4:ℝ)*3/(6+4*3) ∧
    mean illustrationExperiment.design (vBER illustrationExperiment) = 229/144 ∧
    var illustrationExperiment.design (ht illustrationExperiment) = 241/144 ∧
    (6:ℝ)/dAvg illustrationExperiment *
      (mean illustrationExperiment.design (vBER illustrationExperiment) -
        var illustrationExperiment.design (ht illustrationExperiment)) = -1/6 ∧
    (-1/6:ℝ) ≠ (6-3-12)/18 := by
  refine ⟨SparseCompletion.fair_BER _ _, illustration_davg, illustration_msq,
    illustration_B1, illustration_B2, by norm_num, illustration_vBER_mean,
    illustration_ht_variance, ?_, by norm_num⟩
  rw [illustration_davg, illustration_vBER_mean, illustration_ht_variance]
  norm_num

end
end AronowAudit.P009.IllustrationConfidence

namespace AronowAudit.P009

/-- T21, Supplement B p. 8: the explicit six-unit illustration has B2=1/3
rather than the printed 2/3. Its exact expected normalized variance gap is
-1/6 rather than the printed center -1/2; the asymptotic arrow is not refuted. -/
theorem one_source_pair_count_counterexample :
    Bernoulli illustrationExperiment ∧ dAvg illustrationExperiment = 3 ∧
    msq illustrationExperiment = 1 ∧ B1 illustrationExperiment = 1/6 ∧
    B2 illustrationExperiment = 1/3 ∧ (1/3:ℝ) ≠ (4:ℝ)*3/(6+4*3) ∧
    mean illustrationExperiment.design (vBER illustrationExperiment) = 229/144 ∧
    var illustrationExperiment.design (ht illustrationExperiment) = 241/144 ∧
    (6:ℝ)/dAvg illustrationExperiment *
      (mean illustrationExperiment.design (vBER illustrationExperiment) -
        var illustrationExperiment.design (ht illustrationExperiment)) = -1/6 ∧
    (-1/6:ℝ) ≠ (6-3-12)/18 := by
  exact IllustrationConfidence.one_source_pair_count_counterexample

end AronowAudit.P009
