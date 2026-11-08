import SAP.P004c.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004c.Bridge
open SAP.P004c MeasureTheory Filter
open scoped BigOperators Classical
noncomputable section

/-- Turn the exported component inequalities into their stated orders. -/
theorem component_rates (p b : ℝ) (R : ∀ N, CircleTable N)
    (B : ∀ N, Fin N → Finset (Fin N)) (D : ℕ) (hp : 0 < p ∧ p < 1)
    (hseq : ∀ᶠ N in atTop, (∀ i z, |R N i z| < b) ∧
      (∀ i, i ∈ B N i) ∧ maxDegree (B N) ≤ D) :
    Asymptotics.IsBigO atTop (fun N => htDiagonal p (R N)) (fun N => (N : ℝ)⁻¹) ∧
    ∀ a c : Bool, Asymptotics.IsBigO atTop
      (fun N => htPairCov p (R N) (B N) a c) (fun N => (N : ℝ)⁻¹) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound (b^2/p+b^2/(1-p))
    filter_upwards [hseq, eventually_gt_atTop 0] with N hseqN hN
    have hc : 0 ≤ htDiagonal p (R N) ∧
        htDiagonal p (R N) ≤ b^2/(N*p)+b^2/(N*(1-p)) ∧
        ∀ a c : Bool, |htPairCov p (R N) (B N) a c| ≤
          2*b^2*((maxDegree (B N) : ℝ)-1)/N :=
      AronowAudit.P004.ht_variance_components p b (R N) (B N) hN hp hseqN.1 hseqN.2.1
    rw [Real.norm_eq_abs, abs_of_nonneg hc.1]
    apply hc.2.1.trans_eq
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · intro a c
    apply Asymptotics.IsBigO.of_bound (2*b^2*(D : ℝ))
    filter_upwards [hseq, eventually_gt_atTop 0] with N hseqN hN
    have hc : 0 ≤ htDiagonal p (R N) ∧
        htDiagonal p (R N) ≤ b^2/(N*p)+b^2/(N*(1-p)) ∧
        ∀ a c : Bool, |htPairCov p (R N) (B N) a c| ≤
          2*b^2*((maxDegree (B N) : ℝ)-1)/N :=
      AronowAudit.P004.ht_variance_components p b (R N) (B N) hN hp hseqN.1 hseqN.2.1
    have hdeg : (maxDegree (B N) : ℝ)-1 ≤ D :=
      (sub_le_self _ zero_le_one).trans (Nat.cast_le.mpr hseqN.2.2)
    rw [Real.norm_eq_abs]
    calc
      _ ≤ 2*b^2*((maxDegree (B N) : ℝ)-1)/N := hc.2.2 a c
      _ ≤ (2*b^2*(D : ℝ))/N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdeg (by positivity))
          (Nat.cast_nonneg N)
      _ = _ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
        rfl

theorem diagonal_rate (p b : ℝ) (R : ∀ N, CircleTable N) (hp : 0 < p ∧ p < 1)
    (hseq : ∀ᶠ N in atTop, ∀ i z, |R N i z| < b) :
    Asymptotics.IsBigO atTop (fun N => htDiagonal p (R N)) (fun N => (N : ℝ)⁻¹) := by
  apply (component_rates p b R (fun _ i => {i}) 1 hp ?_).1
  filter_upwards [hseq] with N hN
  refine ⟨hN, fun i => Finset.mem_singleton_self i, ?_⟩
  exact Finset.sup_le (fun i _ => by simp)

/-- Restrict the exported denominator event to genuine, nonempty treated arms. -/
theorem denominator_rate (p : ℝ) (hp : 0 < p ∧ p < 1) :
    BigOp (fun _ _ => p) (denominatorError p) (fun N => (Real.sqrt N)⁻¹) := by
  intro ε hε
  obtain ⟨C, hC, htail⟩ :=
    AronowAudit.P004.Wave1.bernoulli_denominator_rate_proof p hp ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with N hN
  have hinc : ∀ z : Assignment N,
      C * |(Real.sqrt N)⁻¹| < |denominatorError p N z| →
        C * |(Real.sqrt N)⁻¹| < abs (abs ((N : ℝ)^2/(armCount z true)^2-1/p^2)) := by
    intro z hz
    by_cases h : 0 < armCount z true
    · simpa only [denominatorError, if_pos h] using hz
    · have hnonneg : 0 ≤ C * |(Real.sqrt N)⁻¹| := mul_nonneg hC.le (abs_nonneg _)
      simp only [denominatorError, if_neg h, abs_zero] at hz
      exact False.elim (not_lt_of_ge hnonneg hz)
  exact (AronowAudit.P004.Wave1.T34_prob_mono (fun _ => p) (fun _ => hp) _ _ hinc).trans_lt hN

end
end SAP.P004c.Bridge
