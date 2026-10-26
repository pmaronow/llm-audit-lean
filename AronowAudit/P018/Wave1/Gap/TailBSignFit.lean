import AronowAudit.P018.Wave1.Gap.TailBSignSample

/-! Uniform fitted-response and residual bounds, including singular sign samples. -/
noncomputable section
namespace AronowAudit.P018.Wave1.TailBSign
open Finset Matrix
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem tb05_response_bound {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i,(w i)^2=1)
    (d : Dyad N) : |tb05_response w d| ≤ 2 := by
  have ha (i : Fin N) : |w i|=1 := by
    rcases sq_eq_one_iff.1 (hw i) with h | h <;> rw [h] <;> norm_num
  exact (abs_add_le _ _).trans (by rw [ha,ha]; norm_num)

/-- Each of the two fitted groups has its sample response average whenever the
bread is nonsingular; this yields a bound independent of group size. -/
theorem tb05_fit_group_bound {N : ℕ} (z w : Fin N → ℝ)
    (hz : ∀ i,(z i)^2=1) (hw : ∀ i,(w i)^2=1)
    (hgram : (Dreal N)^2-(tb05_T z)^2 ≠ 0) (t : ℝ) (ht : t^2=1) :
    |tb05_fitA z w+t*tb05_fitB z w| ≤ 2 := by
  let D := Dreal N
  let T := tb05_T z
  have hweight (d : Dyad N) : 0 ≤ 1+t*z (firstUnit d)*z (secondUnit d) := by
    have h : (t*z (firstUnit d)*z (secondUnit d))^2=1 := by
      rw [mul_pow,mul_pow,ht,hz,hz]; ring
    rcases sq_eq_one_iff.1 h with h | h <;> linarith
  have hsum : (∑ d : Dyad N,(1+t*z (firstUnit d)*z (secondUnit d)))=D+t*T := by
    simp only [Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,printed_card_real,mul_one]
    rfl
  have hnonneg : 0 ≤ D+t*T := by
    rw [← hsum]
    exact Finset.sum_nonneg (fun d _ => hweight d)
  have hpos : 0 < D+t*T := by
    apply lt_of_le_of_ne hnonneg
    intro he
    apply hgram
    rcases sq_eq_one_iff.1 ht with ht | ht
    · rw [ht] at he
      have heq : Dreal N = -tb05_T z := by change 0 = Dreal N+1*tb05_T z at he; linarith
      rw [heq]
      ring
    · rw [ht] at he
      have heq : Dreal N = tb05_T z := by change 0 = Dreal N+(-1)*tb05_T z at he; linarith
      rw [heq]
      ring
  have hnormal : (D+t*T)*(tb05_fitA z w+t*tb05_fitB z w) =
      ((N:ℝ)-1)*(∑ i,w i)+t*((∑ i,z i)*(∑ i,z i*w i)-(∑ i,w i)) := by
    rcases sq_eq_one_iff.1 ht with ht | ht <;> rw [ht] <;>
      dsimp [tb05_fitA,tb05_fitB,D,T] <;> field_simp [hgram] <;> ring
  have hmixed : (∑ d : Dyad N,(1+t*z (firstUnit d)*z (secondUnit d))*tb05_response w d) =
      ((N:ℝ)-1)*(∑ i,w i)+t*((∑ i,z i)*(∑ i,z i*w i)-(∑ i,w i)) := by
    simp_rw [show ∀ d : Dyad N,(1+t*z (firstUnit d)*z (secondUnit d))*tb05_response w d =
      (w (firstUnit d)+w (secondUnit d))+t*(z (firstUnit d)*z (secondUnit d)*
        (w (firstUnit d)+w (secondUnit d))) from fun d => by dsimp [tb05_response]; ring]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,printed_pair_add,tb05_pair_mixed z w hz]
  have hb : |(D+t*T)*(tb05_fitA z w+t*tb05_fitB z w)| ≤ 2*(D+t*T) := by
    rw [hnormal,← hmixed,← hsum]
    calc
      _ ≤ ∑ d : Dyad N, |(1+t*z (firstUnit d)*z (secondUnit d))*tb05_response w d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d : Dyad N,2*(1+t*z (firstUnit d)*z (secondUnit d)) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [abs_mul,abs_of_nonneg (hweight d)]
        nlinarith [mul_le_mul_of_nonneg_left (tb05_response_bound w hw d) (hweight d)]
      _ = _ := by rw [Finset.mul_sum]
  rw [abs_mul,abs_of_pos hpos] at hb
  nlinarith

/-- Totalized OLS is zero on singular samples and otherwise fits two group means. -/
theorem tb05_all_sample_residual_bound {N : ℕ} (z w : Fin N → ℝ)
    (hz : ∀ i,(z i)^2=1) (hw : ∀ i,(w i)^2=1) (d : Dyad N) :
    |fittedResidual (tb05_design z) (tb05_response w) d| ≤ 4 := by
  by_cases hgram : (Dreal N)^2-(tb05_T z)^2=0
  · have hdet : (sampleGram (tb05_design z)).det=0 := by
      rw [tb05_sample_gram z hz,Matrix.det_fin_two]
      dsimp
      nlinarith [hgram]
    have hi : (sampleGram (tb05_design z))⁻¹=0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hdet]; simp)
    simp only [fittedResidual,sampleOLS,hi,Matrix.zero_mulVec]
    have he : dot (tb05_design z d) (0 : Vec 2)=0 := by simp [dot]
    rw [he,sub_zero]
    exact (tb05_response_bound w hw d).trans (by norm_num)
  · have ht : (z (firstUnit d)*z (secondUnit d))^2=1 := by
      rw [mul_pow,hz,hz]; ring
    have hb := tb05_fit_group_bound z w hz hw hgram
      (z (firstUnit d)*z (secondUnit d)) ht
    rw [tb05_fitted_residual z w hz hgram]
    have he : w (firstUnit d)+w (secondUnit d)-tb05_fitA z w-
        tb05_fitB z w*z (firstUnit d)*z (secondUnit d) =
        tb05_response w d-(tb05_fitA z w+z (firstUnit d)*z (secondUnit d)*tb05_fitB z w) := by
      dsimp [tb05_response]
      ring
    rw [he]
    calc
      _ ≤ |tb05_response w d|+|tb05_fitA z w+z (firstUnit d)*z (secondUnit d)*tb05_fitB z w| := by
        simpa only [sub_eq_add_neg,abs_neg] using
          abs_add_le (tb05_response w d) (-(tb05_fitA z w+z (firstUnit d)*z (secondUnit d)*tb05_fitB z w))
      _ ≤ 4 := by linarith [tb05_response_bound w hw d]

end AronowAudit.P018.Wave1.TailBSign
