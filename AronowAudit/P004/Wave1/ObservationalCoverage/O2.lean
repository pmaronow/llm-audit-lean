import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

private theorem clip_bounds (q : ℝ) : (1 / 20 : ℝ) ≤ clip q ∧ clip q ≤ 19 / 20 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

private theorem logit_left_endpoint : logit (1 / 20 : ℝ) = -Real.log 19 := by
  rw [logit, show (1 / 20 : ℝ) / (1 - 1 / 20) = (19 : ℝ)⁻¹ by norm_num,
    Real.log_inv]

private theorem logit_right_endpoint : logit (19 / 20 : ℝ) = Real.log 19 := by
  rw [logit, show (19 / 20 : ℝ) / (1 - 19 / 20) = 19 by norm_num]

private theorem logit_mono {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) (hpq : p ≤ q) : logit p ≤ logit q := by
  have hp' : 0 < 1 - p := sub_pos.mpr hp1
  have hq' : 0 < 1 - q := sub_pos.mpr hq1
  apply (Real.log_le_log_iff (div_pos hp hp') (div_pos hq hq')).2
  apply (div_le_div_iff₀ hp' hq').2
  nlinarith

private theorem logit_clip_bounds (q : ℝ) :
    -Real.log 19 ≤ logit (clip q) ∧ logit (clip q) ≤ Real.log 19 := by
  obtain ⟨hl, hu⟩ := clip_bounds q
  have hp : 0 < clip q := lt_of_lt_of_le (by norm_num) hl
  have hp1 : clip q < 1 := lt_of_le_of_lt hu (by norm_num)
  constructor
  · calc
      -Real.log 19 = logit (1 / 20 : ℝ) := logit_left_endpoint.symm
      _ ≤ logit (clip q) := logit_mono (by norm_num) (by norm_num) hp hp1 hl
  · calc
      logit (clip q) ≤ logit (19 / 20 : ℝ) :=
        logit_mono hp hp1 (by norm_num) (by norm_num) hu
      _ = Real.log 19 := logit_right_endpoint

private theorem logistic_logit {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    logistic (logit p) = p := by
  have h1 : 0 < 1 - p := sub_pos.mpr hp1
  have he : Real.exp (logit p) = p / (1 - p) :=
    Real.exp_log (div_pos hp h1)
  unfold logistic
  rw [he]
  have hd : 0 < 1 + p / (1 - p) := by positivity
  apply (div_eq_iff hd.ne').2
  field_simp [h1.ne'] <;> ring

private theorem logistic_logit_clip (q : ℝ) : logistic (logit (clip q)) = clip q := by
  obtain ⟨hl, hu⟩ := clip_bounds q
  exact logistic_logit (lt_of_lt_of_le (by norm_num) hl)
    (lt_of_le_of_lt hu (by norm_num))

private theorem logistic_monotone : Monotone logistic := by
  intro x y hxy
  have hx : 0 < 1 + Real.exp x := by positivity
  have hy : 0 < 1 + Real.exp y := by positivity
  change Real.exp x / (1 + Real.exp x) ≤ Real.exp y / (1 + Real.exp y)
  apply (div_le_div_iff₀ hx hy).2
  have he : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
  nlinarith

private theorem logistic_left_endpoint : logistic (-Real.log 19) = (1 / 20 : ℝ) := by
  rw [logistic, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 19)] <;> norm_num

private theorem logistic_right_endpoint : logistic (Real.log 19) = (19 / 20 : ℝ) := by
  rw [logistic, Real.exp_log (by norm_num : (0 : ℝ) < 19)] <;> norm_num

private def scalarLogLikelihood (n K t : ℝ) : ℝ :=
  K * t - n * Real.log (1 + Real.exp t)

private theorem scalarLogLikelihood_hasDerivAt (n K t : ℝ) :
    HasDerivAt (scalarLogLikelihood n K) (K - n * logistic t) t := by
  have he : HasDerivAt (fun x : ℝ => 1 + Real.exp x) (Real.exp t) t :=
    (Real.hasDerivAt_exp t).const_add 1
  have hl : HasDerivAt (fun x : ℝ => Real.log (1 + Real.exp x))
      (Real.exp t / (1 + Real.exp t)) t :=
    he.log (by positivity)
  have h := ((hasDerivAt_id' t).const_mul K).sub (hl.const_mul n)
  have hfun : scalarLogLikelihood n K =
      fun y => K * y - n * Real.log (1 + Real.exp y) := rfl
  rw [hfun]
  convert h using 1
  rw [logistic, mul_one]

private theorem scalarLogLikelihood_mono (n K a b : ℝ)
    (hscore : ∀ t ∈ Set.Icc a b, 0 ≤ K - n * logistic t) :
    MonotoneOn (scalarLogLikelihood n K) (Set.Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · intro t ht
    exact (scalarLogLikelihood_hasDerivAt n K t).continuousAt.continuousWithinAt
  · intro t ht
    exact (scalarLogLikelihood_hasDerivAt n K t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(scalarLogLikelihood_hasDerivAt n K t).deriv]
    exact hscore t (interior_subset ht)

private theorem scalarLogLikelihood_antitone (n K a b : ℝ)
    (hscore : ∀ t ∈ Set.Icc a b, K - n * logistic t ≤ 0) :
    AntitoneOn (scalarLogLikelihood n K) (Set.Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · intro t ht
    exact (scalarLogLikelihood_hasDerivAt n K t).continuousAt.continuousWithinAt
  · intro t ht
    exact (scalarLogLikelihood_hasDerivAt n K t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(scalarLogLikelihood_hasDerivAt n K t).deriv]
    exact hscore t (interior_subset ht)

theorem o2_proof : O2 := by
  refine ⟨logit_clip_bounds, logistic_logit_clip, ?_⟩
  intro n K hn hK hKn θ hθl hθu
  change scalarLogLikelihood n K θ ≤
    scalarLogLikelihood n K (logit (clip (K / n)))
  let q : ℝ := K / n
  have hnq : n * q = K := by
    dsimp only [q]
    field_simp [hn.ne'] <;> ring
  change scalarLogLikelihood n K θ ≤ scalarLogLikelihood n K (logit (clip q))
  by_cases hlow : q ≤ (1 / 20 : ℝ)
  · have hclip : clip q = (1 / 20 : ℝ) := by
      exact max_eq_left ((min_le_right _ _).trans hlow)
    rw [hclip, logit_left_endpoint]
    have ha : AntitoneOn (scalarLogLikelihood n K)
        (Set.Icc (-Real.log 19) (Real.log 19)) := by
      apply scalarLogLikelihood_antitone
      intro t ht
      have hpt : (1 / 20 : ℝ) ≤ logistic t := by
        rw [← logistic_left_endpoint]
        exact logistic_monotone ht.1
      have hqpt : q ≤ logistic t := hlow.trans hpt
      have hm := mul_le_mul_of_nonneg_left hqpt hn.le
      rw [hnq] at hm
      linarith
    exact ha ⟨le_rfl, hθl.trans hθu⟩ ⟨hθl, hθu⟩ hθl
  · by_cases hhigh : (19 / 20 : ℝ) ≤ q
    · have hclip : clip q = (19 / 20 : ℝ) := by
        unfold clip
        rw [min_eq_left hhigh, max_eq_right (by norm_num : (1 / 20 : ℝ) ≤ 19 / 20)]
      rw [hclip, logit_right_endpoint]
      have hm : MonotoneOn (scalarLogLikelihood n K)
          (Set.Icc (-Real.log 19) (Real.log 19)) := by
        apply scalarLogLikelihood_mono
        intro t ht
        have hpt : logistic t ≤ (19 / 20 : ℝ) := by
          rw [← logistic_right_endpoint]
          exact logistic_monotone ht.2
        have hptq : logistic t ≤ q := hpt.trans hhigh
        have hmul := mul_le_mul_of_nonneg_left hptq hn.le
        rw [hnq] at hmul
        linarith
      exact hm ⟨hθl, hθu⟩ ⟨hθl.trans hθu, le_rfl⟩ hθu
    · have hql : (1 / 20 : ℝ) ≤ q := (lt_of_not_ge hlow).le
      have hqu : q ≤ (19 / 20 : ℝ) := (lt_of_not_ge hhigh).le
      have hclip : clip q = q := by
        unfold clip
        rw [min_eq_right hqu, max_eq_right hql]
      have htbox := logit_clip_bounds q
      have htprob : logistic (logit (clip q)) = q := by
        rw [logistic_logit_clip, hclip]
      by_cases hθt : θ ≤ logit (clip q)
      · have hm : MonotoneOn (scalarLogLikelihood n K)
            (Set.Icc (-Real.log 19) (logit (clip q))) := by
          apply scalarLogLikelihood_mono
          intro t ht
          have hpt : logistic t ≤ q := by
            rw [← htprob]
            exact logistic_monotone ht.2
          have hmul := mul_le_mul_of_nonneg_left hpt hn.le
          rw [hnq] at hmul
          linarith
        exact hm ⟨hθl, hθt⟩ ⟨htbox.1, le_rfl⟩ hθt
      · have htθ : logit (clip q) ≤ θ := (lt_of_not_ge hθt).le
        have ha : AntitoneOn (scalarLogLikelihood n K)
            (Set.Icc (logit (clip q)) (Real.log 19)) := by
          apply scalarLogLikelihood_antitone
          intro t ht
          have hpt : q ≤ logistic t := by
            rw [← htprob]
            exact logistic_monotone ht.1
          have hmul := mul_le_mul_of_nonneg_left hpt hn.le
          rw [hnq] at hmul
          linarith
        exact ha ⟨le_rfl, htbox.2⟩ ⟨htθ, hθu⟩ htθ

end
end AronowAudit.P004.Wave1.ObservationalCoverage
