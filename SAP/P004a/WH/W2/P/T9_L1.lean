import SAP.P004a.WH.W2.Leaves
import Mathlib.Analysis.Convex.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T9_L1

lemma logistic_hasDerivAt (t : ℝ) :
    HasDerivAt SAP.P004a.logistic
      (Real.exp t / (1 + Real.exp t)^2) t := by
  change HasDerivAt (fun x : ℝ => Real.exp x / (1 + Real.exp x)) _ t
  have he : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have hd : HasDerivAt (fun x : ℝ => 1 + Real.exp x) (Real.exp t) t :=
    he.const_add 1
  have hq := he.div hd (by positivity : 1 + Real.exp t ≠ 0)
  convert hq using 1 <;> ring

lemma score_hasDerivAt (N : ℕ) (z : SAP.P004a.Assignment N) (t : ℝ) :
    HasDerivAt (fun s => SAP.P004a.armCount z true - (N : ℝ) * SAP.P004a.logistic s)
      (-(N : ℝ) * Real.exp t / (1 + Real.exp t)^2) t := by
  have h := (hasDerivAt_const t (SAP.P004a.armCount z true)).sub
    ((logistic_hasDerivAt t).const_mul (N : ℝ))
  convert h using 1 <;> ring

lemma score_deriv_neg (N : ℕ) (hN : 0 < N) (t : ℝ) :
    -(N : ℝ) * Real.exp t / (1 + Real.exp t)^2 < 0 := by
  have hp : 0 < (N : ℝ) * Real.exp t / (1 + Real.exp t)^2 := by
    apply div_pos
    · exact mul_pos (Nat.cast_pos.mpr hN) (Real.exp_pos t)
    · positivity
  have hn := neg_lt_zero.mpr hp
  convert hn using 1 <;> ring

lemma logistic_strictMono : StrictMono SAP.P004a.logistic :=
  strictMono_of_hasDerivAt_pos logistic_hasDerivAt (by
    intro t
    apply div_pos (Real.exp_pos t)
    positivity)

lemma likelihood_hasDerivAt (N : ℕ) (z : SAP.P004a.Assignment N) (t : ℝ) :
    HasDerivAt (SAP.P004a.boundaryLikelihood z)
      (SAP.P004a.armCount z true - (N : ℝ) * SAP.P004a.logistic t) t := by
  change HasDerivAt (fun s =>
    AronowAudit.P004.Wave1.t9b6_likelihood (N : ℝ) (SAP.P004a.armCount z true) s) _ t
  simpa [SAP.P004a.armCount, AronowAudit.P004.armCount,
    SAP.P004a.logistic, AronowAudit.P004.logistic] using
    AronowAudit.P004.Wave1.t9b6_likelihood_deriv (N : ℝ)
      (SAP.P004a.armCount z true) t

lemma logit_clip_of_interior {N : ℕ} (hN : 0 < N)
    (z : SAP.P004a.Assignment N)
    (hS : 0 < SAP.P004a.armCount z true)
    (hSN : SAP.P004a.armCount z true < N) :
    SAP.P004a.boundaryMLE z =
      min 1 (max 0 (Real.log ((SAP.P004a.armCount z true / N) /
        (1 - SAP.P004a.armCount z true / N)))) := by
  let q : ℝ := SAP.P004a.armCount z true / N
  change SAP.P004a.boundaryMLE z = min 1 (max 0 (Real.log (q / (1-q))))
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos hS (Nat.cast_pos.mpr hN)
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one (Nat.cast_pos.mpr hN)]
    exact_mod_cast hSN
  have hlog : SAP.P004a.logistic (Real.log (q / (1-q))) = q := by
    simpa [SAP.P004a.logistic, AronowAudit.P004.logistic] using
      AronowAudit.P004.Wave1.t9b6_logistic_logit hq hq1
  have hlogone : (1/2 : ℝ) < SAP.P004a.logistic 1 := by
    have hzero : SAP.P004a.logistic 0 = (1/2 : ℝ) := by
      norm_num [SAP.P004a.logistic]
    have h := logistic_strictMono (show (0:ℝ) < 1 by norm_num)
    rw [hzero] at h
    exact h
  by_cases hlow : q ≤ (1 / 2 : ℝ)
  · have hlogle : Real.log (q / (1-q)) ≤ 0 := by
      by_contra hn
      have hn' : 0 < Real.log (q / (1-q)) := lt_of_not_ge hn
      have hm := logistic_strictMono hn'
      rw [show SAP.P004a.logistic 0 = 1/2 by
        norm_num [SAP.P004a.logistic], hlog] at hm
      exact (not_lt_of_ge hlow) hm
    have hnotHigh : ¬ SAP.P004a.logistic 1 ≤ q := by linarith
    have hMLE : SAP.P004a.boundaryMLE z = 0 := by
      unfold SAP.P004a.boundaryMLE
      change (if q ≤ 1/2 then 0 else if SAP.P004a.logistic 1 ≤ q then 1 else
        Real.log (q/(1-q))) = 0
      rw [if_pos hlow]
    rw [hMLE]
    change 0 = min 1 (max 0 (Real.log (q/(1-q))))
    rw [max_eq_left hlogle]
    norm_num
  · have hhalf : (1/2 : ℝ) < q := lt_of_not_ge hlow
    by_cases hmid : SAP.P004a.logistic 1 ≤ q
    · have hlogge : 1 ≤ Real.log (q / (1-q)) := by
        by_contra hn
        have hn' : Real.log (q/(1-q)) < 1 := lt_of_not_ge hn
        have hm := logistic_strictMono hn'
        rw [hlog] at hm
        exact (not_lt_of_ge hmid) hm
      have hMLE : SAP.P004a.boundaryMLE z = 1 := by
        unfold SAP.P004a.boundaryMLE
        change (if q ≤ 1/2 then 0 else if SAP.P004a.logistic 1 ≤ q then 1 else
          Real.log (q/(1-q))) = 1
        rw [if_neg (not_le_of_gt hhalf), if_pos hmid]
      rw [hMLE]
      change 1 = min 1 (max 0 (Real.log (q/(1-q))))
      rw [max_eq_right (by linarith : (0:ℝ) ≤ Real.log (q/(1-q)))]
      exact (min_eq_left hlogge).symm
    · have hlogbounds := AronowAudit.P004.Wave1.t9b6_logit_bounds
        hhalf (by simpa [SAP.P004a.logistic, AronowAudit.P004.logistic] using
          (lt_of_not_ge hmid))
      have hMLE : SAP.P004a.boundaryMLE z = Real.log (q/(1-q)) := by
        unfold SAP.P004a.boundaryMLE
        change (if q ≤ 1/2 then 0 else if SAP.P004a.logistic 1 ≤ q then 1 else
          Real.log (q/(1-q))) = Real.log (q/(1-q))
        rw [if_neg (not_le_of_gt hhalf), if_neg hmid]
      rw [hMLE]
      change Real.log (q/(1-q)) = min 1 (max 0 (Real.log (q/(1-q))))
      rw [max_eq_right hlogbounds.1, min_eq_right hlogbounds.2]

end SAP.P004a.WH.W2.P.T9_L1

open SAP.P004a.WH.W2.P.T9_L1

theorem SAP.P004a.WH.W2.T9_L1_proof : SAP.P004a.WH.W2.T9_L1 := by
  intro N hN z
  have hsecond : ∀ t : ℝ,
      -(N : ℝ) * Real.exp t / (1 + Real.exp t)^2 < 0 :=
    fun t => score_deriv_neg N hN t
  have hscoreAnti : StrictAnti
      (fun s => SAP.P004a.armCount z true - (N : ℝ) * SAP.P004a.logistic s) :=
    strictAnti_of_hasDerivAt_neg (score_hasDerivAt N z) hsecond
  have hderivAnti : StrictAntiOn
      (deriv (SAP.P004a.boundaryLikelihood z))
      (interior (Set.Icc (0:ℝ) 1)) := by
    intro x hx y hy hxy
    rw [(likelihood_hasDerivAt N z x).deriv, (likelihood_hasDerivAt N z y).deriv]
    exact hscoreAnti hxy
  have hconc : StrictConcaveOn ℝ (Set.Icc (0:ℝ) 1)
      (SAP.P004a.boundaryLikelihood z) :=
    hderivAnti.strictConcaveOn_of_deriv (convex_Icc 0 1) (by
      intro x hx
      exact (likelihood_hasDerivAt N z x).continuousAt.continuousWithinAt)
  have hmax : IsMaxOn (SAP.P004a.boundaryLikelihood z) (Set.Icc (0:ℝ) 1)
      (SAP.P004a.boundaryMLE z) := by
    intro u hu
    change AronowAudit.P004.Wave1.t9b6_likelihood (N : ℝ)
        (SAP.P004a.armCount z true) u ≤
      AronowAudit.P004.Wave1.t9b6_likelihood (N : ℝ)
        (SAP.P004a.armCount z true)
        (AronowAudit.P004.Wave1.t9b6_choice
          (SAP.P004a.armCount z true / N))
    simpa [SAP.P004a.armCount, AronowAudit.P004.armCount,
      SAP.P004a.logistic, AronowAudit.P004.logistic,
      SAP.P004a.boundaryMLE, AronowAudit.P004.Wave1.t9b6_choice,
      AronowAudit.P004.Wave1.t9b6_likelihood] using
      AronowAudit.P004.Wave1.t9b6_choice_max N
        (SAP.P004a.armCount z true) u (Nat.cast_pos.mpr hN) hu
  have hMLEmem : SAP.P004a.boundaryMLE z ∈ Set.Icc (0:ℝ) 1 := by
    have hb := AronowAudit.P004.Wave1.t9b6_choice_bounds
      (SAP.P004a.armCount z true / N)
    simpa [SAP.P004a.armCount, AronowAudit.P004.armCount,
      SAP.P004a.logistic, AronowAudit.P004.logistic,
      SAP.P004a.boundaryMLE, AronowAudit.P004.Wave1.t9b6_choice] using hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    exact ⟨score_hasDerivAt N z t, hsecond t⟩
  · intro t ht heq
    have hmaxT : IsMaxOn (SAP.P004a.boundaryLikelihood z) (Set.Icc (0:ℝ) 1) t := by
      intro u hu
      rw [heq]
      exact hmax hu
    have hu := hconc.eq_of_isMaxOn (x := SAP.P004a.boundaryMLE z) (y := t)
      hmax hmaxT hMLEmem ht
    exact hu.symm
  · intro hS
    have hq : SAP.P004a.armCount z true / N = 1 := by
      rw [hS]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]
    have hloglt : SAP.P004a.logistic 1 < 1 := by
      simpa [SAP.P004a.logistic, AronowAudit.P004.logistic] using
        AronowAudit.P004.Wave1.t9b6_logistic_lt_one 1
    simp [SAP.P004a.boundaryMLE, hq, hloglt.le]
    norm_num
  · intro hS hSN
    exact logit_clip_of_interior hN z hS hSN
