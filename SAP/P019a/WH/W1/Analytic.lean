import SAP.P019a.WH.W1.Existing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1
open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
open Classical
open AronowAudit.P019.Wave1
set_option maxHeartbeats 800000
local instance : IsProbabilityMeasure wholeGaussianFive := by
  unfold wholeGaussianFive; infer_instance

 theorem t9_linearization : wholeT9Linearization := by
  intro j ε hε
  have h := tendstoInMeasure_iff_measureReal_norm.mp (frc_ratio_remainder j) ε hε
  simp only [sub_zero, Real.norm_eq_abs] at h
  convert h using 1
  funext n
  exact (t19_sample_prob frc_law n (fun s =>
    ε ≤ |Real.sqrt (n : ℝ)*((sequentialStudy j).betaHat s 0 0-1) -
      (Real.sqrt (n : ℝ))⁻¹ * ∑ i, sequentialPsi j (s i)|)).symm

 theorem wholeCovariance_comm {E : Type*} [MeasurableSpace E] (P : Measure E) (f g : E → ℝ) :
    wholeCovariance P f g = wholeCovariance P g f := by
  unfold wholeCovariance
  simp_rw [mul_comm]

 theorem t9_variance_formula
    (hfirst : ∀ j k : Fin 5, j.val < 4 → k.val < 4 → j ≠ k →
      wholeCovariance wholeGaussianFive
        (fun e => wholeFisherG (correlatedNormals e j))
        (fun e => wholeFisherG (correlatedNormals e k)) =
          wholeVariance (gaussianReal 0 1) wholeFisherH)
    (hcross : ∀ j : Fin 5, j.val < 4 →
      wholeCovariance wholeGaussianFive
        (fun e => wholeFisherG (correlatedNormals e j))
        (fun e => wholeFisherG (correlatedNormals e 4)) =
          wholeCovariance (gaussianReal 0 1) wholeFisherH wholeFisherG) :
    continuousVariance sequentialFisherLimit = 20 +
      12*wholeVariance (gaussianReal 0 1) wholeFisherH +
      8*wholeCovariance (gaussianReal 0 1) wholeFisherH wholeFisherG := by
  let F := fun j : Fin 5 => fun e : Fin 5 → ℝ => wholeFisherG (correlatedNormals e j)
  let V := wholeVariance (gaussianReal 0 1) wholeFisherH
  let C := wholeCovariance (gaussianReal 0 1) wholeFisherH wholeFisherG
  have hm (j : Fin 5) : MemLp (F j) 2 wholeGaussianFive := frc_margin_memLp j
  have hcov (j k : Fin 5) : cov[F j, F k; wholeGaussianFive] =
      if j = k then 4 else if j.val < 4 ∧ k.val < 4 then V else C := by
    have he : cov[F j, F k; wholeGaussianFive] = wholeCovariance wholeGaussianFive (F j) (F k) := by
      simpa only [wholeCovariance, Pi.mul_apply] using covariance_eq_sub (hm j) (hm k)
    by_cases hjk : j = k
    · subst k
      simpa using (covariance_self (hm j).aemeasurable).trans (frc_margin_variance j)
    · rw [he, if_neg hjk]
      by_cases hj : j.val < 4
      · by_cases hk : k.val < 4
        · rw [if_pos ⟨hj,hk⟩]
          exact hfirst j k hj hk hjk
        · have hk4 : k = 4 := by apply Fin.ext; change _ = (4 : ℕ); omega
          rw [if_neg (by simp [hk]), hk4]
          exact hcross j hj
      · have hj4 : j = 4 := by apply Fin.ext; change _ = (4 : ℕ); omega
        have hk : k.val < 4 := by
          have hkne : k ≠ 4 := by intro h; exact hjk (hj4.trans h.symm)
          have hklt := k.isLt
          have : k.val ≠ 4 := by intro h; exact hkne (Fin.ext h)
          omega
        rw [if_neg (by simp [hj]), wholeCovariance_comm, hj4]
        exact hcross k hk
  have hvariance : Var[fun e => ∑ j, F j e; wholeGaussianFive] = 20+12*V+8*C := by
    rw [variance_fun_sum hm]
    simp_rw [hcov]
    norm_num [Fin.sum_univ_succ]
    ring
  haveI : IsProbabilityMeasure AronowAudit.P019.sequentialFisherLimit :=
    frc_T_law.isProbabilityMeasure_iff.mp inferInstance
  have he := frc_continuousVariance frc_limit_memLp
  have hl := frc_T_law.variance_eq
  change AronowAudit.P019.continuousVariance AronowAudit.P019.sequentialFisherLimit = _ at he
  rw [sequentialFisherLimit_eq, continuousVariance_eq, he, ← hl]
  exact hvariance

 theorem t9_fisher_law : sequentialFisherLimit =
    wholeGaussianFive.map (fun e => ∑ j, wholeFisherG (correlatedNormals e j)) := by
  rw [sequentialFisherLimit_eq]
  exact frc_T_law.map_eq.symm

 theorem t9_chi_moments :
    Integrable (fun x : ℝ => x) chiSquareTen ∧
    Integrable (fun x : ℝ => x^2) chiSquareTen ∧ continuousVariance chiSquareTen = 20 := by
  rw [chiSquareTen_eq]
  haveI : IsProbabilityMeasure AronowAudit.P019.chiSquareTen := by
    unfold AronowAudit.P019.chiSquareTen; infer_instance
  exact ⟨frc_chi_memLp.integrable (by norm_num), frc_chi_memLp.integrable_sq, frc_chi_variance⟩

end
end SAP.P019a.WH.W1
