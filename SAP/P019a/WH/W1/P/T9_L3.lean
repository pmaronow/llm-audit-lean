import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
open Classical
open AronowAudit.P019.Wave1

namespace SAP.P019a.WH.W1.P.T9_L3

theorem affine_argument (a t : ℝ) :
    (1 / Real.sqrt 2)*t + (1 / Real.sqrt 2)*a = (a+t)/Real.sqrt 2 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  ring

end SAP.P019a.WH.W1.P.T9_L3

noncomputable section

theorem SAP.P019a.WH.W1.T9_L3_proof : SAP.P019a.WH.W1.T9_L3 := by
  let c : ℝ := 1 / Real.sqrt 2
  have hc2 : c^2 = 1/2 := by
    dsimp [c]
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hn : c^2 + c^2 = 1 := by rw [hc2]; norm_num
  have hg : wholeFisherG = frc_g := by
    funext x
    rfl
  have harg (a t : ℝ) : c*t + c*a = (a+t)/Real.sqrt 2 := by
    simpa [c] using SAP.P019a.WH.W1.P.T9_L3.affine_argument a t
  have hh : wholeFisherH = frc_h c c := by
    funext t
    unfold wholeFisherH frc_h
    apply integral_congr_ae
    filter_upwards with a
    rw [hg]
    rw [harg]
  have hG : MemLp wholeFisherG 2 (gaussianReal 0 1) := by
    simpa only [hg] using frc_g_memLp
  have hH : MemLp wholeFisherH 2 (gaussianReal 0 1) := by
    simpa only [hh] using frc_h_memLp c c hn
  have hprod : Integrable (fun t => wholeFisherH t * wholeFisherG t)
      (gaussianReal 0 1) := hH.integrable_mul hG
  have hf : MemLp (fun p : ℝ × ℝ => frc_g (c*p.1 + c*p.2)) 2
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (frc_product_linear c c hn).memLp_comp frc_g_memLp
  have hi : Integrable (fun p : ℝ × ℝ => frc_g (c*p.1 + c*p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := hf.integrable (by norm_num)
  have hslices : ∀ᵐ t ∂gaussianReal 0 1,
      Integrable (fun a => wholeFisherG ((a+t)/Real.sqrt 2)) (gaussianReal 0 1) := by
    filter_upwards [hi.prod_right_ae] with t ht
    have hfun : (fun a => wholeFisherG ((a+t)/Real.sqrt 2)) =
        (fun a => frc_g (c*t + c*a)) := by
      funext a
      rw [hg, ← harg a t]
    rw [hfun]
    exact ht
  have hcov : ∀ j k : Fin 5, j.val < 4 → k.val < 4 → j ≠ k →
      wholeCovariance wholeGaussianFive
        (fun e => wholeFisherG (correlatedNormals e j))
        (fun e => wholeFisherG (correlatedNormals e k)) =
          wholeVariance (gaussianReal 0 1) wholeFisherH := by
    intro j k hj hk hjk
    have hrow := frc_row_dot j k
    have hdot : (∑ l, frc_row j l * frc_row k l) = c^2 := by
      have hrow' : (∑ l, frc_row j l * frc_row k l) = frc_rho j k := by
        simpa [hjk] using hrow
      rw [hrow']
      simp [frc_rho, hj, hk, hc2]
    have h := frc_covariance_common j k c c hn hdot
    have hcovi : cov[fun e => frc_g (correlatedNormals e j),
        fun e => frc_g (correlatedNormals e k); wholeGaussianFive] =
          wholeCovariance wholeGaussianFive
            (fun e => frc_g (correlatedNormals e j))
            (fun e => frc_g (correlatedNormals e k)) := by
      simpa only [correlatedNormals_eq, wholeGaussianFive, wholeCovariance, Pi.mul_apply] using
        (covariance_eq_sub (frc_margin_memLp j) (frc_margin_memLp k))
    have hvari : Var[frc_h c c; gaussianReal 0 1] =
        wholeVariance (gaussianReal 0 1) (frc_h c c) := by
      simpa only [wholeVariance, Pi.pow_apply] using
        (variance_eq_sub (frc_h_memLp c c hn))
    have hdonor : wholeCovariance wholeGaussianFive
        (fun e => frc_g (correlatedNormals e j))
        (fun e => frc_g (correlatedNormals e k)) =
          wholeVariance (gaussianReal 0 1) (frc_h c c) := by
      calc
        _ = cov[fun e => frc_g (correlatedNormals e j),
            fun e => frc_g (correlatedNormals e k); wholeGaussianFive] := hcovi.symm
        _ = Var[frc_h c c; gaussianReal 0 1] := h
        _ = _ := hvari
    simpa only [hg, hh] using hdonor
  exact ⟨hG, hH, hprod, hslices, hcov⟩

end
