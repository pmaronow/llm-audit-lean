import SAP.P019a.WH.W1.Leaves
import AronowAudit.P019.Wave1.Gap.GLP019B4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1.P.T9_L7

open SAP.P019a MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

lemma shiftedGaussianPDFReal_le (t x : ℝ) :
    gaussianPDFReal (t / Real.sqrt 2) (1 / 2 : NNReal) x ≤
      (Real.sqrt 2 * Real.exp (t ^ 2 / 2)) * gaussianPDFReal 0 1 x := by
  let m : ℝ := t / Real.sqrt 2
  have hm : m ^ 2 = t ^ 2 / 2 := by
    dsimp [m]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hconst : (Real.sqrt (2 * Real.pi * (1 / 2 : ℝ)))⁻¹ =
      Real.sqrt 2 * (Real.sqrt (2 * Real.pi * 1))⁻¹ := by
    rw [show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring,
      show 2 * Real.pi * (1 : ℝ) = 2 * Real.pi by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Real.pi]
    have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    field_simp
  have hcomplete :
      t ^ 2 / 2 - x ^ 2 / 2 + (x - m) ^ 2 = (x - 2 * m) ^ 2 / 2 := by
    rw [← hm]
    ring
  have hexp : Real.exp (-(x - m) ^ 2) ≤ Real.exp (t ^ 2 / 2) * Real.exp (-(x ^ 2 / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs := sq_nonneg (x - 2 * m)
    linarith
  rw [gaussianPDFReal_def, gaussianPDFReal_def]
  change (Real.sqrt (2 * Real.pi * (1 / 2 : ℝ)))⁻¹ *
      Real.exp (-(x - m) ^ 2 / (2 * (1 / 2 : ℝ))) ≤
    (Real.sqrt 2 * Real.exp (t ^ 2 / 2)) *
      ((Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))))
  rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num,
    show 2 * (1 : ℝ) = 2 by norm_num, hconst]
  simp only [div_one, sub_zero]
  have hc : 0 ≤ Real.sqrt 2 * (Real.sqrt (2 * Real.pi * 1))⁻¹ := by positivity
  calc
    Real.sqrt 2 * (Real.sqrt (2 * Real.pi * 1))⁻¹ * Real.exp (-(x - m) ^ 2) ≤
        Real.sqrt 2 * (Real.sqrt (2 * Real.pi * 1))⁻¹ *
          (Real.exp (t ^ 2 / 2) * Real.exp (-(x ^ 2 / 2))) := mul_le_mul_of_nonneg_left hexp hc
    _ = (Real.sqrt 2 * Real.exp (t ^ 2 / 2)) *
        ((Real.sqrt (2 * Real.pi * 1))⁻¹ * Real.exp (-(x ^ 2) / 2)) := by
      ring_nf

lemma shiftedGaussian_le (t : ℝ) :
    gaussianReal (t / Real.sqrt 2) (1 / 2 : NNReal) ≤
      ENNReal.ofReal (Real.sqrt 2 * Real.exp (t ^ 2 / 2)) • gaussianReal 0 1 := by
  have hv : (1 / 2 : NNReal) ≠ 0 := by norm_num
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ (by norm_num)]
  calc
    volume.withDensity (gaussianPDF (t / Real.sqrt 2) (1 / 2 : NNReal)) ≤
        volume.withDensity (fun x => ENNReal.ofReal (Real.sqrt 2 * Real.exp (t ^ 2 / 2)) *
          gaussianPDF 0 1 x) := by
      apply withDensity_mono
      filter_upwards with x
      simp only [gaussianPDF_def]
      calc
        ENNReal.ofReal (gaussianPDFReal (t / Real.sqrt 2) (1 / 2 : NNReal) x) ≤
            ENNReal.ofReal (Real.sqrt 2 * Real.exp (t ^ 2 / 2) * gaussianPDFReal 0 1 x) :=
          ENNReal.ofReal_le_ofReal (shiftedGaussianPDFReal_le t x)
        _ = ENNReal.ofReal (Real.sqrt 2 * Real.exp (t ^ 2 / 2)) *
            ENNReal.ofReal (gaussianPDFReal 0 1 x) := by
          rw [show Real.sqrt 2 * Real.exp (t ^ 2 / 2) * gaussianPDFReal 0 1 x =
              gaussianPDFReal 0 1 x * (Real.sqrt 2 * Real.exp (t ^ 2 / 2)) by ring,
            ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
          exact mul_comm _ _
    _ = ENNReal.ofReal (Real.sqrt 2 * Real.exp (t ^ 2 / 2)) •
        volume.withDensity (gaussianPDF 0 1) := by
      change volume.withDensity
        (ENNReal.ofReal (Real.sqrt 2 * Real.exp (t ^ 2 / 2)) • gaussianPDF 0 1) = _
      rw [← withDensity_smul (ENNReal.ofReal (Real.sqrt 2 * Real.exp (t ^ 2 / 2)))
        (measurable_gaussianPDF 0 1)]

end
end SAP.P019a.WH.W1.P.T9_L7

open SAP.P019a MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem SAP.P019a.WH.W1.T9_L7_proof : SAP.P019a.WH.W1.T9_L7 := by
  intro t
  have hmap : (gaussianReal 0 1).map (fun a : ℝ => (a + t) / Real.sqrt 2) =
      gaussianReal (t / Real.sqrt 2) (1 / 2 : NNReal) := by
    have hfun : (fun a : ℝ => (a + t) / Real.sqrt 2) =
        (fun y => y + t / Real.sqrt 2) ∘ (fun a => a / Real.sqrt 2) := by
      funext a
      dsimp
      ring
    rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_div_const,
      gaussianReal_map_add_const]
    congr 1
    · ring
    · ext
      simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  let affine : ℝ → ℝ := fun a => (a + t) / Real.sqrt 2
  have hpres : MeasurePreserving affine (gaussianReal 0 1)
      (gaussianReal (t / Real.sqrt 2) (1 / 2 : NNReal)) := by
    constructor
    · dsimp [affine]
      fun_prop
    · exact hmap
  have hCDF (x : ℝ) : SAP.P019a.normalCDF x = AronowAudit.P019.normalCDF x := by
    rfl
  have hident : SAP.P019a.wholeFisherG = AronowAudit.P019.Wave1.frc_g := by
    funext x
    simp [SAP.P019a.wholeFisherG, AronowAudit.P019.Wave1.frc_g,
      AronowAudit.P019.Wave1.frc_p, hCDF]
  have hg : Integrable SAP.P019a.wholeFisherG (gaussianReal 0 1) := by
    rw [hident]
    exact AronowAudit.P019.Wave1.frc_g_memLp.integrable (by norm_num)
  have hshift : Integrable SAP.P019a.wholeFisherG
      (gaussianReal (t / Real.sqrt 2) (1 / 2 : NNReal)) :=
    Integrable.of_measure_le_smul ENNReal.ofReal_ne_top
      (SAP.P019a.WH.W1.P.T9_L7.shiftedGaussian_le t) hg
  change Integrable (SAP.P019a.wholeFisherG ∘ affine) (gaussianReal 0 1)
  exact hpres.integrable_comp_of_integrable hshift
