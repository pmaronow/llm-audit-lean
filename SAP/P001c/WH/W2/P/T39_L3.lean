import SAP.P001c.WH.W2.Leaves
import AronowAudit.P001.P001_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.WH.W2.P.T39_L3

open MeasureTheory ProbabilityTheory
open AronowAudit.P001
open scoped ENNReal NNReal Topology Classical

private theorem normalDensity_continuous : Continuous (normalDensity 0 1) := by
  unfold normalDensity
  fun_prop (disch := positivity)

private theorem normalDensity_eq_gaussianPDFReal_std :
    normalDensity 0 1 = gaussianPDFReal 0 1 := by
  rw [normalDensity_eq_gaussianPDFReal 0 1 (by norm_num)]
  congr 1
  ext
  change (1 : ℝ) ^ 2 = 1
  norm_num

private theorem normalDensity_nonneg (x : ℝ) : 0 ≤ normalDensity 0 1 x := by
  rw [normalDensity_eq_gaussianPDFReal_std]
  exact gaussianPDFReal_nonneg 0 1 x

private theorem mixtureDensity_continuous : Continuous normalMixtureDensity := by
  unfold normalMixtureDensity bivariatePDF
  fun_prop (disch := positivity)

private theorem mixtureDensity_nonneg : ∀ xy, 0 ≤ normalMixtureDensity xy := by
  have hpos : (3 / 5 : ℝ) ∈ Set.Ioo (-1) 1 := by norm_num
  have hneg : (-3 / 5 : ℝ) ∈ Set.Ioo (-1) 1 := by norm_num
  intro xy
  unfold normalMixtureDensity
  apply div_nonneg
  · exact add_nonneg
      (AronowAudit.P001.Wave1.bivariate_normal_density_nonneg 0 0 1 1 (3 / 5)
        (by norm_num) (by norm_num) hpos xy)
      (AronowAudit.P001.Wave1.bivariate_normal_density_nonneg 0 0 1 1 (-3 / 5)
        (by norm_num) (by norm_num) hneg xy)
  · norm_num

private theorem mixtureDensity_measurable : Measurable normalMixtureDensity := by
  unfold normalMixtureDensity bivariatePDF
  fun_prop (disch := positivity)

private theorem gaussianProduct_density :
    (gaussianReal 0 1).prod (gaussianReal 0 1) =
      volume.withDensity (fun xy : ℝ × ℝ =>
        ENNReal.ofReal (normalDensity 0 1 xy.1 * normalDensity 0 1 xy.2)) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [prod_withDensity₀ (by fun_prop) (by fun_prop)]
  rw [← Measure.volume_eq_prod ℝ ℝ]
  congr 1
  funext xy
  simp only [gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 xy.1)]
  congr 1 <;> rw [normalDensity_eq_gaussianPDFReal_std]

end SAP.P001c.WH.W2.P.T39_L3

open MeasureTheory ProbabilityTheory
open AronowAudit.P001
open scoped ENNReal NNReal Topology Classical

theorem SAP.P001c.WH.W2.T39_L3_proof : SAP.P001c.WH.W2.T39_L3 := by
  intro hprob hx hy hind
  letI : IsProbabilityMeasure normalMixtureLaw := hprob
  have hindmap : normalMixtureLaw.map (fun z : ℝ × ℝ => (z.1, z.2)) =
      (normalMixtureLaw.map Prod.fst).prod (normalMixtureLaw.map Prod.snd) :=
    (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mp hind
  have hlawprod : normalMixtureLaw =
      (normalMixtureLaw.map Prod.fst).prod (normalMixtureLaw.map Prod.snd) := by
    simpa using hindmap
  have hprod : (normalMixtureLaw.map Prod.fst).prod (normalMixtureLaw.map Prod.snd) =
      volume.withDensity (fun xy : ℝ × ℝ =>
        ENNReal.ofReal (normalDensity 0 1 xy.1 * normalDensity 0 1 xy.2)) := by
    rw [hx, hy]
    exact SAP.P001c.WH.W2.P.T39_L3.gaussianProduct_density
  have hmeasure : volume.withDensity (fun xy : ℝ × ℝ =>
      ENNReal.ofReal (normalMixtureDensity xy)) =
      volume.withDensity (fun xy : ℝ × ℝ =>
        ENNReal.ofReal (normalDensity 0 1 xy.1 * normalDensity 0 1 xy.2)) := by
    calc
      _ = normalMixtureLaw := by rfl
      _ = (normalMixtureLaw.map Prod.fst).prod (normalMixtureLaw.map Prod.snd) := hlawprod
      _ = _ := hprod
  have hprodmeas : Measurable (fun xy : ℝ × ℝ =>
      normalDensity 0 1 xy.1 * normalDensity 0 1 xy.2) := by
    fun_prop [normalDensity]
  have haeENN : (fun xy : ℝ × ℝ => ENNReal.ofReal (normalMixtureDensity xy)) =ᵐ[volume]
      (fun xy : ℝ × ℝ =>
        ENNReal.ofReal (normalDensity 0 1 xy.1 * normalDensity 0 1 xy.2)) := by
    exact (withDensity_eq_iff_of_sigmaFinite
      SAP.P001c.WH.W2.P.T39_L3.mixtureDensity_measurable.ennreal_ofReal.aemeasurable
      hprodmeas.ennreal_ofReal.aemeasurable).mp hmeasure
  have hae : normalMixtureDensity =ᵐ[volume]
      (fun xy : ℝ × ℝ => normalDensity 0 1 xy.1 * normalDensity 0 1 xy.2) := by
    filter_upwards [haeENN] with xy hxy
    exact (ENNReal.ofReal_eq_ofReal_iff
      (SAP.P001c.WH.W2.P.T39_L3.mixtureDensity_nonneg xy)
      (mul_nonneg (SAP.P001c.WH.W2.P.T39_L3.normalDensity_nonneg xy.1)
        (SAP.P001c.WH.W2.P.T39_L3.normalDensity_nonneg xy.2))).mp hxy
  have hcontinuousProduct : Continuous (fun xy : ℝ × ℝ =>
      normalDensity 0 1 xy.1 * normalDensity 0 1 xy.2) := by
    exact SAP.P001c.WH.W2.P.T39_L3.normalDensity_continuous.comp continuous_fst |>.mul
      (SAP.P001c.WH.W2.P.T39_L3.normalDensity_continuous.comp continuous_snd)
  have hpoint : normalMixtureDensity =
      (fun xy : ℝ × ℝ => normalDensity 0 1 xy.1 * normalDensity 0 1 xy.2) :=
    Measure.eq_of_ae_eq hae SAP.P001c.WH.W2.P.T39_L3.mixtureDensity_continuous hcontinuousProduct
  have hneq : normalMixtureDensity (0, 0) ≠
      normalDensity 0 1 0 * normalDensity 0 1 0 := by
    have hleft : normalMixtureDensity (0, 0) = 5 / (8 * Real.pi) := by
      norm_num [normalMixtureDensity, Bridge.bivariatePDF_eq, bivariatePDF,
        bivariateNormalPDF] <;> field_simp [Real.pi_ne_zero] <;> ring
    have hright : normalDensity 0 1 0 * normalDensity 0 1 0 = 1 / (2 * Real.pi) := by
      have hval : normalDensity 0 1 0 = (Real.sqrt (2 * Real.pi))⁻¹ := by
        rw [SAP.P001c.WH.W2.P.T39_L3.normalDensity_eq_gaussianPDFReal_std]
        simp [gaussianPDFReal]
      rw [hval]
      have hsqrt : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi :=
        Real.sq_sqrt (by positivity)
      have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
      field_simp [Real.pi_ne_zero, hs]
      rw [hsqrt]
    rw [hleft, hright]
    intro heq
    have hmul := congrArg (fun x : ℝ => x * (8 * Real.pi)) heq
    field_simp [Real.pi_ne_zero] at hmul
    norm_num at hmul
  exact hneq (congrFun hpoint (0, 0))
