import SAP.P001c.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.WH.W2.P.T39_L2

open MeasureTheory ProbabilityTheory
open SAP.P001c SAP.P001c.Bridge AronowAudit.P001 AronowAudit.P001.Wave1
open scoped ENNReal NNReal Topology Classical

noncomputable section

def componentLaw (ρ : ℝ) : Measure (ℝ × ℝ) :=
  volume.withDensity
    (fun xy => ENNReal.ofReal (AronowAudit.P001.bivariateNormalPDF 0 0 1 1 ρ xy))

lemma rho_pos_mem : (3 / 5 : ℝ) ∈ Set.Ioo (-1) 1 := by norm_num

lemma rho_neg_mem : (-3 / 5 : ℝ) ∈ Set.Ioo (-1) 1 := by norm_num

lemma componentLaw_probability (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    IsProbabilityMeasure (componentLaw ρ) := by
  simpa [componentLaw] using
    (AronowAudit.P001.Wave1.bivariate_normal_probability 0 0 1 1 ρ one_pos one_pos hρ).1

lemma componentLaw_moments (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 (componentLaw ρ) ∧
    MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 (componentLaw ρ) ∧
    mean (componentLaw ρ) Prod.fst = 0 ∧
    mean (componentLaw ρ) Prod.snd = 0 ∧
    covariance Prod.fst Prod.snd (componentLaw ρ) = ρ := by
  let ν := volume.withDensity
    (fun z => ENNReal.ofReal (AronowAudit.P001.bivariateNormalPDF 0 0 1 1 ρ z))
  obtain ⟨hX, hY, _, _⟩ :=
    AronowAudit.P001.Wave1.bivariate_normal_second_moments 0 0 1 1 ρ one_pos one_pos hρ
  obtain ⟨hmX, hmY, hc⟩ :=
    AronowAudit.P001.Wave1.bivariate_normal_means_covariance 0 0 1 1 ρ one_pos one_pos hρ
  have hν : ν = componentLaw ρ := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert hX using 1 <;> rfl
  · convert hY using 1 <;> rfl
  · convert hmX using 1 <;> (first | rfl | ring)
  · convert hmY using 1 <;> (first | rfl | ring)
  · convert hc using 1 <;> (first | rfl | ring)

lemma normalMixtureLaw_eq_half_sum :
    normalMixtureLaw = (1 / 2 : ℝ≥0∞) • (componentLaw (3 / 5) + componentLaw (-3 / 5)) := by
  have hp : ∀ xy, 0 ≤ bivariatePDF 0 0 1 1 (3 / 5) xy := by
    intro xy
    exact AronowAudit.P001.Wave1.bivariate_normal_density_nonneg 0 0 1 1 (3 / 5)
      one_pos one_pos rho_pos_mem xy
  have hn : ∀ xy, 0 ≤ bivariatePDF 0 0 1 1 (-3 / 5) xy := by
    intro xy
    exact AronowAudit.P001.Wave1.bivariate_normal_density_nonneg 0 0 1 1 (-3 / 5)
      one_pos one_pos rho_neg_mem xy
  have hdens :
      (fun xy => ENNReal.ofReal (normalMixtureDensity xy)) =
        (1 / 2 : ℝ≥0∞) •
          ((fun xy => ENNReal.ofReal (bivariatePDF 0 0 1 1 (3 / 5) xy)) +
            (fun xy => ENNReal.ofReal (bivariatePDF 0 0 1 1 (-3 / 5) xy))) := by
    funext xy
    simp only [normalMixtureDensity]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_add (hp xy) (hn xy)]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [ENNReal.ofReal_ofNat, div_eq_mul_inv]
    norm_num
    ac_rfl
  have hm₁' : Measurable (fun xy =>
      ENNReal.ofReal (AronowAudit.P001.bivariateNormalPDF 0 0 1 1 (3 / 5) xy)) :=
    (AronowAudit.P001.Wave1.bivariate_normal_density_measurable 0 0 1 1 (3 / 5)).ennreal_ofReal
  have hm₂' : Measurable (fun xy =>
      ENNReal.ofReal (AronowAudit.P001.bivariateNormalPDF 0 0 1 1 (-3 / 5) xy)) :=
    (AronowAudit.P001.Wave1.bivariate_normal_density_measurable 0 0 1 1 (-3 / 5)).ennreal_ofReal
  have hm₁ : Measurable (fun xy => ENNReal.ofReal (bivariatePDF 0 0 1 1 (3 / 5) xy)) := by
    simpa only [SAP.P001c.Bridge.bivariatePDF_eq] using hm₁'
  have hm₂ : Measurable (fun xy => ENNReal.ofReal (bivariatePDF 0 0 1 1 (-3 / 5) xy)) := by
    simpa only [SAP.P001c.Bridge.bivariatePDF_eq] using hm₂'
  rw [normalMixtureLaw, hdens, withDensity_smul _ (hm₁.add hm₂),
    withDensity_add_left hm₁]
  simp only [componentLaw, ← SAP.P001c.Bridge.bivariatePDF_eq]

lemma normalMixtureLaw_eq_sum :
    normalMixtureLaw =
      ((1 / 2 : ℝ≥0∞) • componentLaw (3 / 5)) +
        ((1 / 2 : ℝ≥0∞) • componentLaw (-3 / 5)) := by
  rw [normalMixtureLaw_eq_half_sum, smul_add]

end

end SAP.P001c.WH.W2.P.T39_L2

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory SAP.P001c SAP.P001c.WH.W2 AronowAudit.P001

theorem SAP.P001c.WH.W2.T39_L2_proof : SAP.P001c.WH.W2.T39_L2 := by
  let νpos := SAP.P001c.WH.W2.P.T39_L2.componentLaw (3 / 5)
  let νneg := SAP.P001c.WH.W2.P.T39_L2.componentLaw (-3 / 5)
  let c : ℝ≥0∞ := 1 / 2
  have hρpos : (3 / 5 : ℝ) ∈ Set.Ioo (-1) 1 :=
    SAP.P001c.WH.W2.P.T39_L2.rho_pos_mem
  have hρneg : (-3 / 5 : ℝ) ∈ Set.Ioo (-1) 1 :=
    SAP.P001c.WH.W2.P.T39_L2.rho_neg_mem
  have hP := SAP.P001c.WH.W2.P.T39_L2.componentLaw_moments (3 / 5) hρpos
  have hN := SAP.P001c.WH.W2.P.T39_L2.componentLaw_moments (-3 / 5) hρneg
  have hprobP : IsProbabilityMeasure νpos := by
    simpa [νpos] using
      SAP.P001c.WH.W2.P.T39_L2.componentLaw_probability (3 / 5) hρpos
  have hprobN : IsProbabilityMeasure νneg := by
    simpa [νneg] using
      SAP.P001c.WH.W2.P.T39_L2.componentLaw_probability (-3 / 5) hρneg
  letI : IsProbabilityMeasure νpos := hprobP
  letI : IsProbabilityMeasure νneg := hprobN
  have hmix : normalMixtureLaw = (c • νpos) + (c • νneg) := by
    simpa [c, νpos, νneg] using
      SAP.P001c.WH.W2.P.T39_L2.normalMixtureLaw_eq_sum
  have hPX : MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 νpos := hP.1
  have hPY : MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 νpos := hP.2.1
  have hNX : MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 νneg := hN.1
  have hNY : MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 νneg := hN.2.1
  have hPXc : MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 (c • νpos) :=
    hPX.smul_measure (by norm_num [c])
  have hPYc : MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 (c • νpos) :=
    hPY.smul_measure (by norm_num [c])
  have hNXc : MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 (c • νneg) :=
    hNX.smul_measure (by norm_num [c])
  have hNYc : MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 (c • νneg) :=
    hNY.smul_measure (by norm_num [c])
  have hsqX : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) normalMixtureLaw := by
    rw [hmix]
    exact hPXc.integrable_sq.add_measure hNXc.integrable_sq
  have hsqY : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) normalMixtureLaw := by
    rw [hmix]
    exact hPYc.integrable_sq.add_measure hNYc.integrable_sq
  have hMX : MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 normalMixtureLaw :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hsqX
  have hMY : MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 normalMixtureLaw :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hsqY
  have hiPX : Integrable (Prod.fst : ℝ × ℝ → ℝ) (c • νpos) :=
    (hPX.integrable (by norm_num)).smul_measure (by norm_num [c])
  have hiNX : Integrable (Prod.fst : ℝ × ℝ → ℝ) (c • νneg) :=
    (hNX.integrable (by norm_num)).smul_measure (by norm_num [c])
  have hiPY : Integrable (Prod.snd : ℝ × ℝ → ℝ) (c • νpos) :=
    (hPY.integrable (by norm_num)).smul_measure (by norm_num [c])
  have hiNY : Integrable (Prod.snd : ℝ × ℝ → ℝ) (c • νneg) :=
    (hNY.integrable (by norm_num)).smul_measure (by norm_num [c])
  have hmeanPX : (∫ z : ℝ × ℝ, z.1 ∂νpos) = 0 := by
    simpa [mean] using hP.2.2.1
  have hmeanPY : (∫ z : ℝ × ℝ, z.2 ∂νpos) = 0 := by
    simpa [mean] using hP.2.2.2.1
  have hmeanNX : (∫ z : ℝ × ℝ, z.1 ∂νneg) = 0 := by
    simpa [mean] using hN.2.2.1
  have hmeanNY : (∫ z : ℝ × ℝ, z.2 ∂νneg) = 0 := by
    simpa [mean] using hN.2.2.2.1
  have hmeanX : (∫ z : ℝ × ℝ, z.1 ∂normalMixtureLaw) = 0 := by
    rw [hmix, integral_add_measure hiPX hiNX, integral_smul_measure, integral_smul_measure]
    simp [c, hmeanPX, hmeanNX]
  have hmeanY : (∫ z : ℝ × ℝ, z.2 ∂normalMixtureLaw) = 0 := by
    rw [hmix, integral_add_measure hiPY hiNY, integral_smul_measure, integral_smul_measure]
    simp [c, hmeanPY, hmeanNY]
  have hcrossP : (∫ z : ℝ × ℝ, z.1 * z.2 ∂νpos) = 3 / 5 := by
    have h := ProbabilityTheory.covariance_eq_sub hPX hPY
    rw [hP.2.2.2.2] at h
    rw [hmeanPX, hmeanPY] at h
    simpa [Pi.mul_apply] using h.symm
  have hcrossN : (∫ z : ℝ × ℝ, z.1 * z.2 ∂νneg) = -(3 / 5) := by
    have h := ProbabilityTheory.covariance_eq_sub hNX hNY
    rw [hN.2.2.2.2] at h
    rw [hmeanNX, hmeanNY] at h
    convert h.symm using 1 <;> norm_num [Pi.mul_apply]
  have hiCrossP : Integrable (fun z : ℝ × ℝ => z.1 * z.2) (c • νpos) :=
    hPXc.integrable_mul hPYc
  have hiCrossN : Integrable (fun z : ℝ × ℝ => z.1 * z.2) (c • νneg) :=
    hNXc.integrable_mul hNYc
  have hcross : (∫ z : ℝ × ℝ, z.1 * z.2 ∂normalMixtureLaw) = 0 := by
    rw [hmix, integral_add_measure hiCrossP hiCrossN,
      integral_smul_measure, integral_smul_measure]
    simp [c, hcrossP, hcrossN]
  have hprob : IsProbabilityMeasure normalMixtureLaw := by
    constructor
    rw [hmix]
    norm_num [Measure.add_apply, Measure.smul_apply, c,
      hprobP.measure_univ, hprobN.measure_univ, ENNReal.inv_two_add_inv_two]
  letI : IsProbabilityMeasure normalMixtureLaw := hprob
  refine ⟨hMX, hMY, ?_⟩
  rw [ProbabilityTheory.covariance_eq_sub hMX hMY]
  change (∫ z : ℝ × ℝ, z.1 * z.2 ∂normalMixtureLaw) -
      (∫ z : ℝ × ℝ, z.1 ∂normalMixtureLaw) *
        (∫ z : ℝ × ℝ, z.2 ∂normalMixtureLaw) = 0
  rw [hcross, hmeanX, hmeanY]
  norm_num
