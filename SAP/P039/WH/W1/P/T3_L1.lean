import SAP.P039.WH.W1.Leaves
import AronowAudit.P039.P039_GaussianCompletion
import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.ChiSquaredInverseMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.WH.W1.P.T3_L1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable def pairRatio (ν : ℕ) (p : ℝ × ℝ) : ℝ :=
  p.1 / Real.sqrt (p.2 / (ν : ℝ))

noncomputable def scaleKernel (ν : ℕ) (w t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (w / ν) * gaussianPDFReal 0 1 (Real.sqrt (w / ν) * t))

lemma gammaMeasure_nonpos_zero (a r : ℝ) :
    gammaMeasure a r (Set.Iic (0 : ℝ)) = 0 := by
  rw [gammaMeasure, withDensity_apply (gammaPDF a r) measurableSet_Iic]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Iic,
    ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with x hx hx0
  have hx' : x < 0 := lt_of_le_of_ne hx hx0
  simp [gammaPDF_of_neg hx']

lemma gammaMeasure_ae_pos {a r : ℝ} :
    ∀ᵐ w ∂gammaMeasure a r, 0 < w := by
  rw [ae_iff, show {w : ℝ | ¬ 0 < w} = Set.Iic 0 from by
    ext w
    simp]
  exact gammaMeasure_nonpos_zero a r

@[fun_prop] lemma measurable_pairRatio (ν : ℕ) : Measurable (pairRatio ν) := by
  fun_prop [pairRatio]

@[fun_prop] lemma measurable_scaleKernel (ν : ℕ) :
    Measurable (fun p : ℝ × ℝ => scaleKernel ν p.1 p.2) := by
  fun_prop [scaleKernel]

lemma scaled_gaussian_density {c : ℝ} (hc : 0 < c) :
    (gaussianReal 0 1).map (fun x : ℝ => x / c) =
      volume.withDensity (fun t => ENNReal.ofReal
        (c * gaussianPDFReal 0 1 (c * t))) := by
  have hc0 : c ≠ 0 := hc.ne'
  rw [gaussianReal_map_div_const]
  let v : ℝ≥0 := NNReal.mk (c ^ 2) (sq_nonneg c)
  have hvpos : 0 < v := (NNReal.coe_pos).2 (sq_pos_of_ne_zero hc0)
  have hv : (1 : ℝ≥0) / v ≠ 0 := div_ne_zero one_ne_zero hvpos.ne'
  simp only [zero_div]
  change gaussianReal 0 (1 / v) = _
  rw [gaussianReal_of_var_ne_zero 0 hv]
  congr 1
  funext t
  change ENNReal.ofReal (gaussianPDFReal 0 (1 / v) t) =
    ENNReal.ofReal (c * gaussianPDFReal 0 1 (c * t))
  apply congrArg ENNReal.ofReal
  rw [gaussianPDFReal_mul (μ := 0) (v := 1) hc0]
  have hvar : 1 / v = v⁻¹ * 1 := by simp [one_div]
  rw [hvar]
  have habs : |c⁻¹| = c⁻¹ := abs_of_pos (inv_pos.mpr hc)
  rw [habs]
  have hscale : c * c⁻¹ = 1 := by field_simp
  simp [v]
  rw [← mul_assoc, hscale, one_mul]

lemma pairRatio_map_density (ν : ℕ) (hν : 0 < ν) :
    ((gaussianReal 0 1).prod (gammaMeasure ((ν : ℝ) / 2) (1 / 2))).map
      (pairRatio ν) = volume.withDensity (studentMixtureDensity ν) := by
  let γ := gammaMeasure ((ν : ℝ) / 2) (1 / 2)
  have hγsf : SFinite γ := by
    dsimp [γ, gammaMeasure]
    infer_instance
  haveI : SFinite γ := hγsf
  have hγpos : ∀ᵐ w ∂γ, 0 < w := gammaMeasure_ae_pos
  have hνr : (0 : ℝ) < ν := by exact_mod_cast hν
  ext A hA
  rw [Measure.map_apply (measurable_pairRatio ν) hA,
    withDensity_apply (studentMixtureDensity ν) hA]
  · rw [Measure.prod_apply_symm (by measurability)]
    calc
      ∫⁻ w, (gaussianReal 0 1) ((fun x => (x, w)) ⁻¹'
          {p : ℝ × ℝ | pairRatio ν p ∈ A}) ∂γ
        = ∫⁻ w, ∫⁻ t in A, scaleKernel ν w t ∂volume ∂γ := by
            apply lintegral_congr_ae
            filter_upwards [hγpos] with w hw
            have hc : 0 < Real.sqrt (w / (ν : ℝ)) := by
              apply Real.sqrt_pos.2
              exact div_pos hw hνr
            have hfun : (fun x : ℝ => pairRatio ν (x, w)) =
                fun x => x / Real.sqrt (w / (ν : ℝ)) := by
              funext x
              rfl
            change (gaussianReal 0 1) ((fun x : ℝ => pairRatio ν (x, w)) ⁻¹' A) = _
            rw [← Measure.map_apply (by fun_prop) hA, hfun,
              scaled_gaussian_density hc, withDensity_apply _ hA]
            · rfl
      _ = ∫⁻ t in A, ∫⁻ w, scaleKernel ν w t ∂γ ∂volume := by
            calc
              _ = ∫⁻ w, ∫⁻ t, A.indicator (fun t => scaleKernel ν w t) t
                    ∂volume ∂γ := by
                      congr 1
                      funext w
                      rw [lintegral_indicator hA]
              _ = ∫⁻ t, ∫⁻ w, A.indicator (fun t => scaleKernel ν w t) t
                    ∂γ ∂volume := by
                      apply lintegral_lintegral_swap (μ := γ) (ν := volume)
                      have hF : Measurable (fun p : ℝ × ℝ =>
                          A.indicator (fun t => scaleKernel ν p.1 t) p.2) := by
                        convert (measurable_scaleKernel ν).indicator
                          (hA.preimage measurable_snd) using 1
                        ext p
                        rfl
                      exact hF.aemeasurable
              _ = ∫⁻ t in A, ∫⁻ w, scaleKernel ν w t ∂γ ∂volume := by
                      rw [← lintegral_indicator hA]
                      apply lintegral_congr_ae
                      filter_upwards [] with t
                      by_cases ht : t ∈ A <;> simp [Set.indicator, ht]
      _ = ∫⁻ t in A, studentMixtureDensity ν t ∂volume := by
            rfl

lemma studentLaw_eq_pairRatio_map (ν : ℕ) (hν : 0 < ν) :
    studentLaw ν =
      ((gaussianReal 0 1).prod (gammaMeasure ((ν : ℝ) / 2) (1 / 2))).map
        (pairRatio ν) := by
  have hχ : AronowAudit.P039.chiSquaredLaw ν =
      gammaMeasure ((ν : ℝ) / 2) (1 / 2) := by
    unfold AronowAudit.P039.chiSquaredLaw
    exact AronowAudit.GaussianCompletion.gaussian_squares_eq_gamma hν
  have hsplit := AronowAudit.P039.GaussianCompletion.standard_pair_squares ν
  rw [hχ] at hsplit
  unfold studentLaw
  calc
    _ = (Measure.pi (fun _ : Fin (ν + 1) => gaussianReal 0 1)).map
        (fun z => pairRatio ν (z 0, ∑ i : Fin ν, (z i.succ) ^ 2)) := by
          apply Measure.map_congr
          filter_upwards [] with z
          dsimp [pairRatio]
          rw [AronowAudit.P039.GaussianCompletion.erase_zero_sum]
    _ = ((Measure.pi (fun _ : Fin (ν + 1) => gaussianReal 0 1)).map
        (fun z => (z 0, ∑ i : Fin ν, (z i.succ) ^ 2))).map (pairRatio ν) := by
          rw [Measure.map_map (measurable_pairRatio ν) (by fun_prop)]
          rfl
    _ = ((gaussianReal 0 1).prod (gammaMeasure ((ν : ℝ) / 2) (1 / 2))).map
        (pairRatio ν) := by rw [hsplit]

end SAP.P039.WH.W1.P.T3_L1

theorem SAP.P039.WH.W1.T3_L1_proof : SAP.P039.WH.W1.T3_L1 := by
  intro ν hν
  rw [SAP.P039.WH.W1.P.T3_L1.studentLaw_eq_pairRatio_map ν hν,
    SAP.P039.WH.W1.P.T3_L1.pairRatio_map_density ν hν]
