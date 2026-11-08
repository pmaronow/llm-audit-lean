import SAP.P004a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T8_L5

open MeasureTheory ProbabilityTheory Set
open scoped Classical
noncomputable section

lemma normalCDF_eq_integral (x : ℝ) :
    SAP.P004a.normalCDF x =
      ∫ t in Set.Iic x, ProbabilityTheory.gaussianPDFReal 0 1 t := by
  rw [SAP.P004a.normalCDF,
    ProbabilityTheory.gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal]
  exact integral_nonneg fun t => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 t

lemma normalCDF_zero : SAP.P004a.normalCDF 0 = 1 / 2 := by
  have h := AronowAudit.P004.Wave1.GP0042B2b_capped_pd_normalCDF_neg 0
  rw [neg_zero] at h
  have h' : SAP.P004a.normalCDF 0 = 1 - SAP.P004a.normalCDF 0 := by
    simpa [SAP.P004a.normalCDF, AronowAudit.P004.normalCDF] using h
  linarith

end
end SAP.P004a.WH.W2.P.T8_L5

open MeasureTheory ProbabilityTheory Set

theorem SAP.P004a.WH.W2.T8_L5_proof : SAP.P004a.WH.W2.T8_L5 := by
  intro ν hν hstudent hnorm hhalf hcross x hx
  rcases hcross with ⟨ρ, hρ, hbelow, habove⟩
  have hgauss : Integrable (ProbabilityTheory.gaussianPDFReal 0 1) :=
    ProbabilityTheory.integrable_gaussianPDFReal 0 1
  have hgaussnorm : (∫ t, ProbabilityTheory.gaussianPDFReal 0 1 t) = 1 :=
    ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (by norm_num)
  by_cases hxρ : x ≤ ρ
  · have hstudentdiff : studentCDF ν x - studentCDF ν 0 =
        ∫ t in (0 : ℝ)..x, studentDensity ν t := by
      simpa [SAP.P004a.studentCDF] using
        (intervalIntegral.integral_Iic_sub_Iic
          (f := studentDensity ν)
          (hstudent.integrableOn (s := Set.Iic (0 : ℝ)))
          (hstudent.integrableOn (s := Set.Iic x)))
    have hgaussdiff : SAP.P004a.normalCDF x - SAP.P004a.normalCDF 0 =
        ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t := by
      rw [SAP.P004a.WH.W2.P.T8_L5.normalCDF_eq_integral,
        SAP.P004a.WH.W2.P.T8_L5.normalCDF_eq_integral]
      exact intervalIntegral.integral_Iic_sub_Iic
        (f := ProbabilityTheory.gaussianPDFReal 0 1)
        (hgauss.integrableOn (s := Set.Iic (0 : ℝ)))
        (hgauss.integrableOn (s := Set.Iic x))
    have hdiff : (∫ t in (0 : ℝ)..x, studentDensity ν t) ≤
        ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t := by
      rw [intervalIntegral.integral_of_le hx, intervalIntegral.integral_of_le hx]
      apply setIntegral_mono_on
        (hstudent.integrableOn (s := Set.Ioc (0 : ℝ) x))
        (hgauss.integrableOn (s := Set.Ioc (0 : ℝ) x))
        measurableSet_Ioc
      intro t ht
      exact hbelow t ht.1.le (ht.2.trans hxρ)
    linarith [hstudentdiff, hgaussdiff, hhalf,
      SAP.P004a.WH.W2.P.T8_L5.normalCDF_zero]
  · have hρx : ρ ≤ x := le_of_not_ge hxρ
    have hstudenttail : studentCDF ν x +
        (∫ t in Set.Ioi x, studentDensity ν t) = 1 := by
      have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := x)
        (f := studentDensity ν)
        (hstudent.integrableOn (s := Set.Iic x))
        (hstudent.integrableOn (s := Set.Ioi x))
      simpa [SAP.P004a.studentCDF, hnorm] using hsplit
    have hgausstail : SAP.P004a.normalCDF x +
        (∫ t in Set.Ioi x, ProbabilityTheory.gaussianPDFReal 0 1 t) = 1 := by
      have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := x)
        (f := ProbabilityTheory.gaussianPDFReal 0 1)
        (hgauss.integrableOn (s := Set.Iic x))
        (hgauss.integrableOn (s := Set.Ioi x))
      rw [SAP.P004a.WH.W2.P.T8_L5.normalCDF_eq_integral]
      exact hsplit.trans hgaussnorm
    have htail :
        (∫ t in Set.Ioi x, ProbabilityTheory.gaussianPDFReal 0 1 t) ≤
          ∫ t in Set.Ioi x, studentDensity ν t := by
      apply setIntegral_mono_on
        (hgauss.integrableOn (s := Set.Ioi x))
        (hstudent.integrableOn (s := Set.Ioi x))
        measurableSet_Ioi
      intro t ht
      exact habove t (hρx.trans ht.le)
    linarith
