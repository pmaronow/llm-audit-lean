import SAP.P013a.WH.W1.Support
import AronowAudit.P033.Wave1.Gap.GLP010P033P033B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a.WH.W1

noncomputable section

/-- Certified donor evaluations locate the quantile; square-root bounds and multiplication
then locate the scaled argument used by T1's two remaining CDF evaluations. -/
theorem critical_scaled_bracket :
    1.69737860111425 < normalCritical (1/20)*Real.sqrt (3/4) ∧
    normalCritical (1/20)*Real.sqrt (3/4) < 1.69737860111427 := by
  have hm : StrictMono normalCDF := AronowAudit.P013.Wave1.CorrectedCoverage.n6_proof.2.1
  have hz := AronowAudit.P013.Wave1.CorrectedCoverage.n6_proof.2.2.2
    (1/20) (by norm_num) (by norm_num)
  change 0 < normalCritical (1/20) ∧ normalCDF (normalCritical (1/20))=1-(1/20)/2 at hz
  have h0 : normalCDF 1.9599639845400542 ≤ 97499999999999999794/10^20 := by
    simpa only [normalCDF, AronowAudit.P033.normalCDF, ProbabilityTheory.cdf_eq_real] using
      AronowAudit.P033.Wave1.pseudo_counter_cdf_num_0.2
  have h1 : 97500000000000000375/10^20 ≤ normalCDF 1.9599639845400543 := by
    simpa only [normalCDF, AronowAudit.P033.normalCDF, ProbabilityTheory.cdf_eq_real] using
      AronowAudit.P033.Wave1.pseudo_counter_cdf_num_1.1
  have hlo : 1.9599639845400542 < normalCritical (1/20) := by
    by_contra! hn
    have hh := hm.monotone hn
    linarith [hz.2]
  have hhi : normalCritical (1/20) < 1.9599639845400543 := by
    by_contra! hn
    have hh := hm.monotone hn
    linarith [hz.2]
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/4)
  have hspos : 0 < Real.sqrt (3/4) := Real.sqrt_pos.mpr (by norm_num)
  have hslo : 0.8660254037844386 < Real.sqrt (3/4) := by nlinarith
  have hshi : Real.sqrt (3/4) < 0.8660254037844387 := by nlinarith
  have ha := mul_lt_mul_of_pos_right hlo hspos
  have hb := mul_lt_mul_of_pos_left hslo (by norm_num : (0 : ℝ) < 1.9599639845400542)
  have hd := mul_lt_mul_of_pos_right hhi hspos
  have he := mul_lt_mul_of_pos_left hshi (by norm_num : (0 : ℝ) < 1.9599639845400543)
  constructor <;> linarith

end
end SAP.P013a.WH.W1
