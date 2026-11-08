import SAP.P001d.WH.W2.Leaves
import AronowAudit.P001.P001_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace SAP.P001d.WH.W2.P.T58_L1

lemma integral_signedKernel_Iic (z : ℝ) (hz : z ∈ Set.Icc (-2) (-1)) :
    (∫ u in Set.Iic z, signedKernel u) = -(z + 2) / 2 := by
  classical
  change (∫ u in Set.Iic z, AronowAudit.P001.signedKernel u) = -(z + 2) / 2
  have hi (a b : ℝ) :
      Integrable ((Set.Icc a b).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) volume :=
      integrableOn_const (by simp [Real.volume_Icc])
    exact hc.integrable_indicator measurableSet_Icc
  have ha := (hi (-1) 1).const_mul (3 / 2 : ℝ)
  have hb := (hi (-2) 2).const_mul (1 / 2 : ℝ)
  have he (a b c : ℝ) : Set.Icc a b ∩ Set.Iic c = Set.Icc a (min b c) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, le_min_iff]
    tauto
  rw [AronowAudit.P001.signed_kernel_indicator,
    integral_sub ha.integrableOn hb.integrableOn,
    integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_Icc,
    integral_indicator measurableSet_Icc]
  norm_num [integral_const, measureReal_def,
    Measure.restrict_apply measurableSet_Icc, he,
    Real.volume_Icc, min_eq_right (show (1 : ℝ) ≥ z by linarith [hz.2]),
    min_eq_right (show (2 : ℝ) ≥ z by linarith [hz.2])]
  rw [ENNReal.ofReal_eq_zero.mpr (show z + 1 ≤ 0 by linarith [hz.2]),
    ENNReal.toReal_ofReal (show 0 ≤ z + 2 by linarith [hz.1])]
  simp only [ENNReal.toReal_zero]
  ring

end SAP.P001d.WH.W2.P.T58_L1

theorem SAP.P001d.WH.W2.T58_L1_proof : SAP.P001d.WH.W2.T58_L1 := by
  intro a t ht
  have hz : t - a ∈ Set.Icc (-2 : ℝ) (-1) := by
    constructor <;> linarith [ht.1, ht.2]
  have hcdf := AronowAudit.P001.kernel_cdf_correct_integrand
    (n := 1) (by norm_num) (fun _ : Fin 1 => a) AronowAudit.P001.signedKernel
    AronowAudit.P001.signed_kernel_integrals.1 1 (by norm_num) t
  have hsingle :
      kernelCDF signedKernel 1 (fun _ : Fin 1 => a) t =
        (∫ u in Set.Iic ((t - a) / 1), signedKernel u) := by
    change AronowAudit.P001.kernelCDF AronowAudit.P001.signedKernel 1
      (fun _ : Fin 1 => a) t =
        (∫ u in Set.Iic ((t - a) / 1), AronowAudit.P001.signedKernel u)
    simpa using hcdf
  rw [hsingle, div_one]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    SAP.P001d.WH.W2.P.T58_L1.integral_signedKernel_Iic (t - a) hz
