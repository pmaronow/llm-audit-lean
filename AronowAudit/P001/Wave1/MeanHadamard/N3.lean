import AronowAudit.P001.Wave1.MeanHadamardBlueprint

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.MeanHadamard

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

theorem n3_proof : N3 := by
  classical
  intro h2 n
  letI : IsProbabilityMeasure baseLaw := h2.1
  letI : IsProbabilityMeasure (contam n) := (h2.2.2.2 n).1
  have hr : 0 < contR n := contR_pos n
  have hr1 : 1 ≤ contR n := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [contR]
    linarith
  have ha0 : 0 ≤ contA n := by unfold contA; positivity
  have ha1 : contA n ≤ 1 := by
    have hi : (contR n)⁻¹ ≤ 1 := (inv_le_one₀ hr).2 hr1
    have hi0 : 0 ≤ (contR n)⁻¹ := by positivity
    exact pow_le_one₀ hi0 hi
  have hcoef : 0 ≤ 1-contA n := sub_nonneg.mpr ha1
  have hcdf (x : ℝ) : AronowAudit.P001.cdf (contam n) id x =
      (1-contA n) * AronowAudit.P001.cdf baseLaw id x +
        contA n * (if contR n+1 ≤ x then 1 else 0) := by
    change ((contam n) (Set.Iic x)).toReal = _
    simp only [contam, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top baseLaw _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (Measure.dirac _) _))]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef,
      ENNReal.toReal_ofReal ha0]
    by_cases hx : contR n + 1 ≤ x <;>
      simp [hx, Measure.dirac_apply, Set.indicator, AronowAudit.P001.cdf, prob, Set.Iic_def]
  have hnorm : ‖contCDF n - baseCDF‖ ≤ contA n := by
    apply lp.norm_le_of_forall_le ha0
    intro x
    change ‖contCDF n x - baseCDF x‖ ≤ contA n
    rw [contCDF, baseCDF,
      kolmogorov_embedding_preserves_cdf_supporting (contam n) x,
      kolmogorov_embedding_preserves_cdf_supporting baseLaw x, hcdf]
    have hF0 : 0 ≤ AronowAudit.P001.cdf baseLaw id x := ENNReal.toReal_nonneg
    have hF1 : AronowAudit.P001.cdf baseLaw id x ≤ 1 := measureReal_le_one
    rw [Real.norm_eq_abs, abs_le]
    by_cases hx : contR n+1 ≤ x
    · simp only [if_pos hx]
      constructor <;> nlinarith [mul_nonneg ha0 hF0,
        mul_le_mul_of_nonneg_left hF1 ha0]
    · simp only [if_neg hx]
      constructor <;> nlinarith [mul_nonneg ha0 hF0,
        mul_le_mul_of_nonneg_left hF1 ha0]
  have ht : 0 < contT n := contT_pos n
  have hratio : (contT n)⁻¹ * contA n = (contR n)⁻¹ := by
    unfold contA contT
    field_simp [hr.ne']
    <;> ring
  calc
    ‖dirSeq n‖ = |(contT n)⁻¹| * ‖contCDF n - baseCDF‖ := by
      rw [dirSeq, norm_smul, Real.norm_eq_abs]
    _ ≤ (contT n)⁻¹ * contA n := by
      rw [abs_of_pos (inv_pos.mpr ht)]
      exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr ht.le)
    _ = (contR n)⁻¹ := hratio

end

end AronowAudit.P001.Wave1.MeanHadamard
