import SAP.P046.WH.W1.Leaves
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W1.P.T5_L2

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

lemma q_lower (M : Study) (hM : ValidStudy M) :
    ∀ᵐ o ∂M.law, M.delta ≤ q M (W o) := by
  filter_upwards [hM.positivity] with o ho
  have hp : 0 < M.pi (W o) := lt_trans hM.delta_pos ho.1
  have hp1 : M.pi (W o) < 1 := by linarith [hM.delta_pos]
  rw [q, le_div_iff₀ hp]
  nlinarith [ho.2, mul_nonneg hM.delta_pos.le (sub_nonneg.mpr hp1.le)]

lemma q_upper (M : Study) (hM : ValidStudy M) :
    ∀ᵐ o ∂M.law, 0 ≤ q M (W o) ∧ q M (W o) ≤ M.delta⁻¹ := by
  filter_upwards [hM.positivity] with o ho
  have hp : 0 < M.pi (W o) := lt_trans hM.delta_pos ho.1
  have hp1 : M.pi (W o) < 1 := by linarith [hM.delta_pos]
  refine ⟨div_nonneg (by linarith) hp.le, ?_⟩
  calc
    q M (W o) ≤ (M.pi (W o))⁻¹ := by
      dsimp [q]
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith) hp.le
    _ ≤ M.delta⁻¹ := (inv_le_inv₀ hp hM.delta_pos).2 ho.1.le

lemma zero_risk_bound (M : Study) (hM : ValidStudy M) :
    wholeRisk M (fun _ => 0) ≤ ENNReal.ofReal M.delta⁻¹ := by
  letI := hM.probability
  have hp := q_upper M hM
  have hpoint : ∀ᵐ o ∂M.law,
      ENNReal.ofReal (q M (W o) * (Y1 o - (fun _ => (0 : ℝ)) (W o)) ^ 2) ≤
        ENNReal.ofReal M.delta⁻¹ := by
    filter_upwards [hp] with o ho
    have hy : Y1 o = 0 ∨ Y1 o = 1 := by
      cases o.2.2.2 <;> simp [Y1, bit]
    have hy2 : (Y1 o - (fun _ => (0 : ℝ)) (W o)) ^ 2 ≤ 1 := by
      rcases hy with h | h <;> simp [h]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [ho.1, ho.2, hy2])
  unfold wholeRisk
  calc
    (∫⁻ o, ENNReal.ofReal (q M (W o) * (Y1 o - (fun _ => (0 : ℝ)) (W o)) ^ 2) ∂M.law) ≤
        ∫⁻ _o : Unit, ENNReal.ofReal M.delta⁻¹ ∂M.law :=
          MeasureTheory.lintegral_mono_ae hpoint
    _ = ENNReal.ofReal M.delta⁻¹ := by simp

end SAP.P046.WH.W1.P.T5_L2

theorem SAP.P046.WH.W1.T5_L2_proof : SAP.P046.WH.W1.T5_L2 := by
  classical
  intro M hM g hg hcmp
  letI := hM.probability
  have hzero := SAP.P046.WH.W1.P.T5_L2.zero_risk_bound M hM
  have hzeroFinite : wholeRisk M (fun _ => 0) < ⊤ := by
    exact lt_of_le_of_lt hzero ENNReal.ofReal_lt_top
  have hRiskFinite : wholeRisk M g < ⊤ := lt_of_le_of_lt hcmp hzeroFinite

  let d : Unit → ℝ := fun o => g (W o) - Y1 o
  have hdMeas : Measurable d := (hg.comp measurable_fst).sub measurable_Y1
  have hqlo := SAP.P046.WH.W1.P.T5_L2.q_lower M hM
  have hdBound : ∀ᵐ o ∂M.law,
      ENNReal.ofReal (d o ^ 2) ≤
        ENNReal.ofReal (M.delta⁻¹) *
          ENNReal.ofReal (q M (W o) * (Y1 o - g (W o)) ^ 2) := by
    filter_upwards [hqlo] with o hq
    have hcoef : 1 ≤ M.delta⁻¹ * q M (W o) := by
      rw [mul_comm, ← div_eq_mul_inv]
      exact (one_le_div₀ hM.delta_pos).2 hq
    have hreal : d o ^ 2 ≤ M.delta⁻¹ * (q M (W o) * (Y1 o - g (W o)) ^ 2) := by
      dsimp [d]
      have hs : (g (W o) - Y1 o) ^ 2 = (Y1 o - g (W o)) ^ 2 := by ring
      rw [hs]
      nlinarith [sq_nonneg (Y1 o - g (W o)), hcoef]
    calc
      ENNReal.ofReal (d o ^ 2) ≤
          ENNReal.ofReal (M.delta⁻¹ * (q M (W o) * (Y1 o - g (W o)) ^ 2)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (M.delta⁻¹) *
          ENNReal.ofReal (q M (W o) * (Y1 o - g (W o)) ^ 2) :=
        ENNReal.ofReal_mul (inv_nonneg.mpr hM.delta_pos.le)

  have hqNonneg : ∀ᵐ o ∂M.law, 0 ≤ q M (W o) :=
    (SAP.P046.WH.W1.P.T5_L2.q_upper M hM).mono fun o ho => ho.1
  have hRiskGNonneg : 0 ≤ᵐ[M.law] (fun o => q M (W o) * (Y1 o - g (W o)) ^ 2) :=
    hqNonneg.mono fun o ho => mul_nonneg ho (sq_nonneg _)
  have hRiskGMeas : Measurable (fun o => q M (W o) * (Y1 o - g (W o)) ^ 2) :=
    ((measurable_const.sub (hM.measurable_pi.comp measurable_fst)).div
      (hM.measurable_pi.comp measurable_fst)).mul
      ((measurable_Y1.sub (hg.comp measurable_fst)).pow_const 2)
  have hRiskGOfRealMeas : Measurable
      (fun o => ENNReal.ofReal (q M (W o) * (Y1 o - g (W o)) ^ 2)) :=
    ENNReal.measurable_ofReal.comp hRiskGMeas
  have hRisk0Nonneg : 0 ≤ᵐ[M.law] (fun o => q M (W o) * (Y1 o - 0) ^ 2) :=
    hqNonneg.mono fun o ho => mul_nonneg ho (sq_nonneg _)
  have hRisk0Meas : Measurable (fun o => q M (W o) * (Y1 o - 0) ^ 2) :=
    ((measurable_const.sub (hM.measurable_pi.comp measurable_fst)).div
      (hM.measurable_pi.comp measurable_fst)).mul
      ((measurable_Y1.sub measurable_const).pow_const 2)

  have hdLIntegral : (∫⁻ o, ENNReal.ofReal (d o ^ 2) ∂M.law) < ⊤ := by
    have hle : (∫⁻ o, ENNReal.ofReal (d o ^ 2) ∂M.law) ≤
        ENNReal.ofReal (M.delta⁻¹) * wholeRisk M g := by
      calc
        _ ≤ ∫⁻ o, ENNReal.ofReal (M.delta⁻¹) *
              ENNReal.ofReal (q M (W o) * (Y1 o - g (W o)) ^ 2) ∂M.law :=
            MeasureTheory.lintegral_mono_ae hdBound
        _ = ENNReal.ofReal (M.delta⁻¹) * wholeRisk M g := by
          rw [MeasureTheory.lintegral_const_mul _ hRiskGOfRealMeas]
          rfl
    exact lt_of_le_of_lt hle
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRiskFinite)

  have hdFinite : MeasureTheory.HasFiniteIntegral (fun o => d o ^ 2) M.law := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun o => sq_nonneg (d o)))]
    exact hdLIntegral
  have hdIntegrable : MeasureTheory.Integrable (fun o => d o ^ 2) M.law :=
    ⟨(hdMeas.pow_const 2).aestronglyMeasurable, hdFinite⟩
  have hdLp : MeasureTheory.MemLp d 2 M.law :=
    (MeasureTheory.memLp_two_iff_integrable_sq hdMeas.aestronglyMeasurable).2 hdIntegrable
  have hyLp : MeasureTheory.MemLp Y1 2 M.law :=
    MeasureTheory.MemLp.of_bound measurable_Y1.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun o => by
        cases hb : o.2.2.2 <;> simp [Y1, bit, hb])
  have hgLp : MeasureTheory.MemLp (fun o => g (W o)) 2 M.law := by
    have hadd : MeasureTheory.MemLp (fun o => d o + Y1 o) 2 M.law := hdLp.add hyLp
    have heq : (fun o => d o + Y1 o) =ᵐ[M.law] (fun o => g (W o)) := by
      filter_upwards [] with o
      dsimp [d]
      ring
    exact (MeasureTheory.memLp_congr_ae heq).1 hadd
  have hRiskGId : risk M g = (wholeRisk M g).toReal := by
    unfold risk wholeRisk
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      hRiskGNonneg hRiskGMeas.aestronglyMeasurable
  have hRisk0Id : risk M (fun _ => 0) = (wholeRisk M (fun _ => 0)).toReal := by
    unfold risk wholeRisk
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      hRisk0Nonneg hRisk0Meas.aestronglyMeasurable
  refine ⟨hgLp, hRiskFinite, ?_⟩
  rw [hRiskGId, hRisk0Id]
  exact ENNReal.toReal_mono hzeroFinite.ne hcmp
