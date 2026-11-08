import SAP.P046.WH.W2.Leaves
import AronowAudit.P061.P061_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W2.P.T9_L4

open MeasureTheory ProbabilityTheory Filter

noncomputable section

private theorem measurable_Y_local : Measurable Y := by
  have mx : Measurable X := by
    unfold X
    exact (measurable_of_countable bit).comp measurable_snd.fst
  unfold Y Y0 Y1
  exact (measurable_const.sub mx).mul
    ((measurable_of_countable bit).comp measurable_snd.snd.fst) |>.add
    (mx.mul ((measurable_of_countable bit).comp measurable_snd.snd.snd))

private theorem measurable_X_local : Measurable X := by
  unfold X
  exact (measurable_of_countable bit).comp measurable_snd.fst

private theorem measurable_adjusted_local (M : Study) (hM : ValidStudy M)
    {n : ℕ} (F : CrossFit n) : Measurable (adjusted M F) := by
  unfold adjusted
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i hi
  have mev : Measurable (fun a : Sample n => a i) := measurable_pi_apply i
  have mw : Measurable (fun a : Sample n => W (a i)) := measurable_fst.comp mev
  have mg := (F.measurable_g (F.fold i)).comp (measurable_id.prodMk mw)
  exact (((measurable_X_local.comp mev).mul
    ((measurable_Y_local.comp mev).sub mg)).div
    (hM.measurable_pi.comp mw)).add mg

theorem _root_.SAP.P046.WH.W2.T9_L4_proof : SAP.P046.WH.W2.T9_L4 := by
  intro M hM F G v hagree hnormal
  rcases hnormal with ⟨hv, hprob, hG⟩
  letI := hprob
  let A : ∀ n, Sample n → ℝ := fun n a =>
    Real.sqrt n * (adjusted M (G n) a - mu M)
  let B : ∀ n, Sample n → ℝ := fun n a =>
    Real.sqrt n * (adjusted M (F n) a - mu M)
  have hA : TendstoInDistribution A atTop (fun z : ℝ => z)
      (fun n => sampleLaw M n) (gaussianReal 0 v.toNNReal) := by
    simpa only [A] using hG
  have mA (n : ℕ) : AEMeasurable (A n) (sampleLaw M n) := by
    change AEMeasurable
      (fun a => Real.sqrt n * (adjusted M (G n) a - mu M)) (sampleLaw M n)
    exact ((measurable_adjusted_local M hM (G n)).sub measurable_const |>.const_mul
      (Real.sqrt n)).aemeasurable
  have mB (n : ℕ) : AEMeasurable (B n) (sampleLaw M n) := by
    change AEMeasurable
      (fun a => Real.sqrt n * (adjusted M (F n) a - mu M)) (sampleLaw M n)
    exact ((measurable_adjusted_local M hM (F n)).sub measurable_const |>.const_mul
      (Real.sqrt n)).aemeasurable
  change Tendsto (fun n =>
    (sampleLaw M n {a | adjusted M (F n) a ≠ adjusted M (G n) a}).toReal)
      atTop (nhds 0) at hagree
  have hdisagree := hagree
  have hdist : ∀ eps > 0, Tendsto (fun n => (sampleLaw M n).real
      {a | eps ≤ dist (A n a) (B n a)}) atTop (nhds 0) := by
    intro eps heps
    apply squeeze_zero (fun _ => measureReal_nonneg) _
      (by simpa only [Measure.real] using hdisagree)
    intro n
    apply measureReal_mono (h₂ := by finiteness)
    intro a ha
    by_contra hnot
    have heq : adjusted M (F n) a = adjusted M (G n) a :=
      not_ne_iff.mp hnot
    have hab : A n a = B n a := by simp [A, B, heq]
    change eps ≤ dist (A n a) (B n a) at ha
    rw [hab, dist_self] at ha
    exact (not_le_of_gt heps) ha
  have hweakA : AronowAudit.P061.Analytic.WeakConvergesLaw
      (fun n => (sampleLaw M n).map (A n)) (gaussianReal 0 v.toNNReal) := by
    have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hA.tendsto
    intro test
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id'] using hh test
  have hweakB := AronowAudit.P061.Analytic.weakConvergesLaw_slutsky_dist
    mA mB hweakA hdist
  have hB : TendstoInDistribution B atTop (fun z : ℝ => z)
      (fun n => sampleLaw M n) (gaussianReal 0 v.toNNReal) := by
    refine ⟨mB, measurable_id.aemeasurable, ?_⟩
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
    intro test
    simpa only [ProbabilityMeasure.coe_mk, B, Measure.map_id'] using hweakB test
  refine ⟨hv, hprob, ?_⟩
  simpa only [B] using hB

end
end SAP.P046.WH.W2.P.T9_L4
