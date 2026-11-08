import SAP.P046.WH.W1.Leaves
import AronowAudit.P061.P061_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

namespace SAP.P046.WH.W1.P.T5_L5

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

theorem measurable_adjusted (M : Study) (hM : ValidStudy M) {n : ℕ}
    (F : CrossFit n) : Measurable (adjusted M F) := by
  unfold adjusted
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i hi
  have mev : Measurable (fun a : Sample n => a i) := measurable_pi_apply i
  have mw : Measurable (fun a : Sample n => W (a i)) := measurable_fst.comp mev
  have mg := (F.measurable_g (F.fold i)).comp (measurable_id.prodMk mw)
  exact (((measurable_X.comp mev).mul ((measurable_Y.comp mev).sub mg)).div
    (hM.measurable_pi.comp mw)).add mg

end

end SAP.P046.WH.W1.P.T5_L5

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

theorem SAP.P046.WH.W1.T5_L5_proof : SAP.P046.WH.W1.T5_L5 := by
  classical
  intro M hM F G v hG hdisagree
  letI := hM.probability
  rcases hG with ⟨hv, hG⟩
  rcases hG with ⟨hprob, hG⟩
  letI := hprob
  let A : ∀ n, Sample n → ℝ := fun n a =>
    Real.sqrt n * (adjusted M (G n) a - mu M)
  let B : ∀ n, Sample n → ℝ := fun n a =>
    Real.sqrt n * (adjusted M (F n) a - mu M)
  have hA : TendstoInDistribution A atTop (fun z : ℝ => z)
      (fun n => sampleLaw M n) (gaussianReal 0 v.toNNReal) := by
    simpa only [A] using hG
  have mA (n : ℕ) : AEMeasurable (A n) (sampleLaw M n) := by
    exact ((SAP.P046.WH.W1.P.T5_L5.measurable_adjusted M hM (G n)
      ).sub measurable_const).const_mul _ |>.aemeasurable
  have mB (n : ℕ) : AEMeasurable (B n) (sampleLaw M n) := by
    exact ((SAP.P046.WH.W1.P.T5_L5.measurable_adjusted M hM (F n)
      ).sub measurable_const).const_mul _ |>.aemeasurable
  have hdist : ∀ eps > 0, Tendsto (fun n => (sampleLaw M n).real
      {a | eps ≤ dist (A n a) (B n a)}) atTop (nhds 0) := by
    intro eps heps
    have hsubset (n : ℕ) : {a : Sample n | eps ≤ dist (A n a) (B n a)} ⊆
        {a | adjusted M (F n) a ≠ adjusted M (G n) a} := by
      intro a ha
      by_contra hnot
      have heq : adjusted M (F n) a = adjusted M (G n) a := by
        simpa only [Set.mem_ofPred_eq, not_ne_iff] using hnot
      have hAB : A n a = B n a := by simp [A, B, heq]
      change eps ≤ dist (A n a) (B n a) at ha
      rw [hAB, dist_self] at ha
      exact (not_le_of_gt heps) ha
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hdisagree
    intro n
    exact measureReal_mono (hsubset n)
  have hweakA : AronowAudit.P061.Analytic.WeakConvergesLaw
      (fun n => (sampleLaw M n).map (A n)) (gaussianReal 0 v.toNNReal) := by
    have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hA.tendsto
    intro test
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id'] using hh test
  have hweakB := AronowAudit.P061.Analytic.weakConvergesLaw_slutsky_dist
    hA.forall_aemeasurable mB hweakA hdist
  refine ⟨hv, ⟨hprob, mB, measurable_id.aemeasurable, ?_⟩⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
  intro test
  simpa only [ProbabilityMeasure.coe_mk, B, Measure.map_id'] using hweakB test
