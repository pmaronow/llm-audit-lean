import SAP.P046.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W2.P.T9_L1

noncomputable section

open MeasureTheory
open scoped ENNReal

theorem measurable_wholeL2Error {M : SAP.P046.Study} (hM : SAP.P046.ValidStudy M)
    {n : ℕ} (F : SAP.P046.CrossFit n) (j : Bool) (r : ℝ → ℝ)
    (hr : Measurable r) :
    Measurable (fun a : SAP.P046.Sample n => SAP.P046.wholeL2Error M F j r a) := by
  letI := hM.probability
  have hW : Measurable (fun p : SAP.P046.Sample n × SAP.P046.Unit => SAP.P046.W p.2) := by
    change Measurable (fun p : SAP.P046.Sample n × SAP.P046.Unit => p.2.1)
    exact measurable_fst.comp measurable_snd
  have hfit : Measurable (fun p : SAP.P046.Sample n × SAP.P046.Unit => F.g j p.1 (SAP.P046.W p.2)) := by
    exact (F.measurable_g j).comp (measurable_fst.prodMk hW)
  have hm : Measurable (fun p : SAP.P046.Sample n × SAP.P046.Unit =>
      ENNReal.ofReal ((F.g j p.1 (SAP.P046.W p.2) - r (SAP.P046.W p.2)) ^ 2)) := by
    exact ENNReal.measurable_ofReal.comp ((hfit.sub (hr.comp hW)).pow_const 2)
  simpa [SAP.P046.wholeL2Error] using hm.lintegral_prod_right'

theorem wholeL2Error_training_invariant {M : SAP.P046.Study}
    {n : ℕ} (F : SAP.P046.CrossFit n) (j : Bool) (r : ℝ → ℝ)
    {a b : SAP.P046.Sample n}
    (htrain : ∀ i, F.fold i ≠ j → SAP.P046.observe (a i) = SAP.P046.observe (b i)) :
    SAP.P046.wholeL2Error M F j r a = SAP.P046.wholeL2Error M F j r b := by
  have hfit : F.g j a = F.g j b := F.opposite_fold j a b htrain
  unfold SAP.P046.wholeL2Error
  apply lintegral_congr_ae
  filter_upwards with o
  rw [hfit]

def localizedFit {M : SAP.P046.Study} {n : ℕ}
    (F : SAP.P046.CrossFit n) (g : Bool → ℝ → ℝ) (hg : ∀ j, Measurable (g j))
    (herr : ∀ j, Measurable (fun a : SAP.P046.Sample n =>
      SAP.P046.wholeL2Error M F j (g j) a)) : SAP.P046.CrossFit n where
  fold := F.fold
  g := fun j a w => SAP.P046.wholeLocalPrediction M F g j a w
  measurable_g := by
    intro j
    have hs : MeasurableSet {z : SAP.P046.Sample n × ℝ |
        SAP.P046.wholeL2Error M F j (g j) z.1 ≤ 1} :=
      measurableSet_le ((herr j).comp measurable_fst) measurable_const
    have hm : Measurable (fun z : SAP.P046.Sample n × ℝ =>
        if SAP.P046.wholeL2Error M F j (g j) z.1 ≤ 1
        then F.g j z.1 z.2 else g j z.2) :=
      Measurable.ite hs (F.measurable_g j) ((hg j).comp measurable_snd)
    simpa [SAP.P046.wholeLocalPrediction] using hm
  opposite_fold := by
    intro j a b htrain
    have he := wholeL2Error_training_invariant (M := M) F j (g j) htrain
    funext w
    simp [SAP.P046.wholeLocalPrediction, he, F.opposite_fold j a b htrain]

theorem finite_error_facts {M : SAP.P046.Study}
    {n : ℕ} (F : SAP.P046.CrossFit n) (j : Bool) (r : ℝ → ℝ)
    (hr : Measurable r) (hr2 : MemLp (fun o => r (SAP.P046.W o)) 2 M.law)
    (a : SAP.P046.Sample n)
    (hgood : SAP.P046.wholeL2Error M F j r a ≤ 1) :
    MemLp (fun o => F.g j a (SAP.P046.W o)) 2 M.law ∧
    0 ≤ SAP.P046.l2Sq M (fun w => F.g j a w - r w) ∧
    SAP.P046.l2Sq M (fun w => F.g j a w - r w) ≤ 1 ∧
    ENNReal.ofReal (SAP.P046.l2Sq M (fun w => F.g j a w - r w)) =
      SAP.P046.wholeL2Error M F j r a := by
  let d : SAP.P046.Unit → ℝ := fun o => F.g j a (SAP.P046.W o) - r (SAP.P046.W o)
  have hW : Measurable SAP.P046.W := by
    change Measurable (fun o : SAP.P046.Unit => o.1)
    exact measurable_fst
  have hd : Measurable d := by
    dsimp [d]
    exact ((F.measurable_g j).comp (measurable_const.prodMk hW)).sub
      (hr.comp hW)
  have hfinite : (∫⁻ o, ENNReal.ofReal (d o ^ 2) ∂M.law) < ∞ := by
    have hlt : SAP.P046.wholeL2Error M F j r a < ∞ :=
      lt_of_le_of_lt hgood (by norm_num)
    simpa [SAP.P046.wholeL2Error, d] using hlt
  have hsqInt : Integrable (fun o => d o ^ 2) M.law := by
    refine ⟨(hd.pow_const 2).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun o => sq_nonneg (d o))).2 hfinite
  have hdMem : MemLp d 2 M.law :=
    (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).2 hsqInt
  have hfitMem : MemLp (fun o => F.g j a (SAP.P046.W o)) 2 M.law := by
    convert hdMem.add hr2 using 1
    funext o
    dsimp [d]
    ring
  have hreal0 := ofReal_integral_eq_lintegral_ofReal hsqInt
    (ae_of_all _ fun o => sq_nonneg (d o))
  have hreal : ENNReal.ofReal (SAP.P046.l2Sq M (fun w => F.g j a w - r w)) =
      SAP.P046.wholeL2Error M F j r a := by
    simpa [SAP.P046.l2Sq, SAP.P046.wholeL2Error, d] using hreal0
  have hnonneg : 0 ≤ SAP.P046.l2Sq M (fun w => F.g j a w - r w) :=
    integral_nonneg_of_ae (ae_of_all _ fun o => sq_nonneg (d o))
  have hreal_le : ENNReal.ofReal (SAP.P046.l2Sq M (fun w => F.g j a w - r w)) ≤ 1 := by
    rw [hreal]
    exact hgood
  have hupper : SAP.P046.l2Sq M (fun w => F.g j a w - r w) ≤ 1 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa using hreal_le
  exact ⟨hfitMem, hnonneg, hupper, hreal⟩

end
end SAP.P046.WH.W2.P.T9_L1

theorem SAP.P046.WH.W2.T9_L1_proof : SAP.P046.WH.W2.T9_L1 := by
  intro M hM F g hg hg2
  let G : ∀ n, SAP.P046.CrossFit n := fun n =>
    SAP.P046.WH.W2.P.T9_L1.localizedFit (F n) g hg
      (fun j => SAP.P046.WH.W2.P.T9_L1.measurable_wholeL2Error hM (F n) j (g j) (hg j))
  refine ⟨G, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨rfl, ?_⟩
    intro j a w
    rfl
  · intro n j a
    by_cases he : SAP.P046.wholeL2Error M (F n) j (g j) a ≤ 1
    · have hf := SAP.P046.WH.W2.P.T9_L1.finite_error_facts (F n) j (g j) (hg j) (hg2 j) a he
      simpa [G, SAP.P046.WH.W2.P.T9_L1.localizedFit, SAP.P046.wholeLocalPrediction, he] using hf.1
    · simpa [G, SAP.P046.WH.W2.P.T9_L1.localizedFit,
        SAP.P046.wholeLocalPrediction, he] using hg2 j
  · intro n j a
    by_cases he : SAP.P046.wholeL2Error M (F n) j (g j) a ≤ 1
    · have hf := SAP.P046.WH.W2.P.T9_L1.finite_error_facts (F n) j (g j) (hg j) (hg2 j) a he
      simpa [G, SAP.P046.WH.W2.P.T9_L1.localizedFit, SAP.P046.wholeLocalPrediction, he] using ⟨hf.2.1, hf.2.2.1⟩
    · constructor <;> simp [SAP.P046.l2Sq, G, SAP.P046.WH.W2.P.T9_L1.localizedFit,
        SAP.P046.wholeLocalPrediction, he]
  · intro n j a
    by_cases he : SAP.P046.wholeL2Error M (F n) j (g j) a ≤ 1
    · have hf := SAP.P046.WH.W2.P.T9_L1.finite_error_facts (F n) j (g j) (hg j) (hg2 j) a he
      simpa [G, SAP.P046.WH.W2.P.T9_L1.localizedFit, SAP.P046.wholeLocalPrediction, he] using hf.2.2.2
    · simp [SAP.P046.l2Sq, G, SAP.P046.WH.W2.P.T9_L1.localizedFit,
        SAP.P046.wholeLocalPrediction, he]

