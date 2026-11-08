import SAP.P046.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W2.P.T9_L3

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section

private theorem whole_error_measurable (M : SAP.P046.Study)
    (hM : SAP.P046.ValidStudy M)
    (F : ∀ n, SAP.P046.CrossFit n) (g : Bool → ℝ → ℝ)
    (hg : ∀ j, Measurable (g j)) (n : ℕ) (j : Bool) :
    Measurable (SAP.P046.wholeL2Error M (F n) j (g j)) := by
  have hfun : Measurable (fun p : SAP.P046.Sample n × SAP.P046.Unit =>
      ENNReal.ofReal (((F n).g j p.1 (SAP.P046.W p.2) - g j (SAP.P046.W p.2)) ^ 2)) := by
    apply ENNReal.measurable_ofReal.comp
    have hpred : Measurable (fun p : SAP.P046.Sample n × SAP.P046.Unit =>
        (F n).g j p.1 (SAP.P046.W p.2)) :=
      ((F n).measurable_g j).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hgpred : Measurable (fun p : SAP.P046.Sample n × SAP.P046.Unit =>
        g j (SAP.P046.W p.2)) :=
      (hg j).comp (measurable_fst.comp measurable_snd)
    exact (hpred.sub hgpred).pow_const 2
  letI := hM.probability
  change Measurable (fun a : SAP.P046.Sample n =>
    ∫⁻ o, ENNReal.ofReal (((F n).g j a (SAP.P046.W o) -
      g j (SAP.P046.W o)) ^ 2) ∂M.law)
  exact hfun.lintegral_prod_right'

private theorem local_sq_measurable (M : SAP.P046.Study)
    (hM : SAP.P046.ValidStudy M)
    (F G : ∀ n, SAP.P046.CrossFit n) (g : Bool → ℝ → ℝ)
    (hg : ∀ j, Measurable (g j))
    (hseq : SAP.P046.WH.W2.LocalizedSequence M F G g)
    (n : ℕ) (j : Bool) :
    Measurable (fun a : SAP.P046.Sample n =>
      SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)) := by
  let D : SAP.P046.Sample n → ℝ := fun a =>
    SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)
  let E : SAP.P046.Sample n → ℝ≥0∞ :=
    SAP.P046.wholeL2Error M (F n) j (g j)
  have hE : Measurable E := whole_error_measurable M hM F g hg n j
  have hIF : Measurable (fun a : SAP.P046.Sample n =>
      if E a ≤ 1 then E a else 0) := by
    exact Measurable.ite (measurableSet_le hE measurable_const) hE measurable_const
  have hEq : D = fun a => ENNReal.toReal (if E a ≤ 1 then E a else 0) := by
    funext a
    have hD := hseq.2.2.2 n j a
    have hbound := hseq.2.2.1 n j a
    calc
      D a = ENNReal.toReal (ENNReal.ofReal (D a)) := by
        rw [ENNReal.toReal_ofReal hbound.1]
      _ = ENNReal.toReal (if E a ≤ 1 then E a else 0) := by rw [hD]
  change Measurable D
  rw [hEq]
  exact hIF.ennreal_toReal

private theorem local_sq_integrable (M : SAP.P046.Study)
    (hM : SAP.P046.ValidStudy M) (F G : ∀ n, SAP.P046.CrossFit n)
    (g : Bool → ℝ → ℝ) (hg : ∀ j, Measurable (g j))
    (hseq : SAP.P046.WH.W2.LocalizedSequence M F G g)
    (n : ℕ) (j : Bool) :
    Integrable (fun a : SAP.P046.Sample n =>
      SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)) (SAP.P046.sampleLaw M n) := by
  letI := hM.probability
  letI : IsProbabilityMeasure (SAP.P046.sampleLaw M n) := inferInstance
  apply (memLp_one_iff_integrable).1
  apply memLp_of_bounded (a := 0) (b := 1)
  · exact ae_of_all _ (fun a => hseq.2.2.1 n j a)
  · exact (local_sq_measurable M hM F G g hg hseq n j).aestronglyMeasurable

private theorem local_tail_subset (M : SAP.P046.Study)
    (F G : ∀ n, SAP.P046.CrossFit n) (g : Bool → ℝ → ℝ)
    (hseq : SAP.P046.WH.W2.LocalizedSequence M F G g)
    (n : ℕ) (j : Bool) {eta : ℝ} (heta : 0 < eta) :
    {a : SAP.P046.Sample n | eta <
      SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)} ⊆
    {a | ENNReal.ofReal eta < SAP.P046.wholeL2Error M (F n) j (g j) a} := by
  intro a ha
  let D := SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)
  let E := SAP.P046.wholeL2Error M (F n) j (g j) a
  have hD : ENNReal.ofReal D = if E ≤ 1 then E else 0 := hseq.2.2.2 n j a
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal D :=
    ENNReal.ofReal_pos.mpr (lt_trans heta ha)
  by_cases hE : E ≤ 1
  · rw [if_pos hE] at hD
    calc
      ENNReal.ofReal eta < ENNReal.ofReal D :=
        (ENNReal.ofReal_lt_ofReal_iff (lt_trans heta ha)).mpr ha
      _ = E := hD
  · rw [if_neg hE] at hD
    rw [hD] at hpos
    exact (lt_irrefl _ hpos).elim

private theorem local_expectation_bound (M : SAP.P046.Study)
    (hM : SAP.P046.ValidStudy M) (F G : ∀ n, SAP.P046.CrossFit n)
    (g : Bool → ℝ → ℝ) (hg : ∀ j, Measurable (g j))
    (hseq : SAP.P046.WH.W2.LocalizedSequence M F G g)
    (n : ℕ) (j : Bool) {eta : ℝ} (heta : 0 < eta) :
    (∫ a, SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)
      ∂SAP.P046.sampleLaw M n) ≤
      eta + (SAP.P046.sampleLaw M n
        {a | eta < SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)}).toReal := by
  letI := hM.probability
  letI : IsProbabilityMeasure (SAP.P046.sampleLaw M n) := inferInstance
  let D : SAP.P046.Sample n → ℝ := fun a =>
    SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)
  let A : Set (SAP.P046.Sample n) := {a | eta < D a}
  have hDm : Measurable D := local_sq_measurable M hM F G g hg hseq n j
  have hA : MeasurableSet A := measurableSet_lt measurable_const hDm
  have hDi : Integrable D (SAP.P046.sampleLaw M n) :=
    local_sq_integrable M hM F G g hg hseq n j
  have hIi : Integrable (A.indicator (fun _ : SAP.P046.Sample n => (1 : ℝ)))
      (SAP.P046.sampleLaw M n) := (integrable_const (1 : ℝ)).indicator hA
  have hpoint : ∀ a, D a ≤ eta + A.indicator (fun _ => (1 : ℝ)) a := by
    intro a
    by_cases ha : eta < D a
    · have hDle := (hseq.2.2.1 n j a).2
      simp [A, ha]
      linarith
    · simp [A, ha]
      exact le_of_not_gt ha
  have hmono := integral_mono hDi (integrable_const eta |>.add hIi) hpoint
  have hsimp : (∫ a, eta + A.indicator (fun _ : SAP.P046.Sample n => (1 : ℝ)) a
      ∂SAP.P046.sampleLaw M n) = eta + (SAP.P046.sampleLaw M n A).toReal := by
    rw [integral_add (integrable_const eta) hIi, integral_const]
    rw [integral_indicator_const (e := (1 : ℝ)) hA]
    simp [Measure.real_def, A]
  have hmono' : (∫ a, D a ∂SAP.P046.sampleLaw M n) ≤
      eta + (SAP.P046.sampleLaw M n A).toReal := by
    calc
      (∫ a, D a ∂SAP.P046.sampleLaw M n) ≤
          ∫ a, eta + A.indicator (fun _ : SAP.P046.Sample n => (1 : ℝ)) a
            ∂SAP.P046.sampleLaw M n := hmono
      _ = eta + (SAP.P046.sampleLaw M n A).toReal := hsimp
  simpa [D, A] using hmono'

private theorem local_probability (M : SAP.P046.Study)
    (hM : SAP.P046.ValidStudy M) (F G : ∀ n, SAP.P046.CrossFit n)
    (g : Bool → ℝ → ℝ) (hseq : SAP.P046.WH.W2.LocalizedSequence M F G g)
    (hp : ∀ j, SAP.P046.WholeL2InProbability_W2 M F j (g j))
    (j : Bool) : SAP.P046.L2InProbability M G j (g j) := by
  letI := hM.probability
  intro eps heps
  have hlim := hp j eps heps
  have hsubset (n : ℕ) :
      {a : SAP.P046.Sample n | eps <
        SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)} ⊆
      {a | ENNReal.ofReal eps < SAP.P046.wholeL2Error M (F n) j (g j) a} :=
    local_tail_subset M F G g hseq n j heps
  -- The probability of the localized tail is squeezed by the original tail.
  have hbound : ∀ n, (SAP.P046.sampleLaw M n
      {a | eps < SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)}).toReal ≤
      (SAP.P046.sampleLaw M n
        {a | ENNReal.ofReal eps < SAP.P046.wholeL2Error M (F n) j (g j) a}).toReal := by
    intro n
    exact measureReal_mono (hsubset n)
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound hlim

private theorem local_mean_square (M : SAP.P046.Study)
    (hM : SAP.P046.ValidStudy M) (F G : ∀ n, SAP.P046.CrossFit n)
    (g : Bool → ℝ → ℝ) (hg : ∀ j, Measurable (g j))
    (hseq : SAP.P046.WH.W2.LocalizedSequence M F G g)
    (hp : ∀ j, SAP.P046.WholeL2InProbability_W2 M F j (g j))
    (j : Bool) : SAP.P046.L2InMeanSquare M G j (g j) := by
  letI := hM.probability
  constructor
  · have hnonneg (n : ℕ) :
        0 ≤ ∫ a, SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)
          ∂SAP.P046.sampleLaw M n :=
      integral_nonneg (fun a => (hseq.2.2.1 n j a).1)
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · filter_upwards [] with n
      exact lt_of_lt_of_le hb (hnonneg n)
    · let eta : ℝ := min (b / 2) (1 / 2)
      have heta : 0 < eta := by dsimp [eta]; positivity
      have hetab : eta < b := by dsimp [eta]; linarith [min_le_left (b / 2) (1 / 2)]
      have hgap : 0 < b - eta := sub_pos.mpr hetab
      have hprob := hp j eta heta
      have hsmall : ∀ᶠ n in atTop,
          (SAP.P046.sampleLaw M n
            {a | ENNReal.ofReal eta < SAP.P046.wholeL2Error M (F n) j (g j) a}).toReal
            < b - eta := (tendsto_order.1 hprob).2 (b - eta) hgap
      filter_upwards [hsmall] with n hn
      have hbound := local_expectation_bound M hM F G g hg hseq n j heta
      have hprob_le₀ := measureReal_mono (μ := SAP.P046.sampleLaw M n)
        (local_tail_subset M F G g hseq n j heta)
      have hprob_le :
          (SAP.P046.sampleLaw M n
            {a | eta < SAP.P046.l2Sq M (fun w => (G n).g j a w - g j w)}).toReal ≤
          (SAP.P046.sampleLaw M n
            {a | ENNReal.ofReal eta < SAP.P046.wholeL2Error M (F n) j (g j) a}).toReal := by
        simpa only [Measure.real_def] using hprob_le₀
      linarith
  · intro n
    exact local_sq_integrable M hM F G g hg hseq n j

end
end SAP.P046.WH.W2.P.T9_L3

theorem SAP.P046.WH.W2.T9_L3_proof : SAP.P046.WH.W2.T9_L3 := by
  intro M hM F G g hg hseq hp j
  exact ⟨SAP.P046.WH.W2.P.T9_L3.local_mean_square M hM F G g hg hseq hp j,
    SAP.P046.WH.W2.P.T9_L3.local_probability M hM F G g hseq hp j⟩
