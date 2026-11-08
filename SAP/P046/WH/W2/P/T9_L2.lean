import SAP.P046.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W2.P.T9_L2

open MeasureTheory Filter
open scoped ENNReal Topology

private lemma measurable_wholeL2Error
    (M : SAP.P046.Study) (hM : SAP.P046.ValidStudy M)
    {n : ℕ} (F : SAP.P046.CrossFit n) (j : Bool) (g : ℝ → ℝ)
    (hg : Measurable g) :
    Measurable (SAP.P046.wholeL2Error M F j g) := by
  letI := hM.probability
  have hW : Measurable (fun o : SAP.P046.Unit => SAP.P046.W o) := measurable_fst
  have hpair : Measurable
      (fun p : SAP.P046.Sample n × SAP.P046.Unit => (p.1, SAP.P046.W p.2)) :=
    measurable_fst.prodMk (hW.comp measurable_snd)
  have hpred : Measurable
      (fun p : SAP.P046.Sample n × SAP.P046.Unit => (F.g j) p.1 (SAP.P046.W p.2)) :=
    (F.measurable_g j).comp hpair
  have htarget : Measurable
      (fun p : SAP.P046.Sample n × SAP.P046.Unit => g (SAP.P046.W p.2)) :=
    hg.comp (hW.comp measurable_snd)
  have hsq : Measurable
      (fun p : SAP.P046.Sample n × SAP.P046.Unit =>
        ENNReal.ofReal (((F.g j) p.1 (SAP.P046.W p.2) - g (SAP.P046.W p.2)) ^ 2)) := by
    exact (hpred.sub htarget).pow_const 2 |>.ennreal_ofReal
  change Measurable
    (fun a : SAP.P046.Sample n =>
      ∫⁻ o, ENNReal.ofReal (((F.g j) a (SAP.P046.W o) - g (SAP.P046.W o)) ^ 2)
        ∂M.law)
  exact hsq.lintegral_prod_right'

end SAP.P046.WH.W2.P.T9_L2

open MeasureTheory Filter
open scoped ENNReal Topology

theorem SAP.P046.WH.W2.T9_L2_proof : SAP.P046.WH.W2.T9_L2 := by
  intro M hM F j g hg hmean
  letI := hM.probability
  intro eps heps
  have hmeas : ∀ n, Measurable (SAP.P046.wholeL2Error M (F n) j g) := by
    intro n
    exact SAP.P046.WH.W2.P.T9_L2.measurable_wholeL2Error M hM (F n) j g hg
  have hεne : ENNReal.ofReal eps ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr heps
  have hεtop : ENNReal.ofReal eps ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmarkov : ∀ n,
      sampleLaw M n {a | ENNReal.ofReal eps ≤ wholeL2Error M (F n) j g a} ≤
        (∫⁻ a, wholeL2Error M (F n) j g a ∂sampleLaw M n) / ENNReal.ofReal eps := by
    intro n
    exact MeasureTheory.meas_ge_le_lintegral_div (hmeas n).aemeasurable hεne hεtop
  have hdiv : Filter.Tendsto
      (fun n => (∫⁻ a, wholeL2Error M (F n) j g a ∂sampleLaw M n) /
        ENNReal.ofReal eps) atTop (𝓝 (0 / ENNReal.ofReal eps)) :=
    ENNReal.Tendsto.div_const hmean (Or.inr hεne)
  have hdiv0 : Filter.Tendsto
      (fun n => (∫⁻ a, wholeL2Error M (F n) j g a ∂sampleLaw M n) /
        ENNReal.ofReal eps) atTop (𝓝 0) := by
    simpa using hdiv
  have hprob_ext : Filter.Tendsto
      (fun n => sampleLaw M n
        {a | ENNReal.ofReal eps ≤ wholeL2Error M (F n) j g a}) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv0
    · exact Eventually.of_forall fun _ => zero_le
    · exact Eventually.of_forall hmarkov
  have hsubset : ∀ n,
      {a : SAP.P046.Sample n | ENNReal.ofReal eps < wholeL2Error M (F n) j g a} ⊆
      {a | ENNReal.ofReal eps ≤ wholeL2Error M (F n) j g a} := by
    intro n a ha
    change ENNReal.ofReal eps < wholeL2Error M (F n) j g a at ha
    exact le_of_lt ha
  have hreal_ext : Filter.Tendsto
      (fun n => sampleLaw M n
        {a | ENNReal.ofReal eps < wholeL2Error M (F n) j g a}) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprob_ext
    · exact Eventually.of_forall fun _ => zero_le
    · exact Eventually.of_forall fun n => measure_mono (hsubset n)
  have hfinite : ∀ n, sampleLaw M n
      {a | ENNReal.ofReal eps < wholeL2Error M (F n) j g a} ≠ ⊤ := by
    intro n
    exact MeasureTheory.measure_ne_top _ _
  exact (ENNReal.tendsto_toReal_zero_iff hfinite).2 hreal_ext
