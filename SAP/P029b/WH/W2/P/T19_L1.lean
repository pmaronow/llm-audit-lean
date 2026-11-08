import SAP.P029b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W2.P.T19_L1

open Filter
open MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

lemma logisticCDFW2_eq_sigmoid (t : ℝ) :
    SAP.P029b.logisticCDFW2 t = Real.sigmoid (t / 3) := by
  simp [SAP.P029b.logisticCDFW2, Real.sigmoid_def, neg_div]

noncomputable def logisticStieltjes : StieltjesFunction ℝ where
  toFun t := Real.sigmoid (t / 3)
  mono' := by
    intro a b hab
    apply Real.sigmoid_monotone
    exact div_le_div_of_nonneg_right hab (by norm_num)
  right_continuous' := by
    intro x
    exact (_root_.continuous_sigmoid.comp (continuous_id.div_const 3)).continuousWithinAt

lemma logisticStieltjes_tendsto_atBot :
    Tendsto (logisticStieltjes : ℝ → ℝ) atBot (𝓝 0) := by
  have harg : Tendsto (fun t : ℝ => t / 3) atBot atBot :=
    Filter.Tendsto.atBot_div_const (by norm_num) Filter.tendsto_id
  change Tendsto (fun t : ℝ => Real.sigmoid (t / 3)) atBot (𝓝 0)
  exact Real.tendsto_sigmoid_atBot.comp harg

lemma logisticStieltjes_tendsto_atTop :
    Tendsto (logisticStieltjes : ℝ → ℝ) atTop (𝓝 1) := by
  have harg : Tendsto (fun t : ℝ => t / 3) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) Filter.tendsto_id
  change Tendsto (fun t : ℝ => Real.sigmoid (t / 3)) atTop (𝓝 1)
  exact Real.tendsto_sigmoid_atTop.comp harg

end SAP.P029b.WH.W2.P.T19_L1

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

theorem SAP.P029b.WH.W2.T19_L1_proof : SAP.P029b.WH.W2.T19_L1 := by
  let f := SAP.P029b.WH.W2.P.T19_L1.logisticStieltjes
  have h0 : Tendsto (f : ℝ → ℝ) atBot (𝓝 0) :=
    SAP.P029b.WH.W2.P.T19_L1.logisticStieltjes_tendsto_atBot
  have h1 : Tendsto (f : ℝ → ℝ) atTop (𝓝 1) :=
    SAP.P029b.WH.W2.P.T19_L1.logisticStieltjes_tendsto_atTop
  have hprob : IsProbabilityMeasure f.measure := by
    constructor
    rw [StieltjesFunction.measure_univ f h0 h1]
    norm_num
  refine ⟨f.measure, hprob, ?_⟩
  intro t
  have hcdf : ProbabilityTheory.cdf f.measure t = f t :=
    congrArg (fun g : StieltjesFunction ℝ => g t)
      (ProbabilityTheory.cdf_measure_stieltjesFunction f h0 h1)
  calc
    ProbabilityTheory.cdf f.measure t = f t := hcdf
    _ = SAP.P029b.logisticCDFW2 t := by
      change Real.sigmoid (t / 3) = SAP.P029b.logisticCDFW2 t
      exact (SAP.P029b.WH.W2.P.T19_L1.logisticCDFW2_eq_sigmoid t).symm
