import SAP.P037a.WH.W1.Leaves
import Mathlib.Probability.Distributions.Exponential

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W1.P.T4_L5

open MeasureTheory ProbabilityTheory Set
open SAP.P037a.Bridge
open scoped BigOperators ENNReal NNReal Classical Topology

private theorem measurable_normalizedWeights (n : ℕ) :
    Measurable (@normalizedWeights n) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i).div
    (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))

private theorem uniformDraw_positive_ae : ∀ᵐ x : ℝ ∂uniformDraw, 0 < x := by
  have h := ae_restrict_mem (μ := (volume : Measure ℝ))
    (s := Ioo 0 1) measurableSet_Ioo
  exact h.mono fun x hx => hx.1

private theorem expDraw_positive_ae :
    ∀ᵐ x : ℝ ∂expMeasure 1, 0 < x := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  apply ae_iff.mpr
  have hs : {x : ℝ | ¬ 0 < x} = Iic 0 := by
    ext x
    simp
  rw [hs]
  have hc : cdf (expMeasure 1) 0 = 0 := by
    rw [cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1)]
    norm_num
  have hr : (expMeasure 1).real (Iic 0) = 0 := by
    rw [← cdf_eq_real]
    exact hc
  exact (measureReal_eq_zero_iff).mp hr

private theorem normalized_ratio_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ)
    (X : Fin (n+2) → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hMarg : ∀ i, Measure.map (X i) μ = expMeasure 1)
    (hInd : iIndepFun X μ) :
    Measure.map (fun w => normalizedWeights (fun i => X i w)) μ =
      exponentialWeightLaw n := by
  have hvec : Measurable (fun w i => X i w) := Measurable.of_eval hX
  have hnorm := (measurable_normalizedWeights (n+2)).comp hvec
  have hjoint : μ.map (fun w i => X i w) = exponentialProduct n := by
    rw [hInd.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)]
    simp [exponentialProduct, hMarg]
  calc
    Measure.map (fun w => normalizedWeights (fun i => X i w)) μ =
        (μ.map (fun w i => X i w)).map normalizedWeights := by
          simpa only [Function.comp_def] using
            (Measure.map_map (measurable_normalizedWeights (n+2)) hvec).symm
    _ = exponentialWeightLaw n := by
      rw [hjoint]
      rfl

private theorem bootstrapRandomComparison_of_simplex
    (hSimplex : exponentialSimplexLaw) : bootstrapRandomComparison := by
  intro n Ω _ μ hμ U E hUmeas hEmeas hUind hEind hUmarg hEmarg
  letI : IsProbabilityMeasure uniformDraw := ⟨by
    norm_num [uniformDraw, Real.volume_Ioo]
  ⟩
  have hUvec : Measurable (fun w i => U i w) := Measurable.of_eval hUmeas
  have hEvec : Measurable (fun w i => E i w) := Measurable.of_eval hEmeas
  have hUnorm := (measurable_normalizedWeights (n+2)).comp hUvec
  have hEnorm := (measurable_normalizedWeights (n+2)).comp hEvec
  have hUjoint : μ.map (fun w i => U i w) =
      Measure.pi (fun _ : Fin (n+2) => uniformDraw) := by
    rw [hUind.map_fun_eq_pi_map (fun i => (hUmeas i).aemeasurable)]
    simp [hUmarg]
  have hEjoint : μ.map (fun w i => E i w) = exponentialProduct n := by
    rw [hEind.map_fun_eq_pi_map (fun i => (hEmeas i).aemeasurable)]
    simp [exponentialProduct, hEmarg]
  have hUlaw : Measure.map (fun w => normalizedWeights (fun i => U i w)) μ =
      uniformWeightLaw n := by
    calc
      Measure.map (fun w => normalizedWeights (fun i => U i w)) μ =
          (μ.map (fun w i => U i w)).map normalizedWeights := by
            simpa only [Function.comp_def] using
              (Measure.map_map (measurable_normalizedWeights (n+2)) hUvec).symm
      _ = uniformWeightLaw n := by
        rw [hUjoint]
        rfl
  have hElaw : Measure.map (fun w => normalizedWeights (fun i => E i w)) μ =
      simplexLaw (n+1) := by
    have h := normalized_ratio_probability μ n E hEmeas hEmarg hEind
    rw [← hSimplex n |>.1]
    exact h
  have hUlawComp : Measure.map (normalizedWeights ∘ fun w i => U i w) μ =
      uniformWeightLaw n := by
    simpa only [Function.comp_def] using hUlaw
  have hElawComp : Measure.map (normalizedWeights ∘ fun w i => E i w) μ =
      simplexLaw (n+1) := by
    simpa only [Function.comp_def] using hElaw
  have hUpos : ∀ᵐ w ∂μ, ∀ i, 0 < U i w := by
    apply ae_all_iff.mpr
    intro i
    apply ae_of_ae_map (hUmeas i).aemeasurable
    rw [hUmarg i]
    exact uniformDraw_positive_ae
  have hEpos : ∀ᵐ w ∂μ, ∀ i, 0 < E i w := by
    apply ae_all_iff.mpr
    intro i
    apply ae_of_ae_map (hEmeas i).aemeasurable
    rw [hEmarg i]
    exact expDraw_positive_ae
  have hUfacts : PositiveRatioFacts μ n U := by
    filter_upwards [hUpos] with w hw
    have ht : 0 < ∑ i, U i w :=
      Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
    have hp : 0 < U 0 w + U 1 w := by linarith [hw 0, hw 1]
    have hc := AronowAudit.P037.bootstrap_ratio_cancellation
      (U 0 w) (U 1 w) (∑ i, U i w) (hw 0) (hw 1) ht
    refine ⟨hw, ht, hp, ?_, hc.2⟩
    change (U 0 w / (∑ i, U i w)) /
      ((U 0 w / (∑ i, U i w)) + (U 1 w / (∑ i, U i w))) =
        U 0 w / (U 0 w + U 1 w)
    simpa [normalizedWeights] using hc.1
  have hEfacts : PositiveRatioFacts μ n E := by
    filter_upwards [hEpos] with w hw
    have ht : 0 < ∑ i, E i w :=
      Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
    have hp : 0 < E 0 w + E 1 w := by linarith [hw 0, hw 1]
    have hc := AronowAudit.P037.bootstrap_ratio_cancellation
      (E 0 w) (E 1 w) (∑ i, E i w) (hw 0) (hw 1) ht
    refine ⟨hw, ht, hp, ?_, hc.2⟩
    change (E 0 w / (∑ i, E i w)) /
      ((E 0 w / (∑ i, E i w)) + (E 1 w / (∑ i, E i w))) =
        E 0 w / (E 0 w + E 1 w)
    simpa [normalizedWeights] using hc.1
  have hratioMeas : Measurable (fun p : Fin (n+2) → ℝ => p 0 / (p 0 + p 1)) :=
    (measurable_pi_apply 0).div
      ((measurable_pi_apply 0).add (measurable_pi_apply 1))
  have hratioSet : MeasurableSet (ratioEvent n) := by
    change MeasurableSet {p : Fin (n+2) → ℝ | p 0 / (p 0 + p 1) < 1/4}
    exact measurableSet_lt hratioMeas measurable_const
  have hUprob :
      (μ {w | normalizedWeights (fun i => U i w) ∈ ratioEvent n}).toReal = 1/6 := by
    change (μ ((normalizedWeights ∘ fun w i => U i w) ⁻¹' ratioEvent n)).toReal = 1/6
    rw [← Measure.map_apply hUnorm hratioSet, hUlawComp]
    exact (AronowAudit.P037.Wave1.uniform_weights_not_bayesian_bootstrap_proof n).1
  have hEprob :
      (μ {w | normalizedWeights (fun i => E i w) ∈ ratioEvent n}).toReal = 1/4 := by
    change (μ ((normalizedWeights ∘ fun w i => E i w) ⁻¹' ratioEvent n)).toReal = 1/4
    rw [← Measure.map_apply hEnorm hratioSet, hElawComp]
    exact (AronowAudit.P037.Wave1.uniform_weights_not_bayesian_bootstrap_proof n).2.1
  have hrawEq :
      {w | normalizedWeights (fun i => E i w) ∈ ratioEvent n} =ᵐ[μ]
        {w | E 0 w < E 1 w / 3} := by
    filter_upwards [hEfacts] with w hw
    apply propext
    change (normalizedWeights (fun i => E i w) 0 /
      (normalizedWeights (fun i => E i w) 0 + normalizedWeights (fun i => E i w) 1) <
        1/4) ↔ E 0 w < E 1 w / 3
    rw [hw.2.2.2.1]
    exact hw.2.2.2.2
  have hrawProb : (μ {w | E 0 w < E 1 w / 3}).toReal = 1/4 := by
    rw [← measure_congr hrawEq]
    exact hEprob
  refine ⟨hUfacts, hEfacts, hUlaw, hElaw, hUprob, hEprob, hrawProb, ?_⟩
  intro heq
  have hp := congrArg (fun ν : Measure (Fin (n+2) → ℝ) =>
    (ν (ratioEvent n)).toReal) heq
  rw [hUlaw, hElaw] at hp
  have hbase := AronowAudit.P037.Wave1.uniform_weights_not_bayesian_bootstrap_proof n
  have hu : (uniformWeightLaw n (ratioEvent n)).toReal = 1/6 := by
    simpa only [uniformWeightLaw_eq, ratioEvent_eq] using hbase.1
  have hs : (simplexLaw (n+1) (ratioEvent n)).toReal = 1/4 := by
    simpa only [simplexLaw_eq, ratioEvent_eq] using hbase.2.1
  rw [hu, hs] at hp
  norm_num at hp

end SAP.P037a.WH.W1.P.T4_L5

theorem SAP.P037a.WH.W1.T4_L5_proof : SAP.P037a.WH.W1.T4_L5 := by
  intro h
  exact SAP.P037a.WH.W1.P.T4_L5.bootstrapRandomComparison_of_simplex h
