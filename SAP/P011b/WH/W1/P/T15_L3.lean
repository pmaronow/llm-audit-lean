import SAP.P011b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.WH.W1.P.T15_L3

open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical symmDiff

noncomputable abbrev lowerStar := SAP.P011b.starFamily false

theorem lower_star_core : SAP.P011b.starCore :=
  SAP.P011b.Bridge.starCore_correspondence.mpr
    AronowAudit.P011.Wave1.star_counterexample_proof

theorem negative_variance_tendsto :
    Tendsto
      (fun k => probability (lowerStar.model k)
        {y | V1 (lowerStar.model k).G (weighted (lowerStar.model k) y) < 0})
      atTop (𝓝 0) := by
  have hconv : InProbability lowerStar (scaledOracle lowerStar)
      (fun _ => 3/16) := lower_star_core.2.2.2.2.1
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_)
    (hconv (3/32) (by norm_num))
  let m := lowerStar.model k
  letI : IsProbabilityMeasure m.law := m.probability
  apply measureReal_mono (μ := m.law) ?_ (measure_ne_top _ _)
  intro y hy
  have hn : (0 : ℝ) < lowerStar.size k := by
    exact_mod_cast lowerStar.positive k
  have hscaled : scaledOracle lowerStar k y < 0 := by
    rw [scaledOracle]
    exact mul_neg_of_pos_of_neg hn hy
  have hdev : 3/32 < |scaledOracle lowerStar k y - 3/16| := by
    rw [abs_of_neg (by linarith : scaledOracle lowerStar k y - 3/16 < 0)]
    norm_num at *
    linarith
  exact hdev

end SAP.P011b.WH.W1.P.T15_L3

open SAP.P011b.WH.W1.P.T15_L3
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical symmDiff

theorem SAP.P011b.WH.W1.T15_L3_proof : SAP.P011b.WH.W1.T15_L3 := by
  refine ⟨negative_variance_tendsto, ?_⟩
  intro α hα hα1
  let F := lowerStar
  let limit : ℝ := 2 * Phi (normalQuantile α * Real.sqrt (8/9)) - 1
  have hclip : Tendsto
      (fun k => coverage (F.model k)
        (fun y => V1 (F.model k).G (weighted (F.model k) y)) α)
      atTop (𝓝 limit) := by
    have h := SAP.P011b.WH.W1.P.T15_L3.lower_star_core.2.2.2.2.2.2.1 α hα hα1
    simpa [limit, F, lowerStar] using h.1
  have hdiff_tendsto : Tendsto
      (fun k => |w1DomainCoverage (F.model k)
          (fun y => V1 (F.model k).G (weighted (F.model k) y)) α -
        coverage (F.model k)
          (fun y => V1 (F.model k).G (weighted (F.model k) y)) α|)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun k => ?_)
      SAP.P011b.WH.W1.P.T15_L3.negative_variance_tendsto
    let m := F.model k
    letI : IsProbabilityMeasure m.law := m.probability
    let V : (Fin (F.size k) → ℝ) → ℝ := fun y => V1 m.G (weighted m y)
    let C : Set (Fin (F.size k) → ℝ) :=
      {y | |betaHat m y - beta m| ≤ normalQuantile α * Real.sqrt (max (V y) 0)}
    let D : Set (Fin (F.size k) → ℝ) :=
      {y | 0 ≤ V y ∧ |betaHat m y - beta m| ≤ normalQuantile α * Real.sqrt (V y)}
    let N : Set (Fin (F.size k) → ℝ) := {y | V y < 0}
    have hV : Measurable V := by
      dsimp [V, m]
      unfold V1 quadratic centered average weighted
      fun_prop
    have hbh : Measurable (betaHat m) := by
      unfold betaHat average weighted
      fun_prop
    have habs : Measurable (fun y => |betaHat m y - beta m|) :=
      continuous_abs.measurable.comp (hbh.sub_const _)
    have hwidthC : Measurable (fun y =>
        normalQuantile α * Real.sqrt (max (V y) 0)) :=
      measurable_const.mul (Real.continuous_sqrt.measurable.comp (hV.max measurable_const))
    have hwidthD : Measurable (fun y =>
        normalQuantile α * Real.sqrt (V y)) :=
      measurable_const.mul (Real.continuous_sqrt.measurable.comp hV)
    have hC : MeasurableSet C := by
      dsimp [C]
      exact measurableSet_le habs hwidthC
    have hD : MeasurableSet D := by
      dsimp [D]
      exact (measurableSet_le measurable_const hV).inter (measurableSet_le habs hwidthD)
    have hsubset : C ∆ D ⊆ N := by
      intro y hy
      by_contra hnot
      have hv0 : 0 ≤ V y := le_of_not_gt hnot
      have heq : y ∈ C ↔ y ∈ D := by
        simp only [C, D, Set.mem_setOf_eq]
        rw [max_eq_left hv0]
        constructor
        · exact fun hc => ⟨hv0, hc⟩
        · exact fun hd => hd.2
      rcases Set.mem_symmDiff.mp hy with hCD | hDC
      · exact hCD.2 (heq.mp hCD.1)
      · exact hDC.2 (heq.mpr hDC.1)
    have hmeasure := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := m.law) hC.nullMeasurableSet hD.nullMeasurableSet
    have hmono := measureReal_mono (μ := m.law) hsubset (measure_ne_top _ _)
    have hbound : |probability m D - probability m C| ≤ probability m N := by
      change |m.law.real D - m.law.real C| ≤ m.law.real N
      calc
        |m.law.real D - m.law.real C| = |m.law.real C - m.law.real D| := abs_sub_comm _ _
        _ ≤ m.law.real (C ∆ D) := hmeasure
        _ ≤ m.law.real N := hmono
    have hCprob : coverage m (fun y => V y) α = probability m C := rfl
    have hDprob : w1DomainCoverage m (fun y => V y) α = probability m D := rfl
    simpa [F, lowerStar, m, V, N, hCprob, hDprob] using hbound
  have hclip_error : Tendsto
      (fun k => |coverage (F.model k)
          (fun y => V1 (F.model k).G (weighted (F.model k) y)) α - limit|)
      atTop (𝓝 0) := by
    simpa [Real.dist_eq] using
      hclip.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => limit) atTop (𝓝 limit))
  have hsum : Tendsto
      (fun k =>
        |w1DomainCoverage (F.model k)
            (fun y => V1 (F.model k).G (weighted (F.model k) y)) α -
          coverage (F.model k)
            (fun y => V1 (F.model k).G (weighted (F.model k) y)) α| +
        |coverage (F.model k)
            (fun y => V1 (F.model k).G (weighted (F.model k) y)) α - limit|)
      atTop (𝓝 0) := by
    simpa using hdiff_tendsto.add hclip_error
  have hdomain_error : Tendsto
      (fun k => |w1DomainCoverage (F.model k)
          (fun y => V1 (F.model k).G (weighted (F.model k) y)) α - limit|)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun k => ?_) hsum
    exact abs_sub_le _ _ _
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.dist_eq] using hdomain_error

