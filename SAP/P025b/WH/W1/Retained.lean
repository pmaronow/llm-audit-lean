import SAP.P025b.Defs.WholeW1
import SAP.P025b.Bridge
import AronowAudit.P025.P025_Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b.WH.W1
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem retained_T12 : T12Statement := by
  refine ⟨AronowAudit.P025.census_realizes_boundary, ?_, ?_,
    AronowAudit.P025.equal_probability_proof_counterexample⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [binaryTwo] at *
  · intro k
    funext i
    simp [upperWeights]

theorem retained_T14 : T14Statement := by
  obtain ⟨hi, hc, hn⟩ := AronowAudit.P025.pair_design_realizes_example
  obtain ⟨hl, hh, _, _⟩ := AronowAudit.P025.nonseparation_class_extrema
  refine ⟨hi, hc, hn, ?_, ?_, hl, hh, ?_, AronowAudit.P025.assumption_two_not_necessary⟩
  · norm_num [upperValue, ratio, upperWeights, threeOutcomes, Fin.sum_univ_three]
  · norm_num [upperValue, ratio, upperWeights, threeOutcomes, Fin.sum_univ_three]
  · intro ω h hhpos
    refine ⟨⟨0, hhpos⟩, (0, pairChoice (ω 0) 0), ?_⟩
    exact (AronowAudit.P025.pair_membership (ω 0) 0 (pairChoice (ω 0) 0)).mpr rfl

theorem retained_T15 : T15Statement := by
  intro J hJ y q hy hq hqsum α β hα hab hb1 hcomp
  obtain ⟨hl, hh, himage, hrat, hattL, hattH⟩ :=
    AronowAudit.P025.shares_sharpness_and_attainment hJ y q hy hq hqsum α β hα hab hb1 hcomp
  obtain ⟨hmin, hmax⟩ :=
    AronowAudit.P025.proportion_region_mean_extrema hJ y q hy hq α β hα hab hb1
  refine ⟨?_, ?_, hl, hh, himage, hmin, hmax, hrat, hattL, hattH, ?_, ?_, ?_, ?_⟩
  · intro m mass hmass hm
    exact ⟨AronowAudit.P025.actual_class_weights m mass α β hα hab hmass hm,
      AronowAudit.P025.class_mean_ratio y mass m (fun j => (hmass j).ne')⟩
  · intro m hm
    exact AronowAudit.P025.shares_outer_bound hJ y q hy hq α β hα hab hb1 m hm
  · intro mass m
    exact AronowAudit.P025.absolute_integer_calibration mass m α β hα hab
  · intro mass hmass m hm
    exact AronowAudit.P025.absolute_outer_bound hJ y mass hy hmass α β hα hab hb1 m hm
  · intro mass N v
    change (∃ m, absoluteCompatible α β mass m ∧ (∑ j, m j) = N ∧ classMean y m = v) ↔ _
    -- Rewrite the compatibility condition under the existential quantifier.
    constructor
    · rintro ⟨m, hm, hN, hv⟩
      exact ⟨m, (AronowAudit.P025.absolute_integer_calibration mass m α β hα hab).mp hm, hN, hv⟩
    · rintro ⟨m, hm, hN, hv⟩
      exact ⟨m, (AronowAudit.P025.absolute_integer_calibration mass m α β hα hab).mpr hm, hN, hv⟩

  · intro mass m
    constructor
    · intro hm
      exact ⟨fun j => (hm j).1, fun j =>
        (AronowAudit.P025.one_class_compatibility (m j) (hm j).1 α β (mass j)).mpr (hm j).2⟩
    · rintro ⟨hm, hπ⟩ j
      exact ⟨hm j, (AronowAudit.P025.one_class_compatibility (m j) (hm j) α β (mass j)).mp (hπ j)⟩

theorem retained_T16 : T16Statement := by
  exact ⟨AronowAudit.P025.integrality_design_realizes_example,
    AronowAudit.P025.integrality_sharpness_counterexample,
    AronowAudit.P025.integrality_mean_set_and_gaps,
    AronowAudit.P025.known_size_sharpness_counterexample,
    AronowAudit.P025.known_size_mean_set_and_gap,
    AronowAudit.P025.sharpness_counterexample_box_extrema⟩

theorem retained_T20 : T20Statement := by
  intro n hn y hy α β hα hab hb1
  have he : attainable y (fun _ => 1) α β =
      Set.Icc (binaryLower (populationMean y) (β/α)) (binaryUpper (populationMean y) (β/α)) :=
    AronowAudit.P025.dichotomous_closed_form hn y hy α β hα hab hb1
  have hmem : ratio y (fun _ => 1) (fun _ => 1/α) ∈ attainable y (fun _ => 1) α β :=
    ⟨_, (fun _ => ⟨one_div_le_one_div_of_le hα hab, le_rfl⟩), rfl⟩
  rw [he] at hmem
  have horder := hmem.1.trans hmem.2
  have hγne : β/α ≠ 0 := div_ne_zero (hα.trans_le hab).ne' hα.ne'
  refine ⟨he, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg sInf he).trans (csInf_Icc horder)
  · exact (congrArg sSup he).trans (csSup_Icc horder)
  · intro hp
    simp [hp, binaryLower, binaryUpper]
  · intro hp
    simp [hp, binaryLower, binaryUpper, hγne]
  · intro hγ
    simp [hγ, binaryLower, binaryUpper]

end SAP.P025b.WH.W1
