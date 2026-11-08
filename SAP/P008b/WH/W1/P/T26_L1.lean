import SAP.P008b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b.WH.W1.P.T26_L1

open MeasureTheory
open scoped BigOperators

noncomputable section

lemma count_finite : IsFiniteMeasure (Measure.count : Measure (Fin 3)) := by
  exact ⟨by simp⟩

lemma distance_formula (x : Fin 3) :
    wholeCancellingModel.distance 1 x = (((|((x.val : ℚ) - 1)| : ℚ) : ℝ)) := by
  change dist (AronowAudit.P008.lineEmbedding ((1 : ℚ) - 1))
      (AronowAudit.P008.lineEmbedding ((x.val : ℚ) - 1)) = _
  rw [AronowAudit.P008.line_embedding_distance]
  have h : ((1 : ℚ) - 1) - ((x.val : ℚ) - 1) = -((x.val : ℚ) - 1) := by ring
  rw [h, abs_neg]

lemma node_center : wholeCancellingModel.node 0 = 1 := rfl

lemma distance_table (x : Fin 3) :
    wholeCancellingModel.distance 1 x = if x = 1 then 0 else 1 := by
  fin_cases x <;> norm_num [distance_formula]

lemma circle_zero : wholeCancellingModel.circle 0 0 = ({1} : Set (Fin 3)) := by
  ext x
  simp only [MetricSpatialModel.circle, node_center, distance_table]
  by_cases hx : x = 1
  · simp [hx]
  · simp [hx]

lemma circle_one : wholeCancellingModel.circle 0 1 = ({0, 2} : Set (Fin 3)) := by
  ext x
  simp only [MetricSpatialModel.circle, node_center, distance_table]
  fin_cases x <;> norm_num

lemma circle_other (d : ℝ) (hd0 : d ≠ 0) (hd1 : d ≠ 1) :
    wholeCancellingModel.circle 0 d = ∅ := by
  ext x
  simp only [MetricSpatialModel.circle, node_center, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  rw [distance_table]
  by_cases hx : x = 1
  · rw [if_pos hx]
    exact fun h => hd0 h.symm
  · rw [if_neg hx]
    exact fun h => hd1 h.symm

lemma mass_zero_set :
    (Measure.count : Measure (Fin 3)) ({1} : Set (Fin 3)) = 1 := by
  have hs : ({1} : Set (Fin 3)) = (↑({1} : Finset (Fin 3)) : Set (Fin 3)) := by
    ext x
    simp
  rw [hs, Measure.count_apply_finset]
  simp

lemma mass_one_set :
    (Measure.count : Measure (Fin 3)) ({0, 2} : Set (Fin 3)) = 2 := by
  have hs : ({0, 2} : Set (Fin 3)) = (↑({0, 2} : Finset (Fin 3)) : Set (Fin 3)) := by
    ext x
    simp
  rw [hs, Measure.count_apply_finset]
  simp

lemma mass_zero :
    (Measure.count : Measure (Fin 3)) (wholeCancellingModel.circle 0 0) = 1 := by
  rw [circle_zero]
  exact mass_zero_set

lemma mass_one :
    (Measure.count : Measure (Fin 3)) (wholeCancellingModel.circle 0 1) = 2 := by
  rw [circle_one]
  exact mass_one_set

lemma outcome_integral_zero (z : Assignment 1) :
    ∫ x in ({1} : Set (Fin 3)), wholeCancellingModel.Y x z ∂Measure.count = 0 := by
  have hs : ({1} : Set (Fin 3)) = (↑({1} : Finset (Fin 3)) : Set (Fin 3)) := by
    ext x
    simp
  rw [hs]
  letI : IsFiniteMeasure (Measure.count : Measure (Fin 3)) := count_finite
  rw [MeasureTheory.setIntegral_finset ({1} : Finset (Fin 3)) (MeasureTheory.Integrable.of_finite :
    Integrable (wholeCancellingModel.Y · z)
      (Measure.count.restrict (↑({1} : Finset (Fin 3)) : Set (Fin 3))))]
  simp [wholeCancellingModel, bit]

lemma outcome_integral_one (z : Assignment 1) :
    ∫ x in ({0, 2} : Set (Fin 3)), wholeCancellingModel.Y x z ∂Measure.count = 0 := by
  have hs : ({0, 2} : Set (Fin 3)) = (↑({0, 2} : Finset (Fin 3)) : Set (Fin 3)) := by
    ext x
    simp
  rw [hs]
  letI : IsFiniteMeasure (Measure.count : Measure (Fin 3)) := count_finite
  rw [MeasureTheory.setIntegral_finset ({0, 2} : Finset (Fin 3)) (MeasureTheory.Integrable.of_finite :
    Integrable (wholeCancellingModel.Y · z)
      (Measure.count.restrict (↑({0, 2} : Finset (Fin 3)) : Set (Fin 3))))]
  simp [Measure.real, wholeCancellingModel, bit]

lemma mean_zero (z : Assignment 1) : wholeCancellingModel.M 0 0 z = 0 := by
  unfold MetricSpatialModel.M MetricSpatialModel.regionAverage
  rw [circle_zero]
  change ((Measure.count : Measure (Fin 3)) ({1} : Set (Fin 3))).toReal⁻¹ *
    (∫ x in ({1} : Set (Fin 3)), wholeCancellingModel.Y x z ∂Measure.count) = 0
  rw [mass_zero_set, ENNReal.toReal_one, outcome_integral_zero]
  simp

lemma mean_one (z : Assignment 1) : wholeCancellingModel.M 0 1 z = 0 := by
  unfold MetricSpatialModel.M MetricSpatialModel.regionAverage
  rw [circle_one]
  change ((Measure.count : Measure (Fin 3)) ({0, 2} : Set (Fin 3))).toReal⁻¹ *
    (∫ x in ({0, 2} : Set (Fin 3)), wholeCancellingModel.Y x z ∂Measure.count) = 0
  rw [mass_one_set, ENNReal.toReal_ofNat, outcome_integral_one]
  norm_num

end
end SAP.P008b.WH.W1.P.T26_L1

open SAP.P008b.WH.W1.P.T26_L1
open MeasureTheory

theorem SAP.P008b.WH.W1.T26_L1_proof : SAP.P008b.WH.W1.T26_L1 := by
  constructor
  · intro Q d
    constructor
    · intro hv
      by_contra h
      push_neg at h
      have hc := circle_other d h.1 h.2
      change MeasurableSet (wholeCancellingModel.circle 0 d) ∧
        0 < ((Measure.count : Measure (Fin 3)) (wholeCancellingModel.circle 0 d)).toReal ∧
        (Measure.count : Measure (Fin 3)) (wholeCancellingModel.circle 0 d) ≠ ⊤ ∧ _ at hv
      rw [hc] at hv
      simp at hv
    · rintro (rfl | rfl)
      · change MeasurableSet (wholeCancellingModel.circle 0 0) ∧
          0 < ((Measure.count : Measure (Fin 3)) (wholeCancellingModel.circle 0 0)).toReal ∧
          (Measure.count : Measure (Fin 3)) (wholeCancellingModel.circle 0 0) ≠ ⊤ ∧ _
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [circle_zero]
          exact (Set.toFinite _).measurableSet
        · rw [mass_zero]
          norm_num
        · rw [mass_zero]
          norm_num
        · intro b z hz
          letI : IsFiniteMeasure (Measure.count : Measure (Fin 3)) := count_finite
          change Integrable (fun x => wholeCancellingModel.Y x (Function.update z 0 b))
            ((Measure.count : Measure (Fin 3)).restrict
              (wholeCancellingModel.circle 0 0))
          rw [circle_zero]
          exact MeasureTheory.Integrable.of_finite
      · change MeasurableSet (wholeCancellingModel.circle 0 1) ∧
          0 < ((Measure.count : Measure (Fin 3)) (wholeCancellingModel.circle 0 1)).toReal ∧
          (Measure.count : Measure (Fin 3)) (wholeCancellingModel.circle 0 1) ≠ ⊤ ∧ _
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [circle_one]
          exact (Set.toFinite _).measurableSet
        · rw [mass_one]
          norm_num
        · rw [mass_one]
          norm_num
        · intro b z hz
          letI : IsFiniteMeasure (Measure.count : Measure (Fin 3)) := count_finite
          change Integrable (fun x => wholeCancellingModel.Y x (Function.update z 0 b))
            ((Measure.count : Measure (Fin 3)).restrict
              (wholeCancellingModel.circle 0 1))
          rw [circle_one]
          exact MeasureTheory.Integrable.of_finite
  · intro z
    exact ⟨mean_zero z, mean_one z⟩
