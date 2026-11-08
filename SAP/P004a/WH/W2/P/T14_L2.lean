import SAP.P004a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T14_L2

open MeasureTheory ProbabilityTheory Filter Set
open AronowAudit.P004
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1000000

abbrev AreaPoint := EuclideanSpace ℝ (Fin 2)

private def disk : Set AreaPoint := Metric.closedBall 0 1

private def annulus (a b : ℝ) : Set AreaPoint := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}

private theorem area_closedBall_volume (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.closedBall (0 : AreaPoint) r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [EuclideanSpace.volume_closedBall_fin_two,
    ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  ring

private theorem area_ball_volume (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.ball (0 : AreaPoint) r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [EuclideanSpace.volume_ball_fin_two,
    ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  ring

private theorem annulus_volume (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    volume (annulus a b) = ENNReal.ofReal (Real.pi*(b^2-a^2)) := by
  have hs : annulus a b = Metric.closedBall 0 b \ Metric.ball 0 a := by
    ext x
    simp only [annulus, Set.mem_setOf_eq, Set.mem_diff, Metric.mem_closedBall,
      Metric.mem_ball, dist_zero_right, not_lt]
    exact and_comm
  have hsub : Metric.ball (0 : AreaPoint) a ⊆ Metric.closedBall 0 b := by
    intro x hx
    exact (Metric.mem_ball.mp hx).le.trans hab
  rw [hs, measure_sdiff hsub Metric.isOpen_ball.measurableSet.nullMeasurableSet]
  · rw [area_closedBall_volume b (ha.trans hab), area_ball_volume a ha,
      ← ENNReal.ofReal_sub _ (mul_nonneg Real.pi_pos.le (sq_nonneg a))]
    congr 1
    ring
  · rw [area_ball_volume a ha]
    exact ENNReal.ofReal_ne_top

private theorem radial_region_eq (a b : ℝ) :
    region (radialAreaPopulation (Icc a b)) 0 0 = annulus a b := by
  ext x
  simp [region, annulus, nodeDistance, radialAreaPopulation, Metric.infDist_singleton,
    dist_zero_right, Set.mem_Icc]

private theorem radial_region_measurable (a b : ℝ) :
    MeasurableSet (region (radialAreaPopulation (Icc a b)) 0 0) := by
  rw [radial_region_eq]
  change MeasurableSet {x : AreaPoint | ‖x‖ ∈ Icc a b}
  exact measurableSet_Icc.preimage measurable_norm

private theorem radial_region_mass (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) :
    (radialAreaPopulation (Icc a b)).zeta
      (region (radialAreaPopulation (Icc a b)) 0 0) =
        ENNReal.ofReal (Real.pi*(b^2-a^2)) := by
  rw [radialAreaPopulation]
  change (volume.restrict disk) (region (radialAreaPopulation (Icc a b)) 0 0) = _
  rw [Measure.restrict_apply (by
    exact radial_region_measurable a b)]
  rw [radial_region_eq]
  have hset : annulus a b ∩ disk = annulus a b := by
    ext x
    constructor
    · rintro ⟨h, _⟩
      exact h
    · intro hx
      constructor
      · exact hx
      · rw [disk, Metric.mem_closedBall, dist_zero_right]
        exact hx.2.trans hb
  rw [hset, annulus_volume a b ha hab.le]

private theorem point_effect_formula (x : AreaPoint) :
    pointEffect (radialAreaPopulation (Icc 0 1)) (fun _ => (1/2 : ℝ)) 0 x =
      if ‖x‖ ≤ 1 then ‖x‖ else 0 := by
  have hp : ∀ j : Fin 1, 0 < (fun _ : Fin 1 => (1/2 : ℝ)) j ∧
      (fun _ : Fin 1 => (1/2 : ℝ)) j < 1 := by
    intro j
    norm_num
  have ht : (fun z : Assignment 1 =>
      (radialAreaPopulation (Icc 0 1)).outcome x (Function.update z 0 true)) =
      fun _ => if ‖x‖ ≤ 1 then ‖x‖ else 0 := by
    funext z
    simp [radialAreaPopulation, Function.update, bit]
  have hf : (fun z : Assignment 1 =>
      (radialAreaPopulation (Icc 0 1)).outcome x (Function.update z 0 false)) =
      fun _ => 0 := by
    funext z
    simp [radialAreaPopulation, Function.update, bit]
  rw [← SAP.P004a.Bridge.pointEffect_eq
      (radialAreaPopulation (Icc 0 1)) (fun _ => (1/2 : ℝ))]
  unfold AronowAudit.P004.pointEffect
  simp only [SAP.P004a.Bridge.toPopulation]
  rw [AronowAudit.P004.marginal_is_marginalization _ _ _ _ hp,
    AronowAudit.P004.marginal_is_marginalization _ _ _ _ hp, ht, hf,
    AronowAudit.P004.expect_const, AronowAudit.P004.expect_const]
  simp

private theorem radial_disk_finite :
    volume (Metric.closedBall (0 : AreaPoint) 1) ≠ ⊤ := by
  rw [area_closedBall_volume 1 (by norm_num)]
  exact ENNReal.ofReal_ne_top

private theorem area_population_mass_finite :
    (radialAreaPopulation (Icc 0 1)).zeta Set.univ ≠ ⊤ := by
  rw [radialAreaPopulation]
  change (volume.restrict disk) Set.univ ≠ ⊤
  rw [Measure.restrict_apply MeasurableSet.univ]
  rw [Set.univ_inter, disk]
  exact radial_disk_finite

private theorem area_outcome_measurable (z : Assignment 1) :
    Measurable (fun x : AreaPoint =>
      (radialAreaPopulation (Icc 0 1)).outcome x z) := by
  rw [show (fun x : AreaPoint => (radialAreaPopulation (Icc 0 1)).outcome x z) =
      fun x => if ‖x‖ ≤ 1 then bit (z 0)*‖x‖ else 0 by rfl]
  apply Measurable.ite
  · exact measurableSet_le measurable_norm measurable_const
  · exact measurable_const.mul measurable_norm
  · exact measurable_const

private theorem outcome_abs_le_one (x : AreaPoint) (z : Assignment 1) :
    ‖(radialAreaPopulation (Icc 0 1)).outcome x z‖ ≤ 1 := by
  by_cases hx : ‖x‖ ≤ 1
  · cases hz : z 0 <;>
      simp [radialAreaPopulation, hx, hz, bit, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x)]
  · simp [radialAreaPopulation, hx]

private theorem point_effect_measurable :
    Measurable (fun x : AreaPoint =>
      pointEffect (radialAreaPopulation (Icc 0 1)) (fun _ => (1/2 : ℝ)) 0 x) := by
  rw [show (fun x : AreaPoint =>
      pointEffect (radialAreaPopulation (Icc 0 1)) (fun _ => (1/2 : ℝ)) 0 x) =
      fun x => if ‖x‖ ≤ 1 then ‖x‖ else 0 by
        funext x
        exact point_effect_formula x]
  apply Measurable.ite
  · exact measurableSet_le measurable_norm measurable_const
  · exact measurable_norm
  · exact measurable_const

private theorem radial_area_integrable :
    Integrable (fun x : AreaPoint =>
      pointEffect (radialAreaPopulation (Icc 0 1)) (fun _ => (1/2 : ℝ)) 0 x)
        (radialAreaPopulation (Icc 0 1)).zeta := by
  let μ : Measure AreaPoint := volume.restrict disk
  change Integrable (fun x : AreaPoint =>
    pointEffect (radialAreaPopulation (Icc 0 1)) (fun _ => (1/2 : ℝ)) 0 x) μ
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr radial_disk_finite
  refine (integrable_const (1 : ℝ)).mono' point_effect_measurable.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [point_effect_formula]
  by_cases hx : ‖x‖ ≤ 1
  · simp [hx, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  · simp [hx]

private theorem radius_integrable :
    Integrable (fun x : AreaPoint => ‖x‖)
        (radialAreaPopulation (Icc 0 1)).zeta := by
  let μ : Measure AreaPoint := volume.restrict disk
  change Integrable (fun x : AreaPoint => ‖x‖) μ
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr radial_disk_finite
  refine (integrable_const (1 : ℝ)).mono' measurable_norm.aestronglyMeasurable ?_
  have hmem : ∀ᵐ x ∂μ, x ∈ disk := by
    change ∀ᵐ x ∂volume.restrict disk, x ∈ disk
    exact ae_restrict_mem Metric.isClosed_closedBall.measurableSet
  filter_upwards [hmem] with x hx
  rw [disk, Metric.mem_closedBall, dist_zero_right] at hx
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] using hx

private theorem conditional_moment_property :
    IsRadiusConditionalMean (radialAreaPopulation (Icc 0 1)).zeta
      (pointEffect (radialAreaPopulation (Icc 0 1)) (fun _ => (1/2 : ℝ)) 0)
      (fun r => r) := by
  refine ⟨measurable_id, radial_area_integrable, radius_integrable, ?_⟩
  intro B hB
  let s : Set AreaPoint := {x | ‖x‖ ∈ B}
  have hs : MeasurableSet s := hB.preimage measurable_norm
  have hsupport : ∀ᵐ x ∂(radialAreaPopulation (Icc 0 1)).zeta, x ∈ disk := by
    change ∀ᵐ x ∂volume.restrict disk, x ∈ disk
    exact ae_restrict_mem Metric.isClosed_closedBall.measurableSet
  have hsupport' : ∀ᵐ x ∂((radialAreaPopulation (Icc 0 1)).zeta.restrict s), x ∈ disk :=
    ae_restrict_of_ae hsupport
  apply integral_congr_ae
  filter_upwards [hsupport'] with x hx
  rw [disk, Metric.mem_closedBall, dist_zero_right] at hx
  rw [point_effect_formula]
  simp [hx]

private theorem area_annulus_well_defined (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) : WellDefined (radialAreaPopulation (Icc a b)) 0 := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hmass := radial_region_mass a b ha hab hb
  have harea : 0 < Real.pi*(b^2-a^2) := by
    have hbpos : 0 < b := lt_of_le_of_lt ha hab
    have hsq : 0 < b^2-a^2 := by nlinarith
    exact mul_pos Real.pi_pos hsq
  refine ⟨radial_region_measurable a b, ?_, ?_, ?_⟩
  · rw [hmass]
    exact ENNReal.ofReal_pos.mpr harea
  · rw [hmass]
    exact ENNReal.ofReal_lt_top
  · intro z
    have hfinite : (radialAreaPopulation (Icc a b)).zeta
        (region (radialAreaPopulation (Icc a b)) 0 0) ≠ ⊤ := by
      rw [hmass]
      exact ENNReal.ofReal_ne_top
    have hmeas := area_outcome_measurable z
    exact Measure.integrableOn_of_bounded hfinite hmeas.aestronglyMeasurable
      (f_bdd := by
        filter_upwards [] with x
        exact outcome_abs_le_one x z)

end
end SAP.P004a.WH.W2.P.T14_L2

open SAP.P004a.WH.W2.P.T14_L2

theorem SAP.P004a.WH.W2.T14_L2_proof : SAP.P004a.WH.W2.T14_L2 := by
  unfold SAP.P004a.WH.W2.T14_L2 SAP.P004a.T14AreaExistence
  refine ⟨?_, ?_, ?_, continuous_id, conditional_moment_property, ?_⟩
  · intro x z
    rw [radialAreaPopulation]
    by_cases hx : ‖x‖ ≤ 1
    · cases hz : z 0 <;>
        simp [hx, hz, bit, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
      <;> linarith
    · simp [hx]
  · intro x z hx
    simp [radialAreaPopulation, hx]
  · intro x hx
    rw [point_effect_formula]
    simp [hx]
  · intro a b ha hab hb
    exact ⟨area_annulus_well_defined a b ha hab hb,
      radial_region_mass a b ha hab hb⟩

