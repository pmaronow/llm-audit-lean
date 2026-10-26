import AronowAudit.P004.P004_Spatial
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
Signed Monte Carlo, annulus radial measure, and polygon range results.
-/

namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Classical
open MeasureTheory Filter
noncomputable section

set_option maxHeartbeats 1000000

/-! ## P004-T12: the stipulated signed Monte Carlo tuple -/

private theorem mc_signed_point_injective : Function.Injective eightNodeNullPoint := by
  intro i j hij
  have hcoord := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hij
  have hcast : (i : ℝ) = (j : ℝ) := by
    simp only [eightNodeNullPoint, planePoint, PiLp.toLp_apply,
      Matrix.cons_val_zero] at hcoord
    linarith
  apply Fin.ext
  exact_mod_cast hcast

private theorem mc_signed_region (i : Fin 8) :
    region eightNodeNullPopulation i 0 = {eightNodeNullPoint i} := by
  ext x
  simp only [region, nodeDistance, eightNodeNullPopulation, Metric.infDist_singleton,
    Set.mem_setOf_eq, Set.mem_Icc, Set.mem_singleton_iff]
  exact ⟨fun h => dist_eq_zero.mp (le_antisymm h.2 dist_nonneg),
    fun h => by subst x; simp⟩

private theorem mc_signed_mass (i : Fin 8) :
    eightNodeNullPopulation.zeta {eightNodeNullPoint i} = 1 := by
  change (∑ j : Fin 8, Measure.dirac (eightNodeNullPoint j)) {eightNodeNullPoint i} = 1
  rw [Measure.finsetSum_apply]
  simp [Measure.dirac_apply, Pi.single_apply, mc_signed_point_injective.eq_iff]

private theorem mc_signed_outcome_at_point (i : Fin 8) (z : Assignment 8) :
    eightNodeNullPopulation.outcome (eightNodeNullPoint i) z = eightNodeNullTable i z := by
  change (∑ j : Fin 8, if eightNodeNullPoint i = eightNodeNullPoint j
    then eightNodeNullTable j z else 0) = _
  simp [mc_signed_point_injective.eq_iff]

private theorem mc_signed_average :
    circleAverage eightNodeNullPopulation 0 = eightNodeNullTable := by
  funext i z
  rw [circleAverage, mc_signed_region, integral_singleton]
  simp only [measureReal_def, mc_signed_mass, ENNReal.toReal_one,
    one_smul, div_one, mc_signed_outcome_at_point]

private theorem mc_signed_wellDefined : WellDefined eightNodeNullPopulation 0 := by
  intro i
  rw [mc_signed_region]
  refine ⟨measurableSet_singleton _, ?_, ?_, ?_⟩
  · rw [mc_signed_mass]; norm_num
  · rw [mc_signed_mass]; norm_num
  · intro z
    apply integrableOn_singleton
    · finiteness
    · rw [mc_signed_mass]; norm_num

private theorem mc_signed_observed_value :
    ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) eightNodeObserved =
      -255/512 := by
  rw [mc_signed_average]
  norm_num [ht, eightNodeNullTable, eightNodeObserved, bit, Fin.sum_univ_succ]

private theorem mc_signed_resampled_value :
    ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) eightNodeResampled =
      -1/512 := by
  rw [mc_signed_average]
  norm_num [ht, eightNodeNullTable, eightNodeResampled, bit, Fin.sum_univ_succ]

private theorem mc_signed_design_weight (z : Assignment 8) :
    designWeight (fun _ => 1/2) z = 1/256 := by
  have hc : ∀ i : Fin 8, coin (1/2) (z i) = (1/2 : ℝ) := by
    intro i
    cases z i <;> norm_num [coin]
  simp only [designWeight, hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

private theorem mc_signed_draw_weight :
    mcDrawWeight (fun _ => 1/2) eightNodeMCDraws = (256 : ℝ)^(-101 : ℤ) := by
  simp only [mcDrawWeight, mc_signed_design_weight, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num [zpow_neg, inv_pow]

private theorem mc_signed_draw_statistic (r : Fin 101) :
    ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) (eightNodeMCDraws r) =
      if r = 0 then -255/512 else -1/512 := by
  by_cases hr : r = 0
  · simp only [eightNodeMCDraws, if_pos hr, mc_signed_observed_value]
  · simp only [eightNodeMCDraws, if_neg hr, mc_signed_resampled_value]

private theorem mc_signed_printed_filter :
    Finset.univ.filter (fun r : Fin 101 => r ≠ 0 ∧
      ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) (eightNodeMCDraws 0) ≤
        |ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) (eightNodeMCDraws r)|) =
      Finset.univ.erase 0 := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
    and_true, mc_signed_draw_statistic, if_pos rfl]
  by_cases hr : r = 0 <;> simp [hr] <;> norm_num

private theorem mc_signed_exceedances :
    mcExceedances (ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0))
      eightNodeMCDraws = 0 := by
  unfold mcExceedances
  have hempty : Finset.univ.filter (fun r : Fin 101 => r ≠ 0 ∧
      |ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) (eightNodeMCDraws 0)| ≤
        |ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) (eightNodeMCDraws r)|) = ∅ := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and, mc_signed_draw_statistic, if_pos rfl]
    intro hr
    norm_num [hr]
  rw [hempty, Finset.card_empty]

theorem mc_signed_spatial_counterexample_proof :
    SharpNull eightNodeNullPopulation ∧ WellDefined eightNodeNullPopulation 0 ∧
    ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) eightNodeObserved = -255/512 ∧
    ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) eightNodeResampled = -1/512 ∧
    mcDrawWeight (fun _ => 1/2) eightNodeMCDraws = (256 : ℝ)^(-101 : ℤ) ∧
    0 < mcDrawWeight (fun _ => 1/2) eightNodeMCDraws ∧
    ((Finset.univ.filter (fun r : Fin 101 => r ≠ 0 ∧
      ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) (eightNodeMCDraws 0) ≤
        |ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0) (eightNodeMCDraws r)|)).card : ℝ)/100 = 1 ∧
    mcExceedances (ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0)) eightNodeMCDraws = 0 ∧
    mcPlusPvalue (ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0)) eightNodeMCDraws = 1/101 := by
  refine ⟨?_, mc_signed_wellDefined, mc_signed_observed_value,
    mc_signed_resampled_value, mc_signed_draw_weight, ?_, ?_,
    mc_signed_exceedances, ?_⟩
  · intro x z
    rfl
  · rw [mc_signed_draw_weight]
    positivity
  · rw [mc_signed_printed_filter]
    norm_num
  · norm_num [mcPlusPvalue, mc_signed_exceedances]

/-! ## P004-T15: the normalized radial pushforward of the actual annulus -/

private theorem annulus_radial_delta_pos (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    0 < b^2-a^2 := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  nlinarith

private theorem annulus_radial_closedBall_volume (center : EuclideanSpace ℝ (Fin 2))
    (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.closedBall center r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [EuclideanSpace.volume_closedBall_fin_two,
    ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  ring

private theorem annulus_radial_ball_volume (center : EuclideanSpace ℝ (Fin 2))
    (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.ball center r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [EuclideanSpace.volume_ball_fin_two,
    ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  ring

private theorem annulus_radial_area (center : EuclideanSpace ℝ (Fin 2))
    (a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) :
    volume {x | a ≤ dist x center ∧ dist x center ≤ t} =
      ENNReal.ofReal (Real.pi*(t^2-a^2)) := by
  have hs : {x : EuclideanSpace ℝ (Fin 2) | a ≤ dist x center ∧ dist x center ≤ t} =
      Metric.closedBall center t \ Metric.ball center a := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball,
      not_lt]
    exact and_comm
  have hsub : Metric.ball center a ⊆ Metric.closedBall center t := by
    intro x hx
    exact (Metric.mem_ball.mp hx).le.trans hat
  rw [hs, measure_sdiff hsub Metric.isOpen_ball.measurableSet.nullMeasurableSet
    (by rw [annulus_radial_ball_volume center a ha]; exact ENNReal.ofReal_ne_top)]
  rw [annulus_radial_closedBall_volume center t (ha.trans hat),
    annulus_radial_ball_volume center a ha,
    ← ENNReal.ofReal_sub _ (mul_nonneg Real.pi_pos.le (sq_nonneg a))]
  congr 1
  ring

private theorem annulus_radial_map_Iic (center : EuclideanSpace ℝ (Fin 2))
    (a b s : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    (Measure.map (fun x : EuclideanSpace ℝ (Fin 2) => dist x center)
      (volume.restrict {x | a ≤ dist x center ∧ dist x center ≤ b})) (Set.Iic s) =
      if s < a then 0 else ENNReal.ofReal (Real.pi*((min b s)^2-a^2)) := by
  rw [Measure.map_apply (measurable_id'.dist measurable_const) measurableSet_Iic,
    Measure.restrict_apply ((measurable_id'.dist measurable_const) measurableSet_Iic)]
  by_cases hs : s < a
  · rw [if_pos hs]
    have hempty : (fun x : EuclideanSpace ℝ (Fin 2) => dist x center) ⁻¹' Set.Iic s ∩
        {x | a ≤ dist x center ∧ dist x center ≤ b} = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq,
        Set.notMem_empty, iff_false]
      rintro ⟨hxs, hax, _⟩
      linarith
    rw [hempty, measure_empty]
  · rw [if_neg hs]
    have heq : (fun x : EuclideanSpace ℝ (Fin 2) => dist x center) ⁻¹' Set.Iic s ∩
        {x | a ≤ dist x center ∧ dist x center ≤ b} =
        {x | a ≤ dist x center ∧ dist x center ≤ min b s} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq,
        le_min_iff]
      tauto
    rw [heq, annulus_radial_area center a (min b s) ha
      (le_min hab.le (le_of_not_gt hs))]

private theorem annulus_radial_density_Iic (a b s : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    (volume.withDensity (fun r : ℝ => ENNReal.ofReal
      (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0))) (Set.Iic s) =
      if s < a then 0 else ENNReal.ofReal (((min b s)^2-a^2)/(b^2-a^2)) := by
  have hΔ : 0 < b^2-a^2 := annulus_radial_delta_pos a b ha hab
  rw [withDensity_apply _ measurableSet_Iic]
  have hind : (fun r : ℝ => ENNReal.ofReal
      (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0)) =
      (Set.Icc a b).indicator (fun r : ℝ => ENNReal.ofReal (2*r/(b^2-a^2))) := by
    funext r
    by_cases hr : a ≤ r ∧ r ≤ b <;> simp [Set.indicator, Set.mem_Icc, hr]
  rw [hind, setLIntegral_indicator measurableSet_Icc]
  by_cases hs : s < a
  · rw [if_pos hs]
    have hempty : Set.Icc a b ∩ Set.Iic s = ∅ := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, Set.notMem_empty,
        iff_false]
      rintro ⟨⟨har, _⟩, hrs⟩
      linarith
    rw [hempty]
    simp
  · rw [if_neg hs]
    have hat : a ≤ min b s := le_min hab.le (le_of_not_gt hs)
    have heq : Set.Icc a b ∩ Set.Iic s = Set.Icc a (min b s) := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, le_min_iff]
      tauto
    rw [heq]
    have hg : IntegrableOn (fun r : ℝ => 2*r/(b^2-a^2)) (Set.Icc a (min b s)) := by
      exact (by fun_prop : Continuous (fun r : ℝ => 2*r/(b^2-a^2))).integrableOn_Icc
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc a (min b s))]
        (fun r : ℝ => 2*r/(b^2-a^2)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact div_nonneg (mul_nonneg (by norm_num) (ha.trans hr.1)) hΔ.le
    rw [← ofReal_integral_eq_lintegral_ofReal hg hnonneg,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hat,
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
      integral_id]
    congr 1
    ring

theorem annulus_radial_measure_proof (center : EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) :
    (ENNReal.ofReal (1 / (Real.pi * (b^2-a^2)))) •
      Measure.map (fun x : EuclideanSpace ℝ (Fin 2) => dist x center)
        (volume.restrict {x | a ≤ dist x center ∧ dist x center ≤ b}) =
      volume.withDensity (fun r : ℝ => ENNReal.ofReal
        (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0)) := by
  have hΔ : 0 < b^2-a^2 := annulus_radial_delta_pos a b ha hab
  have harea : volume {x : EuclideanSpace ℝ (Fin 2) |
      a ≤ dist x center ∧ dist x center ≤ b} < ⊤ := by
    rw [annulus_radial_area center a b ha hab.le]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure (volume.restrict {x : EuclideanSpace ℝ (Fin 2) |
      a ≤ dist x center ∧ dist x center ≤ b}) :=
    isFiniteMeasure_restrict.mpr harea.ne
  letI : IsFiniteMeasure ((ENNReal.ofReal (1 / (Real.pi * (b^2-a^2)))) •
      Measure.map (fun x : EuclideanSpace ℝ (Fin 2) => dist x center)
        (volume.restrict {x | a ≤ dist x center ∧ dist x center ≤ b})) :=
    (Measure.map (fun x : EuclideanSpace ℝ (Fin 2) => dist x center)
      (volume.restrict {x | a ≤ dist x center ∧ dist x center ≤ b})).smul_finite
        ENNReal.ofReal_ne_top
  -- Only the left measure must be finite for `Measure.ext_of_Iic`.
  apply Measure.ext_of_Iic
  intro s
  rw [Measure.smul_apply, smul_eq_mul,
    annulus_radial_map_Iic center a b s ha hab,
    annulus_radial_density_Iic a b s ha hab]
  by_cases hs : s < a
  · simp only [if_pos hs, mul_zero]
  · simp only [if_neg hs]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [Real.pi_ne_zero, ne_of_gt hΔ]
    <;> ring

/-! ## P004-T16: the fixed positive-area rectangle witness -/

private theorem polygon_range_rectangle_closed (a b c d : ℝ) :
    IsClosed (rectangle a b c d) := by
  change IsClosed ({x : EuclideanSpace ℝ (Fin 2) | a ≤ x 0} ∩
    ({x | x 0 ≤ b} ∩ ({x | c ≤ x 1} ∩ {x | x 1 ≤ d})))
  exact (isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).inter
    ((isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0) continuous_const).inter
      ((isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)).inter
        (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1) continuous_const)))

private theorem polygon_range_rectangle_volume (a b c d : ℝ) :
    volume (rectangle a b c d) = ENNReal.ofReal (b-a) * ENNReal.ofReal (d-c) := by
  have hpre : (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) ⁻¹'
      rectangle a b c d = Set.Icc (![a,c] : Fin 2 → ℝ) ![b,d] := by
    ext x
    change (a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ d) ↔
      ((∀ i : Fin 2, ![a,c] i ≤ x i) ∧ ∀ i : Fin 2, x i ≤ ![b,d] i)
    constructor
    · rintro ⟨hx0, hx1, hy0, hy1⟩
      constructor
      · intro i
        fin_cases i
        · exact hx0
        · exact hy0
      · intro i
        fin_cases i
        · exact hx1
        · exact hy1
    · rintro ⟨hlo, hhi⟩
      exact ⟨hlo 0, hhi 0, hlo 1, hhi 1⟩
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
    (polygon_range_rectangle_closed a b c d).measurableSet.nullMeasurableSet,
    hpre, Real.volume_Icc_pi]
  simp [Fin.prod_univ_succ]

private theorem polygon_range_node_closed (i : Fin 3) :
    IsClosed (rectangleWitness.node i) := by
  fin_cases i <;> exact polygon_range_rectangle_closed _ _ _ _

private theorem polygon_range_region (i : Fin 3) :
    region rectangleWitness i 0 = rectangleWitness.node i := by
  ext x
  change Metric.infDist x (rectangleWitness.node i) ∈ ({0} : Set ℝ) ↔ _
  rw [Set.mem_singleton_iff]
  exact ((polygon_range_node_closed i).mem_iff_infDist_zero
    (rectangleWitness.node_nonempty i)).symm

private theorem polygon_range_node_mass (i : Fin 3) :
    volume (rectangleWitness.node i) = if i = 2 then 11 else 1 := by
  fin_cases i <;> norm_num [rectangleWitness, polygon_range_rectangle_volume]

private theorem polygon_range_outcome_on_node (i : Fin 3) (z : Assignment 3)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ rectangleWitness.node i) :
    rectangleWitness.outcome x z = if i = 2 then 0 else bit (z 2) := by
  fin_cases i
  · change x ∈ rectangle 0 1 0 1 at hx
    simp [rectangleWitness, hx]
  · change x ∈ rectangle 10 11 0 1 at hx
    simp [rectangleWitness, hx]
  · change x ∈ rectangle 0 11 2 3 at hx
    have hnot : x ∉ rectangle 0 1 0 1 ∪ rectangle 10 11 0 1 := by
      intro h
      rcases h with h | h
      · have hy : x 1 ≤ 1 := h.2.2.2
        have hyl : 2 ≤ x 1 := hx.2.2.1
        linarith
      · have hy : x 1 ≤ 1 := h.2.2.2
        have hyl : 2 ≤ x 1 := hx.2.2.1
        linarith
    change (if x ∈ rectangle 0 1 0 1 ∪ rectangle 10 11 0 1 then bit (z 2) else 0) = 0
    rw [if_neg hnot]

private theorem polygon_range_wellDefined : WellDefined rectangleWitness 0 := by
  intro i
  rw [polygon_range_region]
  have hmeas : MeasurableSet (rectangleWitness.node i) :=
    (polygon_range_node_closed i).measurableSet
  have hpos : 0 < volume (rectangleWitness.node i) := by
    rw [polygon_range_node_mass]
    split_ifs <;> norm_num
  have hfinite : volume (rectangleWitness.node i) < ⊤ := by
    rw [polygon_range_node_mass]
    split_ifs <;> norm_num
  refine ⟨hmeas, hpos, hfinite, ?_⟩
  intro z
  have hc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 2) =>
      if i = 2 then (0 : ℝ) else bit (z 2)) (rectangleWitness.node i) :=
    integrableOn_const hfinite.ne
  exact hc.congr_fun (fun x hx => (polygon_range_outcome_on_node i z x hx).symm) hmeas

private theorem polygon_range_average (i : Fin 3) (z : Assignment 3) :
    circleAverage rectangleWitness 0 i z = if i = 2 then 0 else bit (z 2) := by
  have hout : Set.EqOn (fun x => rectangleWitness.outcome x z)
      (fun _ => if i = 2 then 0 else bit (z 2)) (rectangleWitness.node i) :=
    fun x hx => polygon_range_outcome_on_node i z x hx
  rw [circleAverage, polygon_range_region,
    setIntegral_congr_fun (polygon_range_node_closed i).measurableSet hout]
  change (∫ _ in rectangleWitness.node i, if i = 2 then (0 : ℝ) else bit (z 2)) /
    (volume (rectangleWitness.node i)).toReal = _
  simp only [setIntegral_const, measureReal_def, smul_eq_mul, polygon_range_node_mass]
  by_cases hi : i = 2 <;> simp [hi]

private theorem polygon_range_averages (z : Assignment 3) :
    circleAverage rectangleWitness 0 0 z = bit (z 2) ∧
      circleAverage rectangleWitness 0 1 z = bit (z 2) ∧
        circleAverage rectangleWitness 0 2 z = 0 := by
  simp [polygon_range_average]

private theorem polygon_range_vertical_distance (x : EuclideanSpace ℝ (Fin 2)) :
    dist x (planePoint (x 0) 2) = |x 1 - 2| := by
  simp [EuclideanSpace.dist_eq, planePoint, Fin.sum_univ_succ, Real.dist_eq,
    Real.sqrt_sq_eq_abs]

private theorem polygon_range_source_range : FiniteSourceRange rectangleWitness 2 := by
  intro l x z z' hsame hfar
  by_cases hx : x ∈ rectangle 0 1 0 1 ∪ rectangle 10 11 0 1
  · by_cases hl : l = 2
    · subst l
      have hxy : (0 ≤ x 0 ∧ x 0 ≤ 11) ∧ (0 ≤ x 1 ∧ x 1 ≤ 1) := by
        rcases hx with hx | hx
        · rcases hx with ⟨hx0, hx1, hy0, hy1⟩
          exact ⟨⟨hx0, by linarith⟩, hy0, hy1⟩
        · rcases hx with ⟨hx0, hx1, hy0, hy1⟩
          exact ⟨⟨by linarith, hx1⟩, hy0, hy1⟩
      have hproj : planePoint (x 0) 2 ∈ rectangleWitness.node 2 := by
        change planePoint (x 0) 2 ∈ rectangle 0 11 2 3
        simpa [rectangle, planePoint] using ⟨hxy.1.1, hxy.1.2, (by norm_num : (2 : ℝ) ≤ 3)⟩
      have hd : nodeDistance rectangleWitness 2 x ≤ 2 := by
        unfold nodeDistance
        calc
          Metric.infDist x (rectangleWitness.node 2) ≤ dist x (planePoint (x 0) 2) :=
            Metric.infDist_le_dist_of_mem hproj
          _ = |x 1 - 2| := polygon_range_vertical_distance x
          _ ≤ 2 := by
            rw [abs_of_nonpos (by linarith [hxy.2.2])]
            linarith [hxy.2.1]
      exact False.elim (not_lt_of_ge hd hfar)
    · have hz : z 2 = z' 2 := hsame 2 (Ne.symm hl)
      simp only [rectangleWitness, if_pos hx, hz]
  · simp only [rectangleWitness, if_neg hx]

private theorem polygon_range_outcome_bound :
    ∀ x z, |rectangleWitness.outcome x z| < 2 := by
  intro x z
  change |if x ∈ rectangle 0 1 0 1 ∪ rectangle 10 11 0 1 then bit (z 2) else 0| < 2
  split_ifs <;> cases z 2 <;> norm_num [bit]

private theorem polygon_range_shared_source :
    sharesSource (circleAverage rectangleWitness 0) 0 1 := by
  let z : Assignment 3 := fun _ => false
  let z' : Assignment 3 := Function.update z 2 true
  have hsame : ∀ k : Fin 3, k ≠ 2 → z k = z' k := by
    intro k hk
    simp [z', Function.update_of_ne hk]
  have hzero : circleAverage rectangleWitness 0 0 z ≠
      circleAverage rectangleWitness 0 0 z' := by
    norm_num [polygon_range_average, z, z', bit]
  have hone : circleAverage rectangleWitness 0 1 z ≠
      circleAverage rectangleWitness 0 1 z' := by
    norm_num [polygon_range_average, z, z', bit]
  exact ⟨2, Or.inr ⟨z, z', hsame, hzero⟩, Or.inr ⟨z, z', hsame, hone⟩⟩

private theorem polygon_range_separation : nodeSeparation rectangleWitness 0 1 = 9 := by
  let S : Set ℝ := {r | ∃ x ∈ rectangleWitness.node 0,
    ∃ y ∈ rectangleWitness.node 1, dist x y = r}
  have hmem : (9 : ℝ) ∈ S := by
    refine ⟨planePoint 1 0, ?_, planePoint 10 0, ?_, ?_⟩
    · norm_num [rectangleWitness, rectangle, planePoint]
    · norm_num [rectangleWitness, rectangle, planePoint]
    · norm_num [EuclideanSpace.dist_eq, planePoint, Fin.sum_univ_succ, Real.dist_eq]
  have hlow : ∀ r ∈ S, (9 : ℝ) ≤ r := by
    rintro r ⟨x, hx, y, hy, rfl⟩
    change x ∈ rectangle 0 1 0 1 at hx
    change y ∈ rectangle 10 11 0 1 at hy
    have hx0 : x 0 ≤ 1 := hx.2.1
    have hy0 : 10 ≤ y 0 := hy.1
    have hcoord : |x 0-y 0| ≤ dist x y := by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le x y 0
    have hneg : -(x 0-y 0) ≤ |x 0-y 0| := neg_le_abs _
    linarith
  change sInf S = 9
  exact le_antisymm (csInf_le ⟨9, hlow⟩ hmem) (le_csInf ⟨9, hmem⟩ hlow)

private theorem polygon_range_covariance :
    cov (fun _ => 1/2) (circleAverage rectangleWitness 0 0)
      (circleAverage rectangleWitness 0 1) = 1/4 := by
  have hav0 : circleAverage rectangleWitness 0 0 = fun z => bit (z 2) := by
    funext z
    exact (polygon_range_averages z).1
  have hav1 : circleAverage rectangleWitness 0 1 = fun z => bit (z 2) := by
    funext z
    exact (polygon_range_averages z).2.1
  have hm (k : ℕ) (hk : 0 < k) :
      expect (fun _ : Fin 3 => 1/2) (fun z => (bit (z 2))^k) = 1/2 := by
    have hp : ∀ j : Fin 3, (0 : ℝ) < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 :=
      fun _ => by norm_num
    have h := bernoulli_positive_power (fun _ : Fin 3 => 1/2)
      (fun _ : Assignment 3 => (1 : ℝ)) (2 : Fin 3) k hk hp
    simpa only [mul_one, expect_const] using h
  rw [hav0, hav1, cov]
  simp only [← pow_two]
  have hm1 : expect (fun _ : Fin 3 => 1/2) (fun z => bit (z 2)) = 1/2 := by
    simpa only [pow_one] using hm 1 (by norm_num)
  rw [hm 2 (by norm_num), hm1]
  norm_num

theorem polygon_range_counterexample_proof :
    WellDefined rectangleWitness 0 ∧ FiniteSourceRange rectangleWitness 2 ∧
    (∀ x z, |rectangleWitness.outcome x z| < 2) ∧
    (∀ z, circleAverage rectangleWitness 0 0 z = bit (z 2) ∧
      circleAverage rectangleWitness 0 1 z = bit (z 2) ∧ circleAverage rectangleWitness 0 2 z = 0) ∧
    sharesSource (circleAverage rectangleWitness 0) 0 1 ∧
    nodeSeparation rectangleWitness 0 1 = 9 ∧ (4 : ℝ) < 9 ∧
    cov (fun _ => 1/2) (circleAverage rectangleWitness 0 0) (circleAverage rectangleWitness 0 1) = 1/4 := by
  exact ⟨polygon_range_wellDefined, polygon_range_source_range,
    polygon_range_outcome_bound, polygon_range_averages, polygon_range_shared_source,
    polygon_range_separation, by norm_num, polygon_range_covariance⟩

end
end AronowAudit.P004.Wave1


