import SAP.P004a.WH.W2.Leaves
import AronowAudit.P004.Wave1.Gap.GP0041B1
import AronowAudit.P004.P004_SpatialAlgebraCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T14_L3

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal
noncomputable section
set_option maxHeartbeats 1000000

private lemma disk_region_eq_annulus (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    region (radialAreaPopulation (Icc a b)) 0 0 =
      {x : EuclideanSpace ℝ (Fin 2) | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
  ext x
  simp [region, nodeDistance, radialAreaPopulation, Metric.infDist_singleton,
    dist_eq_norm, ha]

private lemma area_restrict_eq_annulus (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    (radialAreaPopulation (Icc a b)).zeta.restrict
      (region (radialAreaPopulation (Icc a b)) 0 0) =
      volume.restrict {x : EuclideanSpace ℝ (Fin 2) | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
  rw [disk_region_eq_annulus a b ha hb]
  have hA : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
    exact measurableSet_Icc.preimage (measurable_norm)
  have hDisk : MeasurableSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Metric.isClosed_closedBall.measurableSet
  have hsub : {x : EuclideanSpace ℝ (Fin 2) | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ⊆
      Metric.closedBall 0 1 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx.2.trans hb
  change (volume.restrict (Metric.closedBall 0 1)).restrict
    {x : EuclideanSpace ℝ (Fin 2) | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} = _
  rw [Measure.restrict_restrict hA]
  congr 1
  rw [Set.inter_comm]
  exact Set.inter_eq_right.mpr hsub

private lemma annulus_density_integral (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hΔ : 0 < b^2-a^2) :
    (∫ r, r ∂ volume.withDensity (fun r : ℝ => ENNReal.ofReal
      (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0))) =
      ∫ r in Icc a b, r*(2*r/(b^2-a^2)) := by
  let ρ : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal
    (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0)
  have hρ : Measurable ρ := by
    dsimp [ρ]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.ite
    · simpa [Set.Icc] using (measurableSet_Icc : MeasurableSet (Icc a b))
    · fun_prop
    · exact measurable_const
  have hρtop : ∀ᵐ r ∂volume, ρ r < ∞ := by
    filter_upwards [] with r
    exact ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hρ hρtop]
  have hcongr : (fun r : ℝ => (ρ r).toReal • r) =
      Set.indicator (Icc a b) (fun r : ℝ => r*(2*r/(b^2-a^2))) := by
    funext r
    by_cases hr : a ≤ r ∧ r ≤ b
    · have hnonneg : 0 ≤ 2*r/(b^2-a^2) := by
        have hr0 : 0 ≤ r := le_trans ha hr.1
        exact div_nonneg (by positivity) hΔ.le
      simp [ρ, hr, ENNReal.toReal_ofReal hnonneg, smul_eq_mul]
      ring
    · simp [ρ, hr, Set.indicator]
  rw [hcongr, integral_indicator measurableSet_Icc]

end
end SAP.P004a.WH.W2.P.T14_L3

open SAP.P004a.WH.W2.P.T14_L3
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal
set_option maxHeartbeats 1000000

theorem SAP.P004a.WH.W2.T14_L3_proof : SAP.P004a.WH.W2.T14_L3 := by
  intro hE
  rcases hE with ⟨hbound, hout, hpoint, hcontinuous, hconditional, hcert⟩
  refine fun a b ha hab hb => ?_
  let P : SpatialPopulation 1 (EuclideanSpace ℝ (Fin 2)) := radialAreaPopulation (Icc a b)
  let A : Set (EuclideanSpace ℝ (Fin 2)) := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := P.zeta.restrict (region P 0 0)
  let ρ : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal
    (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0)
  have hbpos : 0 < b := lt_of_le_of_lt ha hab
  have hΔ : 0 < b^2-a^2 := by nlinarith
  have hWDmass := hcert a b ha hab hb
  have hWD : WellDefined P 0 := by simpa [P] using hWDmass.1
  have hmass : P.zeta (region P 0 0) = ENNReal.ofReal (Real.pi*(b^2-a^2)) := by
    simpa [P] using hWDmass.2
  have hmasspos : 0 < (P.zeta (region P 0 0)).toReal := by
    rw [hmass, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*(b^2-a^2))]
    exact mul_pos Real.pi_pos hΔ
  have hμ : μ = volume.restrict A := by
    simpa [P, A, μ] using area_restrict_eq_annulus a b ha hb
  have hrad : (ENNReal.ofReal (1/(Real.pi*(b^2-a^2)))) • Measure.map
      (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖) μ =
      volume.withDensity ρ := by
    rw [hμ]
    simpa [ρ, dist_eq_norm] using
      (AronowAudit.P004.Wave1.annulus_radial_measure_proof
        (0 : EuclideanSpace ℝ (Fin 2)) a b ha hab)
  have htransport : (ENNReal.ofReal (1/(Real.pi*(b^2-a^2)))) • Measure.map
      (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖)
      ((radialAreaPopulation (Icc a b)).zeta.restrict
        (region (radialAreaPopulation (Icc a b)) 0 0)) =
      volume.withDensity ρ := by
    simpa [P, ρ] using hrad
  have hmap : (∫ r, r ∂Measure.map
      (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖) μ) = ∫ x, ‖x‖ ∂μ := by
    exact MeasureTheory.integral_map measurable_norm.aemeasurable
      (measurable_id.aestronglyMeasurable)
  have hradInt : (∫ x, ‖x‖ ∂μ) /
      (P.zeta (region P 0 0)).toReal =
      ∫ r in Icc a b, r*(2*r/(b^2-a^2)) := by
    have hscale : (ENNReal.ofReal (1/(Real.pi*(b^2-a^2)))).toReal =
        1/(P.zeta (region P 0 0)).toReal := by
      have hcoeff : 0 ≤ Real.pi*(b^2-a^2) := mul_nonneg Real.pi_pos.le hΔ.le
      have hmReal : (P.zeta (region P 0 0)).toReal = Real.pi*(b^2-a^2) := by
        rw [hmass, ENNReal.toReal_ofReal hcoeff]
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(Real.pi*(b^2-a^2))), hmReal]
    calc
      (∫ x, ‖x‖ ∂μ) / (P.zeta (region P 0 0)).toReal
          = (ENNReal.ofReal (1/(Real.pi*(b^2-a^2)))).toReal * ∫ x, ‖x‖ ∂μ := by
              rw [hscale]
              ring
      _ = ∫ r, r ∂volume.withDensity ρ := by
            rw [← hrad, integral_smul_measure, hmap]
            simp [smul_eq_mul]
      _ = ∫ r in Icc a b, r*(2*r/(b^2-a^2)) := by
            exact annulus_density_integral a b ha hab hΔ
  have hpointAE : (fun x : EuclideanSpace ℝ (Fin 2) => pointEffect P (fun _ => 1/2) 0 x) =ᵐ[μ]
      fun x => ‖x‖ := by
    filter_upwards [ae_restrict_mem (hWD 0).1] with x hx
    have hxA : x ∈ A := by
      simpa [P, A, disk_region_eq_annulus a b ha hb] using hx
    have hxnorm : ‖x‖ ≤ 1 := le_trans hxA.2 hb
    exact hpoint x hxnorm
  have hpointInt : (∫ x in region P 0 0,
      pointEffect P (fun _ => 1/2) 0 x ∂P.zeta) = ∫ x, ‖x‖ ∂μ := by
    calc
      _ = ∫ x, pointEffect P (fun _ => 1/2) 0 x ∂μ := rfl
      _ = ∫ x, ‖x‖ ∂μ := integral_congr_ae hpointAE
  have hband := AronowAudit.P004.band_effect_identity
      (SAP.P004a.Bridge.toPopulation P) (fun _ => (1/2 : ℝ)) 0
      (by intro i; fin_cases i <;> norm_num) (by simpa [SAP.P004a.Bridge.wellDefined_eq] using hWD)
  have hameCross : ame (fun _ => (1/2 : ℝ)) (circleAverage P 0) =
      AronowAudit.P004.ame (fun _ => (1/2 : ℝ))
        (AronowAudit.P004.circleAverage (SAP.P004a.Bridge.toPopulation P) 0) := by
    rfl
  have hame : ame (fun _ => (1/2 : ℝ)) (circleAverage P 0) =
      (∫ x in region P 0 0, pointEffect P (fun _ => 1/2) 0 x ∂P.zeta) /
        (P.zeta (region P 0 0)).toReal := by
    rw [hameCross]
    have hbandConv : AronowAudit.P004.ame (fun _ => (1/2 : ℝ))
        (AronowAudit.P004.circleAverage (SAP.P004a.Bridge.toPopulation P) 0) =
        (∫ x in region P 0 0, pointEffect P (fun _ => 1/2) 0 x ∂(SAP.P004a.Bridge.toPopulation P).zeta) /
          ((SAP.P004a.Bridge.toPopulation P).zeta (region P 0 0)).toReal := by
      simpa [SAP.P004a.Bridge.circleAverage_eq, SAP.P004a.Bridge.region_eq,
        SAP.P004a.Bridge.pointEffect_eq, Fin.sum_univ_one] using hband.2
    simpa [SAP.P004a.Bridge.toPopulation] using hbandConv
  refine ⟨?_, ?_, ?_⟩
  · simpa [P, ρ] using htransport
  · simpa [radialAreaIntegral] using
      (show IntegrableOn (fun r : ℝ => r*(2*r/(b^2-a^2))) (Icc a b) from by
        have hcont : Continuous (fun r : ℝ => r*(2*r/(b^2-a^2))) := by fun_prop
        exact hcont.integrableOn_Icc)
  · rw [hame, hpointInt, hradInt]
    rfl
