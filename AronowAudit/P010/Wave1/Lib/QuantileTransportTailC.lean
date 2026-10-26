import AronowAudit.External.Causalean.Stat.Coupling.Monotone.ProductLoss.PIT
import AronowAudit.P010.Wave1.Gap.GLP010P033B2

namespace AronowAudit.P010.Wave1

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

set_option maxHeartbeats 800000

/-- The extended inverse agrees with the real generalized inverse
at every interior level. No strict increase of the CDF is required. -/
theorem tcQuantile_inverse_bridge (F : Measure ℝ) [IsProbabilityMeasure F]
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    quantile F u = (Causalean.Stat.quantile F u : EReal) := by
  apply le_antisymm
  · apply sInf_le
    simpa only [mem_setOf_eq, EReal.coe_le_coe_iff, Set.Iic_def,
      cdf_eq_real, measureReal_def] using Causalean.Stat.le_cdf_quantile (μ := F) hu1
  · apply le_sInf
    intro z hz
    induction z using EReal.rec with
    | bot =>
      have he : {y : ℝ | (y : EReal) ≤ ⊥} = ∅ := by ext y; simp
      simp only [mem_setOf_eq, he, measure_empty, ENNReal.toReal_zero] at hz
      exact False.elim ((not_le_of_gt hu) hz)
    | coe x =>
      apply EReal.coe_le_coe_iff.mpr
      apply Causalean.Stat.quantile_le_of_le_cdf hu
      simpa only [mem_setOf_eq, EReal.coe_le_coe_iff, Set.Iic_def,
        cdf_eq_real, measureReal_def] using hz
    | top => exact le_top

theorem tcQuantile_real_bridge (F : Measure ℝ) [IsProbabilityMeasure F]
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    quantileReal F u = Causalean.Stat.quantile F u := by
  simp [quantileReal, tcQuantile_inverse_bridge F hu hu1]

theorem tcQuantile_monotone (F : Measure ℝ) : Monotone (quantile F) := by
  intro u v huv
  exact sInf_le_sInf fun x hx => huv.trans hx

theorem tcQuantile_ae_bridge (F : Measure ℝ) [IsProbabilityMeasure F] :
    quantileReal F =ᵐ[Causalean.Stat.unifOI] Causalean.Stat.quantile F := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact tcQuantile_real_bridge F hu.1 hu.2

theorem tcQuantile_aemeasurable (F : Measure ℝ) [IsProbabilityMeasure F] :
    AEMeasurable (quantileReal F) Causalean.Stat.unifOI :=
  (Causalean.Stat.aemeasurable_quantile_unifOI F).congr (tcQuantile_ae_bridge F).symm

/-- Inverse-transform transport for the exact quantile definition. -/
theorem tcQuantile_transport (F : Measure ℝ) [IsProbabilityMeasure F] :
    Causalean.Stat.unifOI.map (quantileReal F) = F := by
  rw [Measure.map_congr (tcQuantile_ae_bridge F)]
  exact Causalean.Stat.quantile_map_uniform F

/-- Atomlessness identifies the exact CDF value at an interior inverse. -/
theorem tcQuantile_cdf (F : Measure ℝ) [IsProbabilityMeasure F] (hc : Atomless F)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) : cdf F (quantileReal F u) = u := by
  obtain ⟨q, hq, hcdf⟩ := upper_tail_proof_corrected_quantile_finite F hc hu hu1
  simpa [quantileReal, hq] using hcdf

/-- Lower-tail membership is precisely a lower interval of uniform levels,
including the extended upper-endpoint cutoff. -/
theorem tcQuantile_lower_level (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) {t u : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hu : 0 < u) (hu1 : u < 1) :
    (quantileReal F u : EReal) ≤ quantile F t ↔ u ≤ t := by
  have hqu : quantile F u = (quantileReal F u : EReal) := by
    simp [tcQuantile_inverse_bridge F hu hu1, tcQuantile_real_bridge F hu hu1]
  rcases lt_or_eq_of_le ht1 with ht1 | rfl
  · rw [tcQuantile_inverse_bridge F ht ht1, EReal.coe_le_coe_iff,
      tcQuantile_real_bridge F hu hu1,
      Causalean.Stat.quantile_le_iff hu hu1]
    rw [← tcQuantile_real_bridge F ht ht1, tcQuantile_cdf F hc ht ht1]
  · exact ⟨fun _ => hu1.le, fun _ => hqu ▸ tcQuantile_monotone F hu1.le⟩

/-- Upper-tail membership is precisely an upper interval of uniform levels,
including the bottom cutoff at level zero. -/
theorem tcQuantile_upper_level (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) {s u : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (hu : 0 < u) (hu1 : u < 1) :
    quantile F s ≤ (quantileReal F u : EReal) ↔ s ≤ u := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [upper_tail_proof_corrected_quantile_zero, hu.le]
  · rw [tcQuantile_inverse_bridge F hs hs1, EReal.coe_le_coe_iff,
      ← tcQuantile_real_bridge F hs hs1]
    constructor
    · intro hq
      have hh := monotone_cdf F hq
      rwa [tcQuantile_cdf F hc hs hs1, tcQuantile_cdf F hc hu hu1] at hh
    · intro hsu
      rw [tcQuantile_real_bridge F hs hs1, tcQuantile_real_bridge F hu hu1]
      exact Causalean.Stat.quantile_mono hs hu1 hsu

theorem tcQuantile_lower_preimage (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (quantileReal F ⁻¹' {y : ℝ | (y : EReal) ≤ quantile F t})
      =ᵐ[Causalean.Stat.unifOI] Iic t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact propext (tcQuantile_lower_level F hc ht ht1 hu.1 hu.2)

theorem tcQuantile_upper_preimage (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    (quantileReal F ⁻¹' {y : ℝ | quantile F s ≤ (y : EReal)})
      =ᵐ[Causalean.Stat.unifOI] Ici s := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact propext (tcQuantile_upper_level F hc hs hs1 hu.1 hu.2)

/-- Exact lower restricted transport; replacing open endpoints is harmless
only in the uniform measure, never in the cutoff definition. -/
theorem tcQuantile_lower_transport (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (volume.restrict (Ioc (0 : ℝ) t)).map (quantileReal F) =
      F.restrict {y : ℝ | (y : EReal) ≤ quantile F t} := by
  have hB : MeasurableSet {y : ℝ | (y : EReal) ≤ quantile F t} :=
    measurableSet_le measurable_coe_real_ereal measurable_const
  have he := Measure.restrict_map_of_aemeasurable (tcQuantile_aemeasurable F) hB
  rw [tcQuantile_transport F,
    Measure.restrict_congr_set (tcQuantile_lower_preimage F hc ht ht1)] at he
  rw [he]
  congr 1
  rw [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc,
    Measure.restrict_restrict measurableSet_Iic, restrict_Ioc_eq_restrict_Icc]
  congr 1
  ext u
  simp only [mem_inter_iff, mem_Iic, mem_Icc]
  constructor
  · rintro ⟨hu0, hut⟩
    exact ⟨hut, hu0, hut.trans ht1⟩
  · rintro ⟨hut, hu0, _⟩
    exact ⟨hu0, hut⟩

theorem tcQuantile_upper_transport (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    (volume.restrict (Ioc s (1 : ℝ))).map (quantileReal F) =
      F.restrict {y : ℝ | quantile F s ≤ (y : EReal)} := by
  have hB := upper_tail_proof_corrected_tail_measurable F s
  have he := Measure.restrict_map_of_aemeasurable (tcQuantile_aemeasurable F) hB
  rw [tcQuantile_transport F,
    Measure.restrict_congr_set (tcQuantile_upper_preimage F hc hs hs1)] at he
  rw [he]
  congr 1
  rw [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc,
    Measure.restrict_restrict measurableSet_Ici, restrict_Ioc_eq_restrict_Icc]
  congr 1
  ext u
  simp only [mem_inter_iff, mem_Ici, mem_Icc]
  constructor
  · rintro ⟨hsu, hu1⟩
    exact ⟨hsu, hs.trans hsu, hu1⟩
  · rintro ⟨hsu, _, hu1⟩
    exact ⟨hsu, hu1⟩

/-- Measurability on any interval contained in the unit interval. -/
theorem tcQuantile_aemeasurable_subinterval (F : Measure ℝ) [IsProbabilityMeasure F]
    {E : Set ℝ} (hE : E ⊆ Icc (0 : ℝ) 1) :
    AEMeasurable (quantileReal F) (volume.restrict E) := by
  apply (tcQuantile_aemeasurable F).mono_measure
  rw [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc]
  exact Measure.restrict_mono hE le_rfl

/-- Exact lower cutoff mass, also at level one. -/
theorem tcQuantile_lower_mass (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (F {y : ℝ | (y : EReal) ≤ quantile F t}).toReal = t := by
  have hh := congrArg (fun ν : Measure ℝ => ν univ)
    (tcQuantile_lower_transport F hc ht ht1)
  rw [Measure.map_apply_of_aemeasurable (tcQuantile_aemeasurable_subinterval F
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht1))) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero] at hh
  rw [← hh, ENNReal.toReal_ofReal ht.le]

/-- Exact upper cutoff mass, also at the bottom cutoff. -/
theorem tcQuantile_upper_mass (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    (F {y : ℝ | quantile F s ≤ (y : EReal)}).toReal = 1-s :=
  upper_tail_proof_corrected_tail_mass F hc hs hs1

/-- Both tail integrals, including the retained-mass-one case. -/
theorem quantile_tail_integrals (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) (hi : Integrable id F) :
    Integrable (quantileReal F) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      (∫ y in {y : ℝ | (y : EReal) ≤ quantile F t}, y ∂F) =
        (∫ u in (0 : ℝ)..t, quantileReal F u) ∧
      (∫ y in {y : ℝ | quantile F (1-t) ≤ (y : EReal)}, y ∂F) =
        ∫ u in (1-t)..(1 : ℝ), quantileReal F u := by
  have hm := tcQuantile_aemeasurable F
  have hiq : Integrable (quantileReal F) Causalean.Stat.unifOI := by
    have hh : Integrable id (Causalean.Stat.unifOI.map (quantileReal F)) := by
      rw [tcQuantile_transport F]
      exact hi
    exact (integrable_map_measure measurable_id.aestronglyMeasurable hm).mp hh
  constructor
  · rwa [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc] at hiq
  · intro t ht ht1
    constructor
    · have hq := tcQuantile_aemeasurable_subinterval F
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht1))
      rw [← tcQuantile_lower_transport F hc ht ht1,
        integral_map hq measurable_id'.aestronglyMeasurable,
        intervalIntegral.integral_of_le ht.le]
    · have hq := tcQuantile_aemeasurable_subinterval F
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith : 0 ≤ 1-t) le_rfl))
      rw [← tcQuantile_upper_transport F hc (by linarith : 0 ≤ 1-t)
          (by linarith : 1-t < 1),
        integral_map hq measurable_id'.aestronglyMeasurable,
        intervalIntegral.integral_of_le (by linarith : 1-t ≤ 1)]

end AronowAudit.P010.Wave1
