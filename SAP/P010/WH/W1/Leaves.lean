import SAP.P010.Defs.WholeW1
import SAP.P010.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P010.WH.W1

open MeasureTheory Set Filter
open scoped ENNReal NNReal

universe u

/-- T12: the printed weighted extended mass is the positive Bayes constant
times the squared-density-ratio extended mass, including infinite values.
Use AronowAudit.P010.transport_mass_factors almost everywhere, then
ENNReal.ofReal_mul, lintegral_congr_ae, and lintegral_const_mul'. No
integrability, normalization, or finiteness of the dominating measure is needed. -/
def T12_L1 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) (π : ℝ) (fR fO : Ω → ℝ),
    0 < π → π < 1 →
    (∀ᵐ x ∂ν, 0 < fR x) → (∀ᵐ x ∂ν, 0 < fO x) →
    printedWeightedMass ν π fR fO =
      ENNReal.ofReal (π / (1-π)) * squareRatioMass ν fR fO

/-- T12: a density of infinite total mass cannot be made a probability
measure by any finite nonnegative scalar, including zero. Evaluate
withDensity_apply on Set.univ, pull out the finite constant using
lintegral_const_mul', and split c=0 from c>0. The resulting mass is zero
or infinity, contradicting IsProbabilityMeasure.measure_univ. -/
def T12_L2 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) (h : Ω → ℝ≥0∞),
    (∫⁻ x, h x ∂ν) = ⊤ →
    ∀ c : ℝ≥0, ¬ IsProbabilityMeasure
      (ν.withDensity (fun x => (c : ℝ≥0∞) * h x))

/-- T17: the observed (S,Z) law gives exactly the passing-and-assigned
and assigned event masses. Apply Measure.map_apply to the two measurable
coordinate events. Measurability of the map follows from
AronowAudit.P010.measurable_observedS and measurable_assignment via prodMk;
their preimages are definitionally passed ∩ assigned a and assigned a.
This requires no independence or passing-positivity premise. -/
def T17_L1 : Prop :=
  ∀ {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K),
    observedCheckArmLaw μ {v | v.1 = true ∧ v.2 = a} = μ (passed ∩ assigned a) ∧
    observedCheckArmLaw μ {v | v.2 = a} = μ (assigned a)

theorem T12_assembly (h1 : T12_L1.{u}) (h2 : T12_L2.{u}) :
    T12WholeStatement.{u} := by
  intro Ω mΩ ν π fR fO hπ hπ1 hR hO hiR hiO hsR hsO
  let Z := squareRatioMass ν fR fO
  have hC : 0 < π / (1-π) := div_pos hπ (sub_pos.mpr hπ1)
  have hcorr : (fun x => fR x * reverseOdds (propensity π (fR x) (fO x))) =ᵐ[ν]
      (fun x => ((1-π)/π) * fO x) := by
    filter_upwards [hR, hO] with x hx hy
    exact (AronowAudit.P010.transport_mass_factors π (fR x) (fO x) hπ hπ1 hx hy).1
  have hprinted : (fun x => fR x * odds (propensity π (fR x) (fO x))) =ᵐ[ν]
      (fun x => (π/(1-π)) * ((fR x)^2 / fO x)) := by
    filter_upwards [hR, hO] with x hx hy
    exact (AronowAudit.P010.transport_mass_factors π (fR x) (fO x) hπ hπ1 hx hy).2
  have hqnon : 0 ≤ᵐ[ν] (fun x => (fR x)^2 / fO x) := by
    filter_upwards [hO] with x hx
    exact div_nonneg (sq_nonneg _) (le_of_lt hx)
  have hqmeas : AEStronglyMeasurable (fun x => (fR x)^2 / fO x) ν :=
    (hiR.aestronglyMeasurable.pow 2).div₀ hiO.aestronglyMeasurable
  have htransport := AronowAudit.P010.transport_corrected_density
    ν π fR fO hπ hπ1 hR hO hiR hiO hsR hsO
  refine ⟨?_, ?_, (hiO.const_mul _).congr hcorr.symm, ?_,
    htransport.1, htransport.2.1, h1 Ω ν π fR fO hπ hπ1 hR hO, ?_, ?_⟩
  · filter_upwards [hR, hO] with x hx hy
    exact AronowAudit.P010.transport_bayes π (fR x) (fO x) hπ hπ1 hx hy
  · filter_upwards [] with x
    simp [odds, reverseOdds]
  · rw [integral_congr_ae hcorr, integral_const_mul, hsO, mul_one]
  · intro hZ
    have hiq : Integrable (fun x => (fR x)^2 / fO x) ν :=
      (lintegral_ofReal_ne_top_iff_integrable hqmeas hqnon).mp (ne_of_lt hZ)
    have hD := (AronowAudit.P010.square_density_normalization
      ν fR fO hR hO hiR hiO hsR hsO hiq).1
    have hDZ : (∫ x, (fR x)^2 / fO x ∂ν) = Z.toReal :=
      integral_eq_lintegral_of_nonneg_ae hqnon hqmeas
    have hZpos : 0 < Z := by
      exact (ENNReal.toReal_pos_iff.mp (hDZ ▸ hD)).1
    have him : Integrable (fun x => fR x * odds (propensity π (fR x) (fO x))) ν :=
      (hiq.const_mul _).congr hprinted.symm
    have hm : (∫ x, fR x * odds (propensity π (fR x) (fO x)) ∂ν) =
        (π/(1-π)) * Z.toReal := by
      rw [integral_congr_ae hprinted, integral_const_mul, hDZ]
    have ht := htransport.2.2 hiq
    have hmasspos : 0 < printedWeightedMass ν π fR fO := by
      rw [h1 Ω ν π fR fO hπ hπ1 hR hO]
      exact bot_lt_iff_ne_bot.mpr (mul_ne_zero
        (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) (ne_of_gt hZpos))
    have hmassfin : printedWeightedMass ν π fR fO < ⊤ := by
      rw [h1 Ω ν π fR fO hπ hπ1 hR hO]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hZ
    refine ⟨hiq, hZpos, hDZ ▸ hD, hmasspos, hmassfin, him, hm, ?_, ?_, ht.2⟩
    · rw [hm]
      exact mul_pos hC (hDZ ▸ hD)
    · change (fun x => normalizeDensity ν fR
        (fun y => odds (propensity π (fR y) (fO y))) x) =ᵐ[ν]
          (fun x => (fR x)^2 / fO x / Z.toReal)
      rw [← hDZ]
      exact ht.1
  · intro hZ
    have hm : printedWeightedMass ν π fR fO = ⊤ := by
      rw [h1 Ω ν π fR fO hπ hπ1 hR hO, hZ]
      exact ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hC))
    exact ⟨hm, h2 Ω ν
      (fun x => ENNReal.ofReal (fR x * odds (propensity π (fR x) (fO x)))) hm⟩

theorem T17_assembly (h1 : T17_L1) : T17WholeStatement := by
  have hobs {K d : ℕ} (μ : Measure (Population K d)) :
      positivePassRates μ ↔ observablePositivePassRates (observedCheckArmLaw μ) := by
    unfold positivePassRates observablePositivePassRates passRate
    simp_rw [(h1 μ _).1, (h1 μ _).2]
  intro K d μ hp hi
  refine ⟨?_, ?_, hobs μ, ?_⟩
  · change (IsProbabilityMeasure μ ∧ randomAssignment μ ∧ positivePassRates μ) ↔
      positivePassRates μ
    exact ⟨fun h => h.2.2, fun h => ⟨hp, hi, h⟩⟩
  · intro h a
    have : IsProbabilityMeasure μ := hp
    exact ⟨ENNReal.toReal_pos (ne_of_gt (hi.2 a)) (measure_ne_top μ _), h.2.2 a⟩
  · intro d' ν _ _ heq
    exact (hobs μ).trans (heq ▸ (hobs ν).symm)

end SAP.P010.WH.W1
