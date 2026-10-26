import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

local instance instDecidableGLP0014B4 (p : Prop) : Decidable p := Classical.propDecidable p

set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-- Event-based MAR and bounded inverse propensity preserve every outcome event. -/
theorem mar_reweighting_indicator_eq {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R)
    (hbinary : ∀ ω, R ω = 0 ∨ R ω = 1) (p : E → ℝ) (hp : IsCEF μ X R p)
    (ε : ℝ) (hε : 0 < ε) (hpos : ∀ ω, ε < p (X ω)) (hmar : CI μ X hX Y R)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫ ω, (if Y ω ∈ A then R ω / p (X ω) else 0) ∂μ) =
      ∫ ω, (if Y ω ∈ A then (1 : ℝ) else 0) ∂μ := by
  let i : Ω → ℝ := fun ω => if Y ω ∈ A then 1 else 0
  let j : Ω → ℝ := fun ω => if Y ω ∈ A ∧ R ω ∈ ({1} : Set ℝ) then 1 else 0
  let w : Ω → ℝ := fun ω => (p (X ω))⁻¹
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  have hwm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] w :=
    ((hp.1.comp hXm).inv).stronglyMeasurable
  have hjm : Measurable j :=
    Measurable.ite ((hA.preimage hY).inter ((measurableSet_singleton 1).preimage hR))
      measurable_const measurable_const
  have hji : Integrable j μ := by
    apply Integrable.of_bound hjm.aestronglyMeasurable 1
    exact ae_of_all _ (fun ω => by dsimp [j]; split_ifs <;> norm_num)
  have hwbound : ∀ ω, ‖w ω‖ ≤ 1 / ε := by
    intro ω
    change ‖(p (X ω))⁻¹‖ ≤ 1 / ε
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hε.trans (hpos ω)), ← one_div]
    exact div_le_div₀ (by norm_num) le_rfl hε (hpos ω).le
  have hwji : Integrable (w * j) μ :=
    hji.bdd_mul ((hp.1.comp hX).inv.aestronglyMeasurable) (ae_of_all _ hwbound)
  have hrind : (fun ω => if R ω ∈ ({1} : Set ℝ) then (1 : ℝ) else 0) = R := by
    funext ω
    rcases hbinary ω with hr | hr <;> simp [hr]
  have hci : μ[j | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω => (μ[i | MeasurableSpace.comap X inferInstance]) ω * p (X ω) := by
    have hc : μ[j | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
        fun ω => (μ[i | MeasurableSpace.comap X inferInstance]) ω *
          (μ[(fun ω => if R ω ∈ ({1} : Set ℝ) then (1 : ℝ) else 0) |
            MeasurableSpace.comap X inferInstance]) ω := by
      convert hmar A {1} hA (measurableSet_singleton 1) using 1 <;> congr!
    rw [hrind] at hc
    filter_upwards [hc, isCEF_condExp μ X hX R p hp] with ω hcω hpω
    change (μ[j | MeasurableSpace.comap X inferInstance]) ω = _ at hcω
    change p (X ω) = (μ[R | MeasurableSpace.comap X inferInstance]) ω at hpω
    simpa only [← hpω] using hcω
  have hweighted : μ[w * j | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      μ[i | MeasurableSpace.comap X inferInstance] := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hwm hwji hji, hci]
      with ω hwω hcω
    rw [hwω, Pi.mul_apply, hcω]
    dsimp [w]
    field_simp [(hε.trans (hpos ω)).ne']
  have hint : (∫ ω, (w * j) ω ∂μ) = ∫ ω, i ω ∂μ := by
    rw [← integral_condExp hX.comap_le (f := w * j),
      ← integral_condExp hX.comap_le (f := i)]
    exact integral_congr_ae hweighted
  calc
    (∫ ω, (if Y ω ∈ A then R ω / p (X ω) else 0) ∂μ) =
        ∫ ω, (w * j) ω ∂μ := by
      apply integral_congr_ae
      apply ae_of_all
      intro ω
      rcases hbinary ω with hr | hr <;>
        by_cases ha : Y ω ∈ A <;> simp [w, j, ha, hr, div_eq_mul_inv]
    _ = ∫ ω, (if Y ω ∈ A then (1 : ℝ) else 0) ∂μ := hint

/-- The inverse-response weighted law of the outcome is its population law.
Measure uniqueness supplies the extension from indicators to all integrable outcomes. -/
theorem mar_reweighting_map_eq {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R)
    (hbinary : ∀ ω, R ω = 0 ∨ R ω = 1) (p : E → ℝ) (hp : IsCEF μ X R p)
    (ε : ℝ) (hε : 0 < ε) (hpos : ∀ ω, ε < p (X ω)) (hmar : CI μ X hX Y R) :
    Measure.map Y (μ.withDensity (fun ω => ENNReal.ofReal (R ω / p (X ω)))) =
      Measure.map Y μ := by
  let W : Ω → ℝ := fun ω => R ω / p (X ω)
  have hWm : Measurable W := hR.div (hp.1.comp hX)
  have hWnonneg : ∀ ω, 0 ≤ W ω := by
    intro ω
    apply div_nonneg _ (hε.trans (hpos ω)).le
    rcases hbinary ω with hr | hr <;> simp [hr]
  have hWi : Integrable W μ := by
    apply Integrable.of_bound hWm.aestronglyMeasurable (1 / ε)
    apply ae_of_all
    intro ω
    dsimp [W]
    rcases hbinary ω with hr | hr
    · simp only [hr, zero_div, abs_zero]
      exact div_nonneg zero_le_one hε.le
    · rw [hr, abs_of_pos (div_pos zero_lt_one (hε.trans (hpos ω)))]
      exact div_le_div₀ (by norm_num) le_rfl hε (hpos ω).le
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hY hA, Measure.map_apply hY hA,
    withDensity_apply _ (hA.preimage hY)]
  change (∫⁻ ω in Y ⁻¹' A, ENNReal.ofReal (W ω) ∂μ) = μ (Y ⁻¹' A)
  rw [← ofReal_integral_eq_lintegral_ofReal hWi.integrableOn (ae_of_all _ hWnonneg)]
  have hevent := mar_reweighting_indicator_eq μ X hX Y R hY hR hbinary p hp
    ε hε hpos hmar A hA
  have hset : (∫ ω in Y ⁻¹' A, W ω ∂μ) = (μ (Y ⁻¹' A)).toReal := by
    rw [← integral_indicator (hA.preimage hY)]
    change (∫ ω, (if Y ω ∈ A then R ω / p (X ω) else 0) ∂μ) = _
    rw [hevent]
    convert (integral_indicator_one (μ := μ) (hA.preimage hY)) using 1 <;> congr!
  rw [hset, ENNReal.ofReal_toReal (measure_ne_top μ _)]

theorem mar_reweighting_corrected_hypothesis_proof {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (hYi : Integrable Y μ)
   (hbinary : ∀ ω,R ω=0 ∨ R ω=1) (p : E → ℝ) (hp : IsCEF μ X R p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω)) (hmar : CI μ X hX Y R) :
   mean μ Y=mean μ (fun ω => censored (Y ω) (R ω)*R ω/p (X ω)) := by
  obtain ⟨ε, hε, hpos⟩ := hpos
  have hlaw := mar_reweighting_map_eq μ X hX Y R hY hR hbinary p hp ε hε hpos hmar
  have hYi_map : Integrable (fun y : ℝ => y) (Measure.map Y μ) :=
    (integrable_map_measure stronglyMeasurable_id.aestronglyMeasurable hY.aemeasurable).2 hYi
  have hWnonneg : ∀ ω, 0 ≤ R ω / p (X ω) := by
    intro ω
    apply div_nonneg _ (hε.trans (hpos ω)).le
    rcases hbinary ω with hr | hr <;> simp [hr]
  change (∫ ω, Y ω ∂μ) = ∫ ω, censored (Y ω) (R ω) * R ω / p (X ω) ∂μ
  calc
    (∫ ω, Y ω ∂μ) = ∫ y : ℝ, y ∂Measure.map Y μ :=
      (integral_map hY.aemeasurable hYi_map.aestronglyMeasurable).symm
    _ = ∫ y : ℝ, y ∂Measure.map Y
        (μ.withDensity (fun ω => ENNReal.ofReal (R ω / p (X ω)))) := by rw [hlaw]
    _ = ∫ ω, Y ω ∂μ.withDensity (fun ω => ENNReal.ofReal (R ω / p (X ω))) :=
      integral_map_of_stronglyMeasurable hY stronglyMeasurable_id
    _ = ∫ ω, (R ω / p (X ω)) * Y ω ∂μ := by
      have hdensity : Measurable (fun ω => ENNReal.ofReal (R ω / p (X ω))) :=
        (hR.div (hp.1.comp hX)).ennreal_ofReal
      simpa only [ENNReal.toReal_ofReal (hWnonneg _), smul_eq_mul] using
        (integral_withDensity_eq_integral_toReal_smul (μ := μ) hdensity
          (ae_of_all _ (fun ω => ENNReal.ofReal_lt_top)) Y)
    _ = ∫ ω, censored (Y ω) (R ω) * R ω / p (X ω) ∂μ := by
      apply integral_congr_ae
      apply ae_of_all
      intro ω
      rcases hbinary ω with hr | hr <;> simp [censored, hr, div_eq_mul_inv, mul_comm]

end

end AronowAudit.P001.Wave1
