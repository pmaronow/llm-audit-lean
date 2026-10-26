import AronowAudit.P001.Wave1.Gap.DecisionT47
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
P001-T100 assumes only integrability of the treatment effect and a.e. binary treatment.
P001-T47 assumes transformations that are a.e. measurable under the marginal laws.
-/

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Matrix
noncomputable section
local instance DecideA_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-! P001-T100: equality of weighted outcome laws, on arbitrary Ω. -/

private lemma DecideA_propensity_bounds {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (D : Ω → ℝ) (hbinary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsCEF μ X D p) :
    ∀ᵐ ω ∂μ, 0 ≤ p (X ω) ∧ p (X ω) ≤ 1 := by
  have hD0 : ∀ᵐ ω ∂μ, 0 ≤ D ω := by
    filter_upwards [hbinary] with ω hb
    rcases hb with h | h <;> simp [h]
  have hD1 : ∀ᵐ ω ∂μ, D ω ≤ 1 := by
    filter_upwards [hbinary] with ω hb
    rcases hb with h | h <;> simp [h]
  have hpCE : (p ∘ X) =ᵐ[μ] μ[D | (MeasurableSpace.comap X inferInstance)] := isCEF_condExp μ X hX D p hp
  have hCE0 : ∀ᵐ ω ∂μ, 0 ≤ μ[D | (MeasurableSpace.comap X inferInstance)] ω := condExp_nonneg hD0
  have hCE1 : ∀ᵐ ω ∂μ, μ[D | (MeasurableSpace.comap X inferInstance)] ω ≤ 1 :=
    condExp_le_nonneg_const (by norm_num : (0 : ℝ) ≤ 1) hD1
  filter_upwards [hpCE, hCE0, hCE1] with ω hpω h0ω h1ω
  change p (X ω) = _ at hpω
  rw [hpω]
  exact ⟨h0ω, h1ω⟩

private lemma DecideA_weighted_apply {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w : Ω → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) (S : Set Ω) (hS : MeasurableSet S) :
    (μ.withDensity (fun ω => ENNReal.ofReal (w ω))) S =
      ENNReal.ofReal (∫ ω in S, w ω ∂μ) := by
  rw [withDensity_apply _ hS]
  exact (ofReal_integral_eq_lintegral_ofReal hw.integrableOn
    (ae_restrict_of_ae hw0)).symm

/-- Transport a real integral through a weighted pushforward. The theorem applies
to all measurable real test functions, and so avoids an L2 restriction. -/
private lemma DecideA_weighted_map_integral {Ω F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace F]
    (μ : Measure Ω) (w : Ω → ℝ) (hw : Measurable w)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) (U : Ω → F) (hU : Measurable U)
    (v : F → ℝ) (hv : Measurable v) :
    (∫ z, v z ∂(μ.withDensity (fun ω => ENNReal.ofReal (w ω))).map U) =
      ∫ ω, w ω * v (U ω) ∂μ := by
  rw [integral_map_of_stronglyMeasurable hU hv.stronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    hw.ennreal_ofReal (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hw0] with ω hω
  simp only [ENNReal.toReal_ofReal hω, smul_eq_mul]

/-- The event-factorization definition of CI gives equality of the two
nonnegative measures on outcome space weighted by D and by p(X). -/
private lemma DecideA_binary_weighted_law {Ω E F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (U : Ω → F) (hU : Measurable U) (D : Ω → ℝ)
    (hbinary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsCEF μ X D p) (hCI : CI μ X hX U D) :
    (μ.withDensity (fun ω => ENNReal.ofReal (D ω))).map U =
      (μ.withDensity (fun ω => ENNReal.ofReal (p (X ω)))).map U := by
  have hG : (MeasurableSpace.comap X inferInstance) ≤ (inferInstance : MeasurableSpace Ω) := hX.comap_le
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := measurable_iff_comap_le.mpr le_rfl
  have hpm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] (p ∘ X) := (hp.1.comp hXm).stronglyMeasurable
  have hpCE : (p ∘ X) =ᵐ[μ] μ[D | (MeasurableSpace.comap X inferInstance)] := isCEF_condExp μ X hX D p hp
  have hD0 : ∀ᵐ ω ∂μ, 0 ≤ D ω := by
    filter_upwards [hbinary] with ω hb
    rcases hb with h | h <;> simp [h]
  have hp0 : ∀ᵐ ω ∂μ, 0 ≤ p (X ω) :=
    (DecideA_propensity_bounds μ X hX D hbinary p hp).mono (fun _ h => h.1)
  apply Measure.ext
  intro A hA
  have hUA : MeasurableSet (U ⁻¹' A) := hU hA
  let u : Ω → ℝ := (U ⁻¹' A).indicator (fun _ => 1)
  have hum : Measurable u := measurable_const.indicator hUA
  have hui : Integrable u μ := (integrable_const (1 : ℝ)).indicator hUA
  have hub : ∀ᵐ ω ∂μ, ‖u ω‖ ≤ 1 := by
    filter_upwards with ω
    by_cases h : U ω ∈ A <;> simp [u, h]
  have hud : Integrable (fun ω => u ω * D ω) μ :=
    hp.2.1.bdd_mul hum.aestronglyMeasurable hub
  have hpu : Integrable (fun ω => p (X ω) * u ω) μ :=
    hp.2.2.1.mul_bdd hum.aestronglyMeasurable hub
  have hfactor : μ[(fun ω => u ω * D ω) | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ]
      (fun ω => μ[u | (MeasurableSpace.comap X inferInstance)] ω * μ[D | (MeasurableSpace.comap X inferInstance)] ω) := by
    have hprod : (fun ω => u ω * D ω) =ᵐ[μ]
        (fun ω => if U ω ∈ A ∧ D ω ∈ ({1} : Set ℝ) then (1 : ℝ) else 0) := by
      filter_upwards [hbinary] with ω hb
      by_cases hAω : U ω ∈ A <;>
        rcases hb with h | h <;> simp [u, hAω, h]
    have hDindicator : (fun ω => if D ω ∈ ({1} : Set ℝ) then (1 : ℝ) else 0) =ᵐ[μ] D := by
      filter_upwards [hbinary] with ω hb
      rcases hb with h | h <;> simp [h]
    have hu : (fun ω => if U ω ∈ A then (1 : ℝ) else 0) = u := by
      funext ω
      by_cases hω : U ω ∈ A <;> simp [u, hω]
    calc
      _ =ᵐ[μ] μ[(fun ω => if U ω ∈ A ∧ D ω ∈ ({1} : Set ℝ) then (1 : ℝ) else 0) |
          (MeasurableSpace.comap X inferInstance)] := condExp_congr_ae hprod
      _ =ᵐ[μ] (fun ω => μ[u | (MeasurableSpace.comap X inferInstance)] ω *
          μ[(fun ω => if D ω ∈ ({1} : Set ℝ) then (1 : ℝ) else 0) |
            (MeasurableSpace.comap X inferInstance)] ω) := by
        have hc := hCI A ({1} : Set ℝ) hA (measurableSet_singleton 1)
        rw [hu] at hc
        exact hc
      _ =ᵐ[μ] _ := by
        filter_upwards [condExp_congr_ae hDindicator] with ω hω
        rw [hω]
  have hpull : μ[(fun ω => p (X ω) * u ω) | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ]
      (fun ω => p (X ω) * μ[u | (MeasurableSpace.comap X inferInstance)] ω) :=
    condExp_mul_of_stronglyMeasurable_left hpm hpu hui
  have hCEeq : μ[(fun ω => u ω * D ω) | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ]
      μ[(fun ω => p (X ω) * u ω) | (MeasurableSpace.comap X inferInstance)] := by
    filter_upwards [hfactor, hpCE, hpull] with ω hfω hpω huω
    change p (X ω) = _ at hpω
    rw [hfω, huω, ← hpω, mul_comm]
  have hint : (∫ ω, u ω * D ω ∂μ) = ∫ ω, p (X ω) * u ω ∂μ := by
    calc
      _ = ∫ ω, μ[(fun ω => u ω * D ω) | (MeasurableSpace.comap X inferInstance)] ω ∂μ := (integral_condExp hG).symm
      _ = ∫ ω, μ[(fun ω => p (X ω) * u ω) | (MeasurableSpace.comap X inferInstance)] ω ∂μ := integral_congr_ae hCEeq
      _ = _ := integral_condExp hG
  have hset : (∫ ω in U ⁻¹' A, D ω ∂μ) = ∫ ω in U ⁻¹' A, p (X ω) ∂μ := by
    calc
      _ = ∫ ω, u ω * D ω ∂μ := by
        rw [← integral_indicator hUA]
        apply integral_congr_ae
        filter_upwards with ω
        by_cases h : U ω ∈ A <;> simp [u, h]
      _ = ∫ ω, p (X ω) * u ω ∂μ := hint
      _ = _ := by
        rw [← integral_indicator hUA]
        apply integral_congr_ae
        filter_upwards with ω
        by_cases h : U ω ∈ A <;> simp [u, h]
  rw [Measure.map_apply hU hA, Measure.map_apply hU hA,
    DecideA_weighted_apply μ D hp.2.1 hD0 _ hUA,
    DecideA_weighted_apply μ (fun ω => p (X ω)) hp.2.2.1 hp0 _ hUA, hset]

theorem att_normalized_propensity_mean_integrable_effect {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
   (hiτ : Integrable (fun ω => Y1 ω-Y0 ω) μ)
   (hbinary : ∀ᵐ ω ∂μ,D ω=0 ∨ D ω=1)
   (hpD : 0 < prob μ {ω | D ω=1} ∧ prob μ {ω | D ω=1} < 1) (p : E → ℝ) (hp : IsCEF μ X D p)
   (hCI : CI μ X hX (fun ω => (Y0 ω,Y1 ω)) D) :
   mean μ (p ∘ X)=prob μ {ω | D ω=1} ∧
   mean μ (fun ω => p (X ω)*(Y1 ω-Y0 ω))=mean μ (fun ω => D ω*(Y1 ω-Y0 ω)) ∧
   (∫ ω in {ω | D ω=1},Y1 ω-Y0 ω ∂μ)/prob μ {ω | D ω=1} =
     mean μ (fun ω => p (X ω)*(Y1 ω-Y0 ω))/mean μ (p ∘ X) := by
  let U : Ω → ℝ × ℝ := fun ω => (Y0 ω, Y1 ω)
  have hU : Measurable U := h0.prodMk h1
  let v : ℝ × ℝ → ℝ := fun z => z.2 - z.1
  have hv : Measurable v := measurable_snd.sub measurable_fst
  have hbounds := DecideA_propensity_bounds μ X hX D hbinary p hp
  have hp0 : ∀ᵐ ω ∂μ, 0 ≤ p (X ω) := hbounds.mono (fun _ h => h.1)
  have hD0 : ∀ᵐ ω ∂μ, 0 ≤ D ω := by
    filter_upwards [hbinary] with ω hb
    rcases hb with h | h <;> simp [h]
  -- These integrability facts also verify that the displayed means are actual L1 means.
  have hpτ : Integrable (fun ω => p (X ω) * (Y1 ω - Y0 ω)) μ := by
    apply hiτ.bdd_mul (c := 1) (hp.1.comp hX).aestronglyMeasurable
    filter_upwards [hbounds] with ω hω
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2
  have hDτ : Integrable (fun ω => D ω * (Y1 ω - Y0 ω)) μ := by
    apply hiτ.bdd_mul (c := 1) hD.aestronglyMeasurable
    filter_upwards [hbinary] with ω hb
    rcases hb with h | h <;> simp [h]
  have hlaw := DecideA_binary_weighted_law μ X hX U hU D hbinary p hp hCI
  have hweighted : mean μ (fun ω => p (X ω) * (Y1 ω - Y0 ω)) =
      mean μ (fun ω => D ω * (Y1 ω - Y0 ω)) := by
    unfold mean
    calc
      _ = ∫ z, v z ∂(μ.withDensity (fun ω => ENNReal.ofReal (p (X ω)))).map U :=
        (DecideA_weighted_map_integral μ (p ∘ X) (hp.1.comp hX) hp0 U hU v hv).symm
      _ = ∫ z, v z ∂(μ.withDensity (fun ω => ENNReal.ofReal (D ω))).map U := by rw [hlaw]
      _ = _ := DecideA_weighted_map_integral μ D hD hD0 U hU v hv
  have hS : MeasurableSet {ω | D ω = 1} := hD (measurableSet_singleton 1)
  have hDindicator : D =ᵐ[μ] {ω | D ω = 1}.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hbinary] with ω hb
    rcases hb with h | h <;> simp [Set.indicator, h]
  have hmeanD : mean μ D = prob μ {ω | D ω = 1} := by
    calc
      _ = ∫ ω, {ω | D ω = 1}.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_congr_ae hDindicator
      _ = _ := by
        rw [integral_indicator_const (1 : ℝ) hS]
        simp only [smul_eq_mul, mul_one, prob, Measure.real]
  have hden : mean μ (p ∘ X) = prob μ {ω | D ω = 1} := by
    have hcef : mean μ D = mean μ (p ∘ X) := by
      simpa only [mean, Set.preimage_univ, setIntegral_univ, Function.comp_apply] using
        hp.2.2.2 Set.univ MeasurableSet.univ
    exact hcef.symm.trans hmeanD
  have hnumerator : (∫ ω in {ω | D ω = 1}, Y1 ω - Y0 ω ∂μ) =
      mean μ (fun ω => D ω * (Y1 ω - Y0 ω)) := by
    rw [← integral_indicator hS]
    unfold mean
    apply integral_congr_ae
    filter_upwards [hbinary] with ω hb
    rcases hb with h | h <;> simp [Set.indicator, h]
  have hden_pos : 0 < mean μ (p ∘ X) := by rw [hden]; exact hpD.1
  refine ⟨hden, hweighted, ?_⟩
  apply (div_eq_div_iff (ne_of_gt hpD.1) (ne_of_gt hden_pos)).2
  rw [hnumerator, ← hweighted, hden]

/-- The six-conjunct statement follows by projecting the law-a.e. version,
which also supplies two coefficient formulas. -/
theorem independent_functions_cef_law_scope {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
  (hX : Measurable X) (hY : Measurable Y) (hi : IndepFun X Y μ)
  (hX2 : MemLp X 2 μ) (hY2 : MemLp Y 2 μ)
  (g h : ℝ → ℝ) (hg : AEMeasurable g (μ.map X)) (hh : AEMeasurable h (μ.map Y))
  (hgX : Measurable (g ∘ X)) (hhY : Measurable (h ∘ Y))
  (hg2 : MemLp (g ∘ X) 2 μ) (hh2 : MemLp (h ∘ Y) 2 μ) :
  IsCEF μ X Y (fun _ => mean μ Y) ∧
  IsCEF μ X (fun ω => (Y ω-mean μ Y)^2) (fun _ => var μ Y) ∧
  (∀ a b : ℝ, linearRisk μ X Y (mean μ Y) 0 ≤ linearRisk μ X Y a b) ∧
  IndepFun (g ∘ X) (h ∘ Y) μ ∧
  IsCEF μ (g ∘ X) (h ∘ Y) (fun _ => mean μ (h ∘ Y)) ∧
  ∀ a b : ℝ, linearRisk μ (g ∘ X) (h ∘ Y) (mean μ (h ∘ Y)) 0 ≤
    linearRisk μ (g ∘ X) (h ∘ Y) a b := by
  have hAll := independent_functions_cef_law_measurable μ X Y hX hY hi hX2 hY2
    g h hgX hhY hg hh hg2 hh2
  exact ⟨hAll.1, hAll.2.1, hAll.2.2.1, hAll.2.2.2.2.1,
    hAll.2.2.2.2.2.1, hAll.2.2.2.2.2.2.1⟩

end
end AronowAudit.P001.Wave1
