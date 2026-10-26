import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance GP0014B2b_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-! The event-to-L¹ extension below follows from equality of
weighted pushforward measures, rather than a simple-function limit. -/

/-- Equality on every outcome event identifies the weighted outcome laws.
Integrating the identity function then extends the equality to the outcome itself.
This lemma uses no moment of order greater than one. -/
private theorem GP0014B2b_mar_weighted_integral_from_events {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U f g : Ω → ℝ) (hU : Measurable U)
    (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ ω, 0 ≤ f ω) (hgn : ∀ ω, 0 ≤ g ω)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (he : ∀ A : Set ℝ, MeasurableSet A →
      (∫ ω in U ⁻¹' A, f ω ∂μ) = ∫ ω in U ⁻¹' A, g ω ∂μ) :
    (∫ ω, f ω * U ω ∂μ) = ∫ ω, g ω * U ω ∂μ := by
  let νf : Measure Ω := μ.withDensity (fun ω => ENNReal.ofReal (f ω))
  let νg : Measure Ω := μ.withDensity (fun ω => ENNReal.ofReal (g ω))
  have hlaw : νf.map U = νg.map U := by
    ext A hA
    rw [Measure.map_apply hU hA, Measure.map_apply hU hA]
    change (μ.withDensity (fun ω => ENNReal.ofReal (f ω))) (U ⁻¹' A) =
      (μ.withDensity (fun ω => ENNReal.ofReal (g ω))) (U ⁻¹' A)
    rw [withDensity_apply _ (hU hA), withDensity_apply _ (hU hA)]
    rw [← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
      (ae_of_all _ hfn), ← ofReal_integral_eq_lintegral_ofReal hgi.integrableOn
      (ae_of_all _ hgn), he A hA]
  have hfr (ω : Ω) : (ENNReal.ofReal (f ω)).toReal = f ω :=
    ENNReal.toReal_ofReal (hfn ω)
  have hgr (ω : Ω) : (ENNReal.ofReal (g ω)).toReal = g ω :=
    ENNReal.toReal_ofReal (hgn ω)
  have hif : (∫ ω, U ω ∂νf) = ∫ ω, f ω * U ω ∂μ := by
    simpa only [νf, hfr, smul_eq_mul] using
      (integral_withDensity_eq_integral_toReal_smul (μ := μ) hf.ennreal_ofReal
        (ae_of_all _ (fun ω => ENNReal.ofReal_lt_top)) U)
  have hig : (∫ ω, U ω ∂νg) = ∫ ω, g ω * U ω ∂μ := by
    simpa only [νg, hgr, smul_eq_mul] using
      (integral_withDensity_eq_integral_toReal_smul (μ := μ) hg.ennreal_ofReal
        (ae_of_all _ (fun ω => ENNReal.ofReal_lt_top)) U)
  calc
    (∫ ω, f ω * U ω ∂μ) = ∫ ω, U ω ∂νf := hif.symm
    _ = ∫ y : ℝ, y ∂νf.map U :=
      (integral_map_of_stronglyMeasurable hU stronglyMeasurable_id).symm
    _ = ∫ y : ℝ, y ∂νg.map U := by rw [hlaw]
    _ = ∫ ω, U ω ∂νg :=
      integral_map_of_stronglyMeasurable hU stronglyMeasurable_id
    _ = ∫ ω, g ω * U ω ∂μ := hig

private theorem GP0014B2b_mar_binary_bounds {Ω : Type*} (R : Ω → ℝ)
    (hbinary : ∀ ω, R ω = 0 ∨ R ω = 1) :
    (∀ ω, 0 ≤ R ω) ∧ (∀ ω, ‖R ω‖ ≤ 1) := by
  constructor <;> intro ω <;> rcases hbinary ω with h | h <;> simp [h]

/-- Restriction to respondents is multiplication by the binary response. -/
private theorem GP0014B2b_mar_response_integral {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (R f : Ω → ℝ) (hR : Measurable R)
    (hbinary : ∀ ω, R ω = 0 ∨ R ω = 1)
    (C : Set E) (hC : MeasurableSet C) :
    (∫ ω in X ⁻¹' C, f ω * R ω ∂μ) =
      ∫ ω in X ⁻¹' C, f ω ∂μ.restrict {ω | R ω = 1} := by
  have hB : MeasurableSet {ω | R ω = 1} := hR (measurableSet_singleton 1)
  have hi : (fun ω => f ω * R ω) = {ω | R ω = 1}.indicator f := by
    funext ω
    rcases hbinary ω with h | h <;> simp [Set.indicator, h]
  rw [hi, integral_indicator hB, Measure.restrict_restrict hB,
    Measure.restrict_restrict (hX hC)]
  rw [Set.inter_comm]

/-- MAR for indicators implies the weighted integral identity on each covariate
cell. The final extension uses weighted measures, so it does not require L². -/
private theorem GP0014B2b_mar_ci_weighted_setIntegral {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R)
    (hbinary : ∀ ω, R ω = 0 ∨ R ω = 1) (p : E → ℝ)
    (hp : IsCEF μ X R p) (hpn : ∀ ω, 0 ≤ p (X ω))
    (hmar : CI μ X hX Y R) (C : Set E) (hC : MeasurableSet C) :
    (∫ ω in X ⁻¹' C, R ω * Y ω ∂μ) =
      ∫ ω in X ⁻¹' C, p (X ω) * Y ω ∂μ := by
  let P : Ω → ℝ := p ∘ X
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := measurable_iff_comap_le.mpr le_rfl
  have hPm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] P := (hp.1.comp hXm).stronglyMeasurable
  have hpce : P =ᵐ[μ] μ[R | (MeasurableSpace.comap X inferInstance)] := isCEF_condExp μ X hX R p hp
  have hRn : ∀ ω, 0 ≤ R ω := (GP0014B2b_mar_binary_bounds R hbinary).1
  have hRb : ∀ ω, ‖R ω‖ ≤ 1 := (GP0014B2b_mar_binary_bounds R hbinary).2
  apply GP0014B2b_mar_weighted_integral_from_events (μ.restrict (X ⁻¹' C)) Y R P hY hR
    (hp.1.comp hX) hRn hpn hp.2.1.integrableOn hp.2.2.1.integrableOn
  intro A hA
  let I : Ω → ℝ := fun ω => if Y ω ∈ A then 1 else 0
  have hIm : Measurable I := Measurable.ite (hY hA) measurable_const measurable_const
  have hIb : ∀ ω, ‖I ω‖ ≤ 1 := by
    intro ω
    by_cases h : Y ω ∈ A <;> simp [I, h]
  have hIi : Integrable I μ := Integrable.of_bound hIm.aestronglyMeasurable 1
    (ae_of_all _ hIb)
  have hIRi : Integrable (I * R) μ :=
    hIi.mul_bdd hR.aestronglyMeasurable (ae_of_all _ hRb)
  have hPIi : Integrable (P * I) μ :=
    hp.2.2.1.mul_bdd hIm.aestronglyMeasurable (ae_of_all _ hIb)
  have hci : μ[I * R | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      (fun ω => (μ[I | MeasurableSpace.comap X inferInstance]) ω *
        (μ[R | MeasurableSpace.comap X inferInstance]) ω) := by
    convert hmar A {1} hA (measurableSet_singleton 1) using 1 <;> congr 1
    · funext ω
      rcases hbinary ω with h | h <;> by_cases hAω : Y ω ∈ A <;>
        simp [I, Pi.mul_apply, h, hAω]
    · funext ω
      congr 2
      funext ω
      rcases hbinary ω with h | h <;> simp [h]
  have hpull : μ[P * I | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] P * μ[I | (MeasurableSpace.comap X inferInstance)] :=
    condExp_mul_of_stronglyMeasurable_left hPm hPIi hIi
  have hce : μ[I * R | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] μ[P * I | (MeasurableSpace.comap X inferInstance)] := by
    filter_upwards [hci, hpce, hpull] with ω hciω hpω hpoω
    change _ = P ω * (μ[I | (MeasurableSpace.comap X inferInstance)]) ω at hpoω
    rw [hciω, ← hpω, hpoω]
    exact mul_comm _ _
  have hS : MeasurableSet[(MeasurableSpace.comap X inferInstance)] (X ⁻¹' C) := ⟨C, hC, rfl⟩
  have heq : (∫ ω in X ⁻¹' C, I ω * R ω ∂μ) =
      ∫ ω in X ⁻¹' C, P ω * I ω ∂μ := by
    calc
      _ = ∫ ω in X ⁻¹' C, (μ[I * R | (MeasurableSpace.comap X inferInstance)]) ω ∂μ :=
        (setIntegral_condExp hX.comap_le hIRi hS).symm
      _ = ∫ ω in X ⁻¹' C, (μ[P * I | (MeasurableSpace.comap X inferInstance)]) ω ∂μ :=
        setIntegral_congr_ae (hX hC) (hce.mono (fun ω h _ => h))
      _ = _ := setIntegral_condExp hX.comap_le hPIi hS
  calc
    (∫ ω in Y ⁻¹' A, R ω ∂μ.restrict (X ⁻¹' C)) =
        ∫ ω in X ⁻¹' C, I ω * R ω ∂μ := by
      rw [← integral_indicator (hY hA)]
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => by
        by_cases h : Y ω ∈ A <;> simp [I, Set.indicator, h])
    _ = ∫ ω in X ⁻¹' C, P ω * I ω ∂μ := heq
    _ = ∫ ω in Y ⁻¹' A, P ω ∂μ.restrict (X ⁻¹' C) := by
      rw [← integral_indicator (hY hA)]
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => by
        by_cases h : Y ω ∈ A <;> simp [I, Set.indicator, h])

/-- Under MAR, a respondent CEF is a population CEF. -/
theorem mar_respondent_cef_is_population_cef_proof {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (hYi : Integrable Y μ)
   (hbinary : ∀ ω,R ω=0 ∨ R ω=1) (p m : E → ℝ) (hp : IsCEF μ X R p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω)) (hmar : CI μ X hX Y R)
   (hm : IsCEF (μ.restrict {ω | R ω=1}) X (fun ω => censored (Y ω) (R ω)) m)
   (hmi : Integrable (m ∘ X) μ) : IsCEF μ X Y m := by
  let P : Ω → ℝ := p ∘ X
  let a : Ω → ℝ := m ∘ X
  let H : Ω → ℝ := μ[Y | (MeasurableSpace.comap X inferInstance)]
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := measurable_iff_comap_le.mpr le_rfl
  have hPm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] P := (hp.1.comp hXm).stronglyMeasurable
  have ham : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] a := (hm.1.comp hXm).stronglyMeasurable
  have hpce : P =ᵐ[μ] μ[R | (MeasurableSpace.comap X inferInstance)] := isCEF_condExp μ X hX R p hp
  obtain ⟨ε, hε, hposε⟩ := hpos
  have hPpos : ∀ ω, 0 < P ω := fun ω => lt_trans hε (hposε ω)
  have hPnonneg : ∀ ω, 0 ≤ P ω := fun ω => (hPpos ω).le
  have hRbound : ∀ ω, ‖R ω‖ ≤ 1 := (GP0014B2b_mar_binary_bounds R hbinary).2
  have hRle : ∀ ω, R ω ≤ 1 := by
    intro ω
    rcases hbinary ω with h | h <;> simp [h]
  have hPle : ∀ᵐ ω ∂μ, P ω ≤ 1 := by
    have hb := condExp_le_nonneg_const (μ := μ) (m := (MeasurableSpace.comap X inferInstance))
      (show (0 : ℝ) ≤ 1 by norm_num) (ae_of_all _ hRle)
    filter_upwards [hpce, hb] with ω hpω hbω
    rw [hpω]
    exact hbω
  have hPbound : ∀ᵐ ω ∂μ, ‖P ω‖ ≤ 1 := by
    filter_upwards [hPle] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hPnonneg ω)] using hω
  have hYRint : Integrable (fun ω => Y ω * R ω) μ :=
    hYi.mul_bdd hR.aestronglyMeasurable (ae_of_all _ hRbound)
  have hPYint : Integrable (P * Y) μ :=
    hYi.bdd_mul (hp.1.comp hX).aestronglyMeasurable hPbound
  have haRint : Integrable (a * R) μ :=
    hmi.mul_bdd hR.aestronglyMeasurable (ae_of_all _ hRbound)
  have hPHint : Integrable (P * H) μ :=
    (integrable_condExp (μ := μ) (m := (MeasurableSpace.comap X inferInstance)) (f := Y)).bdd_mul
      (hp.1.comp hX).aestronglyMeasurable hPbound
  have haPint : Integrable (a * P) μ :=
    hmi.mul_bdd (hp.1.comp hX).aestronglyMeasurable hPbound
  have hB : MeasurableSet {ω | R ω = 1} := hR (measurableSet_singleton 1)
  have hcY : (fun ω => censored (Y ω) (R ω)) =ᵐ[μ.restrict {ω | R ω = 1}] Y := by
    apply (ae_restrict_iff' hB).2
    exact ae_of_all _ (fun ω hω => by
      have hRω : R ω = 1 := hω
      simp [censored, hRω])
  have hresp (C : Set E) (hC : MeasurableSet C) :
      (∫ ω in X ⁻¹' C, Y ω * R ω ∂μ) =
        ∫ ω in X ⁻¹' C, a ω * R ω ∂μ := by
    rw [GP0014B2b_mar_response_integral μ X hX R Y hR hbinary C hC,
      GP0014B2b_mar_response_integral μ X hX R a hR hbinary C hC]
    calc
      _ = ∫ ω in X ⁻¹' C, censored (Y ω) (R ω)
          ∂μ.restrict {ω | R ω = 1} :=
        integral_congr_ae (ae_restrict_of_ae hcY.symm)
      _ = _ := hm.2.2.2 C hC
  have hpullY : μ[P * Y | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] P * H :=
    condExp_mul_of_stronglyMeasurable_left hPm hPYint hYi
  have hpulla : μ[a * R | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] a * μ[R | (MeasurableSpace.comap X inferInstance)] :=
    condExp_mul_of_stronglyMeasurable_left ham haRint hp.2.1
  have hleft : P * H =ᵐ[μ] μ[(fun ω => Y ω * R ω) | (MeasurableSpace.comap X inferInstance)] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hYRint
      (fun s hs hfin => hPHint.integrableOn) ?_
      (hPm.mul (stronglyMeasurable_condExp (μ := μ) (m := (MeasurableSpace.comap X inferInstance)) (f := Y))).aestronglyMeasurable
    intro s hs hfin
    rcases hs with ⟨C, hC, rfl⟩
    calc
      _ = ∫ ω in X ⁻¹' C, (μ[P * Y | (MeasurableSpace.comap X inferInstance)]) ω ∂μ :=
        setIntegral_congr_ae (hX hC) (hpullY.symm.mono (fun ω h _ => h))
      _ = ∫ ω in X ⁻¹' C, P ω * Y ω ∂μ :=
        setIntegral_condExp hX.comap_le hPYint ⟨C, hC, rfl⟩
      _ = ∫ ω in X ⁻¹' C, R ω * Y ω ∂μ :=
        (GP0014B2b_mar_ci_weighted_setIntegral μ X hX Y R hY hR hbinary p hp hPnonneg hmar C hC).symm
      _ = _ := by simp only [mul_comm]
  have hright : a * P =ᵐ[μ] μ[(fun ω => Y ω * R ω) | (MeasurableSpace.comap X inferInstance)] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hYRint
      (fun s hs hfin => haPint.integrableOn) ?_ (ham.mul hPm).aestronglyMeasurable
    intro s hs hfin
    rcases hs with ⟨C, hC, rfl⟩
    have hce : a * P =ᵐ[μ] μ[a * R | (MeasurableSpace.comap X inferInstance)] := by
      filter_upwards [hpce, hpulla] with ω hpω haω
      change a ω * P ω = _
      simpa only [Pi.mul_apply, ← hpω] using haω.symm
    calc
      _ = ∫ ω in X ⁻¹' C, (μ[a * R | (MeasurableSpace.comap X inferInstance)]) ω ∂μ :=
        setIntegral_congr_ae (hX hC) (hce.mono (fun ω h _ => h))
      _ = ∫ ω in X ⁻¹' C, a ω * R ω ∂μ :=
        setIntegral_condExp hX.comap_le haRint ⟨C, hC, rfl⟩
      _ = _ := (hresp C hC).symm
  have hHa : H =ᵐ[μ] a := by
    filter_upwards [hleft, hright] with ω hl hr
    have he : P ω * H ω = P ω * a ω := by
      calc
        _ = (μ[(fun ω => Y ω * R ω) | (MeasurableSpace.comap X inferInstance)]) ω := hl
        _ = a ω * P ω := hr.symm
        _ = _ := mul_comm _ _
    exact mul_left_cancel₀ (hPpos ω).ne' he
  refine ⟨hm.1, hYi, hmi, ?_⟩
  intro C hC
  calc
    (∫ ω in X ⁻¹' C, Y ω ∂μ) = ∫ ω in X ⁻¹' C, H ω ∂μ :=
      (setIntegral_condExp hX.comap_le hYi ⟨C, hC, rfl⟩).symm
    _ = ∫ ω in X ⁻¹' C, m (X ω) ∂μ :=
      setIntegral_congr_ae (hX hC) (hHa.mono (fun ω h _ => h))

/-! Stable outcomes: no MAR or population integrability of `m ∘ X` is used. -/

private theorem GP0014B2b_stable_censoring_on_response {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y R : Ω → ℝ) (hR : Measurable R) :
    (fun ω => censored (Y ω) (R ω)) =ᵐ[μ.restrict {ω | R ω = 1}] Y := by
  have hB : MeasurableSet {ω | R ω = 1} := hR (measurableSet_singleton 1)
  apply (ae_restrict_iff' hB).2
  exact ae_of_all _ (fun ω hω => by
      have hRω : R ω = 1 := hω
      simp [censored, hRω])

private theorem GP0014B2b_stable_censoring_piecewise {Ω : Type*} (Y R : Ω → ℝ)
    (hbinary : ∀ ω, R ω = 0 ∨ R ω = 1) :
    (fun ω => censored (Y ω) (R ω)) =
      {ω | R ω = 1}.piecewise Y (fun _ => -99) := by
  funext ω
  rcases hbinary ω with h | h <;> simp [censored, Set.piecewise, h]

/-- A respondent CEF determines a piecewise CEF of the censored outcome
given response status and covariates. -/
theorem stable_outcomes_respondent_cef_proof {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (hYi : Integrable Y μ)
   (hbinary : ∀ ω,R ω=0 ∨ R ω=1) (m : E → ℝ)
   (hm : IsCEF (μ.restrict {ω | R ω=1}) X Y m) :
   IsCEF (μ.restrict {ω | R ω=1}) X (fun ω => censored (Y ω) (R ω)) m ∧
   IsCEF μ (fun ω => (R ω,X ω)) (fun ω => censored (Y ω) (R ω))
     (fun rx => if rx.1=1 then m rx.2 else -99) := by
  let B : Set Ω := {ω | R ω = 1}
  let c : Ω → ℝ := fun ω => censored (Y ω) (R ω)
  let z : Ω → ℝ := fun ω => if R ω = 1 then m (X ω) else -99
  have hB : MeasurableSet B := hR (measurableSet_singleton 1)
  have hcY : c =ᵐ[μ.restrict B] Y := GP0014B2b_stable_censoring_on_response μ Y R hR
  have hci : Integrable c μ := by
    rw [show c = B.piecewise Y (fun _ => -99) from GP0014B2b_stable_censoring_piecewise Y R hbinary]
    exact Integrable.piecewise hB hYi.integrableOn (integrable_const (-99 : ℝ)).integrableOn
  have hzi : Integrable z μ := by
    have hpieces : z = B.indicator (m ∘ X) + Bᶜ.indicator (fun _ => (-99 : ℝ)) := by
      funext ω
      by_cases h : R ω = 1 <;> simp [z, B, Set.indicator, h]
    rw [hpieces]
    have hmB : IntegrableOn (m ∘ X) B μ := hm.2.2.1
    exact (hmB.integrable_indicator hB).add
      ((integrable_const (-99 : ℝ)).indicator hB.compl)
  have hversion : Measurable (fun rx : ℝ × E => if rx.1 = 1 then m rx.2 else (-99 : ℝ)) :=
    Measurable.ite (measurable_fst (measurableSet_singleton 1))
      (hm.1.comp measurable_snd) measurable_const
  constructor
  · refine ⟨hm.1, hm.2.1.congr hcY.symm, hm.2.2.1, ?_⟩
    intro A hA
    calc
      _ = ∫ ω in X ⁻¹' A, Y ω ∂μ.restrict B :=
        integral_congr_ae (ae_restrict_of_ae hcY)
      _ = _ := hm.2.2.2 A hA
  · refine ⟨hversion, hci, hzi, ?_⟩
    intro A hA
    let A₁ : Set E := (fun x : E => ((1 : ℝ), x)) ⁻¹' A
    let A₀ : Set E := (fun x : E => ((0 : ℝ), x)) ⁻¹' A
    have hA₁ : MeasurableSet A₁ := (measurable_const.prodMk measurable_id) hA
    have hA₀ : MeasurableSet A₀ := (measurable_const.prodMk measurable_id) hA
    let T₁ : Set Ω := B ∩ X ⁻¹' A₁
    let T₀ : Set Ω := Bᶜ ∩ X ⁻¹' A₀
    have hT₁ : MeasurableSet T₁ := hB.inter (hX hA₁)
    have hT₀ : MeasurableSet T₀ := hB.compl.inter (hX hA₀)
    have hdis : Disjoint T₁ T₀ := by
      apply Set.disjoint_left.mpr
      intro ω h₁ h₀
      exact h₀.1 h₁.1
    have hsplit : (fun ω => (R ω, X ω)) ⁻¹' A = T₁ ∪ T₀ := by
      ext ω
      rcases hbinary ω with h | h <;>
        simp [T₁, T₀, B, A₁, A₀, h]
    have hc₁ : (∫ ω in T₁, c ω ∂μ) =
        ∫ ω in X ⁻¹' A₁, Y ω ∂μ.restrict B := by
      rw [Measure.restrict_restrict (hX hA₁), Set.inter_comm (X ⁻¹' A₁) B]
      apply setIntegral_congr_fun hT₁
      intro ω hω
      have hRω : R ω = 1 := hω.1
      simp [c, censored, hRω]
    have hz₁ : (∫ ω in T₁, z ω ∂μ) =
        ∫ ω in X ⁻¹' A₁, m (X ω) ∂μ.restrict B := by
      rw [Measure.restrict_restrict (hX hA₁), Set.inter_comm (X ⁻¹' A₁) B]
      apply setIntegral_congr_fun hT₁
      intro ω hω
      have hRω : R ω = 1 := hω.1
      simp [z, hRω]
    have hfirst : (∫ ω in T₁, c ω ∂μ) = ∫ ω in T₁, z ω ∂μ := by
      rw [hc₁, hz₁]
      exact hm.2.2.2 A₁ hA₁
    have hsecond : (∫ ω in T₀, c ω ∂μ) = ∫ ω in T₀, z ω ∂μ := by
      apply setIntegral_congr_fun hT₀
      intro ω hω
      have hne : R ω ≠ 1 := hω.1
      have hzero : R ω = 0 := (hbinary ω).resolve_right hne
      simp [c, z, censored, hzero]
    change (∫ ω in (fun ω => (R ω, X ω)) ⁻¹' A, c ω ∂μ) =
      ∫ ω in (fun ω => (R ω, X ω)) ⁻¹' A, z ω ∂μ
    rw [hsplit, setIntegral_union hdis hT₀ hci.integrableOn hci.integrableOn,
      setIntegral_union hdis hT₀ hzi.integrableOn hzi.integrableOn, hfirst, hsecond]

end
end AronowAudit.P001.Wave1
