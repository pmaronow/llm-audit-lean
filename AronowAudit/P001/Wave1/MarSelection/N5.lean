import AronowAudit.P001.Wave1.MarSelectionBlueprint
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.MarSelection

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n5_proof : N5.{u, v, w} := by
  classical
  intro hN1 hN4 hN3 hN2 Ω E F _ _ _ μ _ X hX U R g Z p m
    hU hR hg hbin hCI hp hpos hVi hobs hm hMi
  let V : Ω → ℝ := fun ω => g (X ω, U ω)
  let M : Ω → ℝ := m ∘ X
  let S : Set Ω := {ω | R ω = 1}
  let W : Ω → ℝ := V - M
  let ρ : Ω → ℝ := μ[R | (MeasurableSpace.comap X inferInstance)]
  let L : Ω → ℝ := ρ * μ[W | (MeasurableSpace.comap X inferInstance)]
  have hG : (MeasurableSpace.comap X inferInstance) ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := comap_measurable X
  have hMm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] M := (hm.1.comp hXm).stronglyMeasurable
  have hS : MeasurableSet S := measurableSet_eq_fun hR measurable_const
  have hWi : Integrable W μ := hVi.sub hMi
  have hg' : Measurable (fun z : E × F => g z - m z.1) := hg.sub (hm.1.comp measurable_fst)
  obtain ⟨hRWi, hfactor⟩ := hN4 hN1 hN3 hN2 μ X hX U R
    hU hR hbin hCI (fun z => g z - m z.1) hg' hWi
  have hfactor' : μ[R * W | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] L := hfactor
  have hLi : Integrable L μ := integrable_condExp.congr hfactor'
  have hLm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] L :=
    stronglyMeasurable_condExp.mul stronglyMeasurable_condExp
  have hZV : Z =ᵐ[μ.restrict S] V := (ae_restrict_iff' hS).2 hobs
  have hrestricted : ∀ C : Set E, MeasurableSet C →
      (∫ ω in X ⁻¹' C, W ω ∂μ.restrict S) = 0 := by
    intro C hC
    calc
      (∫ ω in X ⁻¹' C, W ω ∂μ.restrict S) =
          ∫ ω in X ⁻¹' C, Z ω - m (X ω) ∂μ.restrict S := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hZV] with ω hω
        change V ω - M ω = Z ω - M ω
        rw [hω]
      _ = (∫ ω in X ⁻¹' C, Z ω ∂μ.restrict S) -
          ∫ ω in X ⁻¹' C, m (X ω) ∂μ.restrict S :=
        integral_sub hm.2.1.integrableOn hm.2.2.1.integrableOn
      _ = 0 := sub_eq_zero.mpr (hm.2.2.2 C hC)
  have hind : R * W =ᵐ[μ] S.indicator W := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [S, Set.indicator, hω]
  have hzero : ∀ C : Set E, MeasurableSet C →
      (∫ ω in X ⁻¹' C, (R * W) ω ∂μ) = 0 := by
    intro C hC
    calc
      (∫ ω in X ⁻¹' C, (R * W) ω ∂μ) =
          ∫ ω in X ⁻¹' C, S.indicator W ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hind)
      _ = ∫ ω in X ⁻¹' C ∩ S, W ω ∂μ := setIntegral_indicator hS
      _ = ∫ ω in X ⁻¹' C, W ω ∂μ.restrict S := by
        rw [Measure.restrict_restrict (hC.preimage hX)]
      _ = 0 := hrestricted C hC
  have hLzero : L =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hG
      (fun _ _ _ => hLi.integrableOn)
      (fun _ _ _ => (integrable_const (0 : ℝ)).integrableOn) ?_
      hLm.aestronglyMeasurable stronglyMeasurable_const.aestronglyMeasurable
    intro s hs _
    rcases hs with ⟨C, hC, rfl⟩
    calc
      (∫ ω in X ⁻¹' C, L ω ∂μ) = ∫ ω in X ⁻¹' C, (μ[R * W | (MeasurableSpace.comap X inferInstance)]) ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hfactor'.symm)
      _ = ∫ ω in X ⁻¹' C, (R * W) ω ∂μ :=
        setIntegral_condExp hG hRWi ⟨C, hC, rfl⟩
      _ = ∫ _ in X ⁻¹' C, (0 : ℝ) ∂μ := by rw [hzero C hC, integral_zero]
  obtain ⟨ε, hε, hεp⟩ := hpos
  have hpρ : p ∘ X =ᵐ[μ] ρ := isCEF_condExp μ X hX R p hp
  have hWzero : μ[W | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    filter_upwards [hLzero, hpρ, hεp] with ω hωL hωp hωpos
    change ρ ω * (μ[W | (MeasurableSpace.comap X inferInstance)]) ω = 0 at hωL
    have hρne : ρ ω ≠ 0 := by
      rw [← hωp]
      exact (hε.trans hωpos).ne'
    exact (mul_eq_zero.mp hωL).resolve_left hρne
  have hMfix : μ[M | (MeasurableSpace.comap X inferInstance)] = M := condExp_of_stronglyMeasurable hG hMm hMi
  have hsub : μ[W | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] μ[V | (MeasurableSpace.comap X inferInstance)] - M := by
    have hs : μ[V - M | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] μ[V | (MeasurableSpace.comap X inferInstance)] - μ[M | (MeasurableSpace.comap X inferInstance)] := condExp_sub hVi hMi (MeasurableSpace.comap X inferInstance)
    rw [hMfix] at hs
    exact hs
  have hVeq : μ[V | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] M := by
    filter_upwards [hWzero, hsub] with ω hω0 hωsub
    change (μ[W | (MeasurableSpace.comap X inferInstance)]) ω = (μ[V | (MeasurableSpace.comap X inferInstance)]) ω - M ω at hωsub
    change (μ[W | (MeasurableSpace.comap X inferInstance)]) ω = 0 at hω0
    linarith
  refine ⟨hm.1, hVi, hMi, ?_⟩
  intro C hC
  calc
    (∫ ω in X ⁻¹' C, V ω ∂μ) = ∫ ω in X ⁻¹' C, (μ[V | (MeasurableSpace.comap X inferInstance)]) ω ∂μ :=
      (setIntegral_condExp hG hVi ⟨C, hC, rfl⟩).symm
    _ = ∫ ω in X ⁻¹' C, m (X ω) ∂μ :=
      integral_congr_ae (ae_restrict_of_ae hVeq)

end

end AronowAudit.P001.Wave1.MarSelection
