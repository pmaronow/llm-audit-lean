import AronowAudit.P001.Wave1.MarSelectionBlueprint

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.MarSelection

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n7_proof : N7.{u, v, w} := by
  intro hN1 hN2 hN3 hN4 hN5 hN6 Ω E F _ _ _ μ _ X hX U R g Z p m q
    hU hR hg _hZ hbin hCI hp hpos hVi hobs hm hq hMi hcorrect
  let V : Ω → ℝ := fun ω => g (X ω, U ω)
  let M : Ω → ℝ := m ∘ X
  let W : Ω → ℝ := V - M
  let ρ : Ω → ℝ := μ[R | (MeasurableSpace.comap X inferInstance)]
  have hG : (MeasurableSpace.comap X inferInstance) ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := comap_measurable X
  have hWi : Integrable W μ := hVi.sub hMi
  have hg' : Measurable (fun z : E × F => g z - m z.1) := hg.sub (hm.comp measurable_fst)
  have hqbound : ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂μ, c ≤ q (X ω) := by
    rcases hcorrect with h | h
    · exact h.2
    · obtain ⟨ε, hε, hεp⟩ := hpos
      refine ⟨ε, hε, ?_⟩
      filter_upwards [h, hεp] with ω hω hωp
      change q (X ω) = p (X ω) at hω
      rw [hω]
      exact hωp.le
  obtain ⟨hweighted, hweightMean⟩ := hN6 hN1 hN4 hN3 hN2 μ X hX U R
    (fun z => g z - m z.1) q hU hR hg' hq hbin hCI hWi hqbound
  have hobsres : (fun ω => R ω * (Z ω - m (X ω)) / q (X ω)) =ᵐ[μ]
      (fun ω => R ω * W ω / q (X ω)) := by
    filter_upwards [hbin, hobs] with ω hω hωobs
    rcases hω with hω | hω
    · simp [hω]
    · rw [hωobs hω]
      rfl
  have hobsint : Integrable (fun ω => R ω * (Z ω - m (X ω)) / q (X ω)) μ :=
    hweighted.congr hobsres.symm
  have hMfix : μ[M | (MeasurableSpace.comap X inferInstance)] = M :=
    condExp_of_stronglyMeasurable hG (hm.comp hXm).stronglyMeasurable hMi
  have hsub : μ[W | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] μ[V | (MeasurableSpace.comap X inferInstance)] - M := by
    have hs : μ[V - M | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] μ[V | (MeasurableSpace.comap X inferInstance)] - μ[M | (MeasurableSpace.comap X inferInstance)] := condExp_sub hVi hMi (MeasurableSpace.comap X inferInstance)
    rw [hMfix] at hs
    exact hs
  have hresmean : (∫ ω, R ω * W ω / q (X ω) ∂μ) =
      (∫ ω, V ω ∂μ) - ∫ ω, M ω ∂μ := by
    rcases hcorrect with ⟨hreg, _⟩ | hqp
    · have hpop : IsCEF μ X V m := hN5 hN1 hN4 hN3 hN2 μ X hX U R g Z p m
        hU hR hg hbin hCI hp hpos hVi hobs hreg hMi
      have hregCE : M =ᵐ[μ] μ[V | (MeasurableSpace.comap X inferInstance)] := isCEF_condExp μ X hX V m hpop
      have hWzero : μ[W | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] (fun _ => (0 : ℝ)) := by
        filter_upwards [hsub, hregCE] with ω hωsub hωreg
        change (μ[W | (MeasurableSpace.comap X inferInstance)]) ω = (μ[V | (MeasurableSpace.comap X inferInstance)]) ω - M ω at hωsub
        rw [hωsub, ← hωreg, sub_self]
      have hmeanVM : (∫ ω, V ω ∂μ) = ∫ ω, M ω ∂μ := by
        have h := hpop.2.2.2 Set.univ MeasurableSet.univ
        simp only [Set.preimage_univ, Measure.restrict_univ] at h
        exact h
      calc
        (∫ ω, R ω * W ω / q (X ω) ∂μ) =
            ∫ ω, ρ ω * (μ[W | (MeasurableSpace.comap X inferInstance)]) ω / q (X ω) ∂μ := hweightMean
        _ = ∫ _ : Ω, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hWzero] with ω hω
          simp [hω]
        _ = (∫ ω, V ω ∂μ) - ∫ ω, M ω ∂μ := by rw [integral_zero, hmeanVM, sub_self]
    · obtain ⟨ε, hε, hεp⟩ := hpos
      have hpρ : p ∘ X =ᵐ[μ] ρ := isCEF_condExp μ X hX R p hp
      have hcancel : (fun ω => ρ ω * (μ[W | (MeasurableSpace.comap X inferInstance)]) ω / q (X ω)) =ᵐ[μ] μ[W | (MeasurableSpace.comap X inferInstance)] := by
        filter_upwards [hqp, hpρ, hεp] with ω hωq hωp hωpos
        change q (X ω) = p (X ω) at hωq
        change p (X ω) = ρ ω at hωp
        have hne : p (X ω) ≠ 0 := (hε.trans hωpos).ne'
        rw [hωq, ← hωp]
        exact mul_div_cancel_left₀ _ hne
      calc
        (∫ ω, R ω * W ω / q (X ω) ∂μ) =
            ∫ ω, ρ ω * (μ[W | (MeasurableSpace.comap X inferInstance)]) ω / q (X ω) ∂μ := hweightMean
        _ = ∫ ω, (μ[W | (MeasurableSpace.comap X inferInstance)]) ω ∂μ := integral_congr_ae hcancel
        _ = ∫ ω, W ω ∂μ := integral_condExp hG
        _ = (∫ ω, V ω ∂μ) - ∫ ω, M ω ∂μ := integral_sub hVi hMi
  refine ⟨hMi.add hobsint, ?_⟩
  have h1 : (∫ ω, (m (X ω) + R ω * (Z ω - m (X ω)) / q (X ω)) ∂μ) =
      (∫ ω, M ω ∂μ) + ∫ ω, R ω * (Z ω - m (X ω)) / q (X ω) ∂μ := integral_add hMi hobsint
  rw [h1, integral_congr_ae hobsres, hresmean]
  show (∫ ω, M ω ∂μ) + ((∫ ω, V ω ∂μ) - ∫ ω, M ω ∂μ) = ∫ ω, V ω ∂μ
  ring

end

end AronowAudit.P001.Wave1.MarSelection
