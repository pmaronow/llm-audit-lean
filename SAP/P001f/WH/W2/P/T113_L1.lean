import SAP.P001f.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

theorem SAP.P001f.WH.W2.T113_L1_proof : SAP.P001f.WH.W2.T113_L1 := by
  intro Ω _ K μ _ X hX R hR hbin p hp hpos m hm hMres
  let M : Ω → ℝ := m ∘ X
  let S : Set Ω := {ω | R ω = 1}
  have hS : MeasurableSet S := hR (measurableSet_singleton (1 : ℝ))
  have hMind : Integrable (S.indicator M) μ := (integrable_indicator_iff hS).2 hMres
  have hMRae : (fun ω => M ω * R ω) =ᵐ[μ] S.indicator M := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω
    · simp [S, hω]
    · simp [S, hω]
  have hMR : Integrable (fun ω => M ω * R ω) μ := hMind.congr hMRae.symm
  have hRint : Integrable R μ := hp.2.1
  have hMsm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] M :=
    (hm.comp (comap_measurable X)).stronglyMeasurable
  have hPull := condExp_mul_of_stronglyMeasurable_left hMsm hMR hRint
  have hpCE : μ[R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] p ∘ X :=
    (AronowAudit.P001.isCEF_condExp μ X hX R p hp).symm
  have hMp : Integrable (fun ω => M ω * p (X ω)) μ := by
    have hcond : Integrable
        (fun ω => M ω * μ[R | MeasurableSpace.comap X inferInstance] ω) μ :=
      integrable_condExp.congr hPull
    have hreplace : (fun ω => M ω * μ[R | MeasurableSpace.comap X inferInstance] ω) =ᵐ[μ]
        (fun ω => M ω * p (X ω)) := by
      filter_upwards [hpCE] with ω hω
      change μ[R | MeasurableSpace.comap X inferInstance] ω = p (X ω) at hω
      rw [hω]
    exact hcond.congr hreplace
  rcases hpos with ⟨ε, hε, hεpos⟩
  have hscaled : Integrable (fun ω => M ω * p (X ω) / ε) μ := hMp.div_const ε
  have hMsmμ : AEStronglyMeasurable M μ :=
    (hm.comp hX).stronglyMeasurable.aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂μ, ‖M ω‖ ≤ ‖M ω * p (X ω) / ε‖ := by
    filter_upwards [hεpos] with ω hω
    have hεnorm : ε ≤ ‖p (X ω)‖ := by
      exact le_trans (le_of_lt hω) (le_abs_self _)
    have hratio : 1 ≤ ‖p (X ω)‖ / ε := by
      apply (le_div_iff₀ hε).2
      simpa using hεnorm
    calc
      ‖M ω‖ = ‖M ω‖ * 1 := by simp
      _ ≤ ‖M ω‖ * (‖p (X ω)‖ / ε) :=
        mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
      _ = ‖M ω * p (X ω) / ε‖ := by
        rw [norm_div, norm_mul]
        simp only [Real.norm_eq_abs, abs_of_pos hε]
        ring
  exact hscaled.mono hMsmμ hbound
