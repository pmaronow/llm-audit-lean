import SAP.P001f.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open SAP.P001f
open scoped BigOperators ENNReal

universe u

noncomputable section

theorem SAP.P001f.WH.W2.T113_L2_proof : SAP.P001f.WH.W2.T113_L2 := by
  intro Ω _ K μ _ X hX Y R hY hR hYi hbin hR0 hR1 p hp hpos hCI
  obtain ⟨ε, hε, hεX⟩ := hpos
  let a : Ω → ℝ := fun ω => (p (X ω))⁻¹
  have hRbound : ∀ᵐ ω ∂μ, ‖R ω‖ ≤ (1 : ℝ) := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hRint : Integrable R μ :=
    Integrable.of_bound hR.aestronglyMeasurable 1 hRbound
  have haBound : ∀ᵐ ω ∂μ, ‖a ω‖ ≤ ε⁻¹ := by
    filter_upwards [hεX] with ω hω
    have hpω : 0 < p (X ω) := hε.trans hω
    change ‖(p (X ω))⁻¹‖ ≤ ε⁻¹
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hpω]
    simpa only [one_div] using one_div_le_one_div_of_le hε hω.le
  have hRY : Integrable (fun ω => R ω * Y ω) μ :=
    hYi.bdd_mul hR.aestronglyMeasurable hRbound
  have hstar : (fun ω => R ω * censoredOutcome (Y ω) (R ω)) =ᵐ[μ]
      (fun ω => R ω * Y ω) := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [censoredOutcome, hω]
  have hRc : Integrable (fun ω => R ω * censoredOutcome (Y ω) (R ω)) μ :=
    hRY.congr hstar.symm
  have haMeas : Measurable a := by
    change Measurable (fun ω => (p (X ω))⁻¹)
    exact (hp.1.comp hX).inv
  have hBmul : Integrable
      (fun ω => (R ω * censoredOutcome (Y ω) (R ω)) * a ω) μ :=
    hRc.mul_bdd haMeas.aestronglyMeasurable haBound
  have hBeq : (fun ω => R ω * censoredOutcome (Y ω) (R ω) / p (X ω)) =ᵐ[μ]
      (fun ω => (R ω * censoredOutcome (Y ω) (R ω)) * a ω) := by
    filter_upwards with ω
    simp only [a, div_eq_mul_inv]
  have hBi : Integrable
      (fun ω => R ω * censoredOutcome (Y ω) (R ω) / p (X ω)) μ :=
    hBmul.congr hBeq.symm
  have hDR := AronowAudit.P001.Wave1.missing_double_robustness_paper_support
    μ X hX Y R hY hR hYi hbin hR0 hR1 p hp ⟨ε, hε, hεX⟩ hCI
    (fun _ => 0) p measurable_const hp.1
    (by
      change Integrable (fun _ : Ω => (0 : ℝ)) μ
      exact integrable_const 0)
    (Or.inr (Filter.EventuallyEq.rfl : (p ∘ X) =ᵐ[μ] (p ∘ X)))
  have hMean : (∫ ω, R ω * censoredOutcome (Y ω) (R ω) / p (X ω) ∂μ) =
      (∫ ω, Y ω ∂μ) := by
    simpa [AronowAudit.P001.mean, AronowAudit.P001.censored, censoredOutcome] using hDR.symm
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X := comap_measurable X
  have haSm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] a :=
    ((hp.1.comp hXm).inv).stronglyMeasurable
  have hWmul : Integrable (a * R) μ :=
    hRint.bdd_mul (haSm.mono hX.comap_le).aestronglyMeasurable haBound
  have hWeq : (fun ω => R ω / p (X ω)) =ᵐ[μ] (a * R) := by
    filter_upwards with ω
    change R ω * (p (X ω))⁻¹ = (p (X ω))⁻¹ * R ω
    ring
  have hWi : Integrable (fun ω => R ω / p (X ω)) μ :=
    hWmul.congr hWeq.symm
  have hpull : μ[a * R | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      a * μ[R | MeasurableSpace.comap X inferInstance] :=
    condExp_mul_of_stronglyMeasurable_left haSm hWmul hRint
  have hcef := AronowAudit.P001.isCEF_condExp μ X hX R p hp
  have hWcond : μ[(fun ω => R ω / p (X ω)) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      (fun _ => (1 : ℝ)) := by
    calc
      μ[(fun ω => R ω / p (X ω)) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
          μ[a * R | MeasurableSpace.comap X inferInstance] := condExp_congr_ae hWeq
      _ =ᵐ[μ] a * μ[R | MeasurableSpace.comap X inferInstance] := hpull
      _ =ᵐ[μ] (fun _ => (1 : ℝ)) := by
        filter_upwards [hcef, hεX] with ω hcefω hεω
        change a ω * μ[R | MeasurableSpace.comap X inferInstance] ω = 1
        rw [← hcefω]
        dsimp [a]
        exact inv_mul_cancel₀ (ne_of_gt (hε.trans hεω))
  exact ⟨hBi, hMean, hWi, hWcond⟩

end
