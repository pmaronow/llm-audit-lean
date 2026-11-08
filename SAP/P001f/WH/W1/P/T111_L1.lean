import SAP.P001f.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory

noncomputable section

theorem SAP.P001f.WH.W1.T111_L1_proof : SAP.P001f.WH.W1.T111_L1 := by
  classical
  intro Ω E _ _ μ _ X hX R hR hbinary p m hp hm hpos hrespondent
  rcases hpos with ⟨ε, hε, hεpos⟩
  let H : Ω → ℝ := m ∘ X
  let S : Set Ω := {ω | R ω = 1}
  have hS : MeasurableSet S := by
    exact (measurableSet_singleton (1 : ℝ)).preimage hR
  have hHsm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] H := by
    exact (hm.comp (measurable_iff_comap_le.mpr le_rfl)).stronglyMeasurable
  have hIndicator : Integrable (Set.indicator S H) μ := by
    exact (integrable_indicator_iff hS).2 hrespondent
  have hIndicatorEq : Set.indicator S H =ᵐ[μ] (fun ω => H ω * R ω) := by
    filter_upwards [hbinary] with ω hω
    rcases hω with hω | hω
    · simp [S, hω]
    · simp [S, hω]
  have hHR : Integrable (fun ω => H ω * R ω) μ := hIndicator.congr hIndicatorEq
  have hPull := condExp_mul_of_stronglyMeasurable_left
    (m := MeasurableSpace.comap X inferInstance) hHsm hHR hp.2.1
  have hRce := AronowAudit.P001.isCEF_condExp μ X hX R p hp
  have hCE : μ[(fun ω => H ω * R ω) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      (fun ω => H ω * p (X ω)) := by
    filter_upwards [hPull, hRce] with ω hmul hmean
    calc
      μ[(fun ω => H ω * R ω) | MeasurableSpace.comap X inferInstance] ω =
          H ω * μ[R | MeasurableSpace.comap X inferInstance] ω := hmul
      _ = H ω * p (X ω) := by
        exact congrArg (fun z : ℝ => H ω * z) hmean.symm
  have hHp : Integrable (fun ω => H ω * p (X ω)) μ :=
    integrable_condExp.congr hCE
  have hInvMeas : Measurable (fun ω => (p (X ω))⁻¹) := (hp.1.comp hX).inv
  have hInvBound : ∀ᵐ ω ∂μ, ‖(p (X ω))⁻¹‖ ≤ 1 / ε := by
    filter_upwards [hεpos] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hε.trans hω))]
    simpa only [one_div, one_mul] using one_div_le_one_div_of_le hε (le_of_lt hω)
  have hMulInv : Integrable
      (fun ω => (H ω * p (X ω)) * (p (X ω))⁻¹) μ := by
    exact hHp.mul_bdd hInvMeas.aestronglyMeasurable hInvBound
  have hCancel : (fun ω => (H ω * p (X ω)) * (p (X ω))⁻¹) =ᵐ[μ] H := by
    filter_upwards [hεpos] with ω hω
    have hp0 : p (X ω) ≠ 0 := ne_of_gt (hε.trans hω)
    calc
      (H ω * p (X ω)) * (p (X ω))⁻¹ = H ω * (p (X ω) * (p (X ω))⁻¹) := by ring
      _ = H ω := by rw [mul_inv_cancel₀ hp0, mul_one]
  exact hMulInv.congr hCancel
