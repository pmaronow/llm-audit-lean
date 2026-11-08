import SAP.P001e.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.WH.W1.P.T83_L1

open SAP.P001e

private theorem condIndependent_congr_response
    {Ω E F G : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace G] (μ : Measure Ω)
    (X : Ω → E) (hX : Measurable X) (Y : Ω → F) (Z Z0 : Ω → G)
    (hZ : Z0 =ᵐ[μ] Z) (hci : CondIndependent μ X hX Y Z) :
    CondIndependent μ X hX Y Z0 := by
  intro A B hA hB
  have hjoint : (fun ω => if Y ω ∈ A ∧ Z0 ω ∈ B then (1 : ℝ) else 0) =ᵐ[μ]
      (fun ω => if Y ω ∈ A ∧ Z ω ∈ B then (1 : ℝ) else 0) := by
    filter_upwards [hZ] with ω hω
    simp [hω]
  have hmargin : (fun ω => if Z0 ω ∈ B then (1 : ℝ) else 0) =ᵐ[μ]
      (fun ω => if Z ω ∈ B then (1 : ℝ) else 0) := by
    filter_upwards [hZ] with ω hω
    simp [hω]
  have hj := condExp_congr_ae (m := MeasurableSpace.comap X inferInstance) hjoint
  have hm := condExp_congr_ae (m := MeasurableSpace.comap X inferInstance) hmargin
  have hc := hci A B hA hB
  filter_upwards [hj, hm, hc] with ω hωj hωm hωc
  calc
    (μ[(fun ω => if Y ω ∈ A ∧ Z0 ω ∈ B then (1 : ℝ) else 0) |
      MeasurableSpace.comap X inferInstance]) ω =
        (μ[(fun ω => if Y ω ∈ A ∧ Z ω ∈ B then (1 : ℝ) else 0) |
          MeasurableSpace.comap X inferInstance]) ω := hωj
    _ = (μ[(fun ω => if Y ω ∈ A then (1 : ℝ) else 0) |
          MeasurableSpace.comap X inferInstance]) ω *
        (μ[(fun ω => if Z ω ∈ B then (1 : ℝ) else 0) |
          MeasurableSpace.comap X inferInstance]) ω := hωc
    _ = (μ[(fun ω => if Y ω ∈ A then (1 : ℝ) else 0) |
          MeasurableSpace.comap X inferInstance]) ω *
        (μ[(fun ω => if Z0 ω ∈ B then (1 : ℝ) else 0) |
          MeasurableSpace.comap X inferInstance]) ω := by rw [hωm]

end SAP.P001e.WH.W1.P.T83_L1

theorem SAP.P001e.WH.W1.T83_L1_proof : SAP.P001e.WH.W1.T83_L1 := by
  classical
  intro Ω E _ _ μ hμ X hX Y R hR hbin p hp hpos hci
  obtain ⟨ε, hε, hεp⟩ := hpos
  let R0 : Ω → ℝ := fun ω => if R ω = 1 then 1 else 0
  let p0 : E → ℝ := fun x => max (p x) ε
  have hR0meas : Measurable R0 := by
    apply Measurable.ite
    · exact measurableSet_eq_fun hR measurable_const
    · exact measurable_const
    · exact measurable_const
  have hR0bin : ∀ ω, R0 ω = 0 ∨ R0 ω = 1 := by
    intro ω
    by_cases h : R ω = 1 <;> simp [R0, h]
  have hR0ae : R0 =ᵐ[μ] R := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω
    · simp [R0, hω]
    · simp [R0, hω]
  have hp0meas : Measurable p0 := hp.1.max measurable_const
  have hp0ae : (fun ω => p0 (X ω)) =ᵐ[μ] (fun ω => p (X ω)) := by
    filter_upwards [hεp] with ω hω
    simp only [p0]
    exact max_eq_left (le_of_lt hω)
  have hR0int : Integrable R0 μ := hp.2.1.congr hR0ae.symm
  have hp0int : Integrable (p0 ∘ X) μ := hp.2.2.1.congr hp0ae.symm
  have hmean0 : IsConditionalMean μ X R0 p0 := by
    refine ⟨hp0meas, hR0int, hp0int, ?_⟩
    intro A hA
    have hRrestrict : (fun ω => R0 ω) =ᵐ[μ.restrict (X ⁻¹' A)] (fun ω => R ω) := by
      exact ae_restrict_of_ae hR0ae
    have hprestrict : (fun ω => p0 (X ω)) =ᵐ[μ.restrict (X ⁻¹' A)] (fun ω => p (X ω)) := by
      exact ae_restrict_of_ae hp0ae
    calc
      ∫ ω in X ⁻¹' A, R0 ω ∂μ = ∫ ω in X ⁻¹' A, R ω ∂μ := integral_congr_ae hRrestrict
      _ = ∫ ω in X ⁻¹' A, p (X ω) ∂μ := hp.2.2.2 A hA
      _ = ∫ ω in X ⁻¹' A, p0 (X ω) ∂μ := (integral_congr_ae hprestrict).symm
  have hdelta : ∃ δ : ℝ, 0 < δ ∧ ∀ ω, δ < p0 (X ω) := by
    refine ⟨ε / 2, half_pos hε, ?_⟩
    intro ω
    exact lt_of_lt_of_le (half_lt_self hε) (le_max_right (p (X ω)) ε)
  have hci0 : CondIndependent μ X hX Y R0 :=
    SAP.P001e.WH.W1.P.T83_L1.condIndependent_congr_response
      μ X hX Y R R0 hR0ae hci
  exact ⟨R0, p0, hR0meas, hR0bin, hR0ae, hp0ae, hmean0, hdelta, hci0⟩
