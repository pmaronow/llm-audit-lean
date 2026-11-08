import SAP.P001e.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.WH.W2.P.T87_L2

universe u v
noncomputable section

theorem respondent_event_bound
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (R : Ω → ℝ) (hR : Measurable R) (hb : ∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1)
    (p : E → ℝ) (hp : IsConditionalMean μ X R p)
    {ε : ℝ} (hpos : ∀ᵐ ω ∂μ, ε < p (X ω))
    {A : Set E} (hA : MeasurableSet A) :
    ENNReal.ofReal ε * μ (X ⁻¹' A) ≤ μ (X ⁻¹' A ∩ {ω | R ω = 1}) := by
  let S : Set Ω := X ⁻¹' A
  have hS : MeasurableSet S := hX hA
  have hS' : MeasurableSet (S ∩ {ω | R ω = 1}) :=
    hS.inter (hR (measurableSet_singleton (1 : ℝ)))
  have hRint : (∫ ω in S, R ω ∂μ) = μ.real (S ∩ {ω | R ω = 1}) := by
    calc
      (∫ ω in S, R ω ∂μ) = ∫ ω, S.indicator R ω ∂μ := (integral_indicator hS).symm
      _ = ∫ ω, (S ∩ {ω | R ω = 1}).indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hb] with ω hω
        by_cases hs : ω ∈ S
        · rcases hω with hzero | hone
          · simp [hs, hzero]
          · simp [hs, hone]
        · simp [hs]
      _ = μ.real (S ∩ {ω | R ω = 1}) := integral_indicator_one hS'
  have hle : (∫ ω in S, (fun _ : Ω => ε) ω ∂μ) ≤ ∫ ω in S, (p ∘ X) ω ∂μ := by
    have hae : (fun _ : Ω => ε) ≤ᵐ[μ.restrict S] (p ∘ X) := by
      filter_upwards [hpos.filter_mono (ae_mono (Measure.restrict_le_self : μ.restrict S ≤ μ))]
        with ω hω
      exact le_of_lt hω
    simpa [Function.comp_def] using
      integral_mono_ae (integrable_const ε) (hp.2.2.1.restrict) hae
  have hcef := hp.2.2.2 A hA
  have hreal : ε * μ.real S ≤ μ.real (S ∩ {ω | R ω = 1}) := by
    calc
      ε * μ.real S = ∫ ω in S, (fun _ : Ω => ε) ω ∂μ := by
        rw [setIntegral_const, smul_eq_mul]
        ring
      _ ≤ ∫ ω in S, (p ∘ X) ω ∂μ := hle
      _ = ∫ ω in S, R ω ∂μ := hcef.symm
      _ = μ.real (S ∩ {ω | R ω = 1}) := hRint
  have hSfin : μ S ≠ ∞ := measure_ne_top μ S
  have hInterfin : μ (S ∩ {ω | R ω = 1}) ≠ ∞ := measure_ne_top μ _
  have hreal' : ε * (μ S).toReal ≤ (μ (S ∩ {ω | R ω = 1})).toReal := by
    simpa [measureReal_def] using hreal
  calc
    ENNReal.ofReal ε * μ S = ENNReal.ofReal ε * ENNReal.ofReal (μ S).toReal := by
      rw [ENNReal.ofReal_toReal hSfin]
    _ = ENNReal.ofReal (ε * (μ S).toReal) := by
      rw [ENNReal.ofReal_mul' (ENNReal.toReal_nonneg)]
    _ ≤ ENNReal.ofReal (μ (S ∩ {ω | R ω = 1})).toReal :=
      ENNReal.ofReal_le_ofReal hreal'
    _ = μ (S ∩ {ω | R ω = 1}) := ENNReal.ofReal_toReal hInterfin

end
end SAP.P001e.WH.W2.P.T87_L2

theorem SAP.P001e.WH.W2.T87_L2_proof : SAP.P001e.WH.W2.T87_L2 := by
  intro Ω E _ _ μ hμ X hX R hR hb p m hp hm hpos hi
  rcases hpos with ⟨ε, hε, hpos⟩
  let ρ : Measure E := (μ.restrict {ω | R ω = 1}).map X
  let ν : Measure E := μ.map X
  have hmeas : ∀ A, MeasurableSet A →
      (ENNReal.ofReal ε • ν) A ≤ ρ A := by
    intro A hA
    have hh := SAP.P001e.WH.W2.P.T87_L2.respondent_event_bound
      μ X hX R hR hb p hp hpos hA
    dsimp [ν, ρ]
    rw [Measure.map_apply hX hA,
      Measure.map_apply hX hA, Measure.restrict_apply (hX hA)]
    simpa [Set.inter_comm] using hh
  have hmeasure : ENNReal.ofReal ε • ν ≤ ρ := Measure.le_iff.2 hmeas
  have hiρ : Integrable m ρ := by
    apply (integrable_map_measure hm.aestronglyMeasurable hX.aemeasurable).mpr
    exact hi
  have hiScaled : Integrable m (ENNReal.ofReal ε • ν) := hiρ.mono_measure hmeasure
  have hiν : Integrable m ν := by
    apply (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr hε)
      ENNReal.ofReal_ne_top).mp hiScaled
  apply (integrable_map_measure hm.aestronglyMeasurable hX.aemeasurable).mp hiν
