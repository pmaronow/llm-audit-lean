import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T15_L1

open MeasureTheory Set
open scoped ENNReal
noncomputable section
universe u

theorem exists_radial_density {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (r : X → ℝ) (δ : X → ℝ)
    (hr : Measurable r) (hδ : Integrable δ μ) :
    ∃ t : ℝ → ℝ, SAP.P004a.W1RadialDensity μ r δ t := by
  let ν : Measure ℝ := Measure.map r μ
  let v : SignedMeasure X := μ.withDensityᵥ δ
  let s : SignedMeasure ℝ := v.map r
  let t : ℝ → ℝ := s.rnDeriv ν
  have hmap : (μ.toENNRealVectorMeasure).map r = ν.toENNRealVectorMeasure := by
    ext1 B hB
    rw [VectorMeasure.map_apply _ hr hB,
      Measure.toENNRealVectorMeasure_apply_measurable (hr hB),
      Measure.toENNRealVectorMeasure_apply_measurable hB]
    change μ (r ⁻¹' B) = (Measure.map r μ) B
    rw [Measure.map_apply hr hB]
  have hac' : (μ.withDensityᵥ δ).map r ≪ᵥ (μ.toENNRealVectorMeasure).map r :=
    VectorMeasure.AbsolutelyContinuous.map
      (Measure.withDensityᵥ_absolutelyContinuous μ δ) r
  have hac : s ≪ᵥ ν.toENNRealVectorMeasure := by
    dsimp [s, v]
    rw [← hmap]
    exact hac'
  have ht : Integrable t ν := by
    dsimp [t, s, ν]
    exact SignedMeasure.integrable_rnDeriv _ _
  have heq : ν.withDensityᵥ t = s := by
    dsimp [t, s, ν]
    exact SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hac
  refine ⟨t, ht, ?_, ?_⟩
  · intro B hB
    change (∫ x in B, t x ∂ν) = ∫ x in r ⁻¹' B, δ x ∂μ
    rw [← withDensityᵥ_apply ht hB, heq, VectorMeasure.map_apply _ hr hB,
      withDensityᵥ_apply hδ (hr hB)]
  · intro a ha
    have hsing := congrArg (fun w : SignedMeasure ℝ => w {a}) heq
    have hpre : MeasurableSet (r ⁻¹' ({a} : Set ℝ)) := hr (measurableSet_singleton a)
    rw [withDensityᵥ_apply ht (measurableSet_singleton a),
      VectorMeasure.map_apply _ hr (measurableSet_singleton a),
      withDensityᵥ_apply hδ hpre] at hsing
    have hmul : (ν {a}).toReal * t a = ∫ x in r ⁻¹' ({a} : Set ℝ), δ x ∂μ := by
      simpa only [integral_singleton, smul_eq_mul, Measure.real] using hsing
    have hpos : 0 < (ν {a}).toReal :=
      ENNReal.toReal_pos (ne_of_gt ha) (measure_ne_top ν {a})
    have hresult : t a =
        (∫ x in r ⁻¹' ({a} : Set ℝ), δ x ∂μ) / (ν {a}).toReal := by
      apply (eq_div_iff (ne_of_gt hpos)).2
      nlinarith [hmul]
    simpa [ν] using hresult

end
end SAP.P004a.WH.W1.P.T15_L1

theorem SAP.P004a.WH.W1.T15_L1_proof : SAP.P004a.WH.W1.T15_L1 := by
  intro X _ μ _ r δ hr hδ
  exact SAP.P004a.WH.W1.P.T15_L1.exists_radial_density μ r δ hr hδ
