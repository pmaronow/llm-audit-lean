import SAP.P010.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

universe u

theorem SAP.P010.WH.W1.T12_L2_proof : SAP.P010.WH.W1.T12_L2.{u} := by
  intro Ω mΩ ν h hinf c
  intro hp
  letI : IsProbabilityMeasure
      (ν.withDensity (fun x => (c : ℝ≥0∞) * h x)) := hp
  have hmass :
      (ν.withDensity (fun x => (c : ℝ≥0∞) * h x)) Set.univ =
        (c : ℝ≥0∞) * ∫⁻ x, h x ∂ν := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact lintegral_const_mul' (c : ℝ≥0∞) h ENNReal.coe_ne_top
  have htotal := IsProbabilityMeasure.measure_univ
      (μ := ν.withDensity (fun x => (c : ℝ≥0∞) * h x))
  rw [hmass, hinf] at htotal
  by_cases hc : c = 0
  · subst c
    simp at htotal
  · have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
    rw [ENNReal.mul_top hc'] at htotal
    exact ENNReal.top_ne_one htotal
