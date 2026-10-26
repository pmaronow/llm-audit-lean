import AronowAudit.P001.Wave1.IrrationalRangeBlueprint
import AronowAudit.P001.Wave1.IrrationalRange.N1

namespace AronowAudit.P001.Wave1.IrrationalRange

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableIrrationalRangeN2 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n2_proof : N2 := by
  have hC : MeasurableSet irrHalf := n1_proof.1
  have hd : (fun x => ENNReal.ofReal (irrHalfDensity x)) =
      irrHalf.indicator (fun _ => (2 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ irrHalf
    · have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 2) \ Set.range (fun q : ℚ => (q : ℝ)) := hx
      simp only [irrHalfDensity, if_pos hx', Set.indicator_of_mem hx]
      norm_num
    · have hx' : x ∉ Set.Icc (0 : ℝ) (1 / 2) \ Set.range (fun q : ℚ => (q : ℝ)) := hx
      simp only [irrHalfDensity, if_neg hx', Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  unfold N2 irrHalfLaw
  rw [Measure.map_smul (2 : ℝ≥0∞) measurable_subtype_coe.aemeasurable,
    map_comap_subtype_coe hC, hd, withDensity_indicator hC, withDensity_const]

end
end AronowAudit.P001.Wave1.IrrationalRange
