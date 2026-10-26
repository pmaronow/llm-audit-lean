import AronowAudit.P001.Wave1.IrrationalRangeBlueprint

namespace AronowAudit.P001.Wave1.IrrationalRange

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableIrrationalRangeN1 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n1_proof : N1 := by
  have hQ : (Set.range (fun q : ℚ => (q : ℝ))).Countable := Set.countable_range _
  have hQm : MeasurableSet (Set.range (fun q : ℚ => (q : ℝ))) := hQ.measurableSet
  have hQ0 : volume (Set.range (fun q : ℚ => (q : ℝ))) = 0 := hQ.measure_zero volume
  refine ⟨measurableSet_Icc.diff hQm, ?_, ?_⟩
  · unfold irrHalf
    rw [measure_sdiff_null hQ0, Real.volume_Icc]
    norm_num
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat, one_div]
  · intro a b hab hsub
    obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
    have hmem : (q : ℝ) ∈ irrHalf := hsub ⟨haq.le, hqb.le⟩
    exact hmem.2 ⟨q, rfl⟩

end
end AronowAudit.P001.Wave1.IrrationalRange
