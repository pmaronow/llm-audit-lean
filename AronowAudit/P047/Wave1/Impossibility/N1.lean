import AronowAudit.P047.Wave1.ImpossibilityBlueprint

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

/-- On the support of `uniform01`, the clipping in `cellLabel` is inactive. -/
private theorem cellLabel_eq_iff (M : ℕ) (j : Fin (M + 1)) (w : ℝ)
    (hw : w ∈ Set.Ioc (0 : ℝ) 1) :
    cellLabel M w = j ↔
      w ∈ Set.Ioc ((j : ℝ) / (M + 1 : ℝ)) (((j : ℝ) + 1) / (M + 1 : ℝ)) := by
  have hD : (0 : ℝ) < (M + 1 : ℝ) := by positivity
  have hceil0 : 0 < ⌈w * (M + 1 : ℝ)⌉₊ :=
    Nat.ceil_pos.mpr (mul_pos hw.1 hD)
  have hceil_le : ⌈w * (M + 1 : ℝ)⌉₊ ≤ M + 1 := by
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_add, Nat.cast_one, one_mul] using
      mul_le_mul_of_nonneg_right hw.2 hD.le
  have hclip : min M (⌈w * (M + 1 : ℝ)⌉₊ - 1) =
      ⌈w * (M + 1 : ℝ)⌉₊ - 1 := min_eq_right (by omega)
  have hlabel : cellLabel M w = j ↔ ⌈w * (M + 1 : ℝ)⌉₊ = j.val + 1 := by
    rw [Fin.ext_iff]
    change min M (⌈w * (M + 1 : ℝ)⌉₊ - 1) = j.val ↔ _
    rw [hclip]
    omega
  rw [hlabel, Nat.ceil_eq_iff (by omega : j.val + 1 ≠ 0)]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Set.mem_Ioc]
  exact and_congr (div_lt_iff₀ hD).symm (le_div_iff₀ hD).symm

/-- Each equal-length cell has its exact uniform mass, including `M = 0`. -/
theorem n1_proof : N1 := by
  classical
  intro M j
  have hD : (0 : ℝ) < (M + 1 : ℝ) := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hj1 : (j : ℝ) + 1 ≤ (M + 1 : ℝ) := by
    exact_mod_cast (show j.val + 1 ≤ M + 1 by omega)
  have hcell : {w | cellLabel M w = j} ∩ Set.Ioc (0 : ℝ) 1 =
      Set.Ioc ((j : ℝ) / (M + 1 : ℝ)) (((j : ℝ) + 1) / (M + 1 : ℝ)) := by
    ext w
    constructor
    · rintro ⟨hj, hw⟩
      exact (cellLabel_eq_iff M j w hw).mp hj
    · intro hw
      have hw01 : w ∈ Set.Ioc (0 : ℝ) 1 :=
        ⟨lt_of_le_of_lt (div_nonneg hj0 hD.le) hw.1,
          hw.2.trans ((div_le_one hD).mpr hj1)⟩
      exact ⟨(cellLabel_eq_iff M j w hw01).mpr hw, hw01⟩
  rw [uniform01, Measure.restrict_apply (show MeasurableSet {w | cellLabel M w = j} from
    (measurable_cellLabel M) (measurableSet_singleton j)), hcell, Real.volume_Ioc]
  congr 1
  field_simp [ne_of_gt hD] <;> ring

end

end AronowAudit.P047.Wave1.Impossibility
