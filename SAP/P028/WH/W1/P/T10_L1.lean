import SAP.P028.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028.WH.W1.P.T10_L1

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

open Classical

theorem arm_indicator_measurable
    {Ω : Type} [MeasurableSpace Ω] {Z : Ω → Bool} {z : Bool}
    (hZ : Measurable Z) : MeasurableSet {ω | Z ω = z} := by
  exact hZ (measurableSet_singleton z)

end SAP.P028.WH.W1.P.T10_L1

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem SAP.P028.WH.W1.T10_L1_proof : SAP.P028.WH.W1.T10_L1 := by
  intro Ω _ μ hμ X Z hX hZ hXZ z hpos hOn
  let A : Set Ω := {ω | Z ω = z}
  let ψ : Bool → ℝ := fun b => if b = z then 1 else 0
  let Y : Ω → ℝ := ψ ∘ Z
  have hposA : 0 < μ.real A := by simpa [A] using hpos
  have hA : MeasurableSet A := SAP.P028.WH.W1.P.T10_L1.arm_indicator_measurable hZ
  have hψ : Measurable ψ := by
    fun_prop
  have hY : Measurable Y := hψ.comp hZ
  have hXY : ProbabilityTheory.IndepFun X Y μ := by
    simpa [Y] using hXZ.comp measurable_id hψ
  have hprod : Integrable (fun ω => X ω * Y ω) μ := by
    have hi := hOn.integrable_indicator hA
    have heq : (fun ω => X ω * Y ω) = A.indicator X := by
      funext ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]
        have hZω : Z ω = z := by simpa [A] using hω
        simp [Y, ψ, hZω]
      · rw [Set.indicator_of_notMem hω]
        have hZω : Z ω ≠ z := by simpa [A] using hω
        simp [Y, ψ, hZω]
    exact heq.symm ▸ hi
  have hYzero : ¬ Y =ᵐ[μ] 0 := by
    intro hy
    have hnull : μ A = 0 := by
      apply (measure_eq_zero_iff_ae_notMem).2
      filter_upwards [hy] with ω hω
      intro hωA
      change Z ω = z at hωA
      have hval : Y ω = 1 := by
        simp [Y, ψ, hωA]
      rw [hω] at hval
      norm_num at hval
    have hpos' : μ A ≠ 0 := (measureReal_ne_zero_iff).1 (ne_of_gt hposA)
    exact hpos' hnull
  exact hXY.integrable_left_of_integrable_op
    (fun x y : ℝ => x * y) 1 (by norm_num)
    (by
      intro x y
      simp [enorm_mul])
    hprod hX.aestronglyMeasurable hY.aestronglyMeasurable hYzero
