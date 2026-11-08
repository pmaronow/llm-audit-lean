import SAP.P028.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028.WH.W2.P.T9_L1

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

theorem arm_integrable_of_independent
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (Z : Ω → Bool) (z : Bool)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hpos : 0 < μ.real {ω | Z ω = z})
    (hOn : IntegrableOn X {ω | Z ω = z} μ) : Integrable X μ := by
  let A : Set Ω := {ω | Z ω = z}
  let g : Bool → ℝ := fun b => if b = z then 1 else 0
  have hA : MeasurableSet A := by
    exact hZ (measurableSet_singleton z)
  have hg : Measurable g := Measurable.of_discrete
  have hYZ : IndepFun X (fun ω => g (Z ω)) μ := by
    simpa [Function.comp_def] using
      hXZ.comp measurable_id hg
  have hprod : Integrable (fun ω => X ω * g (Z ω)) μ := by
    have hi := hOn.integrable_indicator hA
    convert hi using 1
    funext ω
    by_cases hw : Z ω = z <;> simp [Set.indicator, g, hw]
  have hnot : ¬ (fun ω => g (Z ω)) =ᵐ[μ] 0 := by
    intro hzero
    have hint : (∫ ω, g (Z ω) ∂μ) = 0 := by
      simpa using integral_congr_ae hzero
    have hintA : (∫ ω, g (Z ω) ∂μ) = μ.real A := by
      convert integral_indicator_one (μ := μ) (s := A) hA using 1
      congr 1
      funext ω
      simp [g, A, Set.indicator]
    rw [hint] at hintA
    have hp : 0 < μ.real A := by simpa [A] using hpos
    linarith
  apply hYZ.integrable_left_of_integrable_op (fun x y : ℝ => x * y) 1
    (by norm_num)
    (by
      intro x y
      simp [enorm_mul])
    hprod hX.aestronglyMeasurable (hg.comp hZ).aestronglyMeasurable hnot

end SAP.P028.WH.W2.P.T9_L1

theorem SAP.P028.WH.W2.T9_L1_proof : SAP.P028.WH.W2.T9_L1 := by
  intro Ω _ μ _ X Z z hX hZ hXZ hpos hOn
  exact SAP.P028.WH.W2.P.T9_L1.arm_integrable_of_independent
    μ X Z z hX hZ hXZ hpos hOn
