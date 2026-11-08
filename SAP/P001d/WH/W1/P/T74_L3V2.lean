import SAP.P001d.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W1.P.T74_L3V2

end SAP.P001d.WH.W1.P.T74_L3V2

theorem SAP.P001d.WH.W1.T74_L3V2_proof : SAP.P001d.WH.W1.T74_L3V2 := by
  intro Ω _ μ _ K X Y hX hY β s hs hmodel
  classical
  let v : ℝ≥0 := ⟨s ^ 2, sq_nonneg _⟩
  let m : (Fin (K + 1) → ℝ) → ℝ := wholeLinearMean β
  haveI : IsProbabilityMeasure (gaussianReal (0 : ℝ) v) := inferInstance
  have hT : Measurable (fun xy : (Fin (K + 1) → ℝ) × ℝ =>
      (xy.1, m xy.1 + xy.2)) := by
    have hm : Measurable m := by
      change Measurable (fun x : Fin (K + 1) → ℝ => ∑ k, x k * β k)
      exact Finset.measurable_sum _ (by
        intro k hk
        exact (measurable_pi_apply k).mul_const _)
    fun_prop
  have hshift (x : Fin (K + 1) → ℝ) (B : Set ℝ) (hB : MeasurableSet B) :
      (gaussianReal (0 : ℝ) v) ((fun z => m x + z) ⁻¹' B) =
        (wholeNormalKernel β s x) B := by
    calc
      (gaussianReal (0 : ℝ) v) ((fun z => m x + z) ⁻¹' B) =
          ((gaussianReal (0 : ℝ) v).map (fun z => m x + z)) B := by
        rw [Measure.map_apply (by fun_prop) hB]
      _ = (wholeNormalKernel β s x) B := by
        rw [show (fun z : ℝ => m x + z) = (fun z => z + m x) from
          funext fun z => add_comm _ _]
        rw [gaussianReal_map_add_const]
        simp [wholeNormalKernel, m, v]
  apply Measure.ext_prod
  intro A B hA hB
  calc
    (μ.map (fun ω => (X ω, Y ω))) (A ×ˢ B) =
        μ {ω | X ω ∈ A ∧ Y ω ∈ B} := by
      rw [Measure.map_apply (hX.prod hY) (hA.prod hB)]
      rfl
    _ = ∫⁻ x in A, wholeNormalKernel β s x B ∂(μ.map X) :=
      hmodel.2.2 A B hA hB
    _ = ((μ.map X).prod (gaussianReal 0 v)).map
        (fun xy => (xy.1, wholeLinearMean β xy.1 + xy.2)) (A ×ˢ B) := by
      rw [Measure.map_apply hT (hA.prod hB)]
      rw [Measure.prod_apply ((hA.prod hB).preimage hT)]
      change ∫⁻ x in A, wholeNormalKernel β s x B ∂(μ.map X) =
        ∫⁻ x, (gaussianReal (0 : ℝ) v)
          {z | x ∈ A ∧ m x + z ∈ B} ∂(μ.map X)
      symm
      calc
        ∫⁻ x, (gaussianReal (0 : ℝ) v) {z | x ∈ A ∧ m x + z ∈ B} ∂(μ.map X) =
            ∫⁻ x, A.indicator (fun x => wholeNormalKernel β s x B) x ∂(μ.map X) := by
          apply lintegral_congr
          intro x
          by_cases hx : x ∈ A
          · have hsets : {z : ℝ | x ∈ A ∧ m x + z ∈ B} =
                (fun z => m x + z) ⁻¹' B := by
              ext z
              simp [hx]
            rw [hsets]
            simpa [hx] using hshift x B hB
          · simp [hx]
        _ = ∫⁻ x in A, wholeNormalKernel β s x B ∂(μ.map X) :=
          lintegral_indicator hA _
