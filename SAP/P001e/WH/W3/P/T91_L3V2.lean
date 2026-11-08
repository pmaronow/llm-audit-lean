import SAP.P001e.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical


theorem SAP.P001e.WH.W3.T91_L3V2_proof : SAP.P001e.WH.W3.T91_L3V2 := by
  classical
  intro Ω I _ μ _ Y c D hY hD hae
  let U : Ω → I → ℝ := fun ω t => Y t ω
  have hm : Measurable U := Measurable.of_eval hY
  have hind : IndepFun U D μ :=
    (indepFun_const_left (μ := μ) c D).process_congr_left (fun t => (hae t).symm)
  intro A B hA hB
  simp only [MeasurableSpace.comap_const, condExp_bot]
  have indicator_integral (S : Set Ω) (hS : MeasurableSet S) :
      (∫ ω, (if ω ∈ S then (1 : ℝ) else 0) ∂μ) = (μ S).toReal := by
    change (∫ ω, S.indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
    rw [integral_indicator hS]
    simp [measureReal_def]
  have eAB : (∫ ω, (if U ω ∈ A ∧ D ω ∈ B then (1 : ℝ) else 0) ∂μ) =
      (μ (U ⁻¹' A ∩ D ⁻¹' B)).toReal := by
    simpa only [Set.mem_inter_iff, Set.mem_preimage] using
      indicator_integral _ ((hm hA).inter (hD hB))
  have eA : (∫ ω, (if U ω ∈ A then (1 : ℝ) else 0) ∂μ) =
      (μ (U ⁻¹' A)).toReal := indicator_integral _ (hm hA)
  have eB : (∫ ω, (if D ω ∈ B then (1 : ℝ) else 0) ∂μ) =
      (μ (D ⁻¹' B)).toReal := indicator_integral _ (hD hB)
  apply ae_of_all
  intro ω
  change (∫ ξ, (if U ξ ∈ A ∧ D ξ ∈ B then (1 : ℝ) else 0) ∂μ) =
    (∫ ξ, (if U ξ ∈ A then (1 : ℝ) else 0) ∂μ) *
      (∫ ξ, (if D ξ ∈ B then (1 : ℝ) else 0) ∂μ)
  rw [eAB, eA, eB]
  simpa only [ENNReal.toReal_mul] using
    congrArg ENNReal.toReal (hind.measure_inter_preimage_eq_mul A B hA hB)

