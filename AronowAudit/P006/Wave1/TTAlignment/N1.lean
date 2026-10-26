import AronowAudit.P006.Wave1.TTAlignmentBlueprint

set_option autoImplicit false
namespace AronowAudit.P006.Wave1.TTAlignment
open AronowAudit.P006 AronowAudit.P006.Wave1.BinaryExperiment MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section

lemma sum_one_state (f : (Fin 1 → Bool × Bool) → ℝ) :
    (∑ ω, f ω) = ∑ a : Bool × Bool, f (fun _ => a) := by
  classical
  exact (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Bool × Bool)).symm
    (fun a => f (fun _ => a)) f (fun _ => rfl)).symm

theorem n1_proof : N1 := by
  classical
  intro h1 h2 π hπ x
  haveI : IsProbabilityMeasure (unitLaw π) := (h1 π hπ).1
  haveI : IsProbabilityMeasure (E27.law π) := by dsimp [E27, binExp]; infer_instance
  refine ⟨Integrable.of_finite, ?_⟩
  change (∫ ω, estA (ω 0).1 x ∂(Measure.pi fun _ : Fin 1 => unitLaw π)) = 0
  rw [h2 1 π hπ, sum_one_state]
  cases x <;>
    simp [Fintype.sum_prod_type, Fintype.sum_bool, Fin.prod_univ_one, estA, coinMass] <;> ring

end
end AronowAudit.P006.Wave1.TTAlignment
