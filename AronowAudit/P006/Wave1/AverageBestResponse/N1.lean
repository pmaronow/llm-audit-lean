import AronowAudit.P006.Wave1.AverageBestResponseBlueprint

set_option autoImplicit false
namespace AronowAudit.P006.Wave1.AverageBestResponse
open AronowAudit.P006 AronowAudit.P006.Wave1.BinaryExperiment MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section

lemma sum_two_states (f : (Fin 2 → Bool × Bool) → ℝ) :
    (∑ ω, f ω) = ∑ a : Bool × Bool, ∑ b : Bool × Bool, f ![a,b] := by
  classical
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (finTwoArrowEquiv (Bool × Bool)).symm
      (fun p => f ![p.1,p.2]) f (fun _ => rfl)).symm

theorem n1_proof : N1 := by
  classical
  intro _h1 h2 π hπ
  have hATO : E26.expectedATO π = rewardE001 (π false, π true) := by
    unfold Experiment.expectedATO
    change (∫ ω, wATO (fun i => (ω i).2)
      (fun i => if (ω i).2 then effectE001 (ω i).1 else 0)
      ∂(Measure.pi fun _ : Fin 2 => unitLaw π)) = _
    rw [h2 2 π hπ, sum_two_states, rewardE001_formula]
    -- This is the explicit sixteen-state calculation, including the empty branch.
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      wATO, treatedCount, Fin.sum_univ_two, bit, coinMass, effectE001,
      Bool.false_eq_true, ↓reduceIte]
    norm_num
    ring
  have hATT : E26.expectedATT π = E26.expectedATO π := by
    unfold Experiment.expectedATT Experiment.expectedATO
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω =>
      wATT_zero (fun i => E26.X i ω) (fun i => E26.T π i ω) (E26.observed π ω))
  exact ⟨hATO, hATT.trans hATO⟩

end
end AronowAudit.P006.Wave1.AverageBestResponse
