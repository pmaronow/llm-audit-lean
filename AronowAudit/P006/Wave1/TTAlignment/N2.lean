import AronowAudit.P006.Wave1.TTAlignment.N1

set_option autoImplicit false
namespace AronowAudit.P006.Wave1.TTAlignment
open AronowAudit.P006 AronowAudit.P006.Wave1.BinaryExperiment MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section

theorem n2_proof : N2 := by
  classical
  intro _h1 h2 π hπ
  constructor
  · unfold Experiment.expectedTT Experiment.expectedWeightedTT
    change (∫ ω, wWeightedTT (fun x => estA (ω 0).1 x) (fun _ => 1)
      (fun i => (ω i).1) (fun i => (ω i).2)
      (fun i => if (ω i).2 then (1 / 2 : ℝ) else 0)
      ∂(Measure.pi fun _ : Fin 1 => unitLaw π)) = _
    rw [h2 1 π hπ, sum_one_state]
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.prod_univ_one,
      wWeightedTT, Fin.sum_univ_one, bit, estA, coinMass]
    <;> ring
  · unfold Experiment.V
    change (∫ ω, (if (ω 0).2 then (1 / 2 : ℝ) else 0) - 0
      ∂(Measure.pi fun _ : Fin 1 => unitLaw π)) = _
    rw [h2 1 π hπ, sum_one_state]
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.prod_univ_one, coinMass]
    <;> ring

end
end AronowAudit.P006.Wave1.TTAlignment
