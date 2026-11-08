import SAP.P044.Bridge.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044.Bridge

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The optimized full-count weights are the actual exact-design marginals. -/
@[simp] theorem cliqueObservationMarginal_exact :
    SAP.P044.cliqueObservationMarginal 0 false =
      SAP.P044.marginal (fun _ : Fin 66 => (1/66 : ℚ)) SAP.P044.cliqueF := by
  funext i a
  have h := AronowAudit.P044.Wave1.clique_observation_marginal_proof 0 false i (labels a)
  change AronowAudit.P044.marginal (fun _ : Fin 66 => (1/66 : ℚ))
    AronowAudit.P044.cliqueF i (labels a) =
      AronowAudit.P044.cliqueObservationMarginal 0 false i (labels a) at h
  simpa using h.symm

/-- A finite sum and division by a constant preserve the exported integrability. -/
theorem effect_integrable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (B : Ω → Fin N → ℝ)
    (hB : ∀ i, Integrable (fun ω => B ω i) P) :
    Integrable (fun ω => SAP.P044.tau (SAP.P044.dilatedOutcomes (B ω)) .d11 .d00) P := by
  have heq : (fun ω => SAP.P044.tau (SAP.P044.dilatedOutcomes (B ω)) .d11 .d00) =
      (fun ω => (∑ i, B ω i) / N) := by
    funext ω
    exact (AronowAudit.P044.dilated_effects (B ω)).1
  rw [heq]
  exact (integrable_finsetSum Finset.univ (fun i _ => hB i)).div_const _

/-- Product evaluation transports each existing baseline second moment. -/
theorem generatedEffect_integrable {N : ℕ} (A : SAP.P044.Adjacency N) :
    Integrable (fun x => SAP.P044.tau
      (SAP.P044.dilatedOutcomes (SAP.P044.generatedBaselines A x)) .d11 .d00)
      (SAP.P044.normalPopulation N) := by
  letI : IsProbabilityMeasure SAP.P044.normalPair := by
    unfold SAP.P044.normalPair
    infer_instance
  letI : IsProbabilityMeasure AronowAudit.P044.normalPair := by
    unfold AronowAudit.P044.normalPair
    infer_instance
  apply effect_integrable
  intro i
  exact integrable_comp_eval (μ := fun _ : Fin N => SAP.P044.normalPair) (i := i)
    ((AronowAudit.P044.baseline_memLp (SAP.P044.degreeScale A i)).integrable (by norm_num))

/-- The map defining the half-normal law transports its Gaussian moment. -/
theorem halfNormal_integrable : Integrable id SAP.P044.halfNormalLaw := by
  unfold SAP.P044.halfNormalLaw
  exact (integrable_map_measure aestronglyMeasurable_id (by fun_prop)).2
    (((memLp_id_gaussianReal (μ := 0) (v := 1) 2).abs).integrable (by norm_num))

end
end SAP.P044.Bridge
