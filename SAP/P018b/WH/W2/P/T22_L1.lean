import SAP.P018b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P018b.WH.W2.P.T22_L1

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem error_measurable {N T : ℕ} (d : Dyad N) (t : Fin T) :
    Measurable (fun ω : SimulationIndex N T → ℝ => simulationError ω d t) := by
  exact (Finset.measurable_sum (members d) (fun i _ =>
    measurable_pi_apply (Sum.inr (Sum.inl i) : SimulationIndex N T))).add
    (measurable_pi_apply (Sum.inr (Sum.inr (d,t)) : SimulationIndex N T))

private theorem error_memLp_canonical {N T : ℕ} (d : Dyad N) (t : Fin T) :
    MemLp (fun ω : SimulationIndex N T → ℝ => simulationError ω d t) 2
      (simulationLaw N T) := by
  let ν := simulationLaw N T
  have hcoord (a : SimulationIndex N T) : MemLp (fun ω : SimulationIndex N T → ℝ => ω a) 2 ν := by
    have hstd : MemLp id 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
    simpa [ν, simulationLaw, Function.comp_def] using
      hstd.comp_measurePreserving
        (measurePreserving_eval (μ := fun _ : SimulationIndex N T => gaussianReal 0 1) a)
  have hsum : MemLp (fun ω : SimulationIndex N T → ℝ =>
      ∑ i ∈ members d, ω (Sum.inr (Sum.inl i))) 2 ν := by
    exact memLp_finsetSum (members d) (fun i _ => hcoord (Sum.inr (Sum.inl i)))
  change MemLp (fun ω : SimulationIndex N T → ℝ =>
      (∑ i ∈ members d, ω (Sum.inr (Sum.inl i))) +
        ω (Sum.inr (Sum.inr (d,t)))) 2 ν
  exact hsum.add (hcoord (Sum.inr (Sum.inr (d,t))))

end SAP.P018b.WH.W2.P.T22_L1

open MeasureTheory ProbabilityTheory

theorem SAP.P018b.WH.W2.T22_L1_proof : SAP.P018b.WH.W2.T22_L1 := by
  intro N T hN hT Ω mΩ μ hμ Z hZ hLaw
  let ν := simulationLaw N T
  letI : IsProbabilityMeasure ν := by
    dsimp [ν, simulationLaw]
    infer_instance
  let errVec : (SimulationIndex N T → ℝ) → (Dyad N × Fin T) → ℝ :=
    fun ξ dt => simulationError ξ dt.1 dt.2
  let covVec : (SimulationIndex N T → ℝ) → Fin N → ℝ :=
    fun ξ i => simulationX ξ i
  have herr : Measurable errVec := by
    exact Measurable.of_eval (fun dt =>
      SAP.P018b.WH.W2.P.T22_L1.error_measurable dt.1 dt.2)
  have hcov : Measurable covVec := by
    exact Measurable.of_eval (fun i => measurable_pi_apply (Sum.inl i))
  have hpair : Measurable (fun ξ => (errVec ξ, covVec ξ)) := herr.prodMk hcov
  have hcompErr : μ.map (fun ω => errVec (Z ω)) = ν.map errVec := by
    calc
      μ.map (fun ω => errVec (Z ω)) = μ.map (errVec ∘ Z) := rfl
      _ = (μ.map Z).map errVec := (MeasureTheory.Measure.map_map herr hZ).symm
      _ = ν.map errVec := by rw [hLaw.map_eq]
  have hcompCov : μ.map (fun ω => covVec (Z ω)) = ν.map covVec := by
    calc
      μ.map (fun ω => covVec (Z ω)) = μ.map (covVec ∘ Z) := rfl
      _ = (μ.map Z).map covVec := (MeasureTheory.Measure.map_map hcov hZ).symm
      _ = ν.map covVec := by rw [hLaw.map_eq]
  have hcompPair : μ.map (fun ω => (errVec (Z ω), covVec (Z ω))) =
      ν.map (fun ξ => (errVec ξ, covVec ξ)) := by
    calc
      μ.map (fun ω => (errVec (Z ω), covVec (Z ω))) =
          μ.map ((fun ξ => (errVec ξ, covVec ξ)) ∘ Z) := rfl
      _ = (μ.map Z).map (fun ξ => (errVec ξ, covVec ξ)) :=
        (MeasureTheory.Measure.map_map hpair hZ).symm
      _ = ν.map (fun ξ => (errVec ξ, covVec ξ)) := by rw [hLaw.map_eq]
  have hdonor := AronowAudit.P018.Wave1.simulation_design_correction_proof N T hN hT
  have hcanInd :
      ν.map (fun ξ => (errVec ξ, covVec ξ)) = (ν.map errVec).prod (ν.map covVec) := by
    exact hdonor.2.1.map_prod_eq_prod_map_map herr.aemeasurable hcov.aemeasurable
  have hFacts : simulationErrorFacts μ Z := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change IsGaussian (μ.map (fun ω => errVec (Z ω)))
      rw [hcompErr]
      exact hdonor.1
    · apply (indepFun_iff_map_prod_eq_prod_map_map
        (herr.comp hZ).aemeasurable (hcov.comp hZ).aemeasurable).2
      change μ.map (fun ω => (errVec (Z ω), covVec (Z ω))) =
        (μ.map (fun ω => errVec (Z ω))).prod (μ.map (fun ω => covVec (Z ω)))
      rw [hcompPair, hcanInd, hcompErr, hcompCov]
    · intro d t
      have hcanonical := SAP.P018b.WH.W2.P.T22_L1.error_memLp_canonical d t
      exact hLaw.memLp_comp hcanonical
    · intro d t
      have hmean := hLaw.integral_comp
        (SAP.P018b.WH.W2.P.T22_L1.error_measurable d t).aestronglyMeasurable
      simpa [Function.comp_def] using hmean.trans (hdonor.2.2.1 d t)
    · intro d f t u
      have hcovariance := hLaw.covariance_fun_comp
        (SAP.P018b.WH.W2.P.T22_L1.error_measurable d t).aemeasurable
        (SAP.P018b.WH.W2.P.T22_L1.error_measurable f u).aemeasurable
      calc
        ProbabilityTheory.covariance (fun ω => simulationError (Z ω) d t)
            (fun ω => simulationError (Z ω) f u) μ =
          ProbabilityTheory.covariance (fun ξ => simulationError ξ d t)
            (fun ξ => simulationError ξ f u) ν := hcovariance
        _ = ((members d ∩ members f).card : ℝ) + (if d = f ∧ t = u then 1 else 0) := by
          convert hdonor.2.2.2.1 d f t u using 1 <;> congr 1
  exact hFacts
