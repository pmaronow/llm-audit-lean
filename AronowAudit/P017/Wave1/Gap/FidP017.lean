import AronowAudit.P017.Wave1.Gap.GLP017B1

/-! An empirical-data certificate refuting printed Proposition 1. -/

set_option autoImplicit false

namespace AronowAudit.P017.Wave1

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

theorem p017t9_observed_measurable : Measurable ipwObserved := by
  unfold ipwObserved ipwY0 ipwY1
  fun_prop

/-- The IPW mean is a functional of the observed empirical law on every sample. -/
theorem p017t9_empirical_integral (n : ℕ) (s : ℕ → ℝ × (ℝ × ℝ)) :
    sampleMean ipwSummand n s =
      ∫ z : ℝ × ℝ, (2 * z.1 * z.2 - 2 * (1 - z.1) * z.2)
        ∂(empiricalObserved ipwObserved n s) := by
  unfold empiricalObserved
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_natCast, smul_eq_mul, sampleMean, ipwSummand]
    ring
  · intro i hi
    exact integrable_dirac (by simp)

theorem p017t9_bad_event_measurable (b : ℝ) (n : ℕ) :
    MeasurableSet (ipwBadEvent b n) := by
  have heq : ipwBadEvent b n =
      ⋂ i ∈ Finset.range n, {s : ℕ → ℝ × (ℝ × ℝ) |
        (s i).2.1 = b ∧ (s i).2.2 = 0} := by
    ext s
    simp [ipwBadEvent]
  rw [heq]
  apply Finset.measurableSet_biInter
  intro i hi
  exact (measurableSet_eq_fun (measurable_pi_apply i).snd.fst measurable_const).inter
    (measurableSet_eq_fun (measurable_pi_apply i).snd.snd measurable_const)

theorem p017t9_rootNNormal :
    RootNNormal (iidSamples ipwPopulation) (sampleMean ipwSummand)
      (populationMean ipwPopulation ipwEffect) := by
  refine ⟨(53 / 12 : ℝ≥0), by norm_num, ?_⟩
  rw [PropositionOne.n1_proof.2.2]
  exact t1_clt

theorem proposition1_printed_empirical_counterexample :
    Measurable ipwEffect ∧
    Integrable ipwEffect ipwPopulation ∧
    populationMean ipwPopulation ipwEffect = 1 / 2 ∧
    effectSupport ipwPopulation ipwEffect = Icc (0 : ℝ) 1 ∧
    effectRadius ipwPopulation ipwEffect = (1 / 2 : ℝ≥0∞) ∧
    0 < effectRadius ipwPopulation ipwEffect ∧
    Measurable ipwObserved ∧
    RootNNormal (iidSamples ipwPopulation) (sampleMean ipwSummand)
      (populationMean ipwPopulation ipwEffect) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ s : ℕ → ℝ × (ℝ × ℝ),
      sampleMean ipwSummand n s =
        ∫ z : ℝ × ℝ, (2 * z.1 * z.2 - 2 * (1 - z.1) * z.2)
          ∂(empiricalObserved ipwObserved n s)) ∧
    (∀ n : ℕ, 1 ≤ n →
      MeasurableSet (ipwBadEvent (-1) n) ∧
      pr (iidSamples ipwPopulation) (ipwBadEvent (-1) n) = (1 / 4 : ℝ) ^ n ∧
      0 < pr (iidSamples ipwPopulation) (ipwBadEvent (-1) n) ∧
      (∀ s ∈ ipwBadEvent (-1) n,
        empiricalObserved ipwObserved n s = Measure.dirac ((0 : ℝ), (-1 : ℝ)) ∧
        sampleMean ipwSummand n s = 2 ∧
        clipTarget (populationMean ipwPopulation ipwEffect)
          (effectRadius ipwPopulation ipwEffect) (sampleMean ipwSummand n s) = 1 ∧
        ¬ Representable ipwPopulation ipwEffect
          (clipTarget (populationMean ipwPopulation ipwEffect)
            (effectRadius ipwPopulation ipwEffect) (sampleMean ipwSummand n s)))) := by
  rcases uniform_ipw_counterexample_proof with
    ⟨hMeas, hInt, hMean, hSupport, hRadius, hRadiusPos,
      _, _, _, _, _, _, _, _, _, hEvents⟩
  refine ⟨hMeas, hInt, hMean, hSupport, hRadius, hRadiusPos,
    p017t9_observed_measurable, p017t9_rootNNormal,
    (fun n _ s => p017t9_empirical_integral n s), ?_⟩
  intro n hn
  rcases hEvents n hn with ⟨hProb, _, hPos, _, hUpper, _⟩
  refine ⟨p017t9_bad_event_measurable (-1) n, hProb, hProb.symm ▸ hPos, ?_⟩
  intro s hs
  rcases hUpper s hs with ⟨_, hEstimate, hClip, hEmpirical, hNotRepresentable⟩
  exact ⟨hEmpirical, hEstimate, hClip, hNotRepresentable⟩

end

end AronowAudit.P017.Wave1
