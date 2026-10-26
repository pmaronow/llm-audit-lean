import AronowAudit.P017.Wave1.Gap.FidP017

/-! The universally quantified empirical-data statement of P017-T9 and its negation. -/

set_option autoImplicit false

namespace AronowAudit.P017.Wave1

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

namespace FidP017Contracts


/-- P017-T9, Proposition 1, PDF p. 2, under its full empirical-data universal closure.
Conventions the paper leaves implicit:
* All population, observed-record and sampling types (in Lean's universe zero),
  their measurable spaces, and their genuine probability laws are quantified.
  The sampling law and measurable full-data sample map are arbitrary: no IID,
  treatment design, or particular observation space is imposed.
* Effects are real, measurable and integrable. Support is closed support of
  their law. Standing Assumption 1 is retained, `0 < effectRadius G τ`; the radius
  may be infinite, in which case Definition 2 (`clipTarget`) is the identity.
* Positive sample sizes use indices `0,...,n-1`. The observed empirical law is
  exactly the equally weighted empirical measure of `O (data s i)`. "Using F_n"
  means pointwise factorization through that law by an arbitrary functional `H`;
  the known sample size may also enter `H`. No integral form is imposed on `H`.
* Definition 1 means `RootNNormal`, convergence in distribution to a Gaussian
  with strictly positive finite variance. No same-space normal coupling is required.
* "Across all realizations" means every sample point at every positive size,
  rather than an almost-sure or asymptotic assertion. `Representable` allows a
  weight chosen separately at each realization, on all full-data variables:
  measurable, pointwise nonnegative, integrable, with positive expectation and
  integrable weighted effect. Thus its ratio has a finite positive denominator.
  There is no boundedness or measurable-selection requirement on these weights.
-/
def printedContract_P017_T9 : Prop :=
  ∀ {Ω D Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (_hτm : Measurable τ) (_hτi : Integrable τ G)
    (_hc : 0 < effectRadius G τ) (O : Ω → D) (_hOm : Measurable O)
    (P : Measure Ξ) [IsProbabilityMeasure P]
    (data : Ξ → ℕ → Ω) (_hdata : Measurable data)
    (hat : ℕ → Ξ → ℝ) (H : ℕ → Measure D → ℝ)
    (_hfactor : ∀ n : ℕ, 1 ≤ n → ∀ s : Ξ,
      hat n s = H n (empiricalObserved O n (data s)))
    (_hh : RootNNormal P hat (populationMean G τ)),
    ∀ n : ℕ, 1 ≤ n → ∀ s : Ξ,
      Representable G τ
        (clipTarget (populationMean G τ) (effectRadius G τ) (hat n s))

end FidP017Contracts

/-- The empirical IPW certificate negates the entire universally closed
printed P017-T9 contract, including its empirical-statistic premise. -/
theorem proposition1_printed_empirical_counterexample_printed_negation :
    ¬ FidP017Contracts.printedContract_P017_T9 := by
  intro h
  rcases proposition1_printed_empirical_counterexample with
    ⟨hτm, hτi, _, _, _, hc, hOm, hnormal, hfactor, hbad⟩
  have hclaims := h ipwPopulation ipwEffect hτm hτi hc ipwObserved hOm
    (iidSamples ipwPopulation) (fun s => s) measurable_id (sampleMean ipwSummand)
    (fun _ F => ∫ z : ℝ × ℝ, (2 * z.1 * z.2 - 2 * (1 - z.1) * z.2) ∂F)
    hfactor hnormal
  let s : ℕ → ℝ × (ℝ × ℝ) := fun _ => (1 / 2, (-1, 0))
  have hs : s ∈ ipwBadEvent (-1) 1 := by
    intro i hi
    exact ⟨rfl, rfl⟩
  have hnot := ((hbad 1 (by norm_num)).2.2.2 s hs).2.2.2
  exact hnot (hclaims 1 (by norm_num) s)

namespace FidP017Contracts


end FidP017Contracts

end

end AronowAudit.P017.Wave1
