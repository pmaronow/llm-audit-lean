import Mathlib
import SAP.P047.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace SAP.P047

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

/-- Forget the propensity and identifying assumptions, retaining the full
population probability law on covariate, treatment and potential outcomes. -/
def populationProbability (L : CausalLaw) : ProbabilityMeasure UnitData :=
  ⟨L.measure, L.probability⟩

/-- The unrestricted binary causal model, regarded as a class of probability
laws. Larger models need not carry a propensity or identifying assumptions. -/
def unknownPopulations : Set (ProbabilityMeasure UnitData) :=
  {P | ∃ L : CausalLaw, UnknownModel L ∧ populationProbability L = P}

/-- The mean effect of a population law. The whole statement explicitly
requires integrability wherever this quantity is used. -/
def populationEffect (P : ProbabilityMeasure UnitData) : ℝ :=
  ∫ u, potential true u - potential false u ∂(P : Measure UnitData)

/-- Supremum of sample-and-independent-seed event probabilities over a model.
All probabilities lie in [0,1]; inserting zero is neutral for a nonempty model. -/
def modelEventSup {R : Type u} [MeasurableSpace R] (M : Set (ProbabilityMeasure UnitData))
    (Q : Measure R) [IsProbabilityMeasure Q]
    (event : ProbabilityMeasure UnitData → Set ((ℕ → UnitData) × R)) : ℝ :=
  sSup (insert (0 : ℝ) {p | ∃ P ∈ M,
    p = ((sampleLaw (P : Measure UnitData)).prod Q).real (event P)})

/-- Infimum of sample-and-independent-seed event probabilities over a model.
Inserting one is neutral for a nonempty model. -/
def modelEventInf {R : Type u} [MeasurableSpace R] (M : Set (ProbabilityMeasure UnitData))
    (Q : Measure R) [IsProbabilityMeasure Q]
    (event : ProbabilityMeasure UnitData → Set ((ℕ → UnitData) × R)) : ℝ :=
  sInf (insert (1 : ℝ) {p | ∃ P ∈ M,
    p = ((sampleLaw (P : Measure UnitData)).prod Q).real (event P)})

/-- Worst-case weak estimation error over any containing model. -/
def wholeRisk {R : Type u} [MeasurableSpace R] (M : Set (ProbabilityMeasure UnitData))
    (Q : Measure R) [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ) (n : ℕ) (η : ℝ) : ℝ :=
  modelEventSup M Q (fun P =>
    {z | η ≤ |E n (observedSample n z.1, z.2) - populationEffect P|})

/-- Worst-case strict estimation error over any containing model. -/
def wholeStrictRisk {R : Type u} [MeasurableSpace R] (M : Set (ProbabilityMeasure UnitData))
    (Q : Measure R) [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ) (n : ℕ) (η : ℝ) : ℝ :=
  modelEventSup M Q (fun P =>
    {z | η < |E n (observedSample n z.1, z.2) - populationEffect P|})

/-- Worst-case coverage of intervals with measurable extended-real endpoints. -/
def wholeCoverage {R : Type u} [MeasurableSpace R] (M : Set (ProbabilityMeasure UnitData))
    (Q : Measure R) [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal) (n : ℕ) : ℝ :=
  modelEventInf M Q (fun P =>
    {z | lo n (observedSample n z.1, z.2) ≤ (populationEffect P : EReal) ∧
      (populationEffect P : EReal) ≤ hi n (observedSample n z.1, z.2)})

/-- Worst-case probability that interval width exceeds 1/6. The comparison
lo + 1/6 < hi agrees with ordinary width for finite ordered endpoints and
also handles unbounded or empty intervals without undefined subtraction. -/
def wholeWidthRisk {R : Type u} [MeasurableSpace R] (M : Set (ProbabilityMeasure UnitData))
    (Q : Measure R) [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal) (n : ℕ) : ℝ :=
  modelEventSup M Q (fun _ =>
    {z | lo n (observedSample n z.1, z.2) + ((1 / 6 : ℝ) : EReal) <
      hi n (observedSample n z.1, z.2)})

/-- P047-T3; Section 1, second bullet, pp. 85–86 (PDF pp. 2–3).
The usual measure-theoretic conditions are assumed. With unknown propensity,
uniform covariate, binary potential outcomes, joint ignorability and common
overlap [1/4,3/4], every sample-only estimator has worst-case error at least
1/2 at tolerance 1/12 for every positive sample size, and uniform consistency
is impossible. The concrete baseline S belongs to this model, has propensity
1/2 and effect 1/2. For every asymptotically honest interval at level 1-alpha,
0 < alpha < 1/2, its probability under S of width greater than 1/6 has limit
inferior at least 1-2*alpha > 0. Width therefore fails to shrink in probability
under S and uniformly over the model. All conclusions hold for every
containing class of probability laws in which the mean effect exists,
without assumptions on its additional laws. They allow an arbitrary
independent random seed and measurable extended-real interval endpoints.
Thus leaving both nuisance functions unrestricted precludes the two desired
properties; no sufficiency or separate mathematical notion of testability
is asserted. -/
def T3WholeStatement : Prop :=
  (∃ S : CausalLaw,
    S.measure = baselineLaw ∧ S.propensity = (fun _ => (1 / 2 : ℝ)) ∧
      UnknownModel S ∧ ate S = 1 / 2) ∧
  ∀ M : Set (ProbabilityMeasure UnitData), unknownPopulations ⊆ M →
    (∀ P ∈ M, Integrable (fun u => potential true u - potential false u)
      (P : Measure UnitData)) →
    ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q],
      (∀ E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ,
        (∀ n, Measurable (E n)) →
          (∀ n : ℕ, 1 ≤ n → (1 / 2 : ℝ) ≤ wholeRisk M Q E n (1 / 12)) ∧
          (∃ η : ℝ, 0 < η ∧
            0 < Filter.limsup (fun n => wholeStrictRisk M Q E n η) atTop)) ∧
      (∀ lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal,
        (∀ n, Measurable (lo n)) → (∀ n, Measurable (hi n)) →
        ∀ α : ℝ, 0 < α → α < 1 / 2 →
          1 - α ≤ Filter.liminf (wholeCoverage M Q lo hi) atTop →
          (1 - 2 * α ≤ Filter.liminf (widthProb Q lo hi) atTop) ∧
          (1 - 2 * α ≤ Filter.liminf (wholeWidthRisk M Q lo hi) atTop) ∧
          0 < 1 - 2 * α ∧
          ¬ Tendsto (widthProb Q lo hi) atTop (𝓝 0) ∧
          ¬ Tendsto (wholeWidthRisk M Q lo hi) atTop (𝓝 0))

end

end SAP.P047
