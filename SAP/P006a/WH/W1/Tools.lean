import SAP.P006a.Defs.WholeW1
import SAP.P006a.Bridge
import AronowAudit.P006.Wave1.Gap.GP006B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace SAP.P006a.WH.W1
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Proof adapter: put the oracle estimator outside the policies under consideration. -/
def localized {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (P : Set (C → ℝ)) : Experiment Ω C n :=
  { E with μhat := fun π ω x => if π ∈ P then E.μhat π ω x else E.μ0 x }

lemma localized_standing {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (hD : OutcomeStanding E) (P : Set (C → ℝ))
    (hL : EstimatorL1 E P) : Standing (localized E P) where
  px_probability := hD.px_probability
  means_measurable := hD.means_measurable
  means_integrable := hD.means_integrable
  law_probability := hD.law_probability
  measurable_units := hD.measurable_units
  integrable_units := by
    intro π hp i
    refine ⟨(hD.integrable_units π hp i).1, (hD.integrable_units π hp i).2, ?_⟩
    by_cases h : π ∈ P
    · simpa only [localized, ite_eq_left h] using hL π h i
    · simpa only [localized, ite_eq_right h, Function.comp_def] using
        ((hD.covariate_law π hp i).comp hD.means_measurable.1).integrable_iff.mpr
          hD.means_integrable.1
  covariate_law := hD.covariate_law
  potential_law_fixed := hD.potential_law_fixed
  iid_independent := hD.iid_independent
  iid_identical := hD.iid_identical
  conditional_means := hD.conditional_means
  bernoulli := hD.bernoulli
  ignorability := hD.ignorability

lemma localized_vector {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (P : Set (C → ℝ)) (hU : VectorUnbiased E P) :
    VectorUnbiased (localized E P) P := by
  intro π hp i
  simpa only [localized, Experiment.vectorSigma, ite_eq_left hp] using hU π hp i

lemma localized_att {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (P : Set (C → ℝ)) {π : C → ℝ} (hp : π ∈ P) :
    (localized E P).expectedATT π = E.expectedATT π := by
  simp only [Experiment.expectedATT, localized, ite_eq_left hp]
  rfl

lemma outcome_policy {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (hD : OutcomeStanding E) {π : C → ℝ} (hp : Admissible π) :
    PolicyDesign E π where
  px_probability := hD.px_probability
  means_measurable := hD.means_measurable
  means_integrable := hD.means_integrable
  law_probability := hD.law_probability π hp
  measurable_units := hD.measurable_units π hp
  integrable_units := hD.integrable_units π hp
  covariate_law := hD.covariate_law π hp
  conditional_means := hD.conditional_means π hp
  bernoulli := hD.bernoulli π hp
  ignorability := hD.ignorability π hp

lemma oracle_standing {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (hD : OutcomeStanding E) : Standing (oracleBaseline E) := by
  refine {
    px_probability := hD.px_probability
    means_measurable := hD.means_measurable
    means_integrable := hD.means_integrable
    law_probability := hD.law_probability
    measurable_units := hD.measurable_units
    integrable_units := ?_
    covariate_law := hD.covariate_law
    potential_law_fixed := hD.potential_law_fixed
    iid_independent := hD.iid_independent
    iid_identical := hD.iid_identical
    conditional_means := hD.conditional_means
    bernoulli := hD.bernoulli
    ignorability := hD.ignorability }
  intro π hp i
  exact ⟨(hD.integrable_units π hp i).1, (hD.integrable_units π hp i).2,
    ((hD.covariate_law π hp i).comp hD.means_measurable.1).integrable_iff.mpr
      hD.means_integrable.1⟩

lemma oracle_vector {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (hD : OutcomeStanding E) :
    VectorUnbiased (oracleBaseline E) {π | Admissible π} :=
  AronowAudit.P006.Wave1.T2_fid_baseline_vectorUnbiased
    (Bridge.experiment E) (Bridge.averageDesign hD)

lemma independent_vector_local {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (hD : OutcomeStanding E) (P : Set (C → ℝ))
    (hP : ∀ π ∈ P, Admissible π) (hL : EstimatorL1 E P)
    (hU : PointwiseUnbiased E P) (hI : IndependentEstimator E P) : VectorUnbiased E P := by
  have hU' : PointwiseUnbiased (localized E P) P := by
    intro π hp x
    simpa only [localized, ite_eq_left hp] using hU π hp x
  have hI' : IndependentEstimator (localized E P) P := by
    obtain ⟨A, mA, Z, f, hZ, hf⟩ := hI
    refine ⟨A, mA, Z, f, hZ, ?_⟩
    intro π hp
    simpa only [localized, ite_eq_left hp] using hf π hp
  have h := AronowAudit.P006.Wave1.T6_independent_vector
    (Bridge.experiment (localized E P)) (Bridge.standing (localized_standing E hD P hL))
    P hP hU' hI'
  intro π hp i
  simpa only [Bridge.experiment, localized, Experiment.vectorSigma, AronowAudit.P006.Experiment.vectorSigma, ite_eq_left hp] using h π hp i

lemma actual_average_local {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (hD : OutcomeStanding E) (P : Set (C → ℝ))
    (hL : EstimatorL1 E P) (hU : VectorUnbiased E P) {π : C → ℝ}
    (hp : Admissible π) (hπ : π ∈ P) :
    E.expectedATT π = E.averageObjective E.τ π := by
  have h := AronowAudit.P006.Wave1.T2_actual_averages
    (Bridge.experiment (localized E P)) (Bridge.standing (localized_standing E hD P hL)) hp
    (localized_vector E P hU π hπ)
  have hh : (localized E P).expectedATT π = E.averageObjective E.τ π := h.2.2
  exact (localized_att E P hπ).symm.trans hh

end
end SAP.P006a.WH.W1
