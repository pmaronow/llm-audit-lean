import Mathlib
import SAP.P001e.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical

namespace SAP.P001e

noncomputable section

/-- Uniform treatment on [0,1], on the ordinary real Borel sample space. -/
def T91UniformDoseLaw : Measure ℝ := volume.restrict (Icc 0 1)

/-- One discrete covariate stratum. -/
def T91DiscreteCovariate (_ω : ℝ) : Unit := ()

/-- The first model has zero potential outcomes. -/
def T91ZeroPotential (_t _ω : ℝ) : ℝ := 0

/-- The second model equals t except at the null singleton {t}, where it is
zero. Every supported potential outcome is bounded between zero and one. -/
def T91DiagonalPotential (t ω : ℝ) : ℝ := if ω = t then 0 else t

/-- Consistency with the treatment assignment D(ω) = ω. -/
def T91ObservedOutcome (Y : ℝ → ℝ → ℝ) (ω : ℝ) : ℝ := Y ω ω

/-- The continuous observed conditional-mean version in both models. -/
def T91ObservedDoseVersion (_x : Unit) (_t : ℝ) : ℝ := 0

/-- The printed continuous-version standardized contrast at the selected doses. -/
def T91ObservedContrast : ℝ :=
  (∑' x : Unit, T91ObservedDoseVersion x (3 / 4) *
    probability T91UniformDoseLaw {ω | T91DiscreteCovariate ω = x}) -
  (∑' x : Unit, T91ObservedDoseVersion x (1 / 4) *
    probability T91UniformDoseLaw {ω | T91DiscreteCovariate ω = x})

/-- The weaker cylinder-process assumptions in a diagnostic example.
These do not include the independent measurable curve-state and jointly
measurable evaluation contract. The supported process
has the product/cylinder measurable structure indexed by [0,1]. Both the field
and every sample function are Borel measurable. Every supported coordinate is
bounded in [0,1], all coordinate and observed first moments exist, and the
potential conditional mean curve is continuous on the entire real line. -/
def T91RegularProcess (Y : ℝ → ℝ → ℝ) (m : ℝ → ℝ) : Prop :=
  (∀ t, Measurable (Y t) ∧ Integrable (Y t) T91UniformDoseLaw) ∧
  Measurable (fun z : ℝ × ℝ => Y z.1 z.2) ∧
  (∀ ω, Measurable (fun t => Y t ω)) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, ∀ ω, Y t ω ∈ Icc (0 : ℝ) 1) ∧
  Measurable (fun ω (t : Icc (0 : ℝ) 1) => Y t ω) ∧
  CondIndependent T91UniformDoseLaw T91DiscreteCovariate measurable_const
    (fun ω (t : Icc (0 : ℝ) 1) => Y t ω) (id : ℝ → ℝ) ∧
  Measurable (T91ObservedOutcome Y) ∧
  Integrable (T91ObservedOutcome Y) T91UniformDoseLaw ∧
  (∀ t, expectation T91UniformDoseLaw (Y t) = m t ∧
    IsConditionalMean T91UniformDoseLaw T91DiscreteCovariate (Y t)
      (fun _ : Unit => m t)) ∧
  Continuous m

/-- A diagnostic counterexample to the weaker cylinder-process reading.
The diagonal example has identical observable laws and different potential
contrasts, despite cylinder independence and continuous coordinate means.
It does not refute the registered evaluation-ready claim, whose independent
measurable curve-state contract is absent. This legacy definition is retained
for its existing diagnostic proof and is not the Challenge statement for T91. -/
def T91WholeStatement : Prop :=
  StandardBorelSpace ℝ ∧ StandardBorelSpace Unit ∧
  IsProbabilityMeasure T91UniformDoseLaw ∧ SigmaFinite T91UniformDoseLaw ∧
  NullSingletonClass T91UniformDoseLaw ∧
  Measurable (id : ℝ → ℝ) ∧ Measurable T91DiscreteCovariate ∧
  probability T91UniformDoseLaw {ω | T91DiscreteCovariate ω = ()} = 1 ∧
  T91UniformDoseLaw (Icc (0 : ℝ) 1) = 1 ∧
  (∀ᵐ ω ∂T91UniformDoseLaw, ω ∈ Icc (0 : ℝ) 1) ∧
  T91RegularProcess T91ZeroPotential (fun _ => 0) ∧
  T91RegularProcess T91DiagonalPotential (id : ℝ → ℝ) ∧
  (∀ ω, T91ObservedOutcome T91ZeroPotential ω = 0 ∧
    T91ObservedOutcome T91DiagonalPotential ω = 0) ∧
  T91UniformDoseLaw.map
      (fun ω => (T91ObservedOutcome T91ZeroPotential ω, ω, T91DiscreteCovariate ω)) =
    T91UniformDoseLaw.map
      (fun ω => (T91ObservedOutcome T91DiagonalPotential ω, ω, T91DiscreteCovariate ω)) ∧
  IsConditionalMean T91UniformDoseLaw (fun ω => (ω, T91DiscreteCovariate ω))
    (T91ObservedOutcome T91ZeroPotential) (fun _ => 0) ∧
  IsConditionalMean T91UniformDoseLaw (fun ω => (ω, T91DiscreteCovariate ω))
    (T91ObservedOutcome T91DiagonalPotential) (fun _ => 0) ∧
  IsConditionalMean (T91UniformDoseLaw.restrict {ω | T91DiscreteCovariate ω = ()})
    (id : ℝ → ℝ) (T91ObservedOutcome T91DiagonalPotential) (T91ObservedDoseVersion ()) ∧
  Continuous (T91ObservedDoseVersion ()) ∧
  (∀ d ∈ Ioo (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε →
    0 < probability T91UniformDoseLaw (Metric.ball d ε)) ∧
  ((1 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 ∧ (3 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1) ∧
  Integrable (fun ω => T91ZeroPotential (3 / 4) ω - T91ZeroPotential (1 / 4) ω)
    T91UniformDoseLaw ∧
  Integrable (fun ω => T91DiagonalPotential (3 / 4) ω - T91DiagonalPotential (1 / 4) ω)
    T91UniformDoseLaw ∧
  expectation T91UniformDoseLaw
      (fun ω => T91ZeroPotential (3 / 4) ω - T91ZeroPotential (1 / 4) ω) = 0 ∧
  expectation T91UniformDoseLaw
      (fun ω => T91DiagonalPotential (3 / 4) ω - T91DiagonalPotential (1 / 4) ω) = 1 / 2 ∧
  T91ObservedContrast = 0 ∧
  expectation T91UniformDoseLaw
      (fun ω => T91DiagonalPotential (3 / 4) ω - T91DiagonalPotential (1 / 4) ω) ≠
        T91ObservedContrast ∧
  ¬ ((fun t => expectation T91UniformDoseLaw (T91DiagonalPotential t)) =ᵐ[
    T91UniformDoseLaw.map (id : ℝ → ℝ)] T91ObservedDoseVersion ())

end
end SAP.P001e
