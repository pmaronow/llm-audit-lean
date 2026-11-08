import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P047

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

/-- A unit records the covariate, treatment, and two potential outcomes. -/
abbrev UnitData := ℝ × Bool × (ℝ × ℝ)

def covariate (u : UnitData) : ℝ := u.1

def arm (a : Bool) (u : UnitData) : ℝ := if u.2.1 = a then 1 else 0

def potential (a : Bool) (u : UnitData) : ℝ := if a then u.2.2.2 else u.2.2.1

/-- The observed outcome incorporates consistency. -/
def observed (u : UnitData) : ℝ :=
  arm true u * potential true u + arm false u * potential false u

abbrev covariateSigma : MeasurableSpace UnitData :=
  MeasurableSpace.comap covariate inferInstance

def armPropensity (e : ℝ → ℝ) (a : Bool) (u : UnitData) : ℝ :=
  if a then e (covariate u) else 1 - e (covariate u)

/-- Conditional factorization for every measurable integrable test of each
potential outcome; the constant test also calibrates the propensity. -/
def Ignorable (P : Measure UnitData) (e : ℝ → ℝ) : Prop :=
  ∀ (a : Bool) (f : ℝ → ℝ), Measurable f →
    Integrable (fun u => f (potential a u)) P →
    P[fun u => arm a u * f (potential a u) | covariateSigma] =ᵐ[P]
      fun u => armPropensity e a u *
        (P[fun v => f (potential a v) | covariateSigma]) u

/-- A population and its propensity, without any estimator conclusions. -/
structure CausalLaw where
  measure : Measure UnitData
  probability : IsProbabilityMeasure measure
  propensity : ℝ → ℝ
  measurable_propensity : Measurable propensity
  ignorability : Ignorable measure propensity

attribute [instance] CausalLaw.probability

/-- Common outcome and overlap bounds for the known-propensity model. -/
def BoundedOverlap (L : CausalLaw) (B ε : ℝ) : Prop :=
  0 < B ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧
    (∀ a, ∀ᵐ u ∂L.measure, |potential a u| ≤ B) ∧
    (∀ᵐ u ∂L.measure, ε ≤ L.propensity (covariate u) ∧
      L.propensity (covariate u) ≤ 1 - ε)

def score (L : CausalLaw) (u : UnitData) : ℝ :=
  arm true u * observed u / L.propensity (covariate u) -
    arm false u * observed u / (1 - L.propensity (covariate u))

def ate (L : CausalLaw) : ℝ :=
  ∫ u, potential true u - potential false u ∂L.measure

def treatedMean (L : CausalLaw) : ℝ := ∫ u, potential true u ∂L.measure

/-- Every finite sample uses the first n coordinates of this product law. -/
def sampleLaw (P : Measure UnitData) [IsProbabilityMeasure P] :
    Measure (ℕ → UnitData) := Measure.infinitePi fun _ : ℕ => P

instance sampleLaw_probability (P : Measure UnitData) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (sampleLaw P) := by unfold sampleLaw; infer_instance

def estimator (L : CausalLaw) (n : ℕ) (s : ℕ → UnitData) : ℝ :=
  (∑ i ∈ Finset.range n, score L (s i)) / n

/-- This contribution uses only the observed outcome. -/
def treatedScore (L : CausalLaw) (u : UnitData) : ℝ :=
  arm true u * observed u / L.propensity (covariate u)

def treatedEstimator (L : CausalLaw) (n : ℕ) (s : ℕ → UnitData) : ℝ :=
  (∑ i ∈ Finset.range n, treatedScore L (s i)) / n

def halfWidth (B ε α : ℝ) (n : ℕ) : ℝ :=
  B / ε * Real.sqrt (2 * Real.log (2 / α) / n)

def confidenceInterval (L : CausalLaw) (B ε α : ℝ) (n : ℕ)
    (s : ℕ → UnitData) : Set ℝ :=
  Set.Icc (estimator L n s - halfWidth B ε α n)
    (estimator L n s + halfWidth B ε α n)

/-- Endpoint subtraction, used only with a nonnegative half-width. -/
def intervalWidth (L : CausalLaw) (B ε α : ℝ) (n : ℕ)
    (s : ℕ → UnitData) : ℝ :=
  (estimator L n s + halfWidth B ε α n) -
    (estimator L n s - halfWidth B ε α n)

def treatedHalfWidth (ε α : ℝ) (n : ℕ) : ℝ :=
  1 / ε * Real.sqrt (Real.log (2 / α) / (2 * n))

/-- The one-mean component bounds only the treated outcome and propensity. -/
def TreatedMeanModel (L : CausalLaw) (ε : ℝ) : Prop :=
  0 < ε ∧ (∀ᵐ u ∂L.measure, potential true u ∈ Set.Icc 0 1) ∧
    (∀ᵐ u ∂L.measure, ε ≤ L.propensity (covariate u))

end

end SAP.P047
