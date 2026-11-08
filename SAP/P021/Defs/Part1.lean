import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P021

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Joint state space for bounded outcome, degree and binary sample membership.
The index `k : Fin K` denotes the numerical degree `k.val + 1`. -/
abbrev RDSState (B : ℝ) (K : ℕ) := Set.Icc (-B) B × (Fin K × Bool)

def outcome {B : ℝ} {K : ℕ} (x : RDSState B K) : ℝ := x.1.val

def degreeValue {K : ℕ} (k : Fin K) : ℝ := (k.val : ℝ) + 1

def sampleIndicator {B : ℝ} {K : ℕ} (x : RDSState B K) : ℝ :=
  if x.2.2 then 1 else 0

def degreeCell {B : ℝ} {K : ℕ} (k : Fin K) (x : RDSState B K) : ℝ :=
  if x.2.1 = k then 1 else 0

def sampleCell {B : ℝ} {K : ℕ} (k : Fin K) (x : RDSState B K) : ℝ :=
  degreeCell k x * sampleIndicator x

variable {B : ℝ} {K : ℕ}

/-- The population outcome mean under the joint law. -/
def populationMean (F : Measure (RDSState B K)) : ℝ := ∫ x, outcome x ∂F

/-- Population probability of a degree stratum. -/
def degreeMass (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  ∫ x, degreeCell k x ∂F

/-- Joint probability of sampling and membership in a degree stratum. -/
def sampledMass (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  ∫ x, sampleCell k x ∂F

def degreeMoment (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  ∫ x, degreeCell k x * outcome x ∂F

def sampledMoment (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  ∫ x, sampleCell k x * outcome x ∂F

def sampleFraction (F : Measure (RDSState B K)) : ℝ :=
  ∫ x, sampleIndicator x ∂F

/-- Conditional sampling probability, used only on positive-mass strata. -/
def samplingProbability (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  sampledMass F k / degreeMass F k

/-- Population conditional outcome mean, used only on positive-mass strata. -/
def degreeMean (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  degreeMoment F k / degreeMass F k

/-- Sampled conditional outcome mean, used only on positive sampled mass. -/
def sampledMean (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  sampledMoment F k / sampledMass F k

/-- Observed conditional degree probability given sampling. -/
def observedDegreeMass (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  sampledMass F k / sampleFraction F

/-- Positive-mass population strata; the standing convention for Eqs. (2)–(4). -/
def degreeSupport (F : Measure (RDSState B K)) : Finset (Fin K) := by
  classical
  exact Finset.univ.filter fun k => 0 < degreeMass F k

def observedSupport (F : Measure (RDSState B K)) : Finset (Fin K) := by
  classical
  exact Finset.univ.filter fun k => 0 < observedDegreeMass F k

/-- Condition 1: mean ignorability and positive conditional sampling probability. -/
def Ignorability (F : Measure (RDSState B K)) : Prop :=
  ∀ k, 0 < degreeMass F k →
    sampledMean F k = degreeMean F k ∧ 0 < samplingProbability F k

/-- Condition 2 on supported degrees, without separate sign conditions on `c` or `f`. -/
def KnownSampling (F : Measure (RDSState B K)) (c : ℝ) (f : Fin K → ℝ) : Prop :=
  ∀ k, 0 < degreeMass F k → samplingProbability F k = c * f k

end
end SAP.P021
