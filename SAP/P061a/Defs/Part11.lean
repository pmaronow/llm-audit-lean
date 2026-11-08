import SAP.P061a.Defs.Part10

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

/-- Positive-index weighted response and estimator terms in the divergent example. -/
noncomputable def integerResponseTerm (D : AtomicDesign ℝ) (k : ℕ) : ℝ :=
  D.mass ((k+1 : ℕ) : ℝ) * integerResponse 0 ((k+1 : ℕ) : ℝ)

noncomputable def integerEstimatorTerm (D : AtomicDesign ℝ) (k : ℕ) : ℝ :=
  D.mass ((k+1 : ℕ) : ℝ) * estimateExposureMean D integerExposure integerResponse 1 ((k+1 : ℕ) : ℝ)

/-- Ordinary means fail by two divergent nonnegative sign parts, without evaluating their total sums. -/
def T7Statement : Prop :=
  ∃ D : AtomicDesign ℝ,
    D.mass = realIntegerMass ∧
    (∀ z, supported D z ↔ ∃ k : ℕ, (k : ℝ) = z) ∧
    positiveExposure D integerExposure 1 ∧ positiveExposure D integerExposure 0 ∧
    (exposureProbability D integerExposure 0 1 = 1/2 ∧
    exposureProbability D integerExposure 0 0 = 1/2 ∧
    exposureMean D integerExposure integerResponse 0 0 = 0 ∧
    ¬Summable (fun z : ℝ => D.mass z *
      (if integerExposure 0 z = 1 then integerResponse 0 z else 0)) ∧
    ¬HasMean D (estimateExposureMean D integerExposure integerResponse 1)) ∧
    HasMean D (fun z => if integerExposure 0 z=0 then integerResponse 0 z else 0) ∧
    (∀ k, integerResponseTerm D k = (-1 : ℝ)^k) ∧
    (∀ m : ℕ,
      (∑ k ∈ Finset.range (2*m), max (integerResponseTerm D k) 0) = (m : ℝ) ∧
      (∑ k ∈ Finset.range (2*m), max (-(integerResponseTerm D k)) 0) = (m : ℝ) ∧
      (∑ k ∈ Finset.range (2*m), |integerResponseTerm D k|) = 2*m ∧
      (∑ k ∈ Finset.range (2*m), integerResponseTerm D k) = 0 ∧
      (∑ k ∈ Finset.range (2*m+1), integerResponseTerm D k) = 1) ∧
    ¬Summable (fun k => max (integerResponseTerm D k) 0) ∧
    ¬Summable (fun k => max (-(integerResponseTerm D k)) 0) ∧
    (∀ z, estimateExposureMean D integerExposure integerResponse 1 z =
      2*integerResponse 0 z*(if integerExposure 0 z = 1 then 1 else 0)) ∧
    (∀ k, integerEstimatorTerm D k = 2*(-1 : ℝ)^k) ∧
    ¬Summable (fun k => max (integerEstimatorTerm D k) 0) ∧
    ¬Summable (fun k => max (-(integerEstimatorTerm D k)) 0)


end SAP.P061a
