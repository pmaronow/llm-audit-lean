import SAP.P031.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031

open scoped BigOperators Matrix Topology
open Finset Filter

noncomputable section

/-- Finite populations satisfying the paper's standing design condition. -/
structure Population where
  N : ℕ
  M : ℕ
  y1 : Fin N → ℝ
  y0 : Fin N → ℝ
  hM : 1 < M
  hMN : M < N - 1

abbrev VarianceEstimator := (P : Population) → Finset (Fin P.N) → ℝ

/- The normal limit uses the actual Gaussian CDF and eventually
positive true variance. Equivalence uses relative error events, including
zero reference estimates. Coverage includes zero-width intervals. -/

def pointEstimate (P : Population) (s : Finset (Fin P.N)) : ℝ :=
  estimate s (observed s P.y1 P.y0)

def populationEffect (P : Population) : ℝ := averageEffect P.y1 P.y0

def trueVariance (P : Population) : ℝ := randomizationVariance P.M P.y1 P.y0

def neymanEstimator : VarianceEstimator := fun P s => neyman s (observed s P.y1 P.y0)

def hc2Estimator : VarianceEstimator := fun P s => hc2 s (observed s P.y1 P.y0)

def hrEstimator : VarianceEstimator := fun P s => hr s (observed s P.y1 P.y0)

def hc1Estimator : VarianceEstimator := fun P s => hc1 s (observed s P.y1 P.y0)

def hc3Estimator : VarianceEstimator := fun P s => hc3 s (observed s P.y1 P.y0)

def olsEstimator : VarianceEstimator := fun P s => ols s (observed s P.y1 P.y0)

def ceEstimator : VarianceEstimator := fun P s => constantEffects s (observed s P.y1 P.y0)

def eventProbability (P : Population) (event : Finset (Fin P.N) → Prop) : ℝ := by
  classical
  exact expectation P.M (fun s => if event s then 1 else 0)

def normalCDF (x : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x

def GrowingPopulations (P : ℕ → Population) : Prop :=
  Tendsto (fun r => (P r).N) atTop atTop

def StandardizedNormalLimit (P : ℕ → Population) : Prop :=
  (∀ᶠ r in atTop, 0 < trueVariance (P r)) ∧
  ∀ x : ℝ, Tendsto (fun r => eventProbability (P r) (fun s =>
    (pointEstimate (P r) s - populationEffect (P r)) / Real.sqrt (trueVariance (P r)) ≤ x))
    atTop (𝓝 (normalCDF x))

def ConvergesInProbability (P : ℕ → Population) (f : VarianceEstimator) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun r =>
    eventProbability (P r) (fun s => ε < |f (P r) s - c|)) atTop (𝓝 0)

def FirstOrderEquivalent (P : ℕ → Population) (A B : VarianceEstimator) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun r => eventProbability (P r)
    (fun s => ε * |B (P r) s| < |A (P r) s - B (P r) s|)) atTop (𝓝 0)

def coverage (P : Population) (V : VarianceEstimator) (z : ℝ) : ℝ :=
  eventProbability P (fun s => |pointEstimate P s - populationEffect P| ≤ z * Real.sqrt (V P s))

def ConservativeCoverage (P : ℕ → Population) (V : VarianceEstimator) (z : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop, 2 * normalCDF z - 1 - ε ≤ coverage (P r) V z

def UnbalancedVarianceLimit (P : ℕ → Population) (a v : ℝ) : Prop :=
  GrowingPopulations P ∧ (∀ r, (P r).N ≠ 2 * (P r).M) ∧ 0 < v ∧
    Tendsto (fun r => ((P r).N : ℝ) * trueVariance (P r)) atTop (𝓝 v) ∧
    ConvergesInProbability P (fun Q s => (Q.N : ℝ) * olsEstimator Q s) a ∧
    ConvergesInProbability P (fun Q s => (Q.N : ℝ) * ceEstimator Q s) a

end
end SAP.P031
