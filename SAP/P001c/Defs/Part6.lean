import Mathlib
import SAP.P001c.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical
noncomputable section

def T56Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ),
    isIID μ X →
    μ.map (X 0)=(1/2 : ℝ≥0∞) • Measure.dirac (0 : ℝ) +
      (1/2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) →
    hadamardDerivative cdfSet Set.univ (fun _ => 7)
      (embedCDF (cdfAt μ (X 0))) (0 : CDFSpace →L[ℝ] ℝ) ∧
    cdfHadamard (fun _ => (7 : ℝ)) (cdfAt μ (X 0)) ∧
    (∀ n : ℕ, ∀ ω : Ω, Real.sqrt n*((7 : ℝ)-7)=0) ∧
    (∀ v : ℝ≥0, 0 < v →
      ¬ convergesInDistribution μ (fun _ _ => (0 : ℝ)) (gaussianReal 0 v)) ∧
    cdfHadamard quadraticFunctional (cdfAt μ (X 0)) ∧
    quadraticFunctional (cdfAt μ (X 0))=0 ∧
    (∀ n : ℕ, 0 < n → expectation μ (fun ω =>
      (Real.sqrt n*quadraticFunctional (cdfAt (empiricalLaw X n ω) id))^2)=
        (3*(n : ℝ)-2)/(16*(n : ℝ)^2)) ∧
    convergesInProbability μ
      (fun n ω => Real.sqrt n*quadraticFunctional (cdfAt (empiricalLaw X n ω) id)) 0

def T57Statement (Ω : Type*) [MeasurableSpace Ω]
    [MeasurableSpace CDFSpace] [BorelSpace CDFSpace] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ), isIID μ X →
    ∀ (T : CDFSpace → ℝ) (L : CDFSpace →L[ℝ] ℝ),
    hadamardDerivative cdfSet (cdfTangent (cdfAt μ (X 0))) T
      (embedCDF (cdfAt μ (X 0))) L →
    ∀ (νB : Measure CDFSpace) [IsProbabilityMeasure νB],
    isCDFBridge (cdfAt μ (X 0)) νB →
    (∀ n, Measurable (fun ω => T (empiricalCDF X n ω))) →
    MemLp (fun h => L h) 2 νB → ∀ hv : 0 < variance (fun h => L h) νB,
    outerWeakConvergence μ
      (fun n ω => Real.sqrt n • (empiricalCDF X n ω-embedCDF (cdfAt μ (X 0)))) νB ∧
    convergesInDistribution μ
      (fun n ω => Real.sqrt n*(T (empiricalCDF X n ω)-T (embedCDF (cdfAt μ (X 0)))))
      (gaussianReal 0 ⟨variance (fun h => L h) νB, le_of_lt hv⟩)

end
end SAP.P001c
