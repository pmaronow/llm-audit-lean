import Mathlib
import SAP.P015b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P015b

universe u v

noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal
attribute [local instance] Classical.propDecidable

def controlVector {K : ℕ} (x : Fin K → ℝ) : Fin (K+1) → ℝ := Fin.cases 1 x

def regressorVector {K : ℕ} (d : ℝ) (x : Fin K → ℝ) : Fin (K+2) → ℝ :=
  Fin.cases 1 (Fin.cases d x)

def linearOutcome (y₀ τ d : ℝ) : ℝ := y₀+τ*d

def controlDesign {Ω : Type*} {K : ℕ} (X : ℕ → Ω → Fin K → ℝ) (n : ℕ) (s : Ω) :
    Matrix (Fin n) (Fin (K+1)) ℝ := fun i => controlVector (X i s)

def regressionDesign {Ω : Type*} {K : ℕ} (D : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (n : ℕ) (s : Ω) : Matrix (Fin n) (Fin (K+2)) ℝ := fun i => regressorVector (D i s) (X i s)

def fittedTreatmentCoefficients {Ω : Type*} {K : ℕ} (D : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (n : ℕ) (s : Ω) : Fin (K+1) → ℝ := sampleCoefficients (controlDesign X n s) (fun i => D i s)

def fittedTreatmentResidual {Ω : Type*} {K : ℕ} (D : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (n : ℕ) (s : Ω) : Fin n → ℝ :=
  treatmentResidual (controlDesign X n s) (fun i => D i s) (fittedTreatmentCoefficients D X n s)

def treatmentEstimate {Ω : Type*} {K : ℕ} (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (n : ℕ) (s : Ω) : ℝ :=
  sampleCoefficients (regressionDesign D X n s) (fun i => linearOutcome (Y₀ i s) (τ i s) (D i s)) 1

def squaredPopulationResidual {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) (D : Ω → ℝ) (X : Ω → B) (s : Ω) : ℝ :=
  (D s-P[D | MeasurableSpace.comap X inferInstance] s)^2

def MomentConvergence {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℕ → Ω → ℝ) : Prop :=
  (∀ i, Integrable (Z i) P) ∧ TendstoInMeasure P
    (fun n s => (∑ i : Fin n, Z i s)/(n : ℝ)) atTop (fun _ => ∫ s, Z 0 s ∂P)

def RegressionRegularity {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (P : Measure Ω)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ) : Prop :=
  (∀ j k, MomentConvergence P (fun i s => controlVector (X i s) j*controlVector (X i s) k)) ∧
  (∀ j, MomentConvergence P (fun i s => controlVector (X i s) j*D i s)) ∧
  MomentConvergence P (fun i s => D i s^2) ∧ MomentConvergence P (fun i s => D i s*Y₀ i s) ∧
  (∀ j, MomentConvergence P (fun i s => controlVector (X i s) j*Y₀ i s)) ∧
  MomentConvergence P (fun i s => D i s^2*τ i s) ∧
  (∀ j, MomentConvergence P (fun i s => controlVector (X i s) j*D i s*τ i s)) ∧
  (∀ j k, MomentConvergence P (fun i s => controlVector (X i s) j*controlVector (X i s) k*τ i s)) ∧
  Matrix.det (fun j k => ∫ s, controlVector (X 0 s) j*controlVector (X 0 s) k ∂P) ≠ 0 ∧
  Integrable (squaredPopulationResidual P (D 0) (X 0)) P ∧
  0  <  ∫ s, squaredPopulationResidual P (D 0) (X 0) s ∂P

def EffectiveMeanRegularity {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (P : Measure Ω)
    (D Z : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ) (ω : Fin (K+1) → ℝ) : Prop :=
  let r := fun i s => D i s-dotProduct (controlVector (X i s)) ω
  (∀ j k, MomentConvergence P (fun i s => controlVector (X i s) j*controlVector (X i s) k)) ∧
  (∀ j, MomentConvergence P (fun i s => controlVector (X i s) j*D i s)) ∧
  MomentConvergence P (fun i s => r i s^2*Z i s) ∧ MomentConvergence P (fun i s => r i s^2) ∧
  (∀ j, MomentConvergence P (fun i s => r i s*Z i s*controlVector (X i s) j)) ∧
  (∀ j, MomentConvergence P (fun i s => r i s*controlVector (X i s) j)) ∧
  (∀ j k, MomentConvergence P (fun i s => Z i s*controlVector (X i s) j*controlVector (X i s) k)) ∧
  Matrix.det (fun j k => ∫ s, controlVector (X 0 s) j*controlVector (X 0 s) k ∂P) ≠ 0 ∧
  0  <  ∫ s, r 0 s^2 ∂P

/-- The coefficient formula represents a nonsingular OLS fit after a finite prefix. -/
def EventuallyDefinedRegression {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (P : Measure Ω) (D : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ᵐ s ∂P,
    ((regressionDesign D X n s).transpose * regressionDesign D X n s).det ≠ 0

/-- The effective mean has a fitted control regression and a positive weight sum. -/
def EventuallyDefinedEffectiveMean {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (P : Measure Ω) (D : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ᵐ s ∂P,
    ((controlDesign X n s).transpose * controlDesign X n s).det ≠ 0 ∧
    0  <  ∑ i : Fin n, fittedTreatmentResidual D X n s i^2

end
end SAP.P015b
