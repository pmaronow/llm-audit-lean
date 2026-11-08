import Mathlib
import SAP.P001c.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical
noncomputable section

/-- Finite expectations use the displayed PMF weights directly. -/
def finiteMean {n : ℕ} (w X : Fin n → ℝ) : ℝ := ∑ i, w i * X i

def finiteProbability {n : ℕ} (w : Fin n → ℝ) (A : Fin n → Prop)
    [DecidablePred A] : ℝ := ∑ i, if A i then w i else 0

def finiteVariance {n : ℕ} (w X : Fin n → ℝ) : ℝ :=
  finiteMean w (fun i => (X i - finiteMean w X)^2)

def finiteCovariance {n : ℕ} (w X Y : Fin n → ℝ) : ℝ :=
  finiteMean w (fun i => (X i - finiteMean w X) * (Y i - finiteMean w Y))

def finiteCorrelation {n : ℕ} (w X Y : Fin n → ℝ) : ℝ :=
  finiteCovariance w X Y / (Real.sqrt (finiteVariance w X) * Real.sqrt (finiteVariance w Y))

def nullWeights : Fin 3 → ℝ := ![1/2, 1/2, 0]
def signWeights : Fin 2 → ℝ := fun _ => 1/2
def equalWeights (N : ℕ) : Fin N → ℝ := fun _ => (N : ℝ)⁻¹
def fairCoinLoss (c : ℝ) : ℝ := (0-c)^2/2 + (1-c)^2/2

def normalPDF (m s y : ℝ) : ℝ :=
  Real.exp (-(y-m)^2/(2*s^2)) / (s * Real.sqrt (2*Real.pi))

def bivariatePDF (mx my sx sy ρ : ℝ) (xy : ℝ × ℝ) : ℝ :=
  Real.exp (-(((xy.1-mx)/sx)^2 + ((xy.2-my)/sy)^2 -
    2*ρ*(xy.1-mx)*(xy.2-my)/(sx*sy))/(2*(1-ρ^2))) /
    (2*Real.pi*sx*sy*Real.sqrt (1-ρ^2))

def isJointDensity (ν : Measure (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
    ν = volume.withDensity (fun x => ENNReal.ofReal (f x))

def intervalUniform (a b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (if x ∈ Set.Icc a b then (b-a)⁻¹ else 0))

def covarianceEntries {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K : ℕ} (X : Ω → Fin K → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  fun j k => covariance (fun ω => X ω j) (fun ω => X ω k) μ

def affinePredictor {K : ℕ} (b : Fin (K+1) → ℝ) (x : Fin K → ℝ) : ℝ :=
  b 0 + ∑ k, b k.succ * x k

def coordinatePartial {K : ℕ} (f : (Fin K → ℝ) → ℝ) (x : Fin K → ℝ) (k : Fin K) : ℝ :=
  deriv (fun t : ℝ => f (Function.update x k (x k+t))) 0

def powerTailMass (k : ℕ) : ℝ := 7 * (1/8 : ℝ)^(k+1)

end
end SAP.P001c
