import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P015b

universe u v

noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal
attribute [local instance] Classical.propDecidable

noncomputable def sampleCoefficients {N Q : Type*} [Fintype N] [Fintype Q] [DecidableEq Q]
    (W : Matrix N Q ℝ) (Y : N → ℝ) : Q → ℝ :=
  (W.transpose * W)⁻¹.mulVec (W.transpose.mulVec Y)

def precisionMatrix {Q : Type*} [Fintype Q] [DecidableEq Q]
    (S Qg : Matrix Q Q ℝ) (σ₂ : ℝ) : Matrix Q Q ℝ := (S+σ₂ • Qg⁻¹)⁻¹

def pooledCoefficients {G Q : Type*} [Fintype G] [Fintype Q] [DecidableEq Q]
    (P : G → Matrix Q Q ℝ) (t : G → Q → ℝ) : Q → ℝ :=
  (∑ g, P g)⁻¹.mulVec (∑ g, (P g).mulVec (t g))

def precisionLoss {G Q : Type*} [Fintype G] [Fintype Q]
    (P : G → Matrix Q Q ℝ) (t : G → Q → ℝ) (m : Q → ℝ) : ℝ :=
  ∑ g, dotProduct (t g-m) ((P g).mulVec (t g-m))

def finiteMean {A : Type*} [Fintype A] (p Z : A → ℝ) : ℝ := ∑ a, p a * Z a

def IsFiniteLaw {A : Type*} [Fintype A] (p : A → ℝ) : Prop :=
  (∀ a, 0  ≤  p a) ∧ ∑ a, p a = 1

noncomputable def finiteMass {A : Type*} [Fintype A] (p : A → ℝ) (E : A → Prop) : ℝ :=
  ∑ a, if E a then p a else 0

noncomputable def finiteCellMean {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (Z : A → ℝ) (x : B) : ℝ :=
  finiteMean p (fun a => if X a = x then Z a else 0) / finiteMass p (fun a => X a = x)

noncomputable def finiteCellProbability {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (D : A → ℝ) (x : B) (d : ℝ) : ℝ :=
  finiteMass p (fun a => X a = x ∧ D a = d) / finiteMass p (fun a => X a = x)

noncomputable def finiteWeight {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (D : A → ℝ) : A → ℝ :=
  fun a => (D a - finiteCellMean p X D (X a)) ^ 2

noncomputable def finiteEffective {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (D : A → ℝ) : A → ℝ :=
  fun a => p a * finiteWeight p X D a / finiteMean p (finiteWeight p X D)

noncomputable def finiteUnconfounded {A B C : Type*} [Fintype A]
    (p : A → ℝ) (X : A → B) (U : A → C) (D : A → ℝ) : Prop :=
  ∀ x u d, finiteMass p (fun a => X a = x ∧ U a = u ∧ D a = d) *
      finiteMass p (fun a => X a = x) =
    finiteMass p (fun a => X a = x ∧ U a = u) *
      finiteMass p (fun a => X a = x ∧ D a = d)

def finiteVariance {A : Type*} [Fintype A] (p Z : A → ℝ) : ℝ :=
  finiteMean p (fun a => (Z a - finiteMean p Z) ^ 2)

def populationCoefficients {A Q : Type*} [Fintype A] [Fintype Q] [DecidableEq Q]
    (p : A → ℝ) (W : Matrix A Q ℝ) (Y : A → ℝ) : Q → ℝ :=
  Matrix.mulVec (((fun j k => finiteMean p (fun i => W i j*W i k)) : Matrix Q Q ℝ)⁻¹)
    (fun j => finiteMean p (fun i => W i j*Y i))

def treatmentResidual {N Q : Type*} [Fintype Q] (V : Matrix N Q ℝ)
    (D : N → ℝ) (ω : Q → ℝ) : N → ℝ := fun i => D i - V.mulVec ω i

def sigmoidMean : ℝ → ℝ := Real.sigmoid

def logOdds (p : ℝ) : ℝ := Real.log (p / (1-p))

def binomialLogLikelihoodSAP (m : ℝ → ℝ) (n k η : ℝ) : ℝ :=
  k*Real.log (m η) + (n-k)*Real.log (1-m η)

def residualEquation {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (n k : N → ℝ) (m : ℝ → ℝ) (θ : Q → ℝ) : Q → ℝ :=
  fun j => ∑ i, W i j*(k i-n i*m (W.mulVec θ i))

def binaryLogLikelihood {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (n k : N → ℝ) (m : ℝ → ℝ) (θ : Q → ℝ) : ℝ :=
  ∑ i, binomialLogLikelihoodSAP m (n i) (k i) (W.mulVec θ i)

def linkScoreMultiplier (m : ℝ → ℝ) (η : ℝ) : ℝ := deriv m η/(m η*(1-m η))

def affineCoefficients {Q : Type*} [DecidableEq Q] (intercept : Q) (b c : ℝ) (θ : Q → ℝ) : Q → ℝ :=
  fun j => (if j=intercept then b else 0)+c*θ j

end
end SAP.P015b
