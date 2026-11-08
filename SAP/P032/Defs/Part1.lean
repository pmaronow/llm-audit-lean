import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

variable {R M P : Type*} [Fintype R] [Fintype M] [Fintype P]
  [DecidableEq R] [DecidableEq M] [DecidableEq P]

/-! Shared finite covariance, OLS, spectral and probability notions. -/

structure DyadData (M : Type*) where
  members : Finset M
  two : members.card = 2

variable {R M P : Type*} [Fintype R] [Fintype M] [Fintype P]
  [DecidableEq R] [DecidableEq M] [DecidableEq P]

def dyadicMask (d : R → DyadData M) (r s : R) : ℝ :=
  if (d r).members ∩ (d s).members |>.Nonempty then 1 else 0

def repeatedMask (d : R → DyadData M) (r s : R) : ℝ :=
  if (d r).members = (d s).members then 1 else 0

def recordMask (r s : R) : ℝ := if r = s then 1 else 0

def memberMask (d : R → DyadData M) (i : M) (r s : R) : ℝ :=
  (if i ∈ (d r).members ∧ i ∈ (d s).members then 1 else 0) +
  (if r = s ∧ i ∉ (d r).members then 1 else 0)

def scoreCovariance (pattern : R → R → ℝ) (z : R → P → ℝ) : Matrix P P ℝ :=
  fun i j => ∑ r, ∑ s, pattern r s * z r i * z s j

def quadForm (A : Matrix R R ℝ) (h : R → ℝ) : ℝ :=
  ∑ r, ∑ s, h r * h s * A r s

def dyadicRestriction (d : R → DyadData M) (A : Matrix R R ℝ) : Matrix R R ℝ :=
  fun r s => dyadicMask d r s * A r s

def omittedSum (d : R → DyadData M) (A : Matrix R R ℝ) (h : R → ℝ) : ℝ :=
  ∑ r, ∑ s, if ((d r).members ∩ (d s).members).Nonempty then 0
    else h r * h s * A r s

def subjectMask {G : Type*} [DecidableEq G] (g : R → G) (r s : R) : ℝ :=
  if g r = g s then 1 else 0

def subjectCrossMask {G : Type*} [DecidableEq G] (g : R → G) (r s : R) : ℝ :=
  if r ≠ s ∧ g r = g s then 1 else 0

def olsBread (X : Matrix R P ℝ) : Matrix P P ℝ := (X.transpose * X)⁻¹

def leastSquares (X : Matrix R P ℝ) (Y : R → ℝ) : P → ℝ :=
  olsBread X *ᵥ (X.transpose *ᵥ Y)

def fitResidual (X : Matrix R P ℝ) (Y : R → ℝ) : R → ℝ := Y - X *ᵥ leastSquares X Y

def sandwichCovariance (X : Matrix R P ℝ) (A : Matrix R R ℝ) : Matrix P P ℝ :=
  olsBread X * X.transpose * A * X * olsBread X

def patternMeat (pattern : R → R → ℝ) (u : R → ℝ) : Matrix R R ℝ :=
  fun r s => pattern r s * u r * u s

def plugInCovariance (X : Matrix R P ℝ) (u : R → ℝ) (pattern : R → R → ℝ) :=
  sandwichCovariance X (patternMeat pattern u)

def errorMoments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u : R → Ω → ℝ) : Matrix R R ℝ := fun r s => ∫ ω, u r ω * u s ω ∂μ

def clipEigenvalues (Q : Matrix P P ℝ) (eigs : P → ℝ) : Matrix P P ℝ :=
  Q * Matrix.diagonal (fun j => max (eigs j) 0) * Q.transpose

def psdPart (V : Matrix P P ℝ) (hV : V.IsHermitian) : Matrix P P ℝ :=
  clipEigenvalues (hV.eigenvectorUnitary : Matrix P P ℝ) hV.eigenvalues

def diagonalGate (V : Matrix P P ℝ) (hV : V.IsHermitian) : Matrix P P ℝ :=
  if ∃ i, V i i < 0 then psdPart V hV else V

def outcomeAverage {Ω : Type*} (Y₁ Y₂ : Ω → ℝ) : Ω → ℝ := fun ω => (1/2 : ℝ)*(Y₁ ω+Y₂ ω)

def naiveAverageVariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y₁ Y₂ : Ω → ℝ) : ℝ := (1/4 : ℝ)*(variance Y₁ μ+variance Y₂ μ)

def countryOutcomes {Ω : Type*} (Z : Fin 5 → Ω → ℝ) (a b c d : ℝ) :
    (Ω → ℝ) × (Ω → ℝ) :=
  (fun ω => a*Z 0 ω+b*Z 1 ω+Z 3 ω,
   fun ω => c*Z 0 ω+d*Z 2 ω+Z 4 ω)

structure FiniteDistribution (S : Type*) [Fintype S] where
  weight : S → ℝ
  nonneg : ∀ s, 0 ≤ weight s
  total : ∑ s, weight s = 1

def finiteMean {S : Type*} [Fintype S] (law : FiniteDistribution S) (f : S → ℝ) : ℝ :=
  ∑ s, law.weight s * f s

def finiteVar {S : Type*} [Fintype S] (law : FiniteDistribution S) (f : S → ℝ) : ℝ :=
  finiteMean law (fun s => (f s - finiteMean law f)^2)

def distributionMeasure {S : Type*} [Fintype S] [MeasurableSpace S]
    (law : FiniteDistribution S) : Measure S :=
  ∑ ω, (ENNReal.ofReal (law.weight ω)) • Measure.dirac ω

def recordScalarCovariance (z : R → ℝ) : ℝ := ∑ r, (z r)^2

def clusterScalarCovariance {G : Type*} [Fintype G] [DecidableEq G] (g : R → G) (z : R → ℝ) : ℝ :=
  ∑ k, (∑ r, if g r = k then z r else 0)^2

def memberScalarCovariance (d : R → DyadData M) (i : M) (z : R → ℝ) : ℝ :=
  (∑ r, if i ∈ (d r).members then z r else 0)^2 +
    ∑ r, if i ∉ (d r).members then (z r)^2 else 0

end
end SAP.P032
