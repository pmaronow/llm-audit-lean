import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable

structure Design (U Ω : Type) [Fintype U] [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1
  selected : Ω → U → Bool

variable {U Ω : Type} [Fintype U] [Fintype Ω]

def expect (D : Design U Ω) (f : Ω → ℝ) : ℝ := ∑ ω, D.weight ω * f ω

def indicator (D : Design U Ω) (ω : Ω) (k : U) : ℝ :=
  if D.selected ω k then 1 else 0

def pi (D : Design U Ω) (k : U) : ℝ := expect D (fun ω => indicator D ω k)

def joint (D : Design U Ω) (k l : U) : ℝ :=
  expect D (fun ω => indicator D ω k * indicator D ω l)

def Positive (D : Design U Ω) : Prop := ∀ k, 0 < pi D k

def inclusionCov (D : Design U Ω) (k l : U) : ℝ := joint D k l - pi D k * pi D l

def variance (D : Design U Ω) (f : Ω → ℝ) : ℝ :=
  expect D (fun ω => (f ω - expect D f)^2)

def htTotal (D : Design U Ω) (y : U → ℝ) (ω : Ω) : ℝ :=
  ∑ k, indicator D ω k * (y k / pi D k)

def htMean (D : Design U Ω) (y : U → ℝ) (ω : Ω) : ℝ :=
  htTotal D y ω / Fintype.card U

def htVarianceEstimator (D : Design U Ω) (y : U → ℝ) (ω : Ω) : ℝ :=
  ∑ k, ∑ l, if 0 < joint D k l then
    indicator D ω k * indicator D ω l * (inclusionCov D k l / joint D k l) *
      (y k / pi D k) * (y l / pi D l) else 0

def biasA (D : Design U Ω) (y : U → ℝ) : ℝ :=
  ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then y k * y l else 0

def youngA (D : Design U Ω) (y : U → ℝ) (a b : U → U → ℝ) : ℝ :=
  ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then
    |y k| ^ (a k l) / a k l + |y l| ^ (b k l) / b k l else 0

def youngCorrection (D : Design U Ω) (y : U → ℝ) (a b : U → U → ℝ)
    (ω : Ω) : ℝ :=
  ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then
    indicator D ω k * (|y k| ^ (a k l) / (a k l * pi D k)) +
    indicator D ω l * (|y l| ^ (b k l) / (b k l * pi D l)) else 0

def conservativeEstimator (D : Design U Ω) (y : U → ℝ) (a b : U → U → ℝ)
    (ω : Ω) : ℝ := htVarianceEstimator D y ω + youngCorrection D y a b ω

def quadraticCorrection (D : Design U Ω) (y : U → ℝ) (ω : Ω) : ℝ :=
  ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then
    indicator D ω k * (y k ^ 2 / (2 * pi D k)) +
    indicator D ω l * (y l ^ 2 / (2 * pi D l)) else 0

def c2Estimator (D : Design U Ω) (y : U → ℝ) (ω : Ω) : ℝ :=
  htVarianceEstimator D y ω + quadraticCorrection D y ω

def quadraticA (D : Design U Ω) (y : U → ℝ) : ℝ :=
  ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then (y k ^ 2 + y l ^ 2) / 2 else 0

def wrEstimator (D : Design U Ω) (y : U → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  (∑ k, indicator D ω k * (y k / (pi D k / m) - htTotal D y ω)^2) /
    ((Fintype.card U : ℝ)^2 * m * (m - 1 : ℝ))

end
end SAP.P027b
