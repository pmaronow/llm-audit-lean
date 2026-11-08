import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

/-- Finite sample atoms with real weights and sampled subsets. `Valid` says
that the weights are nonnegative and sum to one. -/
structure Design (U Ω : Type) where
  weight : Ω → ℝ
  selected : Ω → U → Bool

variable {U Ω : Type} [Fintype U] [Fintype Ω]

def Valid (D : Design U Ω) : Prop :=
  (∀ ω, 0 ≤ D.weight ω) ∧ (∑ ω, D.weight ω) = 1

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

/-- Half the ordered sum of squared outcome sums at zero-inclusion pairs. -/
def squaredZeroPairs (D : Design U Ω) (y : U → ℝ) : ℝ :=
  ∑ k, ∑ l, if k ≠ l ∧ joint D k l = 0 then (y k+y l)^2/2 else 0

end
end SAP.P027a
