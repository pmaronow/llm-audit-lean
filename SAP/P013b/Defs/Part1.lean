import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

/-- A finite supported randomization law with positive weights summing to one. -/
structure Design (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  positive : ∀ z, 0 < weight z
  total : ∑ z, weight z = 1

/-- Exact randomization expectation as a real weighted finite sum. -/
def expectation (P : Design Ω) (X : Ω → ℝ) : ℝ := ∑ z, P.weight z * X z

def covariance (P : Design Ω) (X Y : Ω → ℝ) : ℝ :=
  expectation P (fun z => X z * Y z) - expectation P X * expectation P Y

def variance (P : Design Ω) (X : Ω → ℝ) : ℝ := covariance P X X

def probability (P : Design Ω) (A : Ω → Prop) : ℝ :=
  by classical exact ∑ z, if A z then P.weight z else 0

def indicator {N K : ℕ} (D : Ω → Fin N → Fin K) (i : Fin N) (d : Fin K)
    (z : Ω) : ℝ := if D z i = d then 1 else 0

/-- Fixed exposure-specific potentials; observed outcomes below encode Conditions 1 and 2. -/
structure Population (P : Design Ω) (N K : ℕ) where
  exposure : Ω → Fin N → Fin K
  outcome : Fin N → Fin K → ℝ

def pi {N K : ℕ} {P : Design Ω} (F : Population P N K) (i : Fin N) (d : Fin K) :=
  expectation P (indicator F.exposure i d)

def jointPi {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (i j : Fin N) (d e : Fin K) :=
  expectation P (fun z => indicator F.exposure i d z * indicator F.exposure j e z)

def observed {N K : ℕ} {P : Design Ω} (F : Population P N K) (z : Ω) (i : Fin N) :=
  F.outcome i (F.exposure z i)

def Positivity {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) : Prop :=
  ∀ i, 0 < pi F i d ∧ pi F i d < 1

def potentialTotal {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) :=
  ∑ i, F.outcome i d

def potentialMean {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) :=
  potentialTotal F d / (N : ℝ)

def causalEffect {N K : ℕ} {P : Design Ω} (F : Population P N K) (d e : Fin K) :=
  potentialMean F d - potentialMean F e

/-- Expression (1), with the masked observed outcome replaced by its equal potential outcome. -/
def htTotal {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  ∑ i, indicator F.exposure i d z * (F.outcome i d / pi F i d)

def htMean {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  htTotal F d z / (N : ℝ)

def htEffect {N K : ℕ} {P : Design Ω} (F : Population P N K) (d e : Fin K) (z : Ω) :=
  (htTotal F d z - htTotal F e z) / (N : ℝ)

def pairTerm {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (i j : Fin N) (d e : Fin K) (z : Ω) : ℝ :=
  (indicator F.exposure i d z * indicator F.exposure j e z) *
    ((jointPi F i j d e - pi F i d * pi F j e) / jointPi F i j d e) *
    (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e)

def varianceHT {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  (∑ i, indicator F.exposure i d z * (1 - pi F i d) * (F.outcome i d / pi F i d)^2) +
  ∑ i, ∑ j ∈ univ.erase i, pairTerm F i j d d z

def correctionA2 {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  ∑ i, ∑ j ∈ univ.erase i, if jointPi F i j d d = 0 then
    indicator F.exposure i d z * F.outcome i d ^ 2 / (2 * pi F i d) +
    indicator F.exposure j d z * F.outcome j d ^ 2 / (2 * pi F j d) else 0

def covarianceHT {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (z : Ω) :=
  (∑ i, ∑ j ∈ univ.erase i, pairTerm F i j d e z) -
  ∑ i, (indicator F.exposure i d z * F.outcome i d ^ 2 / (2 * pi F i d) +
    indicator F.exposure i e z * F.outcome i e ^ 2 / (2 * pi F i e))

def covarianceA {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (z : Ω) :=
  (∑ i, ∑ j ∈ univ.erase i, if 0 < jointPi F i j d e then pairTerm F i j d e z else 0) -
  ∑ i, ∑ j, if jointPi F i j d e = 0 then
    indicator F.exposure i d z * F.outcome i d ^ 2 / (2 * pi F i d) +
    indicator F.exposure j e z * F.outcome j e ^ 2 / (2 * pi F j e) else 0

def effectVariance {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (z : Ω) :=
  (varianceHT F d z + correctionA2 F d z + varianceHT F e z + correctionA2 F e z -
    2 * covarianceA F d e z) / (N : ℝ)^2

def differenceTotal {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (g : Fin N → ℝ) (z : Ω) :=
  htTotal F d z - (∑ i, indicator F.exposure i d z * (g i / pi F i d)) + ∑ i, g i

def htCount {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  ∑ i, indicator F.exposure i d z / pi F i d

/-- Expression (15); the canonical claim explicitly selects the zero-denominator convention. -/
def hajek {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :=
  htTotal F d z / htCount F d z

def Misspecified {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (yr : Fin N → Ω → ℝ) : Prop :=
  ∃ i z z', F.exposure z i = F.exposure z' i ∧ yr i z ≠ yr i z'

def htRandomizationTotal {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (yr : Fin N → Ω → ℝ) (d : Fin K) (z : Ω) :=
  ∑ i, indicator F.exposure i d z * yr i z / pi F i d

def randomizationWeight {N K : ℕ} {P : Design Ω} (F : Population P N K) (i : Fin N) (z : Ω) :=
  P.weight z / pi F i (F.exposure z i)

def conditionalPotentialTotal {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (yr : Fin N → Ω → ℝ) (d : Fin K) :=
  ∑ i, ∑ z, if F.exposure z i = d then randomizationWeight F i z * yr i z else 0

end
end SAP.P013b
