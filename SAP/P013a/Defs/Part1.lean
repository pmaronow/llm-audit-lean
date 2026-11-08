import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a

open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

structure Design (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  positive : ∀ z, 0 < weight z
  total : ∑ z, weight z = 1

def expectation (P : Design Ω) (X : Ω → ℝ) : ℝ := ∑ z, P.weight z * X z

def covariance (P : Design Ω) (X Y : Ω → ℝ) : ℝ :=
  expectation P (fun z => X z * Y z) - expectation P X * expectation P Y

def variance (P : Design Ω) (X : Ω → ℝ) : ℝ := covariance P X X

def probability (P : Design Ω) (A : Ω → Prop) : ℝ :=
  by classical exact ∑ z, if A z then P.weight z else 0

def indicator {N K : ℕ} (D : Ω → Fin N → Fin K) (i : Fin N) (d : Fin K)
    (z : Ω) : ℝ := if D z i = d then 1 else 0

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

def missingA {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) :=
  ∑ i, ∑ j ∈ univ.erase i, if jointPi F i j d d = 0 then
    F.outcome i d * F.outcome j d else 0

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
end
end SAP.P013a
