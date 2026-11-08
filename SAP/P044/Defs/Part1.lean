import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

abbrev Assignment (N : ℕ) := Fin N → Bool

inductive Exposure where
  | d11 | d10 | d01 | d00
  deriving DecidableEq, Repr

instance : Fintype Exposure := ⟨{.d11, .d10, .d01, .d00}, by intro d; cases d <;> simp⟩

abbrev Adjacency (N : ℕ) := Fin N → Fin N → Bool

def peerCount {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N) : ℕ :=
  ∑ j, if A i j && z j then 1 else 0

def exposure {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N) : Exposure :=
  if z i then (if 0 < peerCount A z i then .d11 else .d10)
  else (if 0 < peerCount A z i then .d01 else .d00)

structure FiniteDesign (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

def expect {Ω K : Type*} [Fintype Ω] [CommSemiring K] (p : Ω → K) (t : Ω → K) : K :=
  ∑ ω, p ω * t ω

def designVariance {Ω K : Type*} [Fintype Ω] [CommRing K]
    (p : Ω → K) (t : Ω → K) : K := expect p (fun ω => t ω ^ 2) - (expect p t) ^ 2

abbrev OutcomeSchedule (N : ℕ) (D K : Type*) := Fin N → D → K

def observed {Ω D K : Type*} {N : ℕ} (f : Ω → Fin N → D)
    (y : OutcomeSchedule N D K) (ω : Ω) (i : Fin N) : K := y i (f ω i)

def tau {N : ℕ} {D K : Type*} [Field K] (y : Fin N → D → K) (a b : D) : K :=
  (∑ i, (y i a - y i b)) / N

def marginal {Ω D K : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → D) (i : Fin N) (a : D) : K :=
  ∑ ω, if f ω i = a then p ω else 0

def joint {Ω D K : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → D) (i j : Fin N) (a b : D) : K :=
  ∑ ω, if f ω i = a ∧ f ω j = b then p ω else 0

def htTerm {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a : D) (ω : Ω) (i : Fin N) : K :=
  if f ω i = a then y i a / w i a else 0

def htMean {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a : D) (ω : Ω) : K :=
  (∑ i, htTerm f y w a ω i) / N

def htContrast {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a b : D) (ω : Ω) : K :=
  htMean f y w a ω - htMean f y w b ω

def totalVarianceEstimate {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K)
    (q : Fin N → Fin N → D → D → K) (a : D) (ω : Ω) : K :=
  ∑ i, ∑ j, (
    (if 0 < q i j a a then
      (if f ω i = a ∧ f ω j = a then
        y i a * y j a * (1 / (w i a * w j a) - 1 / q i j a a) else 0)
    else 0) +
    (if i ≠ j ∧ q i j a a = 0 then
      (if f ω i = a then y i a ^ 2 / (2 * w i a) else 0) +
      (if f ω j = a then y j a ^ 2 / (2 * w j a) else 0)
    else 0))

def totalCovarianceEstimate {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K)
    (q : Fin N → Fin N → D → D → K) (a b : D) (ω : Ω) : K :=
  ∑ i, ∑ j, (
    (if 0 < q i j a b then
      (if f ω i = a ∧ f ω j = b then
        y i a * y j b * (1 / (w i a * w j b) - 1 / q i j a b) else 0)
    else 0) -
    (if q i j a b = 0 then
      (if f ω i = a then y i a ^ 2 / (2 * w i a) else 0) +
      (if f ω j = b then y j b ^ 2 / (2 * w j b) else 0)
    else 0))

def varianceEstimate {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K)
    (q : Fin N → Fin N → D → D → K) (a b : D) (ω : Ω) : K :=
  (totalVarianceEstimate f y w q a ω + totalVarianceEstimate f y w q b ω -
    2 * totalCovarianceEstimate f y w q a b ω) / (N : K) ^ 2

def zeroSurplus {N : ℕ} {D : Type*} [DecidableEq D]
    (y : Fin N → D → ℝ) (q : Fin N → Fin N → D → D → ℝ) (a b : D) : ℝ :=
  ((∑ i, ∑ j, if i ≠ j ∧ q i j a a = 0 then (y i a + y j a) ^ 2 / 2 else 0) +
   (∑ i, ∑ j, if i ≠ j ∧ q i j b b = 0 then (y i b + y j b) ^ 2 / 2 else 0) +
   (∑ i, ∑ j, if q i j a b = 0 then (y i a - y j b) ^ 2 else 0)) / (N : ℝ) ^ 2

noncomputable def commonSupport {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (p : Ω → ℝ) (f : Ω → Fin N → D) (a b : D) : Finset (Fin N) :=
  {i | 0 < marginal p f i a ∧ 0 < marginal p f i b}

end
end SAP.P044
