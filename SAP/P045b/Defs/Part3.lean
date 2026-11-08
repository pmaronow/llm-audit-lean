import SAP.P045b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P045b
open Finset
open scoped BigOperators
noncomputable section

def momentVariance {Ω K : Type*} [Fintype Ω] [CommRing K]
    (p : Ω → K) (t : Ω → K) : K := expect p (fun ω => t ω ^ 2) - (expect p t) ^ 2

def exposureEffect {N : ℕ} {D K : Type*} [Field K] (y : Fin N → D → K) (a b : D) : K :=
  (∑ i, (y i a - y i b)) / N

def exposureMarginal {Ω D K : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → D) (i : Fin N) (a : D) : K :=
  ∑ ω, if f ω i = a then p ω else 0

def exposureJoint {Ω D K : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → D) (i j : Fin N) (a b : D) : K :=
  ∑ ω, if f ω i = a ∧ f ω j = b then p ω else 0

def weightedTerm {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a : D) (ω : Ω) (i : Fin N) : K :=
  if f ω i = a then y i a / w i a else 0

def weightedMean {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a : D) (ω : Ω) : K :=
  (∑ i, weightedTerm f y w a ω i) / N

def weightedContrast {Ω D K : Type*} {N : ℕ} [DecidableEq D] [Field K]
    (f : Ω → Fin N → D) (y w : Fin N → D → K) (a b : D) (ω : Ω) : K :=
  weightedMean f y w a ω - weightedMean f y w b ω

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

def exposureCount {R N : ℕ} {D : Type*} [DecidableEq D]
    (f : Fin R → Fin N → D) (i : Fin N) (a : D) : ℕ :=
  (Finset.univ.filter (fun r => f r i = a)).card

def jointCount {R N : ℕ} {D : Type*} [DecidableEq D]
    (f : Fin R → Fin N → D) (i j : Fin N) (a b : D) : ℕ :=
  (Finset.univ.filter (fun r => f r i = a ∧ f r j = b)).card

def smoothedWeight {R N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    (f : Fin R → Fin N → D) (i : Fin N) (a : D) : K :=
  ((exposureCount f i a : K) + 1) / ((R : K) + 1)

def smoothedJoint {R N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    (f : Fin R → Fin N → D) (i j : Fin N) (a b : D) : K :=
  if a = b then ((jointCount f i j a b : K) + if i = j then 1 else 0) / ((R : K) + 1)
  else (jointCount f i j a b : K) / R

end
end SAP.P045b
