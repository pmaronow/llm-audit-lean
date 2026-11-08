import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005b

noncomputable section
open scoped BigOperators Matrix
open Finset Filter

/-! Finite complete randomization and fixed population data. All denominators
are guarded by the target hypotheses when the quantities are used. -/

def design (n m : ℕ) : Finset (Finset (Fin n)) := univ.powersetCard m

def control {n : ℕ} (S : Finset (Fin n)) : Finset (Fin n) := univ \ S

def mean {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) : ℝ :=
  (∑ i ∈ S, a i) / S.card

def popMean {n : ℕ} (a : Fin n → ℝ) : ℝ := mean univ a

def expectation {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) : ℝ :=
  (∑ S ∈ design n m, f S) / (design n m).card

def variance {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) : ℝ :=
  expectation m (fun S => (f S - expectation m f)^2)

def probability {n : ℕ} (m : ℕ) (event : Finset (Fin n) → Prop) : ℝ :=
  by
    classical
    exact ((design n m).filter event).card / ((design n m).card : ℝ)

def sampleCov {n : ℕ} (S : Finset (Fin n)) (a b : Fin n → ℝ) : ℝ :=
  mean S (fun i => a i * b i) - mean S a * mean S b

def popCov {n : ℕ} (a b : Fin n → ℝ) : ℝ := sampleCov univ a b

def centered {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ := a i - popMean a

def covarianceBound {n : ℕ} (m : ℕ) (a b : Fin n → ℝ) : ℝ :=
  2 * ((n : ℝ) - m) / ((m : ℝ) * (n - 1)) *
    popMean (fun i => (a i * b i - popMean (fun j => a j * b j))^2) +
  2 * ((n : ℝ) - m) * n / ((m : ℝ)^3 * (n - 1)) *
    popMean (fun i => a i^2) * popMean (fun i => b i^2)

inductive Arm | treated | control deriving DecidableEq

def armSet {n : ℕ} (t : Arm) (S : Finset (Fin n)) : Finset (Fin n) :=
  match t with | .treated => S | .control => control S

def armSize (n m : ℕ) (t : Arm) : ℕ :=
  match t with | .treated => m | .control => n - m

structure Population (n d : ℕ) where
  x : Fin n → Fin d → ℝ
  yT : Fin n → ℝ
  yC : Fin n → ℝ

def dot {d : ℕ} (u v : Fin d → ℝ) : ℝ := ∑ k, u k * v k

def xMean {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) : Fin d → ℝ :=
  fun k => mean S (fun i => P.x i k)

def gram {n d : ℕ} (P : Population n d) : Matrix (Fin d) (Fin d) ℝ :=
  fun k l => popMean (fun i => P.x i k * P.x i l)

def standardized {n d : ℕ} (P : Population n d) : Prop :=
  xMean P univ = 0 ∧ gram P = 1

def leverage {n d : ℕ} (P : Population n d) (i : Fin n) : ℝ := dot (P.x i) (P.x i)

def kappa {n d : ℕ} (P : Population n d) : ℝ :=
  sSup (Set.range (fun i => leverage P i / n))

def ate {n d : ℕ} (P : Population n d) : ℝ := popMean P.yT - popMean P.yC

def pT (n m : ℕ) : ℝ := (m : ℝ) / n

def pC (n m : ℕ) : ℝ := ((n : ℝ) - m) / n

def populationSlope {n d : ℕ} (P : Population n d) (y : Fin n → ℝ) : Fin d → ℝ :=
  fun k => popMean (fun i => y i * P.x i k)

def N {n d : ℕ} (P : Population n d) (m : ℕ) : Fin d → ℝ :=
  pT n m • populationSlope P P.yT + pC n m • populationSlope P P.yC

def armL {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) : Matrix (Fin d) (Fin d) ℝ :=
  fun k l => mean S (fun i => P.x i k * P.x i l) - xMean P S k * xMean P S l

def armN {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (y : Fin n → ℝ) : Fin d → ℝ :=
  fun k => mean S (fun i => y i * P.x i k) - mean S y * xMean P S k

def Lhat {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) :
    Matrix (Fin d) (Fin d) ℝ :=
  1 - pT n m • Matrix.vecMulVec (xMean P S) (xMean P S) -
    pC n m • Matrix.vecMulVec (xMean P (control S)) (xMean P (control S))

def Nhat {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : Fin d → ℝ :=
  pT n m • armN P S P.yT + pC n m • armN P (control S) P.yC

def betaHat {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : Fin d → ℝ :=
  (Lhat P m S)⁻¹ *ᵥ Nhat P m S

def armBetaHat {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (y : Fin n → ℝ) : Fin d → ℝ := (armL P S)⁻¹ *ᵥ armN P S y

def noninteractedRegular {n d : ℕ} (P : Population n d) (m : ℕ) : Prop :=
  ∀ S ∈ design n m, (Lhat P m S).det ≠ 0

def interactedRegular {n d : ℕ} (P : Population n d) (m : ℕ) : Prop :=
  ∀ S ∈ design n m, (armL P S).det ≠ 0 ∧ (armL P (control S)).det ≠ 0

end
end SAP.P005b
