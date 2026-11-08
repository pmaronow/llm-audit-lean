import SAP.P005a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005a

noncomputable section
open Finset Filter
open scoped BigOperators Matrix Topology

/-- Fixed covariates and both fixed potential-outcome arrays in the Neyman model. -/
structure Population (n d : ℕ) where
  x : Fin n → Fin d → ℝ
  yT : Fin n → ℝ
  yC : Fin n → ℝ

def dot {d : ℕ} (u v : Fin d → ℝ) : ℝ := ∑ k, u k * v k

def xMean {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) : Fin d → ℝ :=
  fun k => mean S (fun i => P.x i k)

def gram {n d : ℕ} (P : Population n d) : Matrix (Fin d) (Fin d) ℝ :=
  fun k l => popMean (fun i => P.x i k * P.x i l)

/-- Assumption 2 at the specified population size: zero mean and identity Gram matrix. -/
def standardized {n d : ℕ} (P : Population n d) : Prop :=
  xMean P univ = 0 ∧ gram P = 1

def leverage {n d : ℕ} (P : Population n d) (i : Fin n) : ℝ := dot (P.x i) (P.x i)

/-- Maximum leverage divided by population size; substantive assertions use n > 0. -/
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

/-- Within-arm slope as defined in Section 4; inverse uses require nonzero determinant. -/
def armBetaHat {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (y : Fin n → ℝ) : Fin d → ℝ := (armL P S)⁻¹ *ᵥ armN P S y

def noninteractedRegular {n d : ℕ} (P : Population n d) (m : ℕ) : Prop :=
  ∀ S ∈ design n m, (Lhat P m S).det ≠ 0

def interactedRegular {n d : ℕ} (P : Population n d) (m : ℕ) : Prop :=
  ∀ S ∈ design n m, (armL P S).det ≠ 0 ∧ (armL P (control S)).det ≠ 0

def adjustedATE {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  mean S P.yT - mean (control S) P.yC - dot (xMean P S - xMean P (control S)) (betaHat P m S)

def interactedATE {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) : ℝ :=
  mean S P.yT - mean (control S) P.yC -
    (dot (xMean P S) (armBetaHat P S P.yT) -
      dot (xMean P (control S)) (armBetaHat P (control S) P.yC))

end
end SAP.P005a
