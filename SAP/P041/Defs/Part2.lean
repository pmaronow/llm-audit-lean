import SAP.P041.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

def balancedSequences (m : ℕ) : Finset (Finset (Fin (2*m))) :=
  Finset.univ.powersetCard m

def scrutinyOutcome {n : ℕ} (z : Finset (Fin n)) (r : Fin n) : ℝ :=
  if ∃ s : Fin n, s < r ∧ s ∉ z then 1 else 0

def citationContrast (m : ℕ) (z : Finset (Fin (2*m)))
    (Y : Fin (2*m) → ℝ) : ℝ :=
  (∑ r ∈ z, Y r) / m - (∑ r ∈ Finset.univ \ z, Y r) / m

def balancedExpectation (m : ℕ) (f : Finset (Fin (2*m)) → ℝ) : ℝ :=
  (∑ z ∈ balancedSequences m, f z) / (balancedSequences m).card

def leadingCited {n : ℕ} (z : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun r => ∀ s : Fin n, s ≤ r → s ∈ z)).card

def leadingCitedProbability (m k : ℕ) : ℝ :=
  ((balancedSequences m).filter (fun z => leadingCited z = k)).card /
    ((balancedSequences m).card : ℝ)

def independentCitationExpectation : ℝ :=
  (∑ z ∈ (Finset.univ : Finset (Fin 4)).powerset,
    (∑ r : Fin 4, (if r ∈ z then (2:ℝ) else -2) * scrutinyOutcome z r) / 4) / 16

def olsCoefficients {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ y)

def olsResidual {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (X : Matrix n k ℝ) (y : n → ℝ) : n → ℝ := y - X *ᵥ olsCoefficients X y

def robustMeat {n k : Type*} [Fintype n] (X : Matrix n k ℝ)
    (u : n → ℝ) : Matrix k k ℝ := fun j l => ∑ i, (u i)^2 * X i j * X i l

def hc1Covariance {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  ((Fintype.card n : ℝ) / (Fintype.card n - Fintype.card k)) •
    ((X.transpose * X)⁻¹ * robustMeat X (olsResidual X y) * (X.transpose * X)⁻¹)

def positiveStudyGram : Matrix (Fin 4) (Fin 4) ℝ :=
  !![300,150,100,100;150,150,50,50;100,50,100,0;100,50,0,100]

def citationCellDesign : Matrix (Fin 4) (Fin 3) ℝ :=
  !![1,0,0; 1,1,0; 1,0,1; 1,1,1]

def citationCellSurvivors : Fin 4 → ℝ := ![12,25,23,42]

def citationGram : Matrix (Fin 3) (Fin 3) ℝ :=
  !![200,100,100; 100,100,50; 100,50,100]

def citationGramInverse : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3/200,-1/100,-1/100; -1/100,1/50,0; -1/100,0,1/50]

def citationBeta : Fin 3 → ℝ := ![21/100,8/25,7/25]

def binaryCellSSR (n a f : ℝ) : ℝ := a*(1-f)^2 + (n-a)*f^2

def survivalIndicator (removalHours : Option ℝ) (h : ℝ) : ℝ :=
  match removalHours with
  | none => 1
  | some t => if h < t then 1 else 0

def removalIndicator (removalHours : Option ℝ) (h : ℝ) : ℝ :=
  1 - survivalIndicator removalHours h

def armSurvivalDifference (nT nB sT sB : ℝ) : ℝ := sT/nT - sB/nB

def withinPrintedPrecision (x v : ℝ) : Prop := |x-v| ≤ 0.0005

def tenureFromYear (C Y : ℝ) : ℝ := C - Y

def yearHazard (h₀ b a g Y T w : ℝ) : ℝ :=
  h₀ * Real.exp (b*Y + a*T + g*T*Y + w)

def tenureHazard (h₀ b a g C L T w : ℝ) : ℝ :=
  (h₀ * Real.exp (C*b)) * Real.exp ((-b)*L + (a+C*g)*T + (-g)*T*L + w)

def illustrativeYearRelativeHazard (T Y : ℝ) : ℝ :=
  Real.exp (Real.log (132/125) * T * (Y-2009))

end SAP.P041
