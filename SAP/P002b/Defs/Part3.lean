import SAP.P002b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The four rows are (1,0), (-1,0), (0,1), and (0,-1), in that order. -/
def coordinateExample (i : Fin 4) (s : Fin 2) : ℝ :=
  if i.val = 0 then (if s.val = 0 then 1 else 0)
  else if i.val = 1 then (if s.val = 0 then -1 else 0)
  else if i.val = 2 then (if s.val = 1 then 1 else 0)
  else (if s.val = 1 then -1 else 0)

/-- Finite maximum with zero adjoined. All Challenge uses are for nonnegative
arrays of positive size, so adjoining zero does not alter the intended maximum. -/
def maximum {n} (q : Fin n → ℝ) : ℝ := (insert 0 (Finset.univ.image q)).max' (by simp)

/-- The printed nested coverage infimum, in extended nonnegative reals.
An empty inner model class contributes the top value. -/
def infCoverageTheta (n : ℕ) (δ r A α : ℝ) : ℝ≥0∞ :=
  ⨅ β : ℝ, ⨅ P : {P : Population n // Theta P δ r A ∧ late P = β},
    ENNReal.ofReal (coverage P.val β α)

/-- The adjusted nested coverage infimum, with the same extended-real convention. -/
def infCoverageXi (n k : ℕ) (δ e A B r α : ℝ) : ℝ≥0∞ :=
  ⨅ β : ℝ, ⨅ P : {P : CovPopulation n k // Xi P δ e A B r ∧ late P.pop = β},
    ENNReal.ofReal (adjustedCoverage P.val β α)

/-- The corrected control-arm expression (E.29), using Mathlib's totalized
matrix inverse and real division. It agrees with the displayed ordinary expression
when the control Gram is invertible and oracle design variance is positive.
T20WholeStatement asserts convergence without imposing those two conditions. -/
def controlRemainder {n k} (P : CovPopulation n k) (S : Finset (Fin n)) : ℝ :=
  groupMean Sᶜ (fun i => dotProduct (xCirc P.x i)
    ((gram P.x Sᶜ)⁻¹ *ᵥ score P.x Sᶜ (residual P false (late P.pop)))) /
      Real.sqrt (designVariance P.pop (oracleTau P (late P.pop)))

def adjustedWald {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  adjustedTau P Y S / adjustedTau P D S

abbrev IVIndex (k : ℕ) := Sum (Fin 2) (Bool × Fin k)

def ivRow {n k} (P : CovPopulation n k) (D : Fin n → ℝ)
    (S : Finset (Fin n)) (i : Fin n) : IVIndex k → ℝ
  | .inl j => if j=0 then D i else 1
  | .inr (a,s) => if decide (i ∈ S) = a then P.x i s else 0

def instrumentRow {n k} (P : CovPopulation n k) (S : Finset (Fin n)) (i : Fin n) :=
  ivRow P (fun l => if l ∈ S then 1 else 0) S i

def ivCross {n k} (P : CovPopulation n k) (D : Fin n → ℝ) (S : Finset (Fin n)) :
    Matrix (IVIndex k) (IVIndex k) ℝ :=
  fun s t => mean fun i => instrumentRow P S i s * ivRow P D S i t

def instrumentGram {n k} (P : CovPopulation n k) (S : Finset (Fin n)) :
    Matrix (IVIndex k) (IVIndex k) ℝ :=
  fun s t => mean fun i => instrumentRow P S i s * instrumentRow P S i t

def ivCoefficients {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ) (S : Finset (Fin n)) :=
  (ivCross P D S)⁻¹ *ᵥ (fun s => mean fun i => instrumentRow P S i s*Y i)

end
end SAP.P002b
