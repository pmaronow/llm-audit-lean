import Mathlib
import SAP.P001b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical
noncomputable section

abbrev DyadicIndex := Σ m : ℕ, Fin (2 ^ m)

def dyadicLocation (i : DyadicIndex) : ℝ := (2 * (i.2 : ℝ) + 1) / (2 : ℝ) ^ (i.1 + 1)
def dyadicWeight (i : DyadicIndex) : ℝ := (1/2 : ℝ) ^ (2 * i.1 + 1)
def dyadicDistributionFunction (x : ℝ) : ℝ :=
  ∑' i, if dyadicLocation i ≤ x then dyadicWeight i else 0

def uniformDistributionFunction (x : ℝ) : ℝ := max 0 (min 1 x)
def closedUniformDensity (x : ℝ) : ℝ := if x ∈ Set.Icc 0 1 then 1 else 0
def openUniformDensity (x : ℝ) : ℝ := if x ∈ Set.Ioo 0 1 then 1 else 0
def modifiedUniformDensity (x : ℝ) : ℝ :=
  if x = 1/3 then 3/2 else closedUniformDensity x

def negativeRectangleDensity (z : ℝ × ℝ) : ℝ :=
  if z.1 ∈ Set.Ioo 0 1 ∧ z.2 ∈ Set.Ioo (-1) 0 then 1 else 0

def infiniteSliceDensity (z : ℝ × ℝ) : ℝ :=
  (Real.exp z.1 / (1 + Real.exp z.1)) ^ 2 /
    (Real.pi * (1 + z.2 ^ 2 * Real.exp (2 * z.1)))

/-- The actual successive closed intervals of the fat Cantor construction. -/
def cantorInterval : List Bool → ℝ × ℝ
  | [] => (0, 1)
  | b :: w =>
    let I := cantorInterval w
    let middle := (I.1 + I.2) / 2
    let halfGap := (1/4 : ℝ) ^ (w.length + 1) / 2
    if b then (middle + halfGap, I.2) else (I.1, middle - halfGap)

def cantorStage (n : ℕ) : Set ℝ :=
  {x | ∃ w : List Bool, w.length = n ∧ x ∈ Set.Icc (cantorInterval w).1 (cantorInterval w).2}
def fatCantorSet : Set ℝ := ⋂ n : ℕ, cantorStage n
def cantorDensity (x : ℝ) : ℝ := if x ∈ fatCantorSet then 2 else 0
def cantorProbability : Measure fatCantorSet :=
  (2 : ℝ≥0∞) • volume.comap (fun x : fatCantorSet => x.val)

/-- The printed expression, with Lean's total real division at its endpoints. -/
def printedBivariateNormal (mx my sx sy ρ : ℝ) (xy : ℝ × ℝ) : ℝ :=
  Real.exp (-(((xy.1-mx)/sx)^2 + ((xy.2-my)/sy)^2 -
    2*ρ*(xy.1-mx)*(xy.2-my)/(sx*sy))/(2*(1-ρ^2))) /
    (2*Real.pi*sx*sy*Real.sqrt (1-ρ^2))

end
end SAP.P001b
