import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

def positiveHazard (q : ℝ) : ℝ := -2 * Real.log q / 12

def negativeHazard (q : ℝ) : ℝ := -3 * Real.log q / 12

def exponentialSurvival (hazard t : ℝ) : ℝ := Real.exp (-hazard * t)

def twelveHourContrast (q : ℝ) : ℝ :=
  exponentialSurvival (positiveHazard q) 12 -
    exponentialSurvival (negativeHazard q) 12

def binomialCountProbability (n k : ℕ) (p : ℝ) : ℝ :=
  (n.choose k : ℝ) * p^k * (1-p)^(n-k)

def observedSurvivalContrast (nP nN rP rN : ℝ) : ℝ :=
  (1-rP/nP) - (1-rN/nN)

def relativeIncrease (pA pB : ℝ) : ℝ := 100 * (pA / pB - 1)

def symmetricDifference (a b : ℝ) : ℝ := 100 * |a - b| / ((a + b) / 2)

def roundsWhole (x : ℝ) (k : ℤ) : Prop := (k:ℝ) - 1 / 2 ≤ x ∧ x < (k:ℝ) + 1 / 2

def logHazardSE (h s : ℝ) : ℝ := s/h

def hazardWald (h s : ℝ) : ℝ := h * Real.log h / s

def normalTwoSided (z : ℝ) : ℝ :=
  2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-|z|)

def printedInterval (v x : ℝ) : Prop := v-0.0005 ≤ x ∧ x ≤ v+0.0005

def hazardWaldInterval (h s : ℝ) : Set ℝ :=
  Set.Icc (Real.exp (Real.log h - (49/25)*logHazardSE h s))
    (Real.exp (Real.log h + (49/25)*logHazardSE h s))

def betweenHazardWald (hF sF hA sA : ℝ) : ℝ :=
  (Real.log hF - Real.log hA) /
    Real.sqrt ((logHazardSE hF sF)^2 + (logHazardSE hA sA)^2)

def significanceTier (z : ℝ) : ℕ :=
  if normalTwoSided z < 0.01 then 3 else if normalTwoSided z < 0.05 then 2
  else if normalTwoSided z < 0.10 then 1 else 0

end SAP.P041
