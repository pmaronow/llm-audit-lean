import Mathlib
import SAP.P008a.Defs.Part1
import SAP.P008a.Defs.Part2
import SAP.P008a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P008a

open MeasureTheory Filter
open scoped BigOperators Classical

noncomputable section

def pairAssignment (k : Fin 4) : Assignment 2 :=
  ![![false, false], ![false, true], ![true, false], ![true, true]] k

def pairField : Finset ℚ := {-1, 0, 1, 2, 3}

def pairNode : Fin 2 → ℚ := ![0, 2]

def pairOutcome (x : ℚ) (z : Assignment 2) : ℝ :=
  (if |x| ≤ 1 then bit (z 0) else 0) +
    (if |x - 2| ≤ 1 then bit (z 1) else 0)

def pairM (i : Fin 2) (z : Assignment 2) : ℝ :=
  lineM pairField pairNode pairOutcome i 1 z

def replicatedPairScore {M : ℕ} (i : Fin M × Fin 2)
    (z : (Fin M × Fin 2) → Bool) : ℝ :=
  (1 / 2 : ℝ) * (2 * bit (z (i.1, 0)) - 1) * (2 * bit (z (i.1, 1)) - 1)

def replicatedNode {M : ℕ} (i : Fin M × Fin 2) : ℚ := 6 * i.1.val + 2 * i.2.val

def replicatedField (M : ℕ) : Finset ℚ :=
  Finset.univ.image (fun gc : Fin M × Fin 5 => 6 * (gc.1.val : ℚ) + gc.2.val - 1)

def replicatedOutcome {M : ℕ} (x : ℚ) (z : (Fin M × Fin 2) → Bool) : ℝ :=
  ∑ i, if |x - replicatedNode i| ≤ 1 then bit (z i) else 0

def replicatedCircle {M : ℕ} (i : Fin M × Fin 2) : Finset ℚ :=
  (replicatedField M).filter (fun x => |x - replicatedNode i| = 1)

def replicatedCircleM {M : ℕ} (i : Fin M × Fin 2) (z : (Fin M × Fin 2) → Bool) : ℝ :=
  countMean (replicatedCircle i) (fun x => replicatedOutcome x z)

def replicatedSpatialScore {M : ℕ} (i : Fin M × Fin 2) (z : (Fin M × Fin 2) → Bool) : ℝ :=
  2 * bit (z i) * (replicatedCircleM i z - 5 / 4) -
    2 * (1 - bit (z i)) * (replicatedCircleM i z - 1 / 4)

abbrev RiskCell := Fin 40000

def riskBaseline : Fin 4 → ℕ := ![400, 1000, 400, 1000]

def riskOutcome (i : Fin 4) (_radius : Fin 4) (k : RiskCell) (z : Assignment 4) : ℝ :=
  if k.val < riskBaseline i - 321 * (if z i then 1 else 0) then 1 else 0

def riskM (i : Fin 4) (j : Fin 4) (z : Assignment 4) : ℝ :=
  countMean Finset.univ (fun k => riskOutcome i j k z)

def companionRiskOutcome (i : Fin 4) (_j : Fin 4) (_k : RiskCell)
    (z : Assignment 4) : ℝ := 1 - bit (z i)

def companionRiskM (i j : Fin 4) (z : Assignment 4) : ℝ :=
  countMean Finset.univ (fun k => companionRiskOutcome i j k z)

def riskSamplingProbability (Q : FiniteLaw (Assignment 4)) (b : Bool) : ℝ :=
  (16 : ℝ)⁻¹ * ∑ i : Fin 4, ∑ j : Fin 4, marginal Q (riskM i j) i b

end
end SAP.P008a
