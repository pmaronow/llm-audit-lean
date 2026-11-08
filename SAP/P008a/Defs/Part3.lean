import Mathlib
import SAP.P008a.Defs.Part1
import SAP.P008a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P008a

open MeasureTheory Filter
open scoped BigOperators Classical

noncomputable section

def groupMean {N : ℕ} (z : Assignment N) (M : Fin N → ℝ) (b : Bool) : ℝ :=
  if b then (∑ i, bit (z i) * M i) / nTreated z
  else (∑ i, (1 - bit (z i)) * M i) / nControl z

def groupResidual {N : ℕ} (z : Assignment N) (M : Fin N → ℝ) (i : Fin N) : ℝ :=
  M i - groupMean z M (z i)

def contrastWeight {N : ℕ} (z : Assignment N) (i : Fin N) : ℝ :=
  bit (z i) / nTreated z - (1 - bit (z i)) / nControl z

def regressionScore {N : ℕ} (z : Assignment N) (M : Fin N → ℝ) (i : Fin N) : ℝ :=
  contrastWeight z i * groupResidual z M i

def hac {N : ℕ} (g : Fin N → ℝ) (D : Fin N → Fin N → ℝ) (c : ℝ) : ℝ :=
  ∑ i, ∑ j, g i * g j * (if D i j ≤ c then 1 else 0)

def binaryDesign {N : ℕ} (z : Assignment N) : Matrix (Fin N) (Fin 2) ℝ :=
  fun i j => if j = 0 then 1 else bit (z i)

def olsResidual {N : ℕ} (z : Assignment N) (M : Fin N → ℝ) : Fin N → ℝ :=
  let X := binaryDesign z
  fun i => M i - (X.mulVec (((X.transpose * X)⁻¹).mulVec (X.transpose.mulVec M))) i

def olsMeat {N : ℕ} (z : Assignment N) (M : Fin N → ℝ)
    (D : Fin N → Fin N → ℝ) (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => ∑ i, ∑ j, (if D i j ≤ c then 1 else 0) *
    olsResidual z M i * olsResidual z M j * binaryDesign z i a * binaryDesign z j b

def archivedVariance {N : ℕ} (g : Fin N → ℝ) (D : Fin N → Fin N → ℝ)
    (cutoff : ℝ) (position : ℕ) : ℝ :=
  hac g D (if 0 < cutoff then cutoff + position else cutoff)

def physicalVariance {N : ℕ} (g : Fin N → ℝ) (D : Fin N → Fin N → ℝ)
    (cutoff : ℝ) (_position : ℕ) : ℝ := hac g D cutoff

def bandwidthExampleDistance (i j : Fin 4) : ℝ := |2 * (i : ℝ) - 2 * (j : ℝ)|

def toyNode (i : Fin 4) : Plane :=
  WithLp.toLp 2 ((![![2028297641 / 2147483648, 4318520789 / 2147483648],
    ![7976664621 / 2147483648, 1029755657 / 268435456],
    ![1053580245 / 536870912, 2017196647 / 2147483648],
    ![7110225301 / 2147483648, 499145583 / 1073741824]] : Fin 4 → Fin 2 → ℝ) i)

def bandwidthSpatialNode (i : Fin 4) : ℚ := 2 * i.val

def bandwidthSpatialOutcome (x : Plane) (_z : Assignment 4) : ℝ :=
  ∑ i : Fin 4, if dist x (lineEmbedding (bandwidthSpatialNode i)) ≤ 3 / 10
    then 2 * (i.val : ℝ) else 0

def bandwidthSpatialMeasure : Measure Plane :=
  ∑ a : Fin 4 × Fin 4,
    Measure.dirac (lineEmbedding (bandwidthSpatialNode a.1 + (a.2.val : ℚ) / 10))

def bandwidthSpatialModel : SpatialModel 4 where
  field := Set.univ
  node i := lineEmbedding (bandwidthSpatialNode i)
  node_mem _ := Set.mem_univ _
  ζ := bandwidthSpatialMeasure
  Y := bandwidthSpatialOutcome

def bandwidthSpatialRadius (j : Fin 3) : ℝ := (j.val + 1 : ℝ) / 10

def bandwidthShortGrid : Fin 2 → ℝ := ![1 / 5, 3 / 10]

def bandwidthLongGrid : Fin 3 → ℝ := ![1 / 10, 1 / 5, 3 / 10]

end
end SAP.P008a
