import Mathlib
import SAP.P008b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b

open scoped BigOperators

noncomputable section

/-- The filled half-side-1/8 squares with centers (0,0) and (20,0). -/
def squarePolygonW3 (i : Fin 2) : Set Plane :=
  {x | 20 * (i : ℝ) - 1 / 8 ≤ x 0 ∧ x 0 ≤ 20 * (i : ℝ) + 1 / 8 ∧
    -1 / 8 ≤ x 1 ∧ x 1 ≤ 1 / 8}

/-- Horizontal offsets of the four nonmissing cells at each polygon. -/
def squareOffsetW3 : Fin 4 → ℝ := ![0, 5 / 2, 7 / 2, 9 / 2]

/-- The eight specified outcome-cell centers; no other cells are nonmissing. -/
def squareCellW3 (i : Fin 2) (c : Fin 4) : Plane :=
  WithLp.toLp 2 ![20 * (i : ℝ) + squareOffsetW3 c, 0]

/-- Euclidean distance to the filled polygon, including zero for interior points. -/
def squareDistanceW3 (i : Fin 2) (ic : Fin 2 × Fin 4) : ℝ :=
  Metric.infDist (squareCellW3 ic.1 ic.2) (squarePolygonW3 i)

/-- Centers of a common raster of square cells of side 1/2: the cell at (a/2,b/2)
is [a/2-1/4,a/2+1/4] times [b/2-1/4,b/2+1/4]. -/
def halfUnitRasterW3 : Set Plane :=
  {x | ∃ a b : ℤ, x = WithLp.toLp 2 ![(a : ℝ) / 2, (b : ℝ) / 2]}

/-- Buffer membership uses the center of each nonmissing cell. -/
def squareBufferW3 (i : Fin 2) (r : ℝ) : Finset (Fin 2 × Fin 4) :=
  Finset.univ.filter (fun ic => squareDistanceW3 i ic ≤ r)

/-- The band centered at radius 4 with half-width 1 and total width 2. -/
def squareCenteredW3 (i : Fin 2) : Finset (Fin 2 × Fin 4) :=
  Finset.univ.filter (fun ic =>
    4 - 1 ≤ squareDistanceW3 i ic ∧ squareDistanceW3 i ic ≤ 4 + 1)

/-- Region means: adjacent buffers (mode 0), centered band (mode 1), disk (mode 2).
The existing outcome schedule has treated-cell outcomes (4,2,0,8) at assignment
(true,false), and zero control-cell outcomes. -/
def squareMeansW3 (mode : Fin 3) (i : Fin 2) (z : Assignment 2) : ℝ :=
  countMean (if mode = 0 then squareBufferW3 i 4 \ squareBufferW3 i 2
    else if mode = 1 then squareCenteredW3 i else squareBufferW3 i 4)
    (fun ic => donutSpatialY ic z)

/-- The two grid radii dVec=(2,4), indexed from zero. -/
def squareRadiusW3 : Fin 2 → ℝ := ![2, 4]

/-- The supplied archived polygon formula, including its first-index branch.
At the second index it divides the difference of buffer sums by the difference
of buffer counts, cast to real numbers before subtraction. There is no bandwidth
argument. The theorem below proves that every denominator used is positive. -/
def squareArchivedMeanW3 (i j : Fin 2) (z : Assignment 2) : ℝ :=
  if j = 0 then
    countMean (squareBufferW3 i (squareRadiusW3 j)) (fun ic => donutSpatialY ic z)
  else
    ((∑ ic ∈ squareBufferW3 i (squareRadiusW3 j), donutSpatialY ic z) -
      (∑ ic ∈ squareBufferW3 i (squareRadiusW3 (j - 1)), donutSpatialY ic z)) /
    ((squareBufferW3 i (squareRadiusW3 j)).card -
      (squareBufferW3 i (squareRadiusW3 (j - 1))).card : ℝ)

/-- P008-T16; pp. 143 and 145 (PDF pp. 6 and 8); supplied archived
polygon-buffer formula, source lines 115–118; canonical fixture corrected
2026-11-04. The usual measure-theoretic conditions are assumed.
For the filled squares [-1/8,1/8]^2 and its translate by (20,0), the eight
specified centers lie on a common half-unit raster. Their distances to their
own filled polygon are 0,19/8,27/8,35/8 and all cross distances exceed 5.
The center is interior, at distance 1/8 from the topological boundary and zero
from the filled polygon. With outcomes (4,2,0,8) and zero controls, the buffers
at radii 2 and 4 have treated counts/sums (1,4) and (3,6). The supplied archived
donut formula averages the added cells in (2,4], giving 1; the band [3,5], of
the same total width 2 and centered at 4, gives 4; the disk gives 2. There is
one polygon in each assignment arm, so the respective Hajek estimates are
1,4,2. Thus this archived donut estimate differs from the centered-band estimate.
All region counts, the buffer-count difference and both arm counts are nonzero. -/
def T16WholeStatement_W3 : Prop :=
  (∀ i : Fin 2,
    (squarePolygonW3 i).Nonempty ∧ IsClosed (squarePolygonW3 i) ∧
    squareCellW3 i 0 ∈ interior (squarePolygonW3 i) ∧
    (frontier (squarePolygonW3 i)).Nonempty ∧
    Metric.infDist (squareCellW3 i 0) (frontier (squarePolygonW3 i)) = 1 / 8 ∧
    squareDistanceW3 i (i, 0) = 0) ∧
  Function.Injective (fun ic : Fin 2 × Fin 4 => squareCellW3 ic.1 ic.2) ∧
  (∀ i c, squareCellW3 i c ∈ halfUnitRasterW3) ∧
  (∀ i c, squareDistanceW3 i (i, c) = bufferCellDistance c) ∧
  (∀ i j c, i ≠ j → 5 < squareDistanceW3 i (j, c)) ∧
  (∀ c, donutSpatialY (0, c) ![true, false] = bufferCellOutcome c ∧
    donutSpatialY (1, c) ![true, false] = 0) ∧
  (nTreated ![true, false] = 1 ∧ nControl ![true, false] = 1) ∧
  (∀ i : Fin 2,
    squareBufferW3 i 2 = {(i, 0)} ∧
    squareBufferW3 i 4 = {(i, 0), (i, 1), (i, 2)} ∧
    squareBufferW3 i 4 \ squareBufferW3 i 2 = {(i, 1), (i, 2)} ∧
    squareBufferW3 i 4 \ squareBufferW3 i 2 =
      Finset.univ.filter (fun ic =>
        2 < squareDistanceW3 i ic ∧ squareDistanceW3 i ic ≤ 4) ∧
    squareCenteredW3 i = {(i, 2), (i, 3)}) ∧
  (∀ i : Fin 2,
    (squareBufferW3 i 2).card = 1 ∧
    (squareBufferW3 i 4).card = 3 ∧
    ((squareBufferW3 i 4).card - (squareBufferW3 i 2).card : ℝ) = 2 ∧
    (squareBufferW3 i 4 \ squareBufferW3 i 2).card = 2 ∧
    (squareCenteredW3 i).card = 2) ∧
  ((∑ ic ∈ squareBufferW3 0 2, donutSpatialY ic ![true, false]) = 4 ∧
    (∑ ic ∈ squareBufferW3 0 4, donutSpatialY ic ![true, false]) = 6) ∧
  (∀ i z, squareArchivedMeanW3 i 1 z = squareMeansW3 0 i z) ∧
  (∀ mode : Fin 3,
    squareMeansW3 mode 0 ![true, false] = (![1, 4, 2] : Fin 3 → ℝ) mode ∧
    squareMeansW3 mode 1 ![true, false] = 0) ∧
  (∀ i : Fin 2,
    squareArchivedMeanW3 i 1 ![true, false] = if i = 0 then 1 else 0) ∧
  (hajek (fun i z => squareArchivedMeanW3 i 1 z) ![true, false] = 1 ∧
    hajek (squareMeansW3 1) ![true, false] = 4 ∧
    hajek (squareMeansW3 2) ![true, false] = 2 ∧
    hajek (fun i z => squareArchivedMeanW3 i 1 z) ![true, false] ≠
      hajek (squareMeansW3 1) ![true, false])

end

end SAP.P008b
