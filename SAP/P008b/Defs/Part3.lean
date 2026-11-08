import SAP.P008b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

abbrev BlockCell := Fin 5 × Fin 5

def blockBoundary : Finset BlockCell :=
  Finset.univ.filter (fun c => c.1 = 0 ∨ c.1 = 4 ∨ c.2 = 0 ∨ c.2 = 4)

def blockY (c : BlockCell) (z : Bool) : ℝ :=
  if c ∈ blockBoundary then 0 else bit z

def rasterBoundary (R : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) := by
  classical
  exact R.filter (fun x => ∃ a b : Fin 3,
    (a.val ≠ 1 ∨ b.val ≠ 1) ∧
    (x.1 + a.val - 1, x.2 + b.val - 1) ∉ R)

def rasterEdgeZeroAverage (R : Finset (ℤ × ℤ)) (Y : (ℤ × ℤ) → ℝ) : ℝ :=
  countMean (rasterBoundary R) Y

def rasterAreaAverage (R : Finset (ℤ × ℤ)) (Y : (ℤ × ℤ) → ℝ) : ℝ :=
  countMean R Y

/-- Index (u,v) has cell center (u+1/2,v+1/2) in the specified 20-by-10 raster. -/
abbrev PolygonRasterCell := Fin 20 × Fin 10

def rasterPolygonLeft (i : Fin 2) : ℕ := if i = 0 then 2 else 12

def rasterPolygonCells (i : Fin 2) : Finset PolygonRasterCell :=
  Finset.univ.filter (fun c => rasterPolygonLeft i ≤ c.1.val ∧
    c.1.val < rasterPolygonLeft i + 5 ∧ 2 ≤ c.2.val ∧ c.2.val < 7)

def rasterPolygonBoundary (i : Fin 2) : Finset PolygonRasterCell :=
  (rasterPolygonCells i).filter (fun c => c.1.val = rasterPolygonLeft i ∨
    c.1.val = rasterPolygonLeft i + 4 ∨ c.2.val = 2 ∨ c.2.val = 6)

def polygonRasterOutcome (c : PolygonRasterCell) (z : Assignment 2) : ℝ :=
  if 3 ≤ c.1.val ∧ c.1.val ≤ 5 ∧ 3 ≤ c.2.val ∧ c.2.val ≤ 5 then bit (z 0) else 0

def polygonRasterEdgeM (i : Fin 2) (z : Assignment 2) : ℝ :=
  countMean (rasterPolygonBoundary i) (fun c => polygonRasterOutcome c z)

def polygonRasterAreaM (i : Fin 2) (z : Assignment 2) : ℝ :=
  countMean (rasterPolygonCells i) (fun c => polygonRasterOutcome c z)

def realLineCircle {N : ℕ} (field : Finset ℚ) (node : Fin N → ℚ)
    (i : Fin N) (d : ℝ) : Finset ℚ :=
  field.filter (fun x => ((|x - node i| : ℚ) : ℝ) = d)

def realLineM {N : ℕ} (field : Finset ℚ) (node : Fin N → ℚ)
    (Y : ℚ → Assignment N → ℝ) (i : Fin N) (d : ℝ) (z : Assignment N) : ℝ :=
  countMean (realLineCircle field node i d) (fun x => Y x z)

def cancellingOutcome (x : ℚ) (z : Assignment 1) : ℝ :=
  if x = 1 then bit (z 0) else if x = -1 then -bit (z 0) else 0

end

end SAP.P008b
