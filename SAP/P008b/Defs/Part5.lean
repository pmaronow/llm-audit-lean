import SAP.P008b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

/-- The adjacent-buffer and centered-band counterexample, using two rectangles. -/
def T16Statement : Prop :=
((∀ i c, donutSpatialDistance i (i, c) = bufferCellDistance c) ∧
    (∀ i j c, i ≠ j → 5 < donutSpatialDistance i (j, c)) ∧
    (donutSpatialBuffer 0 2).card = 1 ∧
    (∑ ic ∈ donutSpatialBuffer 0 2, donutSpatialY ic ![true, false]) = 4 ∧
    (donutSpatialBuffer 0 4).card = 3 ∧
    (∑ ic ∈ donutSpatialBuffer 0 4, donutSpatialY ic ![true, false]) = 6 ∧
    (∀ mode, donutSpatialMeans mode 1 ![true, false] = 0) ∧
    hajek (donutSpatialMeans 0) ![true, false] = 1 ∧
    hajek (donutSpatialMeans 1) ![true, false] = 4 ∧
    hajek (donutSpatialMeans 2) ![true, false] = 2 ∧
    hajek (donutSpatialMeans 0) ![true, false] ≠
      hajek (donutSpatialMeans 1) ![true, false]) ∧
    (countMean (bufferCells 4 \ bufferCells 2) bufferCellOutcome = 1 ∧
    countMean (Finset.univ.filter (fun c =>
      3 ≤ bufferCellDistance c ∧ bufferCellDistance c ≤ 5)) bufferCellOutcome = 4 ∧
    countMean (bufferCells 4) bufferCellOutcome = 2)

/-- The complete 20-by-10 raster counterexample with two 5-by-5 polygons. -/
def T19Statement : Prop :=
((Finset.univ : Finset PolygonRasterCell).card = 200 ∧
    (∀ i, (rasterPolygonCells i).card = 25 ∧ (rasterPolygonBoundary i).card = 16) ∧
    (∀ i c, c ∈ rasterPolygonCells i → (c ∈ rasterPolygonBoundary i ↔
      ∃ a b : Fin 3, (a.val ≠ 1 ∨ b.val ≠ 1) ∧
        ((c.1.val : ℤ) + a.val - 1 < rasterPolygonLeft i ∨
         (rasterPolygonLeft i + 5 : ℤ) ≤ (c.1.val : ℤ) + a.val - 1 ∨
         (c.2.val : ℤ) + b.val - 1 < 2 ∨ 7 ≤ (c.2.val : ℤ) + b.val - 1))) ∧
    (∀ c z, polygonRasterOutcome c z = 0 ∨ polygonRasterOutcome c z = 1) ∧
    (∀ i z, polygonRasterEdgeM i z = 0) ∧
    (∀ i z, polygonRasterAreaM i z = if i = 0 then (9 / 25 : ℝ) * bit (z 0) else 0) ∧
    commonBernoulli (uniformLaw (Assignment 2)) (1 / 2) ∧
    (uniformLaw (Assignment 2)).mass ![true, false] = 1 / 4 ∧
    hajek polygonRasterEdgeM ![true, false] = 0 ∧
    hajek polygonRasterAreaM ![true, false] = 9 / 25 ∧
    finiteAMR (uniformLaw (Assignment 2)) polygonRasterEdgeM = 0 ∧
    finiteAMR (uniformLaw (Assignment 2)) polygonRasterAreaM = 9 / 50 ∧
    (0 : ℝ) ≠ 9 / 25) ∧
  (∀ i, (rasterPolygonCells i \ rasterPolygonBoundary i).card = 9) ∧
  (∀ i, (∑ c ∈ rasterPolygonCells i, polygonRasterOutcome c ![true, false]) =
    if i = 0 then 9 else 0) ∧
  (∀ i, marginal (uniformLaw (Assignment 2)) (polygonRasterAreaM i) i true -
      marginal (uniformLaw (Assignment 2)) (polygonRasterAreaM i) i false =
    if i = 0 then 9 / 25 else 0) ∧
  nTreated ![true, false] = 1 ∧ nControl ![true, false] = 1

end

end SAP.P008b
