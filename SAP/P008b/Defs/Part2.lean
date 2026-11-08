import SAP.P008b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

def SpatialModel.band {N : ℕ} (P : SpatialModel N) (i : Fin N) (d k : ℝ) : Set Plane :=
  {x | x ∈ P.field ∧ d - k ≤ dist (P.node i) x ∧ dist (P.node i) x ≤ d + k}

def SpatialModel.bandAverage {N : ℕ} (P : SpatialModel N) (i : Fin N) (d k : ℝ)
    (f : Plane → ℝ) : ℝ :=
  let μ := P.ζ.restrict (P.band i d k)
  (μ Set.univ).toReal⁻¹ * ∫ x, f x ∂μ

def SpatialModel.disk {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) : Set Plane :=
  {x | x ∈ P.field ∧ dist (P.node i) x ≤ d}

def SpatialModel.sharpNull {N : ℕ} (P : SpatialModel N) : Prop :=
  ∀ x ∈ P.field, ∀ z, P.Y x z = P.Y x (fun _ => false)

def additiveOutcome {N : ℕ} (base : Plane → ℝ) (g : Fin N → Plane → ℝ)
    (x : Plane) (z : Assignment N) : ℝ := base x + ∑ k, bit (z k) * g k x

def toyKernel (r : ℝ) : ℝ := 2 * Real.exp (-2 * r) - (128 / 3) * r ^ 4 * Real.exp (-4 * r)

def bufferCellDistance : Fin 4 → ℝ := ![0, 19 / 8, 27 / 8, 35 / 8]

def bufferCellOutcome : Fin 4 → ℝ := ![4, 2, 0, 8]

def bufferCells (r : ℝ) : Finset (Fin 4) :=
  Finset.univ.filter (fun c => bufferCellDistance c ≤ r)

/-- Boundary of the rectangle [a,a+1] times [-1,1]; the two origins are 0 and 100. -/
def donutPolygonBoundary (a : ℝ) : Set Plane :=
  {x | a ≤ x 0 ∧ x 0 ≤ a + 1 ∧ -1 ≤ x 1 ∧ x 1 ≤ 1 ∧
    (x 0 = a ∨ x 0 = a + 1 ∨ x 1 = -1 ∨ x 1 = 1)}

def donutSpatialCell (i : Fin 2) (c : Fin 4) : Plane :=
  WithLp.toLp 2 ![100 * (i : ℝ) + 1 + bufferCellDistance c, 0]

def donutSpatialY (ic : Fin 2 × Fin 4) (z : Assignment 2) : ℝ :=
  if ic.1 = 0 then bit (z 0) * bufferCellOutcome ic.2 else 0

def donutSpatialDistance (i : Fin 2) (ic : Fin 2 × Fin 4) : ℝ :=
  Metric.infDist (donutSpatialCell ic.1 ic.2) (donutPolygonBoundary (100 * (i : ℝ)))

def donutSpatialBuffer (i : Fin 2) (r : ℝ) : Finset (Fin 2 × Fin 4) :=
  Finset.univ.filter (fun ic => donutSpatialDistance i ic ≤ r)

def donutSpatialCentered (i : Fin 2) : Finset (Fin 2 × Fin 4) :=
  Finset.univ.filter (fun ic => 3 ≤ donutSpatialDistance i ic ∧ donutSpatialDistance i ic ≤ 5)

/-- Modes 0, 1 and 2 use the adjacent annulus (2,4], centered band [3,5], and full buffer. -/
def donutSpatialMeans (mode : Fin 3) (i : Fin 2) (z : Assignment 2) : ℝ :=
  countMean (if mode = 0 then donutSpatialBuffer i 4 \ donutSpatialBuffer i 2
    else if mode = 1 then donutSpatialCentered i else donutSpatialBuffer i 4)
    (fun ic => donutSpatialY ic z)

end

end SAP.P008b
