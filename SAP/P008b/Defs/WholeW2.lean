import Mathlib
import SAP.P008b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

/-- The two polygon summary modes in the supplied archived formula. -/
inductive WholeBufferMode where
  | donut
  | disk
  deriving DecidableEq

/-- The supplied formula, with its first index numbered zero. Only later
donut indices subtract the preceding buffer. -/
def archivedPolygonSummary {X : Type*} (mode : WholeBufferMode)
    (B : ℕ → Finset X) (Y : X → ℝ) (j : ℕ) : ℝ :=
  if mode = .donut ∧ j ≠ 0 then
    ((∑ x ∈ B j, Y x) - (∑ x ∈ B (j - 1), Y x)) /
      ((B j).card - ((B (j - 1)).card : ℝ))
  else countMean (B j) Y

/-- Nonmissing cells whose centroids lie in the closed polygon's full buffer.
Distance is to the polygon itself, including its interior. -/
def polygonFullBuffer {X : Type*} (C : Finset X) (centroid : X → Plane)
    (P : Set Plane) (r : ℝ) : Finset X :=
  distanceBuffer C (fun c => Metric.infDist (centroid c) P) r

/-- P008-T17; pp. 143 and 145 (PDF pp. 6 and 8); supplied archived polygon-buffer formula.
Circle tolerance selects the clipped radial band, of width twice the tolerance
when the inner radius is nonnegative. A point disk is the full disk. In the
supplied polygon formula disks and the first donut use the full buffer, the
zero-radius buffer consists of the polygon's own nonmissing cells, and later
donuts average the added cells between successive radii, with the stated width,
outer endpoint and midpoint. -/
def T17WholeStatement : Prop := by
  classical
  exact T17Statement ∧
  ∀ (X : Type) (C : Finset X) (centroid : X → Plane) (P : Set Plane)
      (Y : X → ℝ) (r : ℕ → ℝ), IsClosed P → P.Nonempty →
    polygonFullBuffer C centroid P 0 = C.filter (fun c => centroid c ∈ P) ∧
    (∀ j, (polygonFullBuffer C centroid P (r j)).Nonempty →
      archivedPolygonSummary .disk (fun j => polygonFullBuffer C centroid P (r j)) Y j =
        countMean (polygonFullBuffer C centroid P (r j)) Y) ∧
    ((polygonFullBuffer C centroid P (r 0)).Nonempty →
      archivedPolygonSummary .donut (fun j => polygonFullBuffer C centroid P (r j)) Y 0 =
        countMean (polygonFullBuffer C centroid P (r 0)) Y) ∧
    (r 0 = 0 → (C.filter (fun c => centroid c ∈ P)).Nonempty →
      archivedPolygonSummary .donut (fun j => polygonFullBuffer C centroid P (r j)) Y 0 =
        countMean (C.filter (fun c => centroid c ∈ P)) Y) ∧
    (∀ j, 0 < j → 0 ≤ r (j - 1) → r (j - 1) < r j →
      (polygonFullBuffer C centroid P (r (j - 1))).card <
        (polygonFullBuffer C centroid P (r j)).card →
      archivedPolygonSummary .donut (fun j => polygonFullBuffer C centroid P (r j)) Y j =
        countMean (polygonFullBuffer C centroid P (r j) \
          polygonFullBuffer C centroid P (r (j - 1))) Y ∧
      archivedPolygonSummary .donut (fun j => polygonFullBuffer C centroid P (r j)) Y j =
        countMean (C.filter (fun c => r (j - 1) < Metric.infDist (centroid c) P ∧
          Metric.infDist (centroid c) P ≤ r j)) Y ∧
      (r (j - 1) + r j) / 2 - r (j - 1) = (r j - r (j - 1)) / 2 ∧
      r j - (r (j - 1) + r j) / 2 = (r j - r (j - 1)) / 2 ∧
      0 < r j - r (j - 1) ∧ (r (j - 1) + r j) / 2 < r j)

/-- The nonnegative term subtracted from the first gamma kernel. -/
def toyNegativeKernel (r : ℝ) : ℝ := (128 / 3) * r ^ 4 * Real.exp (-4 * r)

/-- P008-T18; pp. 146–147 and 149 (PDF pp. 9–10 and 12), Figures 2 and 4; supplied staged kernel.
The plotted function is the difference of the specified gamma densities and is
nonmonotone. In additive raster outcomes every design's effects and AMR scale
by amplitude. The negative term has the stated derivative and attained maximum;
the exact exponential Taylor bound implies the kernel and amplitude-one AMR
exceed minus 384/437 and hence minus one. The printed magnitude minus 1.26 is
excluded at amplitude one and is attainable in the amplitude-three convex
average model. Rational enclosures give the three stated approximate kernel values. -/
def T18WholeStatement : Prop :=
  T18Statement ∧
  (∀ r : ℝ, 0 ≤ r → toyKernel r =
    ProbabilityTheory.gammaPDFReal 1 2 r - ProbabilityTheory.gammaPDFReal 5 4 r) ∧
  (∀ r : ℝ, HasDerivAt toyNegativeKernel
    ((512 / 3) * r ^ 3 * (1 - r) * Real.exp (-4 * r)) r) ∧
  ((∀ r : ℝ, 0 ≤ r → 0 ≤ toyNegativeKernel r ∧
      toyNegativeKernel r ≤ toyNegativeKernel 1) ∧
    toyNegativeKernel 1 = 128 / (3 * Real.exp 4)) ∧
  ((∑ k ∈ Finset.range 7, (4 : ℝ) ^ k / (Nat.factorial k : ℝ)) = 437 / 9 ∧
    (437 / 9 : ℝ) < Real.exp 4) ∧
  (∀ r : ℝ, 0 ≤ r → toyNegativeKernel r < 384 / 437) ∧
  (¬ MonotoneOn toyKernel (Set.Ici 0) ∧ ¬ AntitoneOn toyKernel (Set.Ici 0)) ∧
  (|toyKernel (1 / 10) - 163 / 100| < 1 / 200 ∧
    |toyKernel (6 / 5) + 55 / 100| < 1 / 200 ∧
    |toyKernel 2 + 19 / 100| < 1 / 200) ∧
  (∃ t : ℝ, 0 < t ∧ t < 1 ∧
    3 * (t * toyKernel 1 + (1 - t) * toyKernel 0) = -63 / 50)

/-- Circle selected by the chosen distance. The algebra below works for every
radius selector, in particular for every metric allowed by the claim. -/
def SpatialModel.selectedCircle {N : ℕ} (P : SpatialModel N)
    (ρ : Plane → Plane → ℝ) (i : Fin N) (d : ℝ) : Set Plane :=
  {x | x ∈ P.field ∧ ρ (P.node i) x = d}

def SpatialModel.selectedMeasure {N : ℕ} (P : SpatialModel N)
    (ρ : Plane → Plane → ℝ) (i : Fin N) (d : ℝ) : Measure Plane :=
  P.ζ.restrict (P.selectedCircle ρ i d)

def SpatialModel.selectedAverage {N : ℕ} (P : SpatialModel N)
    (ρ : Plane → Plane → ℝ) (i : Fin N) (d : ℝ) (f : Plane → ℝ) : ℝ :=
  ((P.selectedMeasure ρ i d) Set.univ).toReal⁻¹ * ∫ x, f x ∂P.selectedMeasure ρ i d

def SpatialModel.selectedM {N : ℕ} (P : SpatialModel N)
    (ρ : Plane → Plane → ℝ) (i : Fin N) (d : ℝ) (z : Assignment N) : ℝ :=
  P.selectedAverage ρ i d (fun x => P.Y x z)

def SpatialModel.selectedNodeEffect {N : ℕ} (P : SpatialModel N)
    (ρ : Plane → Plane → ℝ) (Q : FiniteLaw (Assignment N)) (i : Fin N) (d : ℝ) : ℝ :=
  marginal Q (P.selectedM ρ i d) i true - marginal Q (P.selectedM ρ i d) i false

def SpatialModel.selectedAMR {N : ℕ} (P : SpatialModel N)
    (ρ : Plane → Plane → ℝ) (Q : FiniteLaw (Assignment N)) (d : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, P.selectedNodeEffect ρ Q i d

/-- Guards for a genuine local circle average: positive finite mass, a measure
concentrated on the circle it integrates, and integrable potential outcomes.
Concentration is automatic for a null-measurable circle; the whole field need
not be measurable. -/
def SpatialModel.validSelectedCircle {N : ℕ} (P : SpatialModel N)
    (ρ : Plane → Plane → ℝ) (Q : FiniteLaw (Assignment N)) (i : Fin N) (d : ℝ) : Prop :=
  0 < ((P.selectedMeasure ρ i d) Set.univ).toReal ∧
  (P.selectedMeasure ρ i d) Set.univ ≠ ⊤ ∧
  (∀ᵐ x ∂P.selectedMeasure ρ i d, x ∈ P.selectedCircle ρ i d) ∧
  ∀ b z, Q.mass z ≠ 0 →
    Integrable (fun x => P.Y x (Function.update z i b)) (P.selectedMeasure ρ i d)

/-- P008-T27; p. 140 (PDF p. 3); additive mathematical content with the definitions on pp. 141–144.
For every design and chosen metric, additive point effects equal their structural
coefficients. Each defined node effect is the genuine circle average of its
coefficient, and the AMR is the average of these node effects. If coefficients
share a radial function g, point effects equal g of distance, every individually
defined circle effect equals g(d), and the defined AMR equals g(d). Only local
circle-average existence is required; no measurability of the whole field is assumed. -/
def T27WholeStatement : Prop :=
  (∀ (N : ℕ) (P : SpatialModel N) (Q : FiniteLaw (Assignment N))
      (ρ : Plane → Plane → ℝ) (base : Plane → ℝ) (g : Fin N → Plane → ℝ),
    (∀ x ∈ P.field, ∀ z, P.Y x z = additiveOutcome base g x z) →
    (∀ i x, x ∈ P.field → P.pointEffect Q i x = g i x) ∧
    (∀ i d, P.validSelectedCircle ρ Q i d →
      P.selectedNodeEffect ρ Q i d = P.selectedAverage ρ i d (g i)) ∧
    (∀ d, 0 < N → (∀ i, P.validSelectedCircle ρ Q i d) →
      P.selectedAMR ρ Q d = (N : ℝ)⁻¹ * ∑ i, P.selectedAverage ρ i d (g i))) ∧
  (∀ (N : ℕ) (P : SpatialModel N) (Q : FiniteLaw (Assignment N))
      (ρ : Plane → Plane → ℝ) (base : Plane → ℝ) (g : ℝ → ℝ),
    (∀ x ∈ P.field, ∀ z, P.Y x z =
      additiveOutcome base (fun i x => g (ρ (P.node i) x)) x z) →
    (∀ i x, x ∈ P.field → P.pointEffect Q i x = g (ρ (P.node i) x)) ∧
    (∀ i d, P.validSelectedCircle ρ Q i d → P.selectedNodeEffect ρ Q i d = g d) ∧
    (∀ d, 0 < N → (∀ i, P.validSelectedCircle ρ Q i d) →
      P.selectedAMR ρ Q d = g d))

end

end SAP.P008b
