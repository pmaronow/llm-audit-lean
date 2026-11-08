import SAP.P008b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

/-- The corrected outcome-point band and its exclusion of intervention nodes. -/
def T15Statement : Prop :=
  ∀ (N : ℕ) (P : SpatialModel N) (i : Fin N) (d k : ℝ), 0 ≤ d → 0 ≤ k →
    (∀ z, 0 < (P.ζ.restrict (P.band i d k) Set.univ).toReal →
      P.ζ.restrict (P.band i d k) Set.univ ≠ ⊤ →
      Integrable (fun x => P.Y x z) (P.ζ.restrict (P.band i d k)) →
      P.bandAverage i d k (fun x => P.Y x z) =
        (P.ζ.restrict {x | x ∈ P.field ∧ d - k ≤ dist (P.node i) x ∧
          dist (P.node i) x ≤ d + k} Set.univ).toReal⁻¹ *
        ∫ x, P.Y x z ∂P.ζ.restrict {x | x ∈ P.field ∧
          d - k ≤ dist (P.node i) x ∧ dist (P.node i) x ≤ d + k}) ∧
    (0 < d - k → (∀ j, j ≠ i → d + k < dist (P.node i) (P.node j)) →
      {j : Fin N | P.node j ∈ P.band i d k} = ∅)

/-- Circle tolerances, full disks, and the supplied adjacent-buffer formula. -/
def T17Statement : Prop :=
  (∀ (p x : Plane) (d : ℝ), 0 < d →
    Metric.infDist x {q : Plane | dist q p = d} = |dist x p - d|) ∧
  (∀ (p x : Plane) (d k : ℝ), 0 < d → 0 ≤ k →
    (Metric.infDist x {q : Plane | dist q p = d} ≤ k ↔
      max 0 (d - k) ≤ dist x p ∧ dist x p ≤ d + k) ∧
    (k ≤ d → (d + k) - (d - k) = 2 * k)) ∧
  ((4 - 1 : ℝ) = 3 ∧ (4 + 1 : ℝ) = 5 ∧ (5 - 3 : ℝ) = 2) ∧
  (∀ (N : ℕ) (P : SpatialModel N) (i : Fin N) (d : ℝ),
    P.disk i d = {x | x ∈ P.field ∧ dist (P.node i) x ≤ d}) ∧
  (∀ (X : Type) [DecidableEq X] (B : ℕ → Finset X) (Y : X → ℝ),
    ((B 0).Nonempty → bufferRule B Y 0 = countMean (B 0) Y) ∧
    (∀ j, 0 < j → B (j - 1) ⊆ B j → (B (j - 1)).card < (B j).card →
      bufferRule B Y j = countMean (B j \ B (j - 1)) Y)) ∧
  (∀ (X : Type) (C : Finset X) (ρ Y : X → ℝ) (a b : ℝ),
    (∀ x ∈ C, 0 ≤ ρ x) → a < b →
    (distanceBuffer C ρ a).card < (distanceBuffer C ρ b).card →
    ((∑ x ∈ distanceBuffer C ρ b, Y x) - (∑ x ∈ distanceBuffer C ρ a, Y x)) /
        ((distanceBuffer C ρ b).card - ((distanceBuffer C ρ a).card : ℝ)) =
      countMean (C.filter (fun x => a < ρ x ∧ ρ x ≤ b)) Y ∧
    (a + b) / 2 - a = (b - a) / 2 ∧ b - (a + b) / 2 = (b - a) / 2 ∧
    0 < b - a ∧ (a + b) / 2 < b)

/-- The additive raster model, its amplitude scaling, and its strict lower bound. -/
def T18Statement : Prop :=
  (∀ r : ℝ, 0 ≤ r → -(384 / 437 : ℝ) < toyKernel r) ∧
  (-(1 : ℝ) < -(384 / 437 : ℝ)) ∧
  (∀ (C : ℕ) (Q : FiniteLaw (Assignment 4)) (base : Fin C → ℝ)
      (r w : Fin 4 → Fin C → ℝ),
    (∀ i c, 0 ≤ w i c) → (∀ i, ∑ c, w i c = 1) → (∀ i c, 0 ≤ r i c) →
    (∀ a i c z, toyRasterOutcome a base r c (Function.update z i true) -
      toyRasterOutcome a base r c (Function.update z i false) = a * toyKernel (r i c)) ∧
    (∀ a i c, marginal Q (toyRasterOutcome a base r c) i true -
      marginal Q (toyRasterOutcome a base r c) i false = a * toyKernel (r i c)) ∧
    (∀ a, toyRasterAMR Q a base r w =
      (1 / 4 : ℝ) * ∑ i, ∑ c, w i c * (a * toyKernel (r i c))) ∧
    toyRasterAMR Q 3 base r w = 3 * toyRasterAMR Q 1 base r w ∧
    -(384 / 437 : ℝ) < toyRasterAMR Q 1 base r w ∧
    -(1 : ℝ) < toyRasterAMR Q 1 base r w ∧
    toyRasterAMR Q 1 base r w ≠ -(126 / 100 : ℝ))

/-- Discrete and continuous boundary summaries and the explicit difference witness. -/
def T20Statement : Prop :=
  (∀ (R : Finset (ℤ × ℤ)) (Y : (ℤ × ℤ) → ℝ), (rasterBoundary R).Nonempty →
    (∀ x, x ∈ rasterBoundary R ↔ x ∈ R ∧ ∃ a b : Fin 3,
      (a.val ≠ 1 ∨ b.val ≠ 1) ∧ (x.1 + a.val - 1, x.2 + b.val - 1) ∉ R) ∧
    rasterEdgeZeroAverage R Y =
      (∑ x ∈ rasterBoundary R, Y x) / (rasterBoundary R).card ∧
    rasterAreaAverage R Y = (∑ x ∈ R, Y x) / R.card) ∧
  ((Finset.univ : Finset BlockCell).card = 25 ∧ blockBoundary.card = 16 ∧
    ((Finset.univ : Finset BlockCell) \ blockBoundary).card = 9 ∧
    (∀ c : BlockCell, c ∈ blockBoundary ↔ ∃ a b : Fin 3,
      (a.val ≠ 1 ∨ b.val ≠ 1) ∧
      ((c.1.val : ℤ) + a.val - 1 < 0 ∨ 5 ≤ (c.1.val : ℤ) + a.val - 1 ∨
       (c.2.val : ℤ) + b.val - 1 < 0 ∨ 5 ≤ (c.2.val : ℤ) + b.val - 1)) ∧
    (∀ c : BlockCell, c ∈ (Finset.univ \ blockBoundary) ↔
      1 ≤ c.1.val ∧ c.1.val ≤ 3 ∧ 1 ≤ c.2.val ∧ c.2.val ≤ 3)) ∧
  (∀ P : Set Plane, (frontier P).Nonempty →
    {x | Metric.infDist x (frontier P) = 0} = frontier P ∧
    ∀ x ∈ interior P, 0 < Metric.infDist x (frontier P)) ∧
  (hajek polygonRasterEdgeM ![true, false] = 0 ∧
    hajek polygonRasterAreaM ![true, false] = 9 / 25 ∧
    finiteAMR (uniformLaw (Assignment 2)) polygonRasterEdgeM = 0 ∧
    finiteAMR (uniformLaw (Assignment 2)) polygonRasterAreaM = 9 / 50)

/-- Only the printed numerical comparison. -/
def T21Statement : Prop := (-321 / 10000 : ℝ) < -19 / 625

/-- Only the decision of the printed strict percentile rule, using its printed inputs. -/
def T22Statement : Prop :=
  (619 / 50 : ℝ) < -797 / 100 ∨ (797 / 100 : ℝ) < 619 / 50

/-- Zero covariances beyond the cutoff make the truncated covariance sum exact. -/
def T23Statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (N : ℕ) (Q : FiniteLaw Ω)
      (φ : Fin N → Ω → ℝ) (D : Fin N → Fin N → ℝ) (c : ℝ),
    (∀ i j, c < D i j → Q.cov (φ i) (φ j) = 0) →
    (∑ i, ∑ j, Q.cov (φ i) (φ j) * (if D i j ≤ c then 1 else 0)) =
      Q.var (fun z => ∑ i, φ i z)

end

end SAP.P008b
