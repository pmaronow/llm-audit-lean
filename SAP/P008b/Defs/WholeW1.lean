import Mathlib
import SAP.P008b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- A measured spatial field, represented by points with injective two-dimensional
coordinates. Taking the point type to be a subset of Plane recovers the usual
presentation. The measure lives on the field itself, so no measurability of the
field in an ambient measure space is required. The coordinate metric is arbitrary. -/
structure MetricSpatialModel (X : Type) [MeasurableSpace X] (N : ℕ) where
  coord : X → Plane
  coord_injective : Function.Injective coord
  node : Fin N → X
  metric : MetricSpace Plane
  ζ : Measure X
  Y : X → Assignment N → ℝ

namespace MetricSpatialModel

variable {X : Type} [MeasurableSpace X] {N : ℕ}

def distance (P : MetricSpatialModel X N) (x y : X) : ℝ :=
  @dist Plane P.metric.toDist (P.coord x) (P.coord y)

def circle (P : MetricSpatialModel X N) (i : Fin N) (d : ℝ) : Set X :=
  {x | P.distance (P.node i) x = d}

def band (P : MetricSpatialModel X N) (i : Fin N) (d k : ℝ) : Set X :=
  {x | d - k ≤ P.distance (P.node i) x ∧ P.distance (P.node i) x ≤ d + k}

def regionAverage (P : MetricSpatialModel X N) (s : Set X) (f : X → ℝ) : ℝ :=
  (P.ζ s).toReal⁻¹ * ∫ x, f x ∂P.ζ.restrict s

/-- Existence conditions for an average over a measured region. Measurability
concerns only that integration domain, and positive finite mass prevents both
zero denominators and the conversion of infinite mass to a real number. -/
def validRegion (P : MetricSpatialModel X N) (s : Set X) (f : X → ℝ) : Prop :=
  MeasurableSet s ∧ 0 < (P.ζ s).toReal ∧ P.ζ s ≠ ⊤ ∧
    Integrable f (P.ζ.restrict s)

def M (P : MetricSpatialModel X N) (i : Fin N) (d : ℝ) (z : Assignment N) : ℝ :=
  P.regionAverage (P.circle i d) (fun x => P.Y x z)

def marginalY (P : MetricSpatialModel X N) (Q : FiniteLaw (Assignment N))
    (i : Fin N) (b : Bool) (x : X) : ℝ := marginal Q (P.Y x) i b

def pointEffect (P : MetricSpatialModel X N) (Q : FiniteLaw (Assignment N))
    (i : Fin N) (x : X) : ℝ := P.marginalY Q i true x - P.marginalY Q i false x

def m (P : MetricSpatialModel X N) (Q : FiniteLaw (Assignment N))
    (i : Fin N) (b : Bool) (d : ℝ) : ℝ := marginal Q (P.M i d) i b

def nodeEffect (P : MetricSpatialModel X N) (Q : FiniteLaw (Assignment N))
    (i : Fin N) (d : ℝ) : ℝ := P.m Q i true d - P.m Q i false d

def amr (P : MetricSpatialModel X N) (Q : FiniteLaw (Assignment N)) (d : ℝ) : ℝ :=
  finiteAMR Q (fun i => P.M i d)

/-- Only outcome functions actually used by the finite marginal law need be
integrable. Both own-treatment overrides are included, as required by S9(ii). -/
def validCircle (P : MetricSpatialModel X N) (Q : FiniteLaw (Assignment N))
    (i : Fin N) (d : ℝ) : Prop :=
  MeasurableSet (P.circle i d) ∧ 0 < (P.ζ (P.circle i d)).toReal ∧
    P.ζ (P.circle i d) ≠ ⊤ ∧
    ∀ b z, Q.mass z ≠ 0 →
      Integrable (fun x => P.Y x (Function.update z i b)) (P.ζ.restrict (P.circle i d))

def sharpNull (P : MetricSpatialModel X N) : Prop :=
  ∀ x z, P.Y x z = P.Y x (fun _ => false)

end MetricSpatialModel

/-- The rational x-axis in the two-coordinate spatial field. -/
def wholeLine (r : ℚ) : Plane := WithLp.toLp 2 ![(r : ℝ), 0]

/-- A concrete counting-measure field at coordinates (-1,0), (0,0), (1,0),
with its single intervention node at (0,0). Opposite outcomes cancel on radius 1. -/
def wholeCancellingModel : MetricSpatialModel (Fin 3) 1 where
  coord x := wholeLine ((x.val : ℚ) - 1)
  coord_injective := by
    intro x y h
    have hc := congrArg (fun p : Plane => p 0) h
    simp only [wholeLine, PiLp.toLp_apply, Matrix.cons_val_zero] at hc
    apply Fin.ext
    push_cast at hc
    exact_mod_cast (by linarith : (x.val : ℝ) = y.val)
  node _ := 1
  metric := inferInstance
  ζ := Measure.count
  Y x z := ((x.val : ℝ) - 1) * bit (z 0)

/-- Type-7 interpolation on already sorted, nonempty observations, with
zero-based indices. At q = 1 it returns the last observation. -/
def wholeQuantile7 {n : ℕ} (s : Fin (n + 1) → ℝ) (q : ℝ) : ℝ :=
  let h := (n : ℝ) * q
  let j := min (Int.toNat ⌊h⌋) n
  let g := h - j
  (1 - g) * s ⟨j, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ +
    g * s ⟨min (j + 1) n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def wholeTreatedCount {N : ℕ} (z : Assignment N) : ℕ :=
  ∑ i, if z i then 1 else 0

def wholeTestRadius (j : Fin 5) : ℝ := (j.val + 1 : ℝ) / 10

def wholeTestStatistic (P : SpatialModel 4) (a : Fin 6 → Assignment 4)
    (j : Fin 5) (k : Fin 6) : ℝ :=
  hajek (fun i z => P.M i (wholeTestRadius j) z) (a k)

/-- The exact square centers specified by the polygon fixture. -/
def wholeSquareCenter (i : Fin 2) : Plane := WithLp.toLp 2 ![20 * (i : ℝ), 0]

def wholeSquare (i : Fin 2) : Set Plane :=
  {x | |x 0 - 20 * (i : ℝ)| ≤ 1 / 8 ∧ |x 1| ≤ 1 / 8}

/-- P008-T22; pp. 144, 146 and 148–150 (PDF pp. 7, 9 and 11–13).
The printed claim is false: a spatial sharp-null experiment with all six
two-treated assignments, positive finite integrable circle averages at five
radii, and both Hajek arms nonempty has strict type-7 percentile rejection
probability 1/3, greater than 0.05, for each radius and for their sum.
The exact quantiles are respectively minus and plus 15/8 and 75/8. Every
nonempty deterministic rejection set on six equally likely assignments has
probability at least 1/6, greater than 0.05. The printed numbers do satisfy
the nominal rejection rule. -/
def T22WholeStatement : Prop :=
  (∃ (P : SpatialModel 4) (a : Fin 6 → Assignment 4),
    Function.Injective a ∧
    (∀ z, wholeTreatedCount z = 2 ↔ ∃ k, a k = z) ∧
    (∀ k, nTreated (a k) = 2 ∧ nControl (a k) = 2) ∧
    P.sharpNull ∧
    (∀ i j, P.validCircle i (wholeTestRadius j)) ∧
    (∀ i j z, P.M i (wholeTestRadius j) z = (i.val : ℝ)) ∧
    (∀ j, Monotone (wholeTestStatistic P a j) ∧
      wholeQuantile7 (wholeTestStatistic P a j) (1 / 40) = -15 / 8 ∧
      wholeQuantile7 (wholeTestStatistic P a j) (39 / 40) = 15 / 8 ∧
      (uniformLaw (Fin 6)).prob (fun k =>
        wholeTestStatistic P a j k < -15 / 8 ∨ 15 / 8 < wholeTestStatistic P a j k) = 1 / 3) ∧
    Monotone (fun k => ∑ j, wholeTestStatistic P a j k) ∧
    wholeQuantile7 (fun k => ∑ j, wholeTestStatistic P a j k) (1 / 40) = -75 / 8 ∧
    wholeQuantile7 (fun k => ∑ j, wholeTestStatistic P a j k) (39 / 40) = 75 / 8 ∧
    (uniformLaw (Fin 6)).prob (fun k =>
      (∑ j, wholeTestStatistic P a j k) < -75 / 8 ∨
        75 / 8 < ∑ j, wholeTestStatistic P a j k) = 1 / 3 ∧
    (1 / 20 : ℝ) < 1 / 3) ∧
  (∀ R : Finset (Fin 6), R.Nonempty →
    1 / 6 ≤ (uniformLaw (Fin 6)).prob (fun k => k ∈ R) ∧
    1 / 20 < (uniformLaw (Fin 6)).prob (fun k => k ∈ R)) ∧
  T22Statement

/-- P008-T25; pp. 142–143 and 146–147 (PDF pp. 5–6 and 9–10).
For every chosen coordinate metric and suitable measure on the spatial field,
finite marginalization commutes with every existing circle average. Node effects
are circle averages of point effects, and the AMR is the average of these
integrals over a positive number of nodes. Under the uniform four-node design,
each marginalized outcome is the mean over the eight assignments with the
specified own treatment, and its effect is the difference of these means. -/
def T25WholeStatement : Prop :=
  (∀ (X : Type) [MeasurableSpace X] (N : ℕ) (P : MetricSpatialModel X N)
      (Q : FiniteLaw (Assignment N)) (i : Fin N) (d : ℝ),
    P.validCircle Q i d →
    (∀ b, P.m Q i b d = P.regionAverage (P.circle i d) (P.marginalY Q i b)) ∧
    P.nodeEffect Q i d = P.regionAverage (P.circle i d) (P.pointEffect Q i)) ∧
  (∀ (X : Type) [MeasurableSpace X] (N : ℕ) (P : MetricSpatialModel X N)
      (Q : FiniteLaw (Assignment N)) (d : ℝ),
    0 < N → (∀ i, P.validCircle Q i d) →
    P.amr Q d = (N : ℝ)⁻¹ * ∑ i, P.regionAverage (P.circle i d) (P.pointEffect Q i)) ∧
  (∀ (Y : Assignment 4 → ℝ) (i : Fin 4) (b : Bool),
    marginal (uniformLaw (Assignment 4)) Y i b =
      (1 / 8 : ℝ) * ∑ z ∈ Finset.univ.filter (fun z => z i = b), Y z) ∧
  (∀ (Y : Assignment 4 → ℝ) (i : Fin 4),
    marginal (uniformLaw (Assignment 4)) Y i true -
        marginal (uniformLaw (Assignment 4)) Y i false =
      (1 / 8 : ℝ) * (∑ z ∈ Finset.univ.filter (fun z => z i = true), Y z) -
      (1 / 8 : ℝ) * (∑ z ∈ Finset.univ.filter (fun z => z i = false), Y z))

/-- P008-T26; p. 144 (PDF p. 7).
For every coordinate metric, spatial field, suitable measure and finite design,
the sharp null makes every point effect and every existing node effect zero,
and makes every existing AMR over a positive number of nodes zero.
The converse fails: on the three-point counting-measure field at (-1,0),
(0,0), (1,0), with one node at the origin, the AMR vanishes at every radius
where it exists, including radii zero and one, although treatment changes
the outcome at (1,0). No ambient field-measurability assumption is needed. -/
def T26WholeStatement : Prop :=
  (∀ (X : Type) [MeasurableSpace X] (N : ℕ) (P : MetricSpatialModel X N),
    P.sharpNull → ∀ Q : FiniteLaw (Assignment N),
    (∀ i x, P.pointEffect Q i x = 0) ∧
    (∀ i d, P.validCircle Q i d → P.nodeEffect Q i d = 0) ∧
    (∀ d, 0 < N → (∀ i, P.validCircle Q i d) → P.amr Q d = 0)) ∧
  ((∀ (Q : FiniteLaw (Assignment 1)),
      wholeCancellingModel.validCircle Q 0 0 ∧ wholeCancellingModel.validCircle Q 0 1) ∧
    (∀ (Q : FiniteLaw (Assignment 1)) (d : ℝ),
      wholeCancellingModel.validCircle Q 0 d → wholeCancellingModel.amr Q d = 0) ∧
    wholeCancellingModel.Y 2 ![true] ≠ wholeCancellingModel.Y 2 ![false])

/-- P008-T15; p. 143 (PDF p. 6).
For every chosen coordinate metric, the band of width parameter k about
radius d consists of outcome points at distances between d-k and d+k.
Its average is the normalized integral over those points; the edge average
is the corresponding integral over points at distance exactly d. These
formulas apply whenever the respective averages exist. If the inner radius
is positive and the outer radius is below the distance to every other node,
the band contains no intervention node. -/
def T15WholeStatement : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (N : ℕ) (P : MetricSpatialModel X N)
    (i : Fin N) (d k : ℝ), 0 ≤ d → 0 ≤ k →
    (∀ x, x ∈ P.band i d k ↔
      d - k ≤ P.distance (P.node i) x ∧ P.distance (P.node i) x ≤ d + k) ∧
    (∀ z, P.validRegion (P.band i d k) (fun x => P.Y x z) →
      P.regionAverage (P.band i d k) (fun x => P.Y x z) =
        (∫ x, P.Y x z ∂P.ζ.restrict
          {x | d - k ≤ P.distance (P.node i) x ∧ P.distance (P.node i) x ≤ d + k}) /
          (P.ζ {x | d - k ≤ P.distance (P.node i) x ∧
            P.distance (P.node i) x ≤ d + k}).toReal) ∧
    (∀ z, P.validRegion (P.circle i d) (fun x => P.Y x z) →
      P.M i d z = (∫ x, P.Y x z ∂P.ζ.restrict {x | P.distance (P.node i) x = d}) /
        (P.ζ {x | P.distance (P.node i) x = d}).toReal) ∧
    (0 < d - k → (∀ j, j ≠ i → d + k < P.distance (P.node i) (P.node j)) →
      {j : Fin N | P.node j ∈ P.band i d k} = ∅)

/-- P008-T16; pp. 143 and 145 (PDF pp. 6 and 8); supplied archived
polygon-buffer fixture, source lines 115–118.
The printed claim is false: in the specified half-side-1/8 squares centered
at (0,0) and (20,0), the first outcome-cell center is the polygon center.
Its Euclidean distance to the polygon boundary is 1/8, not the asserted zero;
the boundary is nonempty. Its distance to the filled polygon is zero.
Thus the fixture's stated boundary-distance list cannot hold. This refutes
that literal clause of the claim; the intended distinction between adjacent
buffers and centered bands is compatible with these facts. -/
def T16WholeStatement : Prop :=
  (∀ i : Fin 2,
    wholeSquareCenter i ∈ wholeSquare i ∧
    (frontier (wholeSquare i)).Nonempty ∧
    Metric.infDist (wholeSquareCenter i) (frontier (wholeSquare i)) = 1 / 8 ∧
    Metric.infDist (wholeSquareCenter i) (wholeSquare i) = 0 ∧
    Metric.infDist (wholeSquareCenter i) (frontier (wholeSquare i)) ≠ 0) ∧
  ¬ (∀ i : Fin 2, Metric.infDist (wholeSquareCenter i) (frontier (wholeSquare i)) = 0)

end

end SAP.P008b
