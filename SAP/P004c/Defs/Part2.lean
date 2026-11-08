import SAP.P004c.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004c
open scoped BigOperators Classical
open MeasureTheory Filter
noncomputable section

/-- Fixed nodes, spatial measure, potential outcomes and distance bands. -/
structure SpatialPopulation (N : ℕ) (X : Type*) [MetricSpace X] [MeasurableSpace X] where
  node : Fin N → Set X
  node_nonempty : ∀ i, (node i).Nonempty
  zeta : Measure X
  outcome : X → Assignment N → ℝ
  bands : ℝ → Set ℝ

def nodeDistance {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i : Fin N) (x : X) : ℝ := Metric.infDist x (P.node i)

def nodeSeparation {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i j : Fin N) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ P.node i, ∃ y ∈ P.node j, dist x y = r}

def region {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i : Fin N) (d : ℝ) : Set X :=
  {x | nodeDistance P i x ∈ P.bands d}

def circleAverage {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) : CircleTable N :=
  fun i z => (∫ x in region P i d, P.outcome x z ∂P.zeta) /
    (P.zeta (region P i d)).toReal

/-- Conditions ensuring genuine spatial averages, rather than totalized integrals. -/
def WellDefined {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) : Prop :=
  ∀ i, MeasurableSet (region P i d) ∧ 0 < P.zeta (region P i d) ∧
    P.zeta (region P i d) < ⊤ ∧
      ∀ z, IntegrableOn (fun x => P.outcome x z) (region P i d) P.zeta

abbrev PopulationSequence (Space : ℕ → Type*) [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] := ∀ N, SpatialPopulation N (Space N)

variable {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]

/-- C2-C4 with radius-specific eventual thresholds, as in Section 4. -/
def SpatialLocalConditions (P : PopulationSequence Space) : Prop :=
  (∃ b : ℝ, 0 < b ∧ ∀ᶠ N in atTop, ∀ x z, |(P N).outcome x z| < b) ∧
  (∃ h : ℝ → ℝ, (∀ d, 0 ≤ d → 0 ≤ h d) ∧
    ∀ d, 0 ≤ d → ∀ᶠ N in atTop,
      LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) (h d)) ∧
  (∃ c : ℝ → ℝ, ∀ r, 0 ≤ r → ∀ᶠ N in atTop, ∀ i,
    ((ball (nodeSeparation (P N)) i r).card : ℝ) ≤ c r)

def InProb (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N => prob (p N) (fun z => ε < |U N z|)) atTop (nhds 0)

def BigOp (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N in atTop, prob (p N) (fun z => C * |r N| < |U N z|) < ε

def normalCDF (x : ℝ) : ℝ := (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal

/-- CDF convergence to the actual standard Gaussian probability measure. -/
def NormalLimit (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) : Prop :=
  ∀ x : ℝ, Tendsto (fun N => prob (p N) (fun z => U N z ≤ x)) atTop (nhds (normalCDF x))

/-- In particular, the variance denominator is positive eventually. -/
def Nondegenerate (V : ℕ → ℝ) : Prop :=
  ∃ v : ℝ, 0 < v ∧ ∀ᶠ N : ℕ in atTop, v ≤ (N : ℝ) * V N

/-- An arbitrary marginal assignment law; the own coordinate is overwritten. -/
def marginalLawEffect {N : ℕ} (w : Fin N → Assignment N → ℝ)
    (Y : Assignment N → ℝ) (i : Fin N) : ℝ :=
  (∑ z, w i z * Y (Function.update z i true)) -
    (∑ z, w i z * Y (Function.update z i false))

/-- Footnote 22 with outcome points indexed by x, rather than by intervention nodes. -/
def SharpNull {N : ℕ} {X : Type*} (Y : X → Assignment N → ℝ) : Prop :=
  ∀ x z, Y x z = Y x (fun _ => false)

end
end SAP.P004c
