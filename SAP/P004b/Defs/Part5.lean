import SAP.P004b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b

universe u

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

/-- Both observed treatment arms have positive counts. -/
def ValidArms {N : ℕ} (z : Assignment N) : Prop :=
  0 < armCount z true ∧ 0 < armCount z false

/-- An error is tested only on assignments having both treatment arms. -/
def armRestricted {N : ℕ} (U : Assignment N → ℝ) (z : Assignment N) : ℝ :=
  if ValidArms z then U z else 0

/-- The corrected Lemma A.3 formula, with deterministic population arm centres. -/
def linearFormula {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (z : Assignment N) : ℝ :=
  ame p R + (∑ i, (bit (z i)*(R i z-barMu p R true)/p i -
    (1-bit (z i))*(R i z-barMu p R false)/(1-p i))) / N

/-- The conditional uniform law uses these finite assignment supports. -/
def completeSupport (N n1 : ℕ) : Finset (Assignment N) :=
  Finset.univ.filter (fun z => (Finset.univ.filter (fun j => z j = true)).card = n1)

def remainderSupport {N : ℕ} (n1 : ℕ) (i : Fin N) (a : Bool) :
    Finset ({j : Fin N // j ≠ i} → Bool) :=
  Finset.univ.filter (fun u =>
    (Finset.univ.filter (fun j => u j = true)).card = n1 - (if a then 1 else 0))

/-- The balanced-count event used for the sparse counterexample. -/
def SparseGood {N : ℕ} (z : Assignment N) : Prop :=
  2*(N : ℝ)/5 ≤ armCount z true ∧ armCount z true ≤ 3*(N : ℝ)/5

/-- Only a positive variance and two nonempty arms define a studentized interval. -/
def ValidInterval {N : ℕ} (R : CircleTable N) (Q : Matrix (Fin N) (Fin N) ℝ)
    (z : Assignment N) : Prop := ValidArms z ∧ 0 < kernelVariance z (residual R z) Q

/-- This event only claims interval inclusion when the interval is defined.
Undefined intervals count as successes; it is a weaker coverage assertion. -/
def GuardedInterval {N : ℕ} (p : ℝ) (R : CircleTable N)
    (Q : Matrix (Fin N) (Fin N) ℝ) (lo hi : ℝ) (z : Assignment N) : Prop :=
  ValidInterval R Q z →
    lo ≤ (hajek R z-ame (fun _ => p) R)/Real.sqrt (kernelVariance z (residual R z) Q) ∧
    (hajek R z-ame (fun _ => p) R)/Real.sqrt (kernelVariance z (residual R z) Q) ≤ hi

/-- Explicitly excludes the empty or unbounded branch of the real inverse CDF. -/
def FiniteQuantile (a : ℝ) : Prop :=
  {x : ℝ | a ≤ normalCDF x}.Nonempty ∧ BddBelow {x : ℝ | a ≤ normalCDF x}

def RangeFailure : Prop :=
  WellDefined rectangleWitness 0 ∧ FiniteSourceRange rectangleWitness 2 ∧
    (∀ x z, |rectangleWitness.outcome x z| < 2) ∧
    (∀ z, circleAverage rectangleWitness 0 0 z = bit (z 2) ∧
      circleAverage rectangleWitness 0 1 z = bit (z 2) ∧ circleAverage rectangleWitness 0 2 z = 0) ∧
    sharesSource (circleAverage rectangleWitness 0) 0 1 ∧
    nodeSeparation rectangleWitness 0 1 = 9 ∧ (4 : ℝ) < 9 ∧
    cov (fun _ => 1/2) (circleAverage rectangleWitness 0 0) (circleAverage rectangleWitness 0 1) = 1/4

def NoRangeCutoff : Prop :=
  ∀ h : ℝ, 0 ≤ h → ∃ L : ℝ, ∃ hL : 2 ≤ L,
      h+1 < L ∧ WellDefined (polygonRangeFamily L hL) 0 ∧
      FiniteSourceRange (polygonRangeFamily L hL) 2 ∧
      (∀ x z, |(polygonRangeFamily L hL).outcome x z| < 2) ∧
      (∀ i : Fin 3, Polygonal ((polygonRangeFamily L hL).node i)) ∧
      Pairwise (fun i j => Disjoint ((polygonRangeFamily L hL).node i) ((polygonRangeFamily L hL).node j)) ∧
      nodeSeparation (polygonRangeFamily L hL) 0 1 = L-1 ∧
      h < nodeSeparation (polygonRangeFamily L hL) 0 1 ∧
      sharesSource (circleAverage (polygonRangeFamily L hL) 0) 0 1 ∧
      cov (fun _ => 1/2) (circleAverage (polygonRangeFamily L hL) 0 0)
        (circleAverage (polygonRangeFamily L hL) 0 1) = 1/4

def AreaSpacingFailure : Prop :=
  (∀ n : ℕ, 0 < n →
      (∀ i, volume (thinPolygon n i) = 1) ∧
      Pairwise (fun i j => Disjoint (thinPolygon n i) (thinPolygon n j)) ∧
      (∀ i : Fin (n+1), sInf {r : ℝ | ∃ x ∈ thinPolygon n 0, ∃ y ∈ thinPolygon n i, dist x y = r} < 2)) ∧
    (∀ C : ℝ, ∃ n : ℕ, 0 < n ∧ C < (n+1 : ℝ))

def DiameterCutoff : Prop :=
  ∀ {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (hcompact : ∀ i, IsCompact (P.node i))
    (d dbar D : ℝ) (hd : 0 ≤ d) (hb : 0 ≤ dbar) (hD : 0 ≤ D)
    (hband : P.bands d ⊆ Set.Icc 0 d) (hWD : WellDefined P d)
    (hrange : FiniteSourceRange P dbar)
    (hdiam : ∀ i, ∀ x ∈ P.node i, ∀ y ∈ P.node i, dist x y ≤ D),
    (∀ i j, i ≠ j → sharesSource (circleAverage P d) i j →
      nodeSeparation P i j ≤ 2*dbar+2*d+D) ∧ LocalAt (circleAverage P d) (nodeSeparation P) (2*dbar+2*d+D)

def PolygonCountBound : Prop :=
  ∀ {N : ℕ} (P : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)))
    (a D r : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hpoly : ∀ i, Polygonal (P.node i))
    (hdis : Pairwise (fun i j => Disjoint (interior (P.node i)) (interior (P.node j))))
    (harea : ∀ i, ENNReal.ofReal a ≤ volume (P.node i))
    (hdiam : ∀ i, ∀ x ∈ P.node i, ∀ y ∈ P.node i, dist x y ≤ D),
    ∀ i, ((ball (nodeSeparation P) i r).card : ℝ) ≤ Real.pi*(r+2*D)^2/a

def ThinCountFailure : Prop :=
  ∀ n : ℕ, 0 < n →
  (Finset.univ.filter (fun i : Fin (n+1) =>
    sInf {r : ℝ | ∃ x ∈ thinPolygon n 0, ∃ y ∈ thinPolygon n i, dist x y = r} ≤ 2)).card = n+1

def T16Statement : Prop :=
  RangeFailure ∧ NoRangeCutoff ∧ AreaSpacingFailure ∧ ThinCountFailure

def T17Statement : Prop :=
  DiameterCutoff.{u} ∧ NoRangeCutoff ∧ PolygonCountBound ∧ AreaSpacingFailure ∧ ThinCountFailure

def T18Statement : Prop :=
  ∀ {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)],
  ∀ (P : PopulationSequence Space) (p d : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hP : SpatialLocalConditions P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d),
    let R := circleSequence P d
    let π := fun N (_ : Fin N) => p
    InProb π (fun N z => armRestricted (fun z => Real.sqrt N*(linearHajek (π N) (R N) z-hajek (R N) z)) z) ∧
    BigOp π (fun N z => armRestricted (fun z => hajek (R N) z-linearHajek (π N) (R N) z) z) (fun N => (N : ℝ)⁻¹)

def T19Statement : Prop :=
  (∀ N : ℕ, 0 < N →
      (∀ i z, |loneRademacher N i z| ≤ 1) ∧
      (∀ i, expect (fun _ => 1/2) (loneRademacher N i) = 0) ∧
      (∀ i, expect (fun _ => 1/2) (fun z => (loneRademacher N i z)^4) ≤ 1) ∧
      FiniteDependencyGraph (fun _ => 1/2) (loneRademacher N) (fun i => {i}) ∧
      (∀ i : Fin N, ({i} : Finset (Fin N)).card = 1) ∧
      variance (fun _ => 1/2) (fun z => ∑ i, loneRademacher N i z) = 1 ∧
      prob (fun _ => 1/2) (fun z => (∑ i, loneRademacher N i z) ≤ -(1/2 : ℝ)) = 1/2) ∧
    Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (nhds 0) ∧
    normalCDF (-(1/2 : ℝ)) < 1/2 ∧
    ¬ NormalLimit (fun _ _ => 1/2) (fun N z =>
      (∑ i, loneRademacher N i z) / Real.sqrt
        (variance (fun _ => 1/2) (fun z' => ∑ i, loneRademacher N i z')))

end
end SAP.P004b
