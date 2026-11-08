import Mathlib
import SAP.P004b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b

universe u

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology
noncomputable section

/-- Set separation, used only below for explicitly nonempty compact sets. -/
def planeSeparation (A B : Set (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ A, ∃ y ∈ B, dist x y = r}

/-- The full forced-diagonal interference matrix for the zero-radius examples. -/
def RangeIndicatorTable (R : CircleTable 3) : Prop :=
  ∀ i j, interferes R i j ↔ i = j ∨ (i ≠ 2 ∧ j = 2)

/-- Sources A and B have no influence on any outcome, even inside the range cutoff. -/
def OnlyThirdOutcome (P : SpatialPopulation 3 (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ x z z', z 2 = z' 2 → P.outcome x z = P.outcome x z'

/-- The two atoms of positive-distance Witness A'. -/
def positiveAtom (a : Bool) : EuclideanSpace ℝ (Fin 2) :=
  if a then planePoint (21/2) 2 else planePoint (1/2) 2

/-- Counting measure on the two specified outcome points; outcomes vanish elsewhere. -/
def positiveRectangleWitness : SpatialPopulation 3 (EuclideanSpace ℝ (Fin 2)) where
  node := ![rectangle 0 1 0 1, rectangle 10 11 0 1, rectangle 0 11 3 4]
  node_nonempty := by
    intro i
    fin_cases i
    · exact ⟨planePoint 0 0, by norm_num [rectangle, planePoint]⟩
    · exact ⟨planePoint 10 0, by norm_num [rectangle, planePoint]⟩
    · exact ⟨planePoint 0 3, by norm_num [rectangle, planePoint]⟩
  zeta := Measure.dirac (positiveAtom false) + Measure.dirac (positiveAtom true)
  outcome := fun x z => if x = positiveAtom false ∨ x = positiveAtom true then bit (z 2) else 0
  bands := fun d => {d}

/-- All facts of the prescribed-L family, rather than just an existential subfamily. -/
def PrescribedRangeFacts (L : ℝ) (hL : 2 ≤ L) : Prop :=
  let P := polygonRangeFamily L hL
  WellDefined P 0 ∧ FiniteSourceRange P 2 ∧
  (∀ x z, |P.outcome x z| < 2) ∧
  OnlyThirdOutcome P ∧
  (∀ x ∈ P.node 0 ∪ P.node 1,
    nodeDistance P 2 x = 2-x 1 ∧ 1 ≤ nodeDistance P 2 x ∧ nodeDistance P 2 x ≤ 2) ∧
  (∀ z, circleAverage P 0 0 z = bit (z 2) ∧
    circleAverage P 0 1 z = bit (z 2) ∧ circleAverage P 0 2 z = 0) ∧
  RangeIndicatorTable (circleAverage P 0) ∧ sharesSource (circleAverage P 0) 0 1 ∧
  nodeSeparation P 0 1 = L-1 ∧
  cov (fun _ => 1/2) (circleAverage P 0 0) (circleAverage P 0 1) = 1/4

/-- Complete positive-distance counterexample, including the two contours' attained gap. -/
def PositiveRangeFacts : Prop :=
  let P := positiveRectangleWitness
  WellDefined P 1 ∧ FiniteSourceRange P 1 ∧ (∀ x z, |P.outcome x z| < 2) ∧
  OnlyThirdOutcome P ∧
  nodeDistance P 0 (positiveAtom false) = 1 ∧
  nodeDistance P 1 (positiveAtom true) = 1 ∧
  (∀ a, nodeDistance P 2 (positiveAtom a) = 1) ∧
  (nodeDistance P 0 (positiveAtom true))^2 = 365/4 ∧
  (nodeDistance P 1 (positiveAtom false))^2 = 365/4 ∧ (1 : ℝ) < 365/4 ∧
  (∀ i, P.zeta (region P i 1) = if i = 2 then 2 else 1) ∧
  (∀ i z, circleAverage P 1 i z = bit (z 2)) ∧
  sharesSource (circleAverage P 1) 0 1 ∧ nodeSeparation P 0 1 = 9 ∧ (4 : ℝ) < 9 ∧
  planeSeparation (region P 0 1) (region P 1 1) = 7 ∧ (2 : ℝ) < 7 ∧
  (∃ x ∈ region P 0 1, ∃ y ∈ region P 1 1, dist x y = 7)

/-- P004-T16; p. 752 (PDF p. 9), paragraph 'For an interpretable sufficient condition ...';
p. 753 (PDF p. 10), polygon-intervention spacing sentence; footnote 25, p. 763.
The zero-radius rectangle witness, every prescribed separation L>5, and the positive-radius
two-atom witness refute the range-only cutoff, with exact distances, averages, interference
indicators and covariance. Disjoint area-one thin polygons have the stated exact squared
distances and an unbounded radius-two neighborhood count, refuting area-only spacing. -/
def T16WholeStatement : Prop :=
  RangeFailure ∧ NoRangeCutoff ∧ OnlyThirdOutcome rectangleWitness ∧
  (∀ x ∈ rectangleWitness.node 0 ∪ rectangleWitness.node 1,
    nodeDistance rectangleWitness 2 x = 2-x 1 ∧
    1 ≤ nodeDistance rectangleWitness 2 x ∧ nodeDistance rectangleWitness 2 x ≤ 2) ∧
  RangeIndicatorTable (circleAverage rectangleWitness 0) ∧
  (∀ L : ℝ, ∀ hL : 2 ≤ L, 5 < L → PrescribedRangeFacts L hL) ∧
  PositiveRangeFacts ∧ AreaSpacingFailure ∧ ThinCountFailure ∧
  (∀ n : ℕ, 0 < n → ∀ k : Fin n,
    let δ := planeSeparation (thinPolygon n 0) (thinPolygon n ⟨k.val+1, by omega⟩)
    0 ≤ δ ∧ δ^2 = 1+(max 0 (2*(k : ℝ)/n-1))^2 ∧ δ^2 < 2) ∧
  ¬ (∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    ((Finset.univ.filter (fun i : Fin (n+1) =>
      planeSeparation (thinPolygon n 0) (thinPolygon n i) ≤ 2)).card : ℝ) ≤ C)

/-- Literal printed linearization: its control denominator is Np. -/
def printedLinear {N : ℕ} (p : ℝ) (R : CircleTable N) (z : Assignment N) : ℝ :=
  ame (fun _ => p) R +
    (∑ i, (bit (z i)*(R i z-barMu (fun _ => p) R true)/p -
      (1-bit (z i))*(R i z-barMu (fun _ => p) R false)/p)) / N

/-- Deterministic balanced outcomes on even rows; the first half have outcome +1. -/
def balancedSign (N : ℕ) (i : Fin N) : ℝ := if i.val < N/2 then 1 else -1

def balancedTable (N : ℕ) : CircleTable N := fun i _ => balancedSign N i

/-- Convergence in probability along the even sample sizes, under Bernoulli(1/4). -/
def EvenInProb (U : ∀ m : ℕ, Assignment (2*m) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun m => prob (fun _ : Fin (2*m) => 1/4) (fun z => ε < |U m z|)) atTop (nhds 0)

/-- The exact finite balanced-outcome witness calculations. -/
def BalancedLinearFacts : Prop :=
  ∀ m : ℕ, 0 < m →
  let N := 2*m
  let R := balancedTable N
  let π := fun _ : Fin N => (1/4 : ℝ)
  barMu π R true = 0 ∧ barMu π R false = 0 ∧
  (∀ z, printedLinear (1/4) R z-linearHajek π R z =
    -(1/(1/4 : ℝ)-1/(1-1/4 : ℝ)) *
      (∑ i, (1-bit (z i))*balancedSign N i) / N) ∧
  (N : ℝ)*variance π (fun z => printedLinear (1/4) R z-linearHajek π R z) = 4/3

/-- P004-T18; Supplement A p. 4 (Lemma A.3), p. 5 (Lemma A.4), and eq. (27), p. 11.
Under C1-C4 the corrected displayed Hajek linearization has root-N negligible error and
O_p(N^-1) remainder, with zero as each empty arm's mean. It equals the augmented class
member. The balanced fixed-outcome witness at p=1/4 has the exact printed-minus-corrected
formula and scaled variance 4/3, and the printed expansion fails even along even sample
sizes. The printed and corrected linearizations coincide at p=1/2. -/
def T18WholeStatement : Prop :=
  (∀ {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)],
    ∀ (P : PopulationSequence Space) (p d : ℝ),
    (0 < p ∧ p < 1) → 0 ≤ d → SpatialLocalConditions P →
    (∀ᶠ N in atTop, WellDefined (P N) d) →
    let R := circleSequence P d
    let π := fun N (_ : Fin N) => p
    InProb π (fun N z => Real.sqrt N*(linearHajek (π N) (R N) z-hajek (R N) z)) ∧
    BigOp π (fun N z => hajek (R N) z-linearHajek (π N) (R N) z) (fun N => (N : ℝ)⁻¹)) ∧
  (∀ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N), 0 < N →
    ∀ z, linearHajek p R z = linearFormula p R z) ∧
  BalancedLinearFacts ∧
  (∀ N i z, |balancedTable N i z| = 1) ∧
  (∀ N i z z', balancedTable N i z = balancedTable N i z') ∧
  ¬ EvenInProb (fun m z => Real.sqrt (2*m : ℕ) *
    (printedLinear (1/4) (balancedTable (2*m)) z-hajek (balancedTable (2*m)) z)) ∧
  (∀ {N : ℕ} (R : CircleTable N) z,
    printedLinear (1/2) R z = linearHajek (fun _ => 1/2) R z)

/-- Independent coin index supplying a cancelling pair (with index zero unpaired). -/
def cancellingSource (m : ℕ) (i : Fin (2*m+1)) : Fin (2*m+1) :=
  ⟨(i.val+1)/2, by omega⟩

def cancellingArray (m : ℕ) : CircleTable (2*m+1) := fun i z =>
  let r := 2*bit (z (cancellingSource m i))-1
  if i.val = 0 ∨ i.val % 2 = 1 then r else -r

def cancellingNeighborhood (m : ℕ) (i : Fin (2*m+1)) : Finset (Fin (2*m+1)) :=
  Finset.univ.filter (fun j => cancellingSource m j = cancellingSource m i)

/-- All finite facts of the every-marginal-variance-one witness. -/
def CancellingFacts : Prop :=
  ∀ m : ℕ,
  let π := fun _ : Fin (2*m+1) => (1/2 : ℝ)
  let U := cancellingArray m
  (∀ i z, |U i z| = 1) ∧ (∀ i, expect π (U i) = 0) ∧
  (∀ i, expect π (fun z => (U i z)^4) = 1) ∧ (∀ i, variance π (U i) = 1) ∧
  FiniteDependencyGraph π U (cancellingNeighborhood m) ∧
  (∀ i, (cancellingNeighborhood m i).card ≤ 2) ∧
  (∀ z, (∑ i, U i z) = 2*bit (z 0)-1) ∧
  variance π (fun z => ∑ i, U i z) = 1 ∧
  (∀ z, (∑ i, U i z)/Real.sqrt (variance π (fun z' => ∑ i, U i z')) = 2*bit (z 0)-1) ∧
  prob π (fun z => (∑ i, U i z)/Real.sqrt (variance π (fun z' => ∑ i, U i z')) ≤ -(1/2 : ℝ)) = 1/2

/-- P004-T19; Supplement A p. 6 (Lemma A.5).
Both exact bounded dependency-neighborhood counterexamples satisfy the printed hypotheses
and fail the normal limit. The first has one fair sign and zero remaining variables; the
second has one unpaired fair sign and cancelling independent sign pairs, with every
marginal variance one and closed neighborhoods of size at most two. Their sums and
standardized sums are exactly the unpaired fair sign. -/
def T19WholeStatement : Prop :=
  T19Statement ∧
  (∀ N : ℕ, ∀ hN : 0 < N, ∀ z,
    (∑ i, loneRademacher N i z) = 2*bit (z ⟨0,hN⟩)-1 ∧
    (∑ i, loneRademacher N i z)/Real.sqrt
      (variance (fun _ => 1/2) (fun z' => ∑ i, loneRademacher N i z')) = 2*bit (z ⟨0,hN⟩)-1) ∧
  CancellingFacts ∧ Tendsto (fun m : ℕ => (4 : ℝ)/(2*m+1)) atTop (nhds 0) ∧
  ¬ (∀ x : ℝ, Tendsto (fun m => prob (fun _ => 1/2) (fun z =>
    (∑ i, cancellingArray m i z)/Real.sqrt
      (variance (fun _ => 1/2) (fun z' => ∑ i, cancellingArray m i z')) ≤ x))
      atTop (nhds (normalCDF x)))

/-- Raw HT (false) or population-centered linearized Hajek (true) contrast. -/
def cltRaw {N : ℕ} (p : ℝ) (R : CircleTable N) (a : Bool) : CircleTable N :=
  residualContrast (fun _ => p) R (fun _ b => if a then barMu (fun _ => p) R b else 0)

def cltCentered {N : ℕ} (p : ℝ) (R : CircleTable N) (a : Bool) : CircleTable N :=
  fun i z => cltRaw p R a i z-expect (fun _ => p) (cltRaw p R a i)

def cltEstimator {N : ℕ} (p : ℝ) (R : CircleTable N) (a : Bool) : Assignment N → ℝ :=
  if a then linearHajek (fun _ => p) R else ht (fun _ => p) R

/-- The graph joins precisely the pairs sharing an assignment source, including self. -/
def sharedNeighborhood {N : ℕ} (R : CircleTable N) (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun j => sharesSource R i j)

/-- Exact centered summands and variance scaling for the two estimator arrays. -/
def CLTContrastIdentities : Prop :=
  ∀ {N : ℕ} (p : ℝ) (R : CircleTable N), 0 < N → (0 < p ∧ p < 1) →
  (∀ a i, expect (fun _ => p) (cltRaw p R a i) =
    nodeEffect (fun _ => p) R i - if a then ame (fun _ => p) R else 0) ∧
  (∑ i, expect (fun _ => p) (cltRaw p R true i)) = 0 ∧
  (∀ a i, expect (fun _ => p) (cltCentered p R a i) = 0) ∧
  (∀ a z, (∑ i, cltCentered p R a i z) =
    N*(cltEstimator p R a z-ame (fun _ => p) R)) ∧
  (∀ a, variance (fun _ => p) (fun z => ∑ i, cltCentered p R a i z) =
    (N : ℝ)^2*variance (fun _ => p) (cltEstimator p R a))

/-- Unit-sum-variance form. Centering, measurability and full graph independence are retained;
no variance-one assertion is imposed on the empty row. -/
def NormalizedDependencyCLT : Prop :=
  ∀ {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) (hμ : ∀ N, IsProbabilityMeasure (μ N))
    (U : ∀ N, Fin N → Ω N → ℝ) (B : ∀ N, Fin N → Finset (Fin N)),
    (∀ N i, Measurable (U N i)) →
    (∀ N i, ∫ ω, U N i ω ∂μ N = 0) →
    (∃ K : ℝ, 0 < K ∧ ∀ N, 0 < N → ∀ i, ∀ᵐ ω ∂μ N, |U N i ω| ≤ K/Real.sqrt N) →
    (∀ N, DependencyGraph (μ N) (U N) (B N)) →
    (∃ D : ℕ, ∀ N i, (B N i).card ≤ D) →
    (∀ N, 0 < N → (∫ ω, (∑ i, U N i ω)^2 ∂μ N) = 1) →
    ∀ x : ℝ, Tendsto (fun N => ((μ N) {ω | (∑ i, U N i ω) ≤ x}).toReal)
      atTop (nhds (normalCDF x))

/-- Centered contrast bounds, with no geometry assumed. -/
def CLTSharpBounds : Prop :=
  ∀ {N : ℕ} (p b : ℝ) (R : CircleTable N), 0 < N → (0 < p ∧ p < 1) →
    0 ≤ b → (∀ i z, |R i z| ≤ b) →
    ∀ a i z, |cltCentered p R a i z| ≤ (if a then 4 else 2)*b/min p (1-p)

/-- Spatial verification of the hypotheses and both variance-conditional applications. -/
def SpatialCLTApplications : Prop :=
  ∀ {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)],
  ∀ (P : PopulationSequence Space) (p d : ℝ),
    (0 < p ∧ p < 1) → 0 ≤ d → SpatialLocalConditions P →
    (∀ᶠ N in atTop, WellDefined (P N) d) →
    let R := circleSequence P d
    (∀ N a, FiniteDependencyGraph (fun _ => p) (cltCentered p (R N) a)
      (sharedNeighborhood (R N))) ∧
    (∃ b : ℝ, 0 < b ∧ ∃ D : ℕ, ∀ᶠ N in atTop,
      (∀ i z, |cltCentered p (R N) false i z| ≤ 2*b/min p (1-p)) ∧
      (∀ i z, |cltCentered p (R N) true i z| ≤ 4*b/min p (1-p)) ∧
      (∀ i, (sharedNeighborhood (R N) i).card ≤ D)) ∧
    (∀ a, Nondegenerate (fun N => variance (fun _ => p) (cltEstimator p (R N) a)) →
      (∃ v : ℝ, 0 < v ∧ ∀ᶠ N in atTop, v*N ≤
        variance (fun _ => p) (fun z => ∑ i, cltCentered p (R N) a i z)) ∧
      NormalLimit (fun _ _ => p) (fun N z =>
        (cltEstimator p (R N) a z-ame (fun _ => p) (R N)) /
          Real.sqrt (variance (fun _ => p) (cltEstimator p (R N) a))))

/-- P004-T20; Supplement A p. 6 (Lemma A.5), and its use in Propositions 2 and 3.
Uniformly bounded centered arrays with bounded-degree dependency graphs and a linear
sum-variance lower bound satisfy the corrected normal limit. The unit-sum-variance
normalization also holds. The specified HT and linearized Hajek contrasts have their
exact centered identities, bounds 2b/min(p,1-p) and 4b/min(p,1-p), the shared-source
dependency graph of eventually bounded degree, and the two variance-conditional CLTs. -/
def T20WholeStatement : Prop :=
  T20Statement.{u} ∧ NormalizedDependencyCLT.{u} ∧ CLTContrastIdentities ∧
    CLTSharpBounds ∧ SpatialCLTApplications.{u}

/-- Conditional first and second residual moments; each conditioning arm has positive mass. -/
def residualFirst {N : ℕ} (p : ℝ) (R : CircleTable N) (i : Fin N) (a : Bool) : ℝ :=
  marginal (fun _ => p) (fun j z => R j z-barMu (fun _ => p) R a) i a

def residualSecond {N : ℕ} (p : ℝ) (R : CircleTable N) (i : Fin N) (a : Bool) : ℝ :=
  marginal (fun _ => p) (fun j z => (R j z-barMu (fun _ => p) R a)^2) i a

/-- The literal printed SAH bound, including the treated conditional control term and
its erroneously squared second moment. -/
def printedSAH {N : ℕ} (p : ℝ) (R : CircleTable N) (B : Fin N → Finset (Fin N)) : ℝ :=
  (∑ i, (B i).card * (residualSecond p R i true/p +
    (marginal (fun _ => p) (fun j z => (R j z-barMu (fun _ => p) R false)^2) i true)^2/(1-p))) /
      (N : ℝ)^2

/-- The literal printed node expression squares the second moments in its negative terms. -/
def printedNodeVariance {N : ℕ} (p : ℝ) (R : CircleTable N) (i : Fin N) : ℝ :=
  residualSecond p R i true/p-(residualSecond p R i true)^2 +
  residualSecond p R i false/(1-p)-(residualSecond p R i false)^2 +
  2*residualFirst p R i true*residualFirst p R i false

def sahBoundWitness : CircleTable 2 := fun i z =>
  (if i = 0 then 1 else -1)*(1-bit (z i))

def sahNodeWitness : CircleTable 2 := fun i z =>
  (if i = 0 then 1 else -1)*bit (z i)/2

/-- P004-T21; Supplement A pp. 9-10 (A.4.2, Proposition 2 and its first proof identity);
eq. (24), p. 9, and article eq. (20), p. 755 (PDF p. 12).
The corrected node variance equals both the expanded squares-of-first-means expression
and its compact residual-mean-difference form. The corrected finite SAH bound holds,
including its spatial C3 specialization. The two explicit two-node schedules give
variance 1/6 versus printed bound zero (corrected bound 2/3), and node variance 3/4
versus printed expression 15/16. The excluded feasible-estimator consistency claim is
not asserted. -/
def T21WholeStatement : Prop :=
  T21Statement ∧
  (∀ {N : ℕ} (p : ℝ) (R : CircleTable N), 0 < N → (0 < p ∧ p < 1) → ∀ i,
    let V := variance (fun _ => p) (cltRaw p R true i)
    V = residualSecond p R i true/p-(residualFirst p R i true)^2 +
      residualSecond p R i false/(1-p)-(residualFirst p R i false)^2 +
      2*residualFirst p R i true*residualFirst p R i false ∧
    V = residualSecond p R i true/p+residualSecond p R i false/(1-p) -
      (residualFirst p R i true-residualFirst p R i false)^2) ∧
  (∀ {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (p d h : ℝ), 0 < N → (0 < p ∧ p < 1) →
    0 ≤ d → 0 ≤ h → WellDefined P d → LocalAt (circleAverage P d) (nodeSeparation P) h →
    variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage P d)) ≤
      sahLimit (fun _ => p) (circleAverage P d) (fun i => ball (nodeSeparation P) i h)
        (fun _ a => barMu (fun _ => p) (circleAverage P d) a)) ∧
  (barMu (fun _ => 1/4) sahBoundWitness true = 0 ∧
    barMu (fun _ => 1/4) sahBoundWitness false = 0 ∧
    (∀ i j, interferes sahBoundWitness i j ↔ i = j) ∧
    variance (fun _ => 1/4) (linearHajek (fun _ => 1/4) sahBoundWitness) = 1/6 ∧
    printedSAH (1/4) sahBoundWitness (fun i => {i}) = 0 ∧
    sahLimit (fun _ => 1/4) sahBoundWitness (fun i => {i})
      (fun _ a => barMu (fun _ => 1/4) sahBoundWitness a) = 2/3) ∧
  (barMu (fun _ => 1/4) sahNodeWitness true = 0 ∧
    barMu (fun _ => 1/4) sahNodeWitness false = 0 ∧
    (∀ z, sahNodeWitness 0 (Function.update z 0 true) = 1/2 ∧
      sahNodeWitness 0 (Function.update z 0 false) = 0) ∧
    variance (fun _ => 1/4) (cltRaw (1/4) sahNodeWitness true 0) = 3/4 ∧
    printedNodeVariance (1/4) sahNodeWitness 0 = 15/16)

end
end SAP.P004b
