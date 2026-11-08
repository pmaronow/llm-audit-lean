import Mathlib
import SAP.P012b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012b

open Finset
noncomputable section

/-- Equality of displayed pairs; traits outside the graph are irrelevant. -/
def SamePair (H K : State) : Prop :=
  H.vertices = K.vertices ∧ H.edges = K.edges ∧
    ∀ v ∈ H.vertices, H.trait v = K.trait v

/-- A dyad with a finite set of distinct private leaves at its second endpoint.
The leaves may have any names outside the two sampled vertices. -/
def StarAtTwo (H : State) (U : Finset Vertex) : Prop :=
  Disjoint U {s 1, s 2} ∧ H.vertices = {s 1, s 2} ∪ U ∧
    H.edges = insert {s 1, s 2} (U.image (fun v => {s 2, v}))

/-- Sum of the binary traits on a specified finite set. -/
def onesOn (H : State) (U : Finset Vertex) : ℕ :=
  (U.filter (fun v => H.trait v = true)).card

/-- The interval is the smallest interval containing the values, including
comparison with open, unbounded and degenerate intervals. -/
def SmallestValueInterval (values : Set ℝ) (L U : ℝ) : Prop :=
  values ⊆ Set.Icc L U ∧
    ∀ I : Set ℝ, Set.OrdConnected I → values ⊆ I → Set.Icc L U ⊆ I

def hDefinedStates (D : Data) : Set State :=
  {H | Compatible D H ∧ HomophilyDefined H}

/-- The two-seed common-neighbour graph used to distinguish compatibility
with upper degree bounds from compatibility with exact degrees. -/
def commonNeighbourState : State :=
  ⟨{s 1, s 2, u 0 0}, {{s 1, u 0 0}, {s 2, u 0 0}}, fun _ => false⟩

/-- One augmented graph for the two recruitment-history comparisons. -/
def historyState : State :=
  ⟨{s 1, s 2, s 3, u 0 0},
    {{s 1, s 2}, {s 1, s 3}, {s 2, s 3}, {s 1, u 0 0}},
    fun v => decide (v = s 3)⟩

def starHistory : Data :=
  ⟨{1,2,3}, {1}, fun _ => 1, id,
    fun i => if i = 1 then 3 else 2, fun i => i == 3⟩

def chainHistory : Data :=
  {starHistory with parent := fun j => if j = 3 then 2 else 1}

def reorderedHistory : Data :=
  {starHistory with time := fun i => if i = 2 then 3 else if i = 3 then 2 else i}

/-- The illustrative headline data: sampled traits (0,1), degrees (1,2). -/
def oneLeafData : Data :=
  ⟨{1,2}, {1}, fun _ => 1, fun i => i-1,
    fun i => if i = 1 then 1 else 2, fun i => i == 2⟩

def oneLeafState (b : Bool) : State :=
  ⟨{s 1, s 2, u 0 0}, {{s 1, s 2}, {s 2, u 0 0}},
    fun v => if v = s 2 then true else if v = u 0 0 then b else false⟩

def wholeEdgeCount (E : Finset (Finset Vertex)) (Z : Vertex → Bool) (b : Bool) : ℕ :=
  (E.filter (fun e => ∀ v ∈ e, Z v = b)).card

def wholeMixedCount (E : Finset (Finset Vertex)) (Z : Vertex → Bool) : ℕ :=
  (E.filter (fun e => (∃ v ∈ e, Z v = true) ∧ (∃ v ∈ e, Z v = false))).card

def wholePhi (x y c : ℝ) : ℝ := 1 - c / (2*x+c) - c / (2*y+c)

/-- Exact, strictly positive trait-1 private-leaf flip difference. The counts
exclude the flipped edge, so they are natural numbers without subtraction. -/
def WholeLeafFlip (D : Data) (i : ℕ) : Prop :=
  let H := leafCompletion D true
  let K := flipTrait H (u i 0)
  let E := H.edges.erase {s i, u i 0}
  let x : ℝ := wholeEdgeCount E H.trait true
  let y : ℝ := wholeEdgeCount E H.trait false
  let c : ℝ := wholeMixedCount E H.trait
  HomophilyDefined H ∧ HomophilyDefined K ∧
    u i 0 ∈ unsampled D H ∧ graphDegree H (u i 0) = 1 ∧
    H.trait (u i 0) = D.trait i ∧ K.trait (u i 0) = !D.trait i ∧
    (D.trait i = true →
      0 < 2*y+c ∧
      hValue H = wholePhi (x+1) y c ∧ hValue K = wholePhi x y (c+1) ∧
      hValue H - hValue K =
        2*(x+c+1)/((2*x+c+1)*(2*x+c+2)) +
        2*y/((2*y+c+1)*(2*y+c)) ∧
      0 < hValue H - hValue K)

/-- The printed claim is false: P012-T14; Definitions 1, 2 and 4,
p. 155 (PDF p. 3); Web Appendix 1, p. 1.
The four admissible examples A--D exhibit undefined printed quotients.
A and C have unique displayed compatible pairs; B has raw numerator -1/2
and denominator 1/2 and an empty recruitment average at every pair. Every
D graph is a dyad with three private leaves at vertex 2; all eight trait
assignments are compatible, and their trait sum gives h=-3/5,-1/3,-1/7 or
an undefined 0/0, while p=0. A and D have no whole-compatible-set h interval. -/
def T14WholeStatement : Prop :=
  T14Statement ∧
  (∀ H, Compatible domainA H →
    SamePair H (dyad false false) ∧ hNumerator H = 0 ∧ hDenominator H = 0 ∧
    homophily H = none ∧ preferential domainA H = some 0) ∧
  (hNumerator (dyad false true) = -1/2 ∧ hDenominator (dyad false true) = 1/2 ∧
    ∀ H, (nonseeds domainB).card = 0 ∧ pSum domainB H = 0) ∧
  (∀ H, Compatible domainC H →
    SamePair H domainCState ∧ H.edges.card = 0 ∧
    (∀ v ∈ H.vertices, ∀ w ∈ H.vertices,
      (graphDegree H v : ℝ) * graphDegree H w = 0 ∧ 2*(H.edges.card : ℝ) = 0) ∧
    (nonseeds domainC).card = 0 ∧ homophily H = none ∧
    preferential domainC H = none) ∧
  (∀ H, Compatible domainD H → ∃ U : Finset Vertex,
    StarAtTwo H U ∧ U.card = 3 ∧
    let r := onesOn H U;
    r ≤ 3 ∧ preferential domainD H = some 0 ∧
    (r = 0 → homophily H = some (-3/5)) ∧
    (r = 1 → homophily H = some (-1/3)) ∧
    (r = 2 → homophily H = some (-1/7)) ∧
    (r = 3 → hNumerator H = 0 ∧ hDenominator H = 0 ∧ homophily H = none)) ∧
  (¬ ∃ L U, FullHomophilyRegion domainA L U) ∧
  (¬ ∃ L U, FullHomophilyRegion domainD L U)

/-- P012-T15; Definitions 1, 2 and 4, p. 155 (PDF p. 3);
Web Appendix 1, p. 1.
The denominator identities give the exact individual domains of h and p.
On admissible data the whole-compatible-set domains are exactly positive
sampled degree in each trait class for h and at least one nonseed for p.
Under each condition separately, unique attained endpoints give the smallest
containing interval. If the h condition fails no whole-set h region exists;
the h-defined-only set can be empty (example A), while p still has region {0}.
The hypotheses of Results 2 and 3 imply the respective domain conditions. -/
def T15WholeStatement : Prop :=
  T15Statement ∧
  (∀ H : State,
    (∑ v ∈ H.vertices, (graphDegree H v : ℝ) * (1-z H v)) =
      (traitDegree H false : ℝ)) ∧
  (∀ H : State, Simple H →
    (HomophilyDefined H ↔ 0 < H.edges.card ∧
      0 < traitDegree H false ∧ 0 < traitDegree H true)) ∧
  (∀ D : Data, Admissible D →
    (∃ H, Compatible D H) ∧
    ((0 < sampledTraitDegree D false ∧ 0 < sampledTraitDegree D true) →
      ∃ L U, FullHomophilyRegion D L U ∧ SmallestValueInterval (hValues D) L U ∧
        ∀ L' U', FullHomophilyRegion D L' U' → L' = L ∧ U' = U) ∧
    (D.seeds.card < D.sampled.card →
      ∃ L U, FullPreferentialRegion D L U ∧ SmallestValueInterval (pValues D) L U ∧
        ∀ L' U', FullPreferentialRegion D L' U' → L' = L ∧ U' = U)) ∧
  (hDefinedStates domainA = ∅ ∧ hValues domainA = ∅ ∧
    (∀ H, Compatible domainA H → preferential domainA H = some 0) ∧
    FullPreferentialRegion domainA 0 0)

/-- P012-T17; Appendix p. 160 (PDF p. 8), proof of Result 1;
Definition 3, p. 155.
Deleting unsampled vertices preserves compatibility with upper degree bounds.
Exact degrees survive precisely when there is no sampled-to-unsampled edge,
equivalently no unsampled vertex, equivalently the graph equals its induced
graph. The two seeds with one common unsampled neighbour have degrees (1,1)
but induced degrees (0,0); the edge-between-seeds comparison has both (1,1). -/
def T17WholeStatement : Prop :=
  (∀ (D : Data) (H : State), Admissible D → GraphCompatible D H →
    InducedCompatible D (induced D H) ∧
    ((∀ i ∈ D.sampled, graphDegree (induced D H) (s i) = D.degree i) ↔
      H.vertices = sampledVertices D) ∧
    ((∀ i ∈ D.sampled, ∀ v ∈ H.vertices,
      {s i,v} ∈ H.edges → v ∈ sampledVertices D) ↔
      H.vertices = sampledVertices D) ∧
    (H.vertices = sampledVertices D ↔
      H.vertices = (induced D H).vertices ∧ H.edges = (induced D H).edges)) ∧
  (Admissible domainB ∧ GraphCompatible domainB commonNeighbourState ∧
    GraphCompatible domainB (dyad false true) ∧
    (∀ i ∈ domainB.sampled,
      graphDegree commonNeighbourState (s i) = 1 ∧
      graphDegree (dyad false true) (s i) = 1 ∧
      graphDegree (induced domainB commonNeighbourState) (s i) = 0 ∧
      graphDegree (induced domainB (dyad false true)) (s i) = 1) ∧
    (induced domainB commonNeighbourState).edges = ∅ ∧
    InducedCompatible domainB (induced domainB commonNeighbourState) ∧
    ¬ GraphCompatible domainB (induced domainB commonNeighbourState) ∧
    GraphCompatible domainB (induced domainB (dyad false true)))

/-- P012-T18; Appendix p. 160 (PDF p. 8), proof of Result 2;
p. 155 (PDF p. 3), after equation (2).
Homophily depends only on the displayed augmented graph and its traits,
including agreement of undefined partial values. Preferential recruitment
can change with the recruiter map alone or with entry order alone: on the
fixed four-vertex example the star, chain and reordered star histories give
the defined values -1/12, 1/6 and -1/3 respectively. -/
def T18WholeStatement : Prop :=
  (∀ H K : State, SamePair H K → homophily H = homophily K) ∧
  (Admissible starHistory ∧ Admissible chainHistory ∧ Admissible reorderedHistory ∧
    Compatible starHistory historyState ∧ Compatible chainHistory historyState ∧
    Compatible reorderedHistory historyState ∧
    chainHistory = {starHistory with parent := chainHistory.parent} ∧
    reorderedHistory = {starHistory with time := reorderedHistory.time} ∧
    recruitmentEdges starHistory ≠ recruitmentEdges chainHistory ∧
    recruitmentEdges starHistory = recruitmentEdges reorderedHistory ∧
    starHistory.time 2 < starHistory.time 3 ∧
    reorderedHistory.time 3 < reorderedHistory.time 2 ∧
    preferential starHistory historyState = some (-1/12) ∧
    preferential chainHistory historyState = some (1/6) ∧
    preferential reorderedHistory historyState = some (-1/3))

/-- P012-T22; abstract p. 153, introduction p. 154,
and text after Result 3, pp. 155--156 (PDF pp. 1--4).
On the stated whole-set domain, joint point identification is equivalent
to zero spare degree and to every compatible graph being the undirected
recruitment graph with its observed traits. A same-trait private-leaf flip
witnesses h variation, with the exact positive edge-count difference.
Preferential recruitment alone is identified exactly when actual recruiters
have no spare degree. In the (1,2)-degree, (0,1)-trait example every graph
has one private leaf at vertex 2: p=0 and h is -1 or -1/3 according to its
trait. Thus the exact value sets are {0} and {-1,-1/3}, and the smallest
containing intervals are {0} and [-1,-1/3], with attained endpoints. -/
def T22WholeStatement : Prop :=
  T22Statement ∧
  (∀ (D : Data), Admissible D →
    0 < sampledTraitDegree D false → 0 < sampledTraitDegree D true →
    ∀ i ∈ D.sampled, recruitmentDegree D i < D.degree i → WholeLeafFlip D i) ∧
  (Admissible oneLeafData ∧
    (∀ b : Bool, Compatible oneLeafData (oneLeafState b)) ∧
    (∀ H, Compatible oneLeafData H → ∃ v : Vertex,
      StarAtTwo H {v} ∧
      preferential oneLeafData H = some 0 ∧
      homophily H = some (if H.trait v then (-1/3) else (-1)) ∧
      H.vertices ≠ sampledVertices oneLeafData) ∧
    hValues oneLeafData = {(-1 : ℝ), -1/3} ∧ pValues oneLeafData = {0} ∧
    FullHomophilyRegion oneLeafData (-1) (-1/3) ∧
    FullPreferentialRegion oneLeafData 0 0 ∧
    SmallestValueInterval (hValues oneLeafData) (-1) (-1/3) ∧
    SmallestValueInterval (pValues oneLeafData) 0 0)

end
end SAP.P012b
