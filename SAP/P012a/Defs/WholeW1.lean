import Mathlib
import SAP.P012a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a

open Finset
open scoped Classical
noncomputable section

/-- Equality of graph/trait pairs on their active vertex sets. -/
def WholeActiveEq (H K : State) : Prop :=
  H.vertices = K.vertices ∧ H.edges = K.edges ∧
    ∀ v ∈ H.vertices, H.trait v = K.trait v

/-- Renaming unobserved identities, fixing every observed identity (R2). -/
def WholeRelabeling (D : Data) (H K : State) : Prop :=
  ∃ e : Equiv.Perm Vertex,
    (∀ i ∈ D.sampled, e (s i) = s i) ∧ H.vertices.image e = K.vertices ∧
    H.edges.image (fun edge => edge.image e) = K.edges ∧
    ∀ v ∈ H.vertices, K.trait (e v) = H.trait v

def wholeNeighbors (H : State) (v : Vertex) : Finset Vertex :=
  H.vertices.filter (fun w => {v,w} ∈ H.edges)

/-! T7: an exact rational streaming algorithm. The supplied records are already
chronological (S2). Indexed cells have unit lookup/update cost. Arithmetic is
exact, with unit arithmetic cost; no bit-complexity or constant-space claim is
made. A seed transition is charged 8 primitive operations and a nonseed
transition 32, upper bounds including reading, branching, casts and cell access.
A final charge of 4 covers the count cast and two divisions. Only cells at labels already read are stored. -/

structure PWholeRecord where
  label : ℕ
  seed : Bool
  parent : ℕ
  degree : ℕ
  trait : Bool

structure PWholeCell where
  remaining : ℕ
  reciprocal : ℚ
  trait : Bool
  deriving Inhabited

structure PWholeState where
  cells : ℕ → Option PWholeCell
  low : ℚ
  high : ℚ
  count : ℕ
  reads : ℕ
  reciprocals : ℕ
  work : ℕ

def pWholeInitial : PWholeState := ⟨fun _ => none, 0, 0, 0, 0, 0, 0⟩

def pWholeRecord (D : Data) (i : ℕ) : PWholeRecord :=
  ⟨i, decide (i ∈ D.seeds), D.parent i, D.degree i, D.trait i⟩

/-- A transition consults only the incoming record and stored recruiter cell. -/
def pWholeStep (st : PWholeState) (a : PWholeRecord) : PWholeState :=
  let cells := Function.update st.cells a.label
    (some ⟨a.degree - (if a.seed then 0 else 1), 0, a.trait⟩)
  if a.seed then
    {st with cells := cells, reads := st.reads + 1, work := st.work + 8}
  else
    let c := (cells a.parent).getD default
    let R := c.reciprocal + 1 / (c.remaining : ℚ)
    let I : ℚ := if a.trait = c.trait then 1 else 0
    {cells := Function.update cells a.parent
        (some {c with remaining := c.remaining - 1, reciprocal := R}),
      low := st.low + (1-I)*(R-1), high := st.high + I*(1-R),
      count := st.count + 1, reads := st.reads + 1,
      reciprocals := st.reciprocals + 1, work := st.work + 32}

def pWholeRun (D : Data) (order : List ℕ) : PWholeState :=
  (order.map (pWholeRecord D)).foldl pWholeStep pWholeInitial

def pWholeOutput (st : PWholeState) : ℚ × ℚ :=
  (st.low / (st.count : ℚ), st.high / (st.count : ℚ))

def WholeChronological (D : Data) (order : List ℕ) : Prop :=
  order.Nodup ∧ order.toFinset = D.sampled ∧
    order.Pairwise (fun i j => D.time i < D.time j)

def pWholeDelta (D : Data) (r : ℕ) : ℕ := if r ∈ D.seeds then 0 else 1

def pWholeChildrenBefore (D : Data) (pre : List ℕ) (r : ℕ) : Finset ℕ :=
  pre.toFinset.filter (fun k => k ∈ nonseeds D ∧ D.parent k = r)

def pWholeDenom (D : Data) (j : ℕ) : ℕ :=
  (laterChildren D j).card + spare D (D.parent j)

def pWholePrefixReciprocal (D : Data) (pre : List ℕ) (r : ℕ) : ℚ :=
  ∑ k ∈ pWholeChildrenBefore D pre r, 1 / (pWholeDenom D k : ℚ)

def pWholePastReciprocal (D : Data) (j : ℕ) : ℚ :=
  ∑ k ∈ (nonseeds D).filter
    (fun k => D.parent k = D.parent j ∧ D.time k ≤ D.time j),
    1 / (pWholeDenom D k : ℚ)

def pWholeMatch (D : Data) (j : ℕ) : ℚ :=
  if D.trait j = D.trait (D.parent j) then 1 else 0

def pWholeForwardLow (D : Data) (pre : List ℕ) : ℚ :=
  ∑ j ∈ pre.toFinset.filter (fun j => j ∈ nonseeds D),
    (1-pWholeMatch D j)*(pWholePastReciprocal D j-1)

def pWholeForwardHigh (D : Data) (pre : List ℕ) : ℚ :=
  ∑ j ∈ pre.toFinset.filter (fun j => j ∈ nonseeds D),
    pWholeMatch D j*(1-pWholePastReciprocal D j)

/-- Recruitment incidence and the positive residual at every event. -/
def PWholeSchedule (D : Data) (order : List ℕ) : Prop :=
  (∀ r ∈ D.sampled, recruitmentDegree D r = pWholeDelta D r +
    ((nonseeds D).filter (fun k => D.parent k = r)).card) ∧
  ∀ pre j post, order = pre ++ j :: post → j ∈ nonseeds D →
    D.parent j ∈ pre ∧
    D.degree (D.parent j) - pWholeDelta D (D.parent j) -
      (pWholeChildrenBefore D pre (D.parent j)).card = pWholeDenom D j ∧
    0 < pWholeDenom D j

/-- Full prefix invariant. In particular the default cell and zero reciprocal
denominator in the total program are never used on an admissible input. -/
def PWholeInvariant (D : Data) (order : List ℕ) : Prop :=
  (∀ pre post, order = pre ++ post →
    let st := pWholeRun D pre
    st.count = (pre.toFinset.filter (fun j => j ∈ nonseeds D)).card ∧
    st.low = pWholeForwardLow D pre ∧ st.high = pWholeForwardHigh D pre ∧
    ∀ r, st.cells r = if r ∈ pre.toFinset then
      some ⟨D.degree r - pWholeDelta D r - (pWholeChildrenBefore D pre r).card,
        pWholePrefixReciprocal D pre r, D.trait r⟩ else none) ∧
  ∀ pre j post, order = pre ++ j :: post → j ∈ nonseeds D →
    ∃ c, (pWholeRun D pre).cells (D.parent j) = some c ∧
      c.trait = D.trait (D.parent j) ∧
      c.remaining = pWholeDenom D j ∧ 0 < c.remaining

/-- A single read of each chronological record, exact endpoint output, safe
event divisions, at most n stored cells and at most 32n+4 unit operations. -/
def PWholeOnePass (D : Data) (order : List ℕ) : Prop :=
  let st := pWholeRun D order
  ((pWholeOutput st).1 : ℝ) = pLower D ∧
  ((pWholeOutput st).2 : ℝ) = pUpper D ∧
  st.count = (nonseeds D).card ∧ 0 < st.count ∧
  st.reads = D.sampled.card ∧ st.reciprocals = (nonseeds D).card ∧
  st.work + 4 ≤ 32 * D.sampled.card + 4 ∧
  (∀ pre post, order = pre ++ post →
    (pWholeRun D pre).reads = pre.length ∧
    ∃ keys : Finset ℕ, keys = pre.toFinset ∧ keys.card ≤ D.sampled.card ∧
      ∀ r, ((pWholeRun D pre).cells r).isSome = true ↔ r ∈ keys) ∧
  ∀ pre j post, order = pre ++ j :: post → j ∈ nonseeds D →
    ∃ c, (pWholeRun D pre).cells (D.parent j) = some c ∧
      c.trait = D.trait (D.parent j) ∧
      c.remaining = pWholeDenom D j ∧ 0 < c.remaining

/-- P012-T7; Web Appendix p. 1 (supplement PDF p. 1); Definitions 2–4:
p. 155 (PDF p. 3).
The observed recruitment history and spare degrees give the sharp attained
preferential-recruitment interval. Obligatory child sets are nonempty; every
compatible susceptible fraction has the stated decomposition and sharp bounds.
Same-trait private degree-one neighbours attain p_min, and opposite-trait
private degree-one neighbours attain p_max. The smallest containing interval
is [p_min,p_max]. An exact rational forward algorithm computes
both endpoints in one pass over the supplied chronological records, with positive
event denominators, one read per record, at most n stored cells and at most 32n+4
unit arithmetic and indexed-cell operations, including the final divisions. -/
def T7WholeStatement : Prop :=
  T7Statement ∧
  (∀ D : Data, Admissible D → D.seeds.card < D.sampled.card →
    ∀ order, WholeChronological D order → PWholeOnePass D order) ∧
  (∀ D : Data, Admissible D → ∃ order, WholeChronological D order) ∧
  (∀ D : Data, Admissible D → ∀ same : Bool,
    ∀ i ∈ D.sampled, ∀ k < spare D i,
      wholeNeighbors (leafCompletion D same) (u i k) = {s i})

/-- The printed claim is false: P012-T9; Appendix, p. 160 (PDF p. 8);
Result 2: p. 155 (PDF p. 3).
The specified compatible starting pair has both cross edges already present.
The printed swap leaves degrees (2,2,2,1,1) instead of (3,2,3,2,2), and four
edges instead of six, so its output is incompatible. Its equation-(1)
denominator is 15/8, whereas the starting denominator is 35/12; both are positive
and unequal. This refutes the printed proof step. -/
def T9WholeStatement : Prop :=
  T9Statement ∧
  result2BadEnd.trait = result2BadStart.trait ∧
  degreeTraitSum result2BadStart = 5 ∧ degreeTraitSum result2BadEnd = 3 ∧
  hDenominator result2BadStart = 35/12 ∧ hDenominator result2BadEnd = 15/8 ∧
  0 < hDenominator result2BadStart ∧ 0 < hDenominator result2BadEnd ∧
  hDenominator result2BadStart ≠ hDenominator result2BadEnd

/-! T10: choose concrete fresh labels. The shared label is u i 0. Its old
private slot at i and slot 0 at j are omitted from the further leaf sets. -/

def r1WholeLeaves (D : Data) (i j v : ℕ) : Finset Vertex :=
  ((range (spare D v)).filter (fun k => k ≠ 0 ∨ (v ≠ i ∧ v ≠ j))).image (u v)

def r1WholeStart (D : Data) (i j : ℕ) (τ : Vertex → Bool) : State :=
  ⟨sampledVertices D ∪ insert (u i 0) (D.sampled.biUnion (r1WholeLeaves D i j)),
    recruitmentEdges D ∪ {{s i,u i 0},{s j,u i 0}} ∪
      D.sampled.biUnion (fun v => (r1WholeLeaves D i j v).image (fun w => {s v,w})),
    τ⟩

def r1WholeEnd (D : Data) (i j : ℕ) (τ : Vertex → Bool) : State :=
  let H := r1WholeStart D i j τ
  ⟨H.vertices.erase (u i 0),
    insert {s i,s j} ((H.edges.erase {s i,u i 0}).erase {s j,u i 0}), τ⟩

def R1WholeGeometry (D : Data) (i j : ℕ) : Prop :=
  0 < spare D i ∧ 0 < spare D j ∧ {s i,s j} ∉ recruitmentEdges D ∧
  (∀ v ∈ D.sampled,
    (r1WholeLeaves D i j v).card =
      if v = i ∨ v = j then spare D v - 1 else spare D v) ∧
  (∀ v ∈ D.sampled, Disjoint (r1WholeLeaves D i j v) (sampledVertices D) ∧
    u i 0 ∉ r1WholeLeaves D i j v) ∧
  (∀ v ∈ D.sampled, ∀ w ∈ D.sampled, v ≠ w →
    Disjoint (r1WholeLeaves D i j v) (r1WholeLeaves D i j w)) ∧
  ∀ τ : Vertex → Bool,
    let H := r1WholeStart D i j τ
    let K := r1WholeEnd D i j τ
    u i 0 ∈ unsampled D H ∧ wholeNeighbors H (u i 0) = {s i,s j} ∧
    (∀ v ∈ D.sampled, ∀ w ∈ r1WholeLeaves D i j v,
      wholeNeighbors H w = {s v} ∧ wholeNeighbors K w = {s v}) ∧
    {s i,s j} ∉ H.edges ∧ {s i,s j} ∈ K.edges ∧
    (induced D H).edges = recruitmentEdges D ∧
    (induced D K).edges = insert {s i,s j} (recruitmentEdges D)

/-- P012-T10; Result 1: p. 155 (PDF p. 3); corrected proof: Appendix,
p. 160 (PDF p. 8).
Two time-ordered sampled vertices not joined by a recruitment edge, each with
positive spare degree, give two distinct compatible augmented graphs and two
distinct compatible sampled induced graphs. The first graph has exactly one shared unsampled neighbour of
the two chosen vertices, s_i-1 and s_j-1 further private leaves there, and s_v
private leaves at every other sampled vertex. The shared vertex has exactly the
two chosen neighbours; every private leaf has degree one. For every binary
assignment extending the observed traits both graphs are compatible. The second
deletes precisely the shared vertex and its two edges, adds {i,j}, and keeps all
remaining traits. The induced edge sets are B and B union {{i,j}}. The graphs
remain distinct under every renaming of unsampled identities, so neither graph
is identified. -/
def T10WholeStatement : Prop :=
  ∀ (D : Data), Admissible D → ∀ i j : ℕ,
    i ∈ D.sampled → j ∈ D.sampled → D.time i < D.time j →
    ¬ (j ∈ nonseeds D ∧ D.parent j = i) →
    recruitmentDegree D i < D.degree i → recruitmentDegree D j < D.degree j →
    R1WholeGeometry D i j ∧
    ∀ τ : Vertex → Bool, (∀ k ∈ D.sampled, τ (s k) = D.trait k) →
      let H := r1WholeStart D i j τ
      let K := r1WholeEnd D i j τ
      Compatible D H ∧ Compatible D K ∧
      K.vertices = H.vertices.erase (u i 0) ∧
      K.edges = insert {s i,s j} ((H.edges.erase {s i,u i 0}).erase {s j,u i 0}) ∧
      K.trait = H.trait ∧
      cleanup D true (addEdge (removeEdge (removeEdge H (s i) (u i 0))
        (s j) (u i 0)) (s i) (s j)) = K ∧
      InducedCompatible D (induced D H) ∧ InducedCompatible D (induced D K) ∧
      ¬ WholeRelabeling D H K ∧ H ≠ K ∧ induced D H ≠ induced D K

/-! T11: all choices of the two private neighbours, not just slot 0. -/

def wholeSwap (H : State) (i j x y : ℕ) : State :=
  addEdge (addEdge (removeEdge (removeEdge H (s i) (u i x))
    (s j) (u j y)) (s i) (u j y)) (s j) (u i x)

def WholeSwapFacts (D : Data) (H : State) (i j x y : ℕ) : Prop :=
  let K := wholeSwap H i j x y
  let Q := degreeTraitSum H
  Compatible D H ∧ Compatible D K ∧
  {s i,u i x} ∈ H.edges ∧ {s j,u j y} ∈ H.edges ∧
  {s i,u j y} ∉ H.edges ∧ {s j,u i x} ∉ H.edges ∧
  H.vertices = K.vertices ∧ H.trait = K.trait ∧ H.edges.card = K.edges.card ∧
  (∀ v, graphDegree H v = graphDegree K v) ∧
  hDenominator H = Q-Q^2/(2*(H.edges.card:ℝ)) ∧
  hDenominator H = Q*(2*(H.edges.card:ℝ)-Q)/(2*(H.edges.card:ℝ)) ∧
  hDenominator H = hDenominator K ∧ 0 < hDenominator H ∧
  hValue H-hValue K =
    (2*(1-(graphDegree H (s j):ℝ)*graphDegree H (u j y)/(2*(H.edges.card:ℝ))) -
      2*(0-(graphDegree H (s j):ℝ)*graphDegree H (u j y)/(2*(H.edges.card:ℝ)))) /
      hDenominator H ∧
  hValue H-hValue K = 2/hDenominator H ∧ hValue H ≠ hValue K ∧
  HomophilyDefined H ∧ HomophilyDefined K

/-- P012-T11; Result 2: p. 155 (PDF p. 3); corrected proof and (A1):
Appendix, p. 160 (PDF p. 8).
Opposite-trait sampled vertices with spare degree make homophily not point
identified. Attach exactly s_v private degree-one neighbours to each sampled
vertex. Any selected private neighbours of the normalized trait-0 and trait-1
vertices can be assigned traits 0 and 1, with all other unsampled traits arbitrary.
The cross edges are absent and the swap is compatible and preserves vertices,
traits, all degrees and edge count. With Q the trait-weighted degree sum, both
denominators equal Q-Q^2/(2m)=Q(2m-Q)/(2m)>0, because Q≥d_j>0 and
2m-Q≥d_i>0. Both forms of (A1) give h_1-h_2=2/D≠0. The stated exact
two-subject instance has m=3, Q=3, D=3/2, h_1=1/3, h_2=-1 and difference 4/3. -/
def T11WholeStatement : Prop :=
  T11Statement ∧
  (∀ (D : Data), Admissible D → ∀ i j x y : ℕ,
    i ∈ D.sampled → j ∈ D.sampled →
    recruitmentDegree D i < D.degree i → recruitmentDegree D j < D.degree j →
    D.trait i = false → D.trait j = true → x < spare D i → y < spare D j →
    ∀ H : State, H.vertices = (leafCompletion D true).vertices →
      H.edges = (leafCompletion D true).edges →
      (∀ k ∈ D.sampled, H.trait (s k) = D.trait k) →
      H.trait (u i x) = false → H.trait (u j y) = true →
      WholeSwapFacts D H i j x y ∧
      (D.degree j : ℝ) ≤ degreeTraitSum H ∧ 0 < D.degree j ∧
      (D.degree i : ℝ) ≤ 2*(H.edges.card : ℝ)-degreeTraitSum H ∧ 0 < D.degree i) ∧
  (∀ D : Data, Admissible D → ∀ same : Bool,
    ∀ i ∈ D.sampled, ∀ k < spare D i,
      wholeNeighbors (leafCompletion D same) (u i k) = {s i})

/-! T1: the printed relation retains its chosen i,j and both coin results.
`true` denotes the B<1/2 branch. Freshness refers to the pending vertex set,
and replacement pools are computed from the original state, as in S9. -/

inductive WholeCoinReplacement (D : Data) (current pending : State)
    (i : ℕ) (coin : Bool) : Vertex → State → Prop
  | existing (v : Vertex) (hc : coin = true)
      (hv : v ∈ replacementPool D current i) :
      WholeCoinReplacement D current pending i coin v pending
  | fresh (v : Vertex) (hc : coin = false ∨ replacementPool D current i = ∅)
      (hv : v ∉ pending.vertices) (t : Bool) :
      WholeCoinReplacement D current pending i coin v (addVertex pending v t)

inductive WholePrintedRun (D : Data) (H : State) (i : ℕ) (j : Vertex)
    (coin₁ coin₂ : Bool) : State → Prop
  | deleteUnobserved (v : Vertex) (P : State)
      (hi : i ∈ D.sampled) (hj : j ∈ H.vertices) (hne : s i ≠ j)
      (he : {s i,j} ∈ H.edges) (hr : {s i,j} ∉ recruitmentEdges D)
      (hju : j ∉ sampledVertices D)
      (hp : WholeCoinReplacement D H (removeEdge H (s i) j) i coin₁ v P) :
      WholePrintedRun D H i j coin₁ coin₂
        (cleanup D false (addEdge (addEdge P (s i) v) j v))
  | deleteObserved (k : ℕ) (hjk : j = s k) (v w : Vertex) (P Q : State)
      (hi : i ∈ D.sampled) (hk : k ∈ D.sampled) (hne : i ≠ k)
      (he : {s i,s k} ∈ H.edges) (hr : {s i,s k} ∉ recruitmentEdges D)
      (hp : WholeCoinReplacement D H (removeEdge H (s i) (s k)) i coin₁ v P)
      (hq : WholeCoinReplacement D H (addEdge P (s i) v) k coin₂ w Q) :
      WholePrintedRun D H i j coin₁ coin₂ (cleanup D false (addEdge Q (s k) w))
  | addObserved (v w : Vertex)
      (hi : i ∈ D.sampled) (hj : j ∈ H.vertices) (hne : s i ≠ j)
      (he : {s i,j} ∉ H.edges)
      (hv : v ∈ unsampled D H) (hw : w ∈ unsampled D H)
      (hiv : {s i,v} ∈ H.edges) (hjw : {j,w} ∈ H.edges) :
      WholePrintedRun D H i j coin₁ coin₂ (cleanup D false
        (addEdge (removeEdge (removeEdge H (s i) v) j w) (s i) j))
  | unchanged (hi : i ∈ D.sampled) (hj : j ∈ H.vertices) (hne : s i ≠ j)
      (hdel : ¬ ({s i,j} ∈ H.edges ∧ {s i,j} ∉ recruitmentEdges D))
      (hadd : ¬ ({s i,j} ∉ H.edges ∧ ∃ v ∈ unsampled D H,
        ∃ w ∈ unsampled D H, {s i,v} ∈ H.edges ∧ {j,w} ∈ H.edges)) :
      WholePrintedRun D H i j coin₁ coin₂ (cleanup D false H)

def wholeBadPending (H : State) (i : ℕ) (old fresh : Vertex) (t : Bool) : State :=
  addEdge (addEdge (addVertex (removeEdge H (s i) old) fresh t) (s i) fresh) old fresh

def WholeBadOutput (D : Data) (H : State) (i : ℕ) (old fresh : Vertex)
    (t : Bool) : Prop :=
  let P := wholeBadPending H i old fresh t
  cleanup D false P = P ∧ P.vertices = insert fresh H.vertices ∧
  P.edges = insert {old,fresh} (insert {s i,fresh} (H.edges.erase {s i,old})) ∧
  P.trait = Function.update H.trait fresh t ∧
  (∀ v ∈ P.vertices, graphDegree P v ≠ 0) ∧
  old ∉ sampledVertices D ∧ fresh ∉ sampledVertices D ∧ {old,fresh} ∈ P.edges ∧
  (∀ k ∈ D.sampled, {s k,old} ∉ P.edges) ∧
  sampledVertices D ⊆ P.vertices ∧ recruitmentEdges D ⊆ P.edges ∧
  (∀ k ∈ D.sampled, P.trait (s k) = D.trait k) ∧
  (∀ k ∈ D.sampled, graphDegree P (s k) = D.degree k) ∧
  ¬ Compatible D P

/-- The printed claim is false: P012-T1; Web Appendix pp. 2–3
(supplement PDF pp. 2–3); the kernel K: Web Appendix p. 1; augmented graphs
and Definition 3: p. 155 (PDF p. 3).
All four specified counterexamples hold, including their functional values.
In (a) and (b), for the fixed chosen i,j and either coin outcome, every execution
uses a fresh vertex of either trait and produces exactly the stated old graph
with the removed sampled edge replaced by a sampled–fresh edge and an
old-unsampled–fresh edge. Cleanup deletes nothing. The old unsampled vertex
has no sampled neighbour; the output is incompatible, while conditions 1,2,4
remain true in (a). Every fresh name gives the named output up to renaming
unsampled identities. In (c) both branches fail and cleanup deletes precisely
sampled seed 3, violating vertex preservation and inclusion of the observed
active trait assignment. In (d) every compatible pair is the displayed dyad
on its active domain, so the trait proposal has no vertex to choose. -/
def T1WholeStatement : Prop :=
  T1Statement ∧
  (∀ D H i j c₁ c₂ K, WholePrintedRun D H i j c₁ c₂ K →
    GraphProposal D false H K) ∧
  (∀ c₁ c₂ K,
    (WholePrintedRun proposalData proposalStart 1 (u 3 0) c₁ c₂ K ↔
      ∃ v, v ∉ proposalStart.vertices ∧ ∃ t : Bool,
        K = cleanup proposalData false (wholeBadPending proposalStart 1 (u 3 0) v t))) ∧
  (∀ c₁ c₂ K,
    (WholePrintedRun proposalDataB proposalStartB 2 (u 4 0) c₁ c₂ K ↔
      ∃ v, v ∉ proposalStartB.vertices ∧ ∃ t : Bool,
        K = cleanup proposalDataB false (wholeBadPending proposalStartB 2 (u 4 0) v t))) ∧
  (∀ v, v ∉ proposalStart.vertices → ∀ t : Bool,
    WholeBadOutput proposalData proposalStart 1 (u 3 0) v t ∧
    WholeRelabeling proposalData (wholeBadPending proposalStart 1 (u 3 0) v t)
      (proposalBad t)) ∧
  (∀ v, v ∉ proposalStartB.vertices → ∀ t : Bool,
    WholeBadOutput proposalDataB proposalStartB 2 (u 4 0) v t ∧
    WholeRelabeling proposalDataB (wholeBadPending proposalStartB 2 (u 4 0) v t)
      (proposalBadB t)) ∧
  (∀ c₁ c₂ K, WholePrintedRun cleanupData cleanupStart 1 (s 2) c₁ c₂ K ↔
    K = cleanup cleanupData false cleanupStart) ∧
  (let K := cleanup cleanupData false cleanupStart;
    K.vertices = {s 1,s 2} ∧ K.edges = {{s 1,s 2}} ∧
    s 3 ∈ sampledVertices cleanupData ∧ s 3 ∉ K.vertices ∧
    ¬ sampledVertices cleanupData ⊆ K.vertices ∧
    ¬ (∀ k ∈ cleanupData.sampled,
      s k ∈ K.vertices ∧ K.trait (s k) = cleanupData.trait k)) ∧
  (∀ H, Compatible emptyPoolData H → WholeActiveEq H (dyad false true))

end
end SAP.P012a
