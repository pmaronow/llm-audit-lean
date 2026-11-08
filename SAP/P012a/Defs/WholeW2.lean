import Mathlib
import SAP.P012a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a

open Finset
open scoped Classical
noncomputable section

/-- A replacement uses the original pool, or invents a vertex fresh in the
pending state. Invention leaves the edge set fixed. -/
def W2ReplacementFacts (D : Data) (H L : State) (i : ℕ) (v : Vertex)
    (P : State) : Prop :=
  v ∈ P.vertices ∧ v ∉ sampledVertices D ∧ P.edges = L.edges ∧
  {s i, v} ∉ P.edges ∧
  ((v ∈ replacementPool D H i ∧ P = L) ∨
    (v ∉ L.vertices ∧ ∃ t : Bool, P = addVertex L v t))

/-- Detailed trace for the deletion branch with an unsampled second endpoint.
The final equivalence uses the original edges, so it says exactly that the
deleted edge was the old vertex's only incident edge. -/
def W2DeleteUnobserved (D : Data) (H : State) (i : ℕ) (j v : Vertex)
    (P : State) : Prop :=
  let R := removeEdge H (s i) j
  let A := addEdge P (s i) v
  W2ReplacementFacts D H R i v P ∧
  (∀ k ∈ D.sampled,
    graphDegree R (s k) + (if k = i then 1 else 0) = graphDegree H (s k)) ∧
  (∀ x : Vertex, graphDegree P x = graphDegree R x) ∧
  (∀ k ∈ D.sampled, graphDegree A (s k) = graphDegree H (s k)) ∧
  (j ∉ (cleanup D true A).vertices ↔
    ∀ e ∈ H.edges, j ∈ e → e = {s i, j})

/-- Detailed trace for the sampled--sampled deletion branch. The two replacement
choices need not be distinct when existing vertices are chosen. -/
def W2DeleteObserved (D : Data) (H : State) (i j : ℕ) (v w : Vertex)
    (P Q : State) : Prop :=
  let R := removeEdge H (s i) (s j)
  let A := addEdge P (s i) v
  let B := addEdge Q (s j) w
  W2ReplacementFacts D H R i v P ∧
  W2ReplacementFacts D H A j w Q ∧
  (∀ z ∈ replacementPool D H j, {s j, z} ∉ A.edges) ∧
  (∀ k ∈ D.sampled,
    graphDegree R (s k) + (if k = i then 1 else 0) +
      (if k = j then 1 else 0) = graphDegree H (s k)) ∧
  (∀ x : Vertex, graphDegree P x = graphDegree R x) ∧
  (∀ k ∈ D.sampled,
    graphDegree A (s k) + (if k = j then 1 else 0) = graphDegree H (s k)) ∧
  (∀ x : Vertex, graphDegree Q x = graphDegree A x) ∧
  (∀ k ∈ D.sampled, graphDegree B (s k) = graphDegree H (s k))

/-- Detailed trace for the addition branch. The two incidence indicators count
two lost edges at a shared selected unsampled vertex as well. -/
def W2AddObserved (D : Data) (H : State) (i : ℕ) (j v w : Vertex) : Prop :=
  let R := removeEdge (removeEdge H (s i) v) j w
  let A := addEdge R (s i) j
  j ∈ sampledVertices D ∧
  ({s i, v} : Finset Vertex) ≠ {j, w} ∧
  {s i, v} ∉ recruitmentEdges D ∧ {j, w} ∉ recruitmentEdges D ∧
  (∀ x : Vertex,
    graphDegree R x + (if x ∈ ({s i, v} : Finset Vertex) then 1 else 0) +
      (if x ∈ ({j, w} : Finset Vertex) then 1 else 0) = graphDegree H x) ∧
  (∀ k ∈ D.sampled, graphDegree A (s k) = graphDegree H (s k)) ∧
  (v ∉ (cleanup D true A).vertices ↔ graphDegree A v = 0) ∧
  (w ∉ (cleanup D true A).vertices ↔ graphDegree A w = 0)

/-- P012-T2; Web Appendix pp. 2–3 (supplement PDF pp. 2–3).
Every execution of either corrected mechanism preserves compatibility. In the
unsampled deletion branch exactly one sampled degree is restored, and cleanup
deletes the old unsampled endpoint exactly when its only neighbour was the
selected sampled vertex. In the sampled deletion branch both degrees are
restored and the original second replacement pool remains nonadjacent. In the
addition branch the second endpoint is sampled, two distinct non-recruitment
edges are removed even for a shared unsampled endpoint, both sampled degrees
are restored, and cleanup deletes exactly the selected vertices left isolated.
If neither branch applies the state is unchanged. Recruitment edges, sampled
vertices and traits, and the augmented graph rules are preserved throughout
the returned states. The trait mechanism flips one unsampled trait or returns
the same state when the unsampled set is empty.
-/
def T2WholeStatement : Prop :=
  corrected_proposal_preservesClaim ∧
  (∀ (D : Data) (H : State) (i : ℕ) (j v : Vertex) (P : State),
    Admissible D → Compatible D H → i ∈ D.sampled → j ∈ H.vertices →
    s i ≠ j → {s i, j} ∈ H.edges → {s i, j} ∉ recruitmentEdges D →
    j ∉ sampledVertices D → Replacement D H (removeEdge H (s i) j) i v P →
    W2DeleteUnobserved D H i j v P) ∧
  (∀ (D : Data) (H : State) (i j : ℕ) (v w : Vertex) (P Q : State),
    Admissible D → Compatible D H → i ∈ D.sampled → j ∈ D.sampled → i ≠ j →
    {s i, s j} ∈ H.edges → {s i, s j} ∉ recruitmentEdges D →
    Replacement D H (removeEdge H (s i) (s j)) i v P →
    Replacement D H (addEdge P (s i) v) j w Q → W2DeleteObserved D H i j v w P Q) ∧
  (∀ (D : Data) (H : State) (i : ℕ) (j v w : Vertex),
    Admissible D → Compatible D H → i ∈ D.sampled → j ∈ H.vertices → s i ≠ j →
    {s i, j} ∉ H.edges → v ∈ unsampled D H → w ∈ unsampled D H →
    {s i, v} ∈ H.edges → {j, w} ∈ H.edges → W2AddObserved D H i j v w) ∧
  (∀ (D : Data) (H : State), Compatible D H → cleanup D true H = H) ∧
  (∀ (D : Data) (H K : State), TraitProposal D true H K →
    K.vertices = H.vertices ∧ K.edges = H.edges ∧
    ((unsampled D H = ∅ ∧ K = H) ∨
      ∃ v ∈ unsampled D H, K = flipTrait H v ∧ K.trait v = !H.trait v ∧
        ∀ x : Vertex, x ≠ v → K.trait x = H.trait x))

/-- Private degree-one neighbours and sampled degrees in the explicit attaining
construction. The neighbour assertion ranges over all edges, not just sampled
neighbours. -/
def W2LeafStructure (D : Data) (same : Bool) : Prop :=
  (∀ i ∈ D.sampled, ∀ k < spare D i,
    u i k ∈ unsampled D (leafCompletion D same) ∧
    graphDegree (leafCompletion D same) (u i k) = 1 ∧
    (∀ e ∈ (leafCompletion D same).edges, u i k ∈ e → e = {s i, u i k}) ∧
    (leafCompletion D same).trait (u i k) =
      (if same then D.trait i else !D.trait i)) ∧
  (∀ i ∈ D.sampled,
    graphDegree (leafCompletion D same) (s i) = recruitmentDegree D i + spare D i ∧
    recruitmentDegree D i + spare D i = D.degree i)

/-- The printed claim is false: P012-T3; Table 1: p. 158 (PDF p. 6);
network counts and seeds: p. 156 (PDF p. 4); bounds: pp. 156–157 (PDF pp. 4–5);
Definitions 3–4: p. 155 (PDF p. 3).
For every admissible data set with 527 sampled vertices, six seeds and sampled
degree total 4487, the opposite-trait private-leaf completion is compatible,
has 521 recruitment edges, 3445 private degree-one leaves and 3972 vertices,
and has positive equation-(1) denominator. Its edge counts and quotient value
obey the uniform real bound -1462/1983 and the sharp integer bound
-178409/241987, attained by the two stated integer triples. The displayed
polynomial certificate is nonnegative. All three printed lower bounds are
violated, with the exact stated gaps exceeding four-decimal rounding error;
even a rounded lower endpoint cannot enclose every compatible homophily value.
The larger completion is allowed because compatibility fixes no population size.
-/
def T3WholeStatement : Prop :=
  T3Statement ∧
  (∀ (D : Data), Admissible D → D.sampled.card = 527 → D.seeds.card = 6 →
    (∑ i ∈ D.sampled, D.degree i) = 4487 →
    (recruitmentEdges D).card = 521 ∧
    0 < hDenominator (leafCompletion D false) ∧
    (leafCompletion D false).vertices.card = 3972 ∧
    2626 < (leafCompletion D false).vertices.card ∧ W2LeafStructure D false ∧
    ∀ q ∈ ({-7027/10000, -6918/10000, -7179/10000} : Finset ℝ),
      ∀ L U : ℝ, |L - q| ≤ 1/20000 →
        hValue (leafCompletion D false) < L ∧ ¬ hValues D ⊆ Set.Icc L U) ∧
  (∀ (a b c : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ c → a + b + c = 521 →
    (-1462/1983 : ℝ) * ((2*a+c+3445)*(2*b+c+3445)) -
        (4*a*b-(c+3445)^2) = 7932*c + (3445/1983)*(a-b)^2 ∧
    0 ≤ 7932*c + (3445/1983)*(a-b)^2) ∧
  ((1/20000 : ℝ) < 685459/19830000 ∧
    (1/20000 : ℝ) < 450803/9915000 ∧ (1/20000 : ℝ) < 384043/19830000)

end

/-- The five sufficient statistics plus instrumentation. Instrumentation updates
are excluded from the measured arithmetic of the underlying algorithm. -/
structure W2HCounts where
  d0 : ℕ := 0
  d1 : ℕ := 0
  ones : ℕ := 0
  zeros : ℕ := 0
  mixed : ℕ := 0
  visits : ℕ := 0
  additions : ℕ := 0
  deriving DecidableEq

/-- One indexed trait/degree lookup and one accumulator addition. -/
def w2VertexStep (D : Data) (i : ℕ) (q : W2HCounts) : W2HCounts :=
  if D.trait i then
    {q with d1 := q.d1 + D.degree i, visits := q.visits + 1, additions := q.additions + 1}
  else
    {q with d0 := q.d0 + D.degree i, visits := q.visits + 1, additions := q.additions + 1}

/-- An edge record is its recruited child; indexed parent and trait access
classifies the recruitment edge with one accumulator addition. -/
def w2EdgeStep (D : Data) (j : ℕ) (q : W2HCounts) : W2HCounts :=
  if D.trait (D.parent j) then
    if D.trait j then
      {q with ones := q.ones + 1, visits := q.visits + 1, additions := q.additions + 1}
    else
      {q with mixed := q.mixed + 1, visits := q.visits + 1, additions := q.additions + 1}
  else
    if D.trait j then
      {q with mixed := q.mixed + 1, visits := q.visits + 1, additions := q.additions + 1}
    else
      {q with zeros := q.zeros + 1, visits := q.visits + 1, additions := q.additions + 1}

/-- Tail recursion consumes each vertex record once. -/
def w2ScanVertices (D : Data) : List ℕ → W2HCounts → W2HCounts
  | [], q => q
  | i :: rest, q => w2ScanVertices D rest (w2VertexStep D i q)

/-- Tail recursion consumes each directed recruitment record once. -/
def w2ScanEdges (D : Data) : List ℕ → W2HCounts → W2HCounts
  | [], q => q
  | j :: rest, q => w2ScanEdges D rest (w2EdgeStep D j q)

/-- A single scan of each of the two observed input streams. There is no call
to a vertex's recruitment degree, graph incidence filter, or edge enumeration. -/
def w2Scan (D : Data) (vertices children : List ℕ) : W2HCounts :=
  w2ScanEdges D children (w2ScanVertices D vertices {})

/-- A representation condition, not a restriction on the observed data. -/
def W2Enumerates (D : Data) (vertices children : List ℕ) : Prop :=
  vertices.Nodup ∧ vertices.toFinset = D.sampled ∧
  children.Nodup ∧ children.toFinset = nonseeds D

/-- Constant postprocessing in exact arithmetic. The degree-budget identities
proved in the blueprint ensure neither natural subtraction truncates. There
are six operations to recover the two spare totals, four further natural
additions, and eight rational operations per endpoint: 26 arithmetic operations.
Coercions and record access are not arithmetic operations in this cost model. -/
def w2Finish (q : W2HCounts) : ℚ × ℚ :=
  let s1 := q.d1 - (2*q.ones + q.mixed)
  let s0 := q.d0 - (2*q.zeros + q.mixed)
  let c := q.mixed + (s0+s1)
  let x := q.ones + s1
  let y := q.zeros + s0
  (1 - (c : ℚ)/(2*(q.ones : ℚ)+c) - (c : ℚ)/(2*(q.zeros : ℚ)+c),
    1 - (q.mixed : ℚ)/(2*(x : ℚ)+q.mixed) -
      (q.mixed : ℚ)/(2*(y : ℚ)+q.mixed))

noncomputable section

/-- P012-T6; Web Appendix p. 1 (supplement PDF p. 1);
Definitions 1, 3 and 4: p. 155 (PDF p. 3).
For admissible observed data with positive sampled degree total in each trait
group, every compatible graph has the positive displayed denominator and the
displayed edge-count and homophily bounds. Opposite-trait and same-trait private
degree-one leaf completions attain the bounds, so their endpoints give the
smallest containing interval. An explicit algorithm scans each sampled-vertex
record and each directed recruitment-edge record once, in any order within
each stream, accumulating the two degree totals and three edge-type counts.
It recovers the spare totals without truncated subtraction and returns the
two exact rational endpoints. The instrumented scan has exactly n+|E_R| visits
and accumulator additions, followed by 26 arithmetic operations, with indexed
trait/degree/parent access and unit-cost exact arithmetic.
-/
def T6WholeStatement : Prop :=
  T6Statement ∧
  (∀ (D : Data), Admissible D → 0 < sampledTraitDegree D false →
    0 < sampledTraitDegree D true →
    W2LeafStructure D false ∧ W2LeafStructure D true ∧
    (∀ L U : ℝ, hValues D ⊆ Set.Icc L U ↔ L ≤ hLower D ∧ hUpper D ≤ U) ∧
    ∀ vertices children : List ℕ, W2Enumerates D vertices children →
      let q := w2Scan D vertices children
      q.d0 = sampledTraitDegree D false ∧ q.d1 = sampledTraitDegree D true ∧
      q.ones = a D ∧ q.zeros = b D ∧ q.mixed = cR D ∧
      q.d1 = 2*q.ones + q.mixed + traitSpare D true ∧
      q.d0 = 2*q.zeros + q.mixed + traitSpare D false ∧
      q.d1 - (2*q.ones + q.mixed) = traitSpare D true ∧
      q.d0 - (2*q.zeros + q.mixed) = traitSpare D false ∧
      ((w2Finish q).1 : ℝ) = hLower D ∧ ((w2Finish q).2 : ℝ) = hUpper D ∧
      q.visits = D.sampled.card + (recruitmentEdges D).card ∧
      q.additions = D.sampled.card + (recruitmentEdges D).card)

end
end SAP.P012a
