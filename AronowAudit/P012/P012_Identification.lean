import Mathlib.Tactic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
P012: finite graph model of Definitions 1--4 and related statements.
Source: American Journal of Epidemiology 187(1), 153--160, and its Web Appendix.
Vertices have two disjoint namespaces. `s i` names observed subject i when
i belongs to the observed sample; `u i k` is an unobserved vertex. Unused `s`
names are also unobserved. Actual sample membership, never the namespace alone,
determines whether a neighbour has entered the study.
Times are distinct natural-number ranks: every expression in the paper uses only
their order, so this represents arbitrary distinct recruitment times.
The public functionals are partial (`Option ℝ`); the total quotient expressions
are used only with their domain predicates or to exhibit a zero denominator.
-/

namespace AronowAudit.P012

open Finset
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option linter.unusedVariables false

/-- "Members ... are vertices" (p. 154); observed and unobserved names are disjoint.
Every finite augmented graph can be named in this countable universe. -/
abbrev Vertex := ℕ ⊕ (ℕ × ℕ)

def s (i : ℕ) : Vertex := Sum.inl i
def u (i k : ℕ) : Vertex := Sum.inr (i, k)

/-- Equality of unordered two-endpoint edge sets in the simple graph model
(p. 154); used only to normalize explicit finite examples. -/
@[simp] theorem pair_edge_eq (v w x y : Vertex) :
    ({v,w} : Finset Vertex) = {x,y} ↔ (v=x ∧ w=y) ∨ (v=y ∧ w=x) := by
  constructor
  · intro h
    have hv : v ∈ ({x,y} : Finset Vertex) := by rw [← h]; simp
    have hw : w ∈ ({x,y} : Finset Vertex) := by rw [← h]; simp
    have hx : x ∈ ({v,w} : Finset Vertex) := by rw [h]; simp
    have hy : y ∈ ({v,w} : Finset Vertex) := by rw [h]; simp
    simp only [mem_insert,mem_singleton] at hv hw hx hy
    grind
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp [Finset.pair_comm]

attribute [local simp] Finset.filter_insert Finset.image_insert Finset.sdiff_insert
  Finset.insert_sdiff_of_mem Finset.insert_sdiff_of_notMem Finset.insert_subset_iff
  Finset.filter_singleton Finset.image_singleton Finset.sdiff_singleton_eq_erase
  Finset.erase_insert_of_ne


/-- "The directed recruitment graph ... degrees and times ... set of seeds ...
binary trait values" (p. 155). `parent j` records the sole recruiter of a nonseed.
Its value at a seed is ignored. `time` records recruitment-time order. -/
structure Data where
  sampled : Finset ℕ
  seeds : Finset ℕ
  parent : ℕ → ℕ
  time : ℕ → ℕ
  degree : ℕ → ℕ
  trait : ℕ → Bool

/-- "V_SU = V_S ∪ U ... E_SU = E_S ∪ E_U" (p. 155).
Raw states also admit malformed proposals, so incompatibility can be expressed.
Edges are stored as finite vertex sets; `Simple` requires exactly two distinct
endpoints. The outer finite set prevents parallel copies. -/
structure State where
  vertices : Finset Vertex
  edges : Finset (Finset Vertex)
  trait : Vertex → Bool

/-- "n - |M|" nonseed recruitment events (Definition 2, p. 155). -/
def nonseeds (D : Data) : Finset ℕ := D.sampled \ D.seeds
def sampledVertices (D : Data) : Finset Vertex := D.sampled.image s

/-- The undirected skeleton of G_R (p. 155 and Appendix p. 160). -/
def recruitmentEdges (D : Data) : Finset (Finset Vertex) :=
  (nonseeds D).image (fun j => {s (D.parent j), s j})

/-- "d_i ... number of edges incident to i" (p. 155). On a simple graph this
is exactly the number of adjacent vertices, not the number of edge orientations. -/
def graphDegree (H : State) (v : Vertex) : ℕ :=
  (H.edges.filter (fun e => v ∈ e)).card

def recruitmentDegree (D : Data) (i : ℕ) : ℕ :=
  ((recruitmentEdges D).filter (fun e => s i ∈ e)).card

/-- "s_i = d_i - d_i^r" (corrections T3--T7); subtraction is natural, with
admissibility ensuring the minuend is at least the subtrahend. -/
def spare (D : Data) (i : ℕ) : ℕ := D.degree i - recruitmentDegree D i
def totalSpare (D : Data) : ℕ := ∑ i ∈ D.sampled, spare D i
def traitSpare (D : Data) (z : Bool) : ℕ :=
  ∑ i ∈ D.sampled.filter (fun i => D.trait i = z), spare D i
def sampledTraitDegree (D : Data) (z : Bool) : ℕ :=
  ∑ i ∈ D.sampled.filter (fun i => D.trait i = z), D.degree i

/-- Standing assumptions: distinct entry times; exactly one earlier recruiter
for each nonseed; seeds have no recruiter; d_i ≥ d_i^r (pp. 154--155). -/
abbrev Admissible (D : Data) : Prop :=
  D.seeds ⊆ D.sampled ∧
  (∀ i ∈ D.sampled, ∀ j ∈ D.sampled, D.time i = D.time j → i = j) ∧
  (∀ j ∈ nonseeds D, D.parent j ∈ D.sampled ∧ D.time (D.parent j) < D.time j) ∧
  (∀ i ∈ D.sampled, recruitmentDegree D i ≤ D.degree i)

/-- "Undirected ... no parallel edges or self-loops" (p. 154); the edges have
exactly two distinct endpoints, both in the displayed vertex set. -/
abbrev Simple (H : State) : Prop :=
  ∀ e ∈ H.edges, e.card = 2 ∧ e ⊆ H.vertices

/-- "G_SU does not contain edges between vertices in U" (p. 155). -/
abbrev Augmented (D : Data) (H : State) : Prop :=
  Simple H ∧ ∀ e ∈ H.edges, ∃ i ∈ D.sampled, s i ∈ e

/-- Definition 3 (p. 155): recruitment graph, sampled traits, an observed
neighbour for every unobserved vertex, and exact observed degrees are preserved.
The standing definition of an augmented subgraph is also imposed. -/
abbrev Compatible (D : Data) (H : State) : Prop :=
  Augmented D H ∧ sampledVertices D ⊆ H.vertices ∧
  recruitmentEdges D ⊆ H.edges ∧
  (∀ i ∈ D.sampled, H.trait (s i) = D.trait i) ∧
  (∀ v ∈ H.vertices, v ∉ sampledVertices D →
    ∃ i ∈ D.sampled, {s i, v} ∈ H.edges) ∧
  (∀ i ∈ D.sampled, graphDegree H (s i) = D.degree i)

/-- A_ij, the adjacency matrix in Definition 1, equation (1), p. 155. -/
def adjacency (H : State) (v w : Vertex) : ℝ :=
  if v ≠ w ∧ {v, w} ∈ H.edges then 1 else 0

/-- Binary attribute Z_i in Definitions 1--2, p. 155. -/
def z (H : State) (v : Vertex) : ℝ := if H.trait v then 1 else 0

/-- Numerator of (1), with the sum over ordered pairs and null term d_i d_j/(2m). -/
def hNumerator (H : State) : ℝ :=
  ∑ v ∈ H.vertices, ∑ w ∈ H.vertices,
    (adjacency H v w - (graphDegree H v : ℝ) * graphDegree H w /
      (2 * (H.edges.card : ℝ))) * z H v * z H w

/-- Denominator of (1), with δ_ij = 1 exactly when i = j (p. 155). -/
def hDenominator (H : State) : ℝ :=
  ∑ v ∈ H.vertices, ∑ w ∈ H.vertices,
    ((if v = w then (graphDegree H v : ℝ) else 0) -
      (graphDegree H v : ℝ) * graphDegree H w / (2 * (H.edges.card : ℝ))) *
      z H v * z H w

def hValue (H : State) : ℝ := hNumerator H / hDenominator H

/-- Correction T15(a): equation (1) has a value only with m > 0 and a
nonzero correlation denominator. No value is assigned to 0/0. -/
abbrev HomophilyDefined (H : State) : Prop := 0 < H.edges.card ∧ hDenominator H ≠ 0

/-- "Homophily is the correlation between trait values ... connected by an
edge" (Definition 1, p. 155, (1)), on its ordinary domain (correction T15). -/
noncomputable def homophily (H : State) : Option ℝ :=
  if HomophilyDefined H then some (hValue H) else none

/-- "S_i(t) ... susceptible neighbors ... just before time t" (p. 155).
Unobserved neighbours remain susceptible; observed neighbours enter at their
entry time, so equality with the present time is included (left continuity). -/
@[simp] def notYetSampled (D : Data) (j : ℕ) (v : Vertex) : Bool :=
  match v with
  | Sum.inl k => decide (k ∉ D.sampled ∨ D.time j ≤ D.time k)
  | Sum.inr _ => true

/-- S_i(t_j), the susceptible-neighbour set just before entry j, including j
itself when i recruited j (Definition 2, p. 155). -/
def susceptible (D : Data) (H : State) (i j : ℕ) : Finset Vertex :=
  H.vertices.filter (fun v => {s i,v} ∈ H.edges ∧ notYetSampled D j v = true)

def sameSusceptible (D : Data) (H : State) (i j : ℕ) : Finset Vertex :=
  (susceptible D H i j).filter (fun v => H.trait v = H.trait (s i))

/-- The full sum in equation (2), Definition 2, p. 155. -/
def pSum (D : Data) (H : State) : ℝ :=
  ∑ j ∈ nonseeds D,
    ((if H.trait (s j) = H.trait (s (D.parent j)) then (1 : ℝ) else 0) -
      (sameSusceptible D H (D.parent j) j).card /
      ((susceptible D H (D.parent j) j).card : ℝ))

def pValue (D : Data) (H : State) : ℝ := pSum D H / (nonseeds D).card

/-- Correction T15(b): (2) is a nonempty average with positive susceptible
set denominators. Admissibility and compatibility guarantee the latter. -/
abbrev PreferentialDefined (D : Data) (H : State) : Prop :=
  0 < (nonseeds D).card ∧
  ∀ j ∈ nonseeds D, 0 < (susceptible D H (D.parent j) j).card

/-- "Preferential recruitment is the average deviation from proportional
recruitment" (Definition 2, p. 155, (2)), with the domain correction T15. -/
noncomputable def preferential (D : Data) (H : State) : Option ℝ :=
  if PreferentialDefined D H then some (pValue D H) else none

/-- Degree totals D_z (correction T15(a)); unlike sampledTraitDegree, all
vertices of the augmented graph contribute. -/
def traitDegree (H : State) (b : Bool) : ℕ :=
  ∑ v ∈ H.vertices.filter (fun v => H.trait v = b), graphDegree H v

/-- Counts x=e_11, y=e_00, c=e_01 (corrections T3--T6). -/
def edgeCount (H : State) (b : Bool) : ℕ :=
  (H.edges.filter (fun e => ∀ v ∈ e, H.trait v = b)).card
def mixedCount (H : State) : ℕ :=
  (H.edges.filter (fun e => (∃ v ∈ e, H.trait v = true) ∧
    (∃ v ∈ e, H.trait v = false))).card

def recruitmentState (D : Data) : State :=
  ⟨sampledVertices D, recruitmentEdges D,
    fun v => match v with | Sum.inl i => D.trait i | Sum.inr _ => false⟩
def a (D : Data) : ℕ := edgeCount (recruitmentState D) true
def b (D : Data) : ℕ := edgeCount (recruitmentState D) false
def cR (D : Data) : ℕ := mixedCount (recruitmentState D)

/-- φ(x,y,c) in corrections T5--T6: the two-stub-total expression for (1).
The fraction form is proved below with its nonzero-denominator hypotheses. -/
def phi (x y c : ℝ) : ℝ := 1 - c / (2*x+c) - c / (2*y+c)
def hLower (D : Data) : ℝ := phi (a D) (b D) (cR D + totalSpare D)
def hUpper (D : Data) : ℝ :=
  phi (a D + traitSpare D true) (b D + traitSpare D false) (cR D)

/-- B_j, the recruiter's children entering at or after j (correction T7).
Seeds are excluded even if the ignored value of parent at a seed coincides. -/
def laterChildren (D : Data) (j : ℕ) : Finset ℕ :=
  (nonseeds D).filter (fun k => D.parent k = D.parent j ∧ D.time j ≤ D.time k)
def childMatches (D : Data) (j : ℕ) : ℕ :=
  ((laterChildren D j).filter (fun k => D.trait k = D.trait (D.parent j))).card
def observedMatch (D : Data) (j : ℕ) : ℝ :=
  if D.trait j = D.trait (D.parent j) then 1 else 0

/-- Closed-form lower and upper p endpoints, correction T7(iii), equation (2). -/
def pLower (D : Data) : ℝ :=
  (∑ j ∈ nonseeds D, (observedMatch D j -
    ((childMatches D j : ℝ) + spare D (D.parent j)) /
    (((laterChildren D j).card : ℝ) + spare D (D.parent j)))) / (nonseeds D).card
def pUpper (D : Data) : ℝ :=
  (∑ j ∈ nonseeds D, (observedMatch D j - (childMatches D j : ℝ) /
    (((laterChildren D j).card : ℝ) + spare D (D.parent j)))) / (nonseeds D).card

/-- "Identification regions ... smallest intervals" (Definition 4, p. 155).
Endpoint least/greatest properties express the smallest closed interval; the
full-region predicates additionally require definedness on every compatible pair. -/
def hValues (D : Data) : Set ℝ := {r | ∃ H, Compatible D H ∧ homophily H = some r}
def pValues (D : Data) : Set ℝ := {r | ∃ H, Compatible D H ∧ preferential D H = some r}
def FullHomophilyRegion (D : Data) (L U : ℝ) : Prop :=
  (∀ H, Compatible D H → HomophilyDefined H) ∧
  IsLeast (hValues D) L ∧ IsGreatest (hValues D) U
def FullPreferentialRegion (D : Data) (L U : ℝ) : Prop :=
  (∀ H, Compatible D H → PreferentialDefined D H) ∧
  IsLeast (pValues D) L ∧ IsGreatest (pValues D) U

/-- "Contains only a single point ... point identified" (Definition 4, p. 155).
Existence prevents an empty, undefined value set from counting as identification. -/
def PointIdentified (values : Set ℝ) : Prop := ∃ r, values = {r}

/-- The private degree-one vertices in corrections T3, T5--T7, T10--T13.
`u i k` here is a fresh vertex owned by observed i, for 0 ≤ k < s_i. -/
def leafVertices (D : Data) : Finset Vertex :=
  D.sampled.biUnion (fun i => (range (spare D i)).image (u i))
def leafEdges (D : Data) : Finset (Finset Vertex) :=
  D.sampled.biUnion (fun i => (range (spare D i)).image (fun k => {s i, u i k}))

/-- The common sharp-endpoint completion (corrections T3, T5--T7): retain
exactly the recruitment edges and attach s_i private leaves to each observed i.
`same=true` gives the leaf its owner's trait; false gives the opposite trait. -/
def leafCompletion (D : Data) (same : Bool) : State :=
  ⟨sampledVertices D ∪ leafVertices D, recruitmentEdges D ∪ leafEdges D,
    fun v => match v with
      | Sum.inl i => D.trait i
      | Sum.inr (i, _) => if same then D.trait i else !(D.trait i)⟩

/-- Removing U and its incident edges gives G_S (p. 155; Appendix p. 160). -/
def induced (D : Data) (H : State) : State :=
  ⟨sampledVertices D, H.edges.filter (fun e => e ⊆ sampledVertices D), H.trait⟩

/-- Compatibility for G_S at the opening of the Result 1 proof (p. 160):
preserve recruitment edges and bound, rather than equal, observed degrees. -/
def InducedCompatible (D : Data) (H : State) : Prop :=
  Simple H ∧ H.vertices = sampledVertices D ∧ recruitmentEdges D ⊆ H.edges ∧
  ∀ i ∈ D.sampled, graphDegree H (s i) ≤ D.degree i

def removeEdge (H : State) (v w : Vertex) : State :=
  {H with edges := H.edges.erase {v, w}}
def addEdge (H : State) (v w : Vertex) : State :=
  {H with edges := insert {v, w} H.edges}
def addVertex (H : State) (v : Vertex) (t : Bool) : State :=
  {H with vertices := insert v H.vertices, trait := Function.update H.trait v t}
def flipTrait (H : State) (v : Vertex) : State :=
  {H with trait := Function.update H.trait v (!H.trait v)}

/-- U and U_-k from Web Appendix 2, pp. 2--3: pools refer to the current,
unstarred graph, including during the second replacement. -/
def unsampled (D : Data) (H : State) : Finset Vertex := H.vertices \ sampledVertices D
def replacementPool (D : Data) (H : State) (i : ℕ) : Finset Vertex :=
  (unsampled D H).filter (fun v => {s i, v} ∉ H.edges)

/-- Line 27 (Web Appendix p. 3): printed cleanup removes all isolated vertices;
corrected cleanup preserves sampled vertices, including zero-degree seeds. -/
def cleanup (D : Data) (repaired : Bool) (H : State) : State :=
  {H with vertices := H.vertices.filter (fun v =>
    (repaired = true ∧ v ∈ sampledVertices D) ∨ graphDegree H v ≠ 0)}

/-- Lines 5--12 or 14--20: any existing nonneighbour or a fresh vertex with
either binary trait can be chosen. This relation marginalizes the Bernoulli
choice: each existing choice is possible with B=0, each fresh choice with B=1.
There is no compatibility test in the execution relation. -/
inductive Replacement (D : Data) (current pendingState : State) (i : ℕ) : Vertex → State → Prop
  | existing (v : Vertex) (hv : v ∈ replacementPool D current i) :
      Replacement D current pendingState i v pendingState
  | fresh (v : Vertex) (hv : v ∉ pendingState.vertices) (t : Bool) :
      Replacement D current pendingState i v (addVertex pendingState v t)

/-- All graph-mechanism executions (Web Appendix 2, lines 1--27), read as
imperative code. `repaired=false` executes line 22 also for unobserved j;
`repaired=true` moves it inside the sampled-j branch and guards cleanup. -/
inductive GraphProposal (D : Data) (repaired : Bool) (H : State) : State → Prop
  | deleteUnobserved (i : ℕ) (j v : Vertex) (P : State)
      (hi : i ∈ D.sampled) (hj : j ∈ H.vertices) (hne : s i ≠ j)
      (he : {s i, j} ∈ H.edges) (hr : {s i, j} ∉ recruitmentEdges D)
      (hju : j ∉ sampledVertices D)
      (hp : Replacement D H (removeEdge H (s i) j) i v P) :
      GraphProposal D repaired H
        (cleanup D repaired (if repaired then addEdge P (s i) v
          else addEdge (addEdge P (s i) v) j v))
  | deleteObserved (i j : ℕ) (v w : Vertex) (P Q : State)
      (hi : i ∈ D.sampled) (hj : j ∈ D.sampled) (hne : i ≠ j)
      (he : {s i, s j} ∈ H.edges) (hr : {s i, s j} ∉ recruitmentEdges D)
      (hp : Replacement D H (removeEdge H (s i) (s j)) i v P)
      (hq : Replacement D H (addEdge P (s i) v) j w Q) :
      GraphProposal D repaired H (cleanup D repaired (addEdge Q (s j) w))
  | addObserved (i : ℕ) (j v w : Vertex)
      (hi : i ∈ D.sampled) (hj : j ∈ H.vertices) (hne : s i ≠ j)
      (he : {s i, j} ∉ H.edges)
      (hv : v ∈ unsampled D H) (hw : w ∈ unsampled D H)
      (hiv : {s i, v} ∈ H.edges) (hjw : {j, w} ∈ H.edges) :
      GraphProposal D repaired H (cleanup D repaired
        (addEdge (removeEdge (removeEdge H (s i) v) j w) (s i) j))
  | unchanged (i : ℕ) (j : Vertex)
      (hi : i ∈ D.sampled) (hj : j ∈ H.vertices) (hne : s i ≠ j)
      (hdel : ¬ ({s i, j} ∈ H.edges ∧ {s i, j} ∉ recruitmentEdges D))
      (hadd : ¬ ({s i, j} ∉ H.edges ∧ ∃ v ∈ unsampled D H,
        ∃ w ∈ unsampled D H, {s i, v} ∈ H.edges ∧ {j, w} ∈ H.edges)) :
      GraphProposal D repaired H (cleanup D repaired H)

/-- Second proposal, Web Appendix p. 3: flip one unsampled trait.
The corrected mechanism also returns the input when its pool is empty. -/
inductive TraitProposal (D : Data) (repaired : Bool) (H : State) : State → Prop
  | flip (v : Vertex) (hv : v ∈ unsampled D H) : TraitProposal D repaired H (flipTrait H v)
  | empty (hr : repaired = true) (hu : unsampled D H = ∅) : TraitProposal D repaired H H

def Proposal (D : Data) (repaired : Bool) (H K : State) : Prop :=
  GraphProposal D repaired H K ∨ TraitProposal D repaired H K

/-- The graph-only compatibility in the opening of the Result 1 proof (p. 160):
conditions 1, 3 and 4 of Definition 3, with the augmented-graph standing rules.
Traits play no role in this object. -/
abbrev GraphCompatible (D : Data) (H : State) : Prop :=
  Augmented D H ∧ sampledVertices D ⊆ H.vertices ∧
  recruitmentEdges D ⊆ H.edges ∧
  (∀ v ∈ H.vertices, v ∉ sampledVertices D →
    ∃ i ∈ D.sampled, {s i,v} ∈ H.edges) ∧
  (∀ i ∈ D.sampled, graphDegree H (s i) = D.degree i)

/-- T3, T5--T7, T10--T13, supporting construction: private leaves satisfy all
four compatibility clauses, for either endpoint trait assignment. This proves
existence of compatible states without assuming existence as a new hypothesis. -/
theorem leafCompletion_compatible (D : Data) (hD : Admissible D) (same : Bool) :
    Compatible D (leafCompletion D same) := by
  have hr : ∀ e ∈ recruitmentEdges D, e.card = 2 ∧ e ⊆ sampledVertices D := by
    intro e he
    obtain ⟨j,hj,rfl⟩ := mem_image.mp he
    have hjS : j ∈ D.sampled := (mem_sdiff.mp hj).1
    have hp := hD.2.2.1 j hj
    have hne : s (D.parent j) ≠ s j := by
      intro hh
      have heq : D.parent j = j := Sum.inl.inj hh
      rw [heq] at hp
      exact (lt_irrefl _ hp.2)
    constructor
    · simp [hne]
    · intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact mem_image_of_mem s hp.1
      · exact mem_image_of_mem s hjS
  have hE : ∀ e ∈ leafEdges D, ∃ i ∈ D.sampled, ∃ k ∈ range (spare D i),
      e = {s i,u i k} := by
    intro e he
    obtain ⟨i,hi,hie⟩ := mem_biUnion.mp he
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hie
    exact ⟨i,hi,k,hk,rfl⟩
  have hf : ∀ i ∈ D.sampled,
      (leafEdges D).filter (fun e => s i ∈ e) =
        (range (spare D i)).image (fun k => {s i,u i k}) := by
    intro i hi
    ext e
    constructor
    · intro he
      obtain ⟨he,hie⟩ := mem_filter.mp he
      obtain ⟨j,hj,k,hk,rfl⟩ := hE e he
      have hji : i = j := by simpa [s,u] using hie
      subst j
      exact mem_image.mpr ⟨k,hk,rfl⟩
    · intro he
      obtain ⟨k,hk,rfl⟩ := mem_image.mp he
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i,hi,mem_image.mpr ⟨k,hk,rfl⟩⟩,
        by simp⟩
  have hd : ∀ i ∈ D.sampled, graphDegree (leafCompletion D same) (s i) = D.degree i := by
    intro i hi
    have hdis : Disjoint ((recruitmentEdges D).filter (fun e => s i ∈ e))
        ((range (spare D i)).image (fun k => {s i,u i k})) := by
      apply disjoint_left.mpr
      intro e he hl
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hl
      have hsub := (hr _ (mem_filter.mp he).1).2
      have hu : u i k ∈ sampledVertices D := hsub (by simp)
      simpa [sampledVertices,s,u] using hu
    have hinj : Function.Injective (fun k : ℕ => ({s i,u i k} : Finset Vertex)) := by
      intro k l heq
      change ({s i,u i k} : Finset Vertex) = {s i,u i l} at heq
      have hmem : u i k ∈ ({s i,u i l} : Finset Vertex) := by rw [← heq]; simp
      simpa [s,u] using hmem
    change ((recruitmentEdges D ∪ leafEdges D).filter (fun e => s i ∈ e)).card = _
    rw [filter_union,hf i hi,card_union_of_disjoint hdis,card_image_of_injective _ hinj,
      card_range]
    exact Nat.add_sub_of_le (hD.2.2.2 i hi)
  refine ⟨⟨?_,?_⟩, ?_, ?_, ?_, ?_, hd⟩
  · intro e he
    rcases mem_union.mp he with hrE | hlE
    · obtain ⟨hcard,hsub⟩ := hr e hrE
      exact ⟨hcard,Subset.trans hsub subset_union_left⟩
    · obtain ⟨i,hi,k,hk,rfl⟩ := hE e hlE
      refine ⟨by simp [s,u], ?_⟩
      intro v hv
      simp only [mem_insert,mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact mem_union_left _ (mem_image_of_mem s hi)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨i,hi,mem_image.mpr ⟨k,hk,rfl⟩⟩)
  · intro e he
    rcases mem_union.mp he with hrE | hlE
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hrE
      exact ⟨j,(mem_sdiff.mp hj).1,by simp⟩
    · obtain ⟨i,hi,k,hk,rfl⟩ := hE e hlE
      exact ⟨i,hi,by simp⟩
  · exact subset_union_left
  · exact subset_union_left
  · intro i hi
    rfl
  · intro v hv hnot
    have hvL : v ∈ leafVertices D := (mem_union.mp hv).resolve_left hnot
    obtain ⟨i,hi,hiv⟩ := mem_biUnion.mp hvL
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hiv
    exact ⟨i,hi,mem_union_right _ (mem_biUnion.mpr ⟨i,hi,mem_image.mpr ⟨k,hk,rfl⟩⟩)⟩

/-- T15(b), finite domain lemma: a nonseed is in its recruiter's susceptible
set immediately before entry, at every compatible state. Hence every inner
denominator in equation (2) is positive. Definition 2, p. 155. -/
theorem recruit_is_susceptible (D : Data) (H : State) (hH : Compatible D H)
    (j : ℕ) (hj : j ∈ nonseeds D) :
    s j ∈ susceptible D H (D.parent j) j ∧
      0 < (susceptible D H (D.parent j) j).card := by
  have hmem : s j ∈ susceptible D H (D.parent j) j := by
    change s j ∈ H.vertices.filter (fun v => {s (D.parent j),v} ∈ H.edges ∧ notYetSampled D j v = true)
    refine mem_filter.mpr ⟨hH.2.1 (mem_image_of_mem s (mem_sdiff.mp hj).1), ?_⟩
    refine ⟨hH.2.2.1 (mem_image_of_mem _ hj), ?_⟩
    simp [notYetSampled,s]
  exact ⟨hmem,card_pos.mpr ⟨s j,hmem⟩⟩

/-- T2, trait-mechanism part: the corrected unsampled flip and empty-pool no-op
preserve compatibility for every graph, not just the counterexamples. -/
theorem corrected_trait_preserves (D : Data) (H K : State)
    (hH : Compatible D H) (hP : TraitProposal D true H K) : Compatible D K := by
  cases hP with
  | empty _ _ => exact hH
  | flip v hv =>
    refine ⟨hH.1,hH.2.1,hH.2.2.1,?_,hH.2.2.2.2.1,hH.2.2.2.2.2⟩
    intro i hi
    have hneq : s i ≠ v := by
      intro heq
      have hs : v ∈ sampledVertices D := heq ▸ mem_image_of_mem s hi
      exact (mem_sdiff.mp hv).2 hs
    simpa [flipTrait,Function.update_of_ne hneq] using hH.2.2.2.1 i hi

/- Concrete observed data. Unobserved label 3 in a displayed example is u 3 0. -/
/-- Example T1(a): "V_R={1,2}, M={1}, E_R={(1,2)}, d_R=(2,1), Z_R=(0,1)"; entry order is 1,2. Counterexample to Web Appendix 2, pp. 2-3. -/
def proposalData : Data :=
  ⟨{1,2}, {1}, fun _ => 1, id, fun i => if i = 1 then 2 else 1,
    fun i => i == 2⟩
/-- Example T1(a): "V_SU={1,2,3}, E_SU={{1,2},{1,3}}, Z_3=0". Unsampled vertex 3 is named u 3 0; Web Appendix 2 counterexample. -/
def proposalStart : State :=
  ⟨{s 1,s 2,u 3 0}, {{s 1,s 2},{s 1,u 3 0}}, fun v => decide (v = s 2)⟩
/-- The literal T1(a) output: delete {1,3}, invent vertex 4 with trait t, add {1,4} and {3,4}, then apply printed cleanup. Web Appendix 2, lines 4-27. -/
def proposalBad (t : Bool) : State :=
  cleanup proposalData false (addEdge
    (addEdge (addVertex (removeEdge proposalStart (s 1) (u 3 0)) (u 4 0) t)
      (s 1) (u 4 0)) (u 3 0) (u 4 0))

/-- T1(a), Web Appendix 2: a fully specified execution from a compatible graph
has a forbidden unsampled--unsampled edge and an unsampled vertex without a
sampled neighbour, for either new trait. All paper hypotheses are satisfied. -/
theorem proposal_counterexample :
    Admissible proposalData ∧ Compatible proposalData proposalStart ∧
    replacementPool proposalData proposalStart 1 = ∅ ∧
    (∀ t : Bool, Proposal proposalData false proposalStart (proposalBad t) ∧
      ¬ Compatible proposalData (proposalBad t)) ∧
    homophily proposalStart = some (-1/3) ∧
    preferential proposalData proposalStart = some (-1/2) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩
  · intro t
    constructor
    · left
      exact GraphProposal.deleteUnobserved 1 (u 3 0) (u 4 0)
        (addVertex (removeEdge proposalStart (s 1) (u 3 0)) (u 4 0) t)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (Replacement.fresh (u 4 0) (by decide) t)
    · cases t <;> decide
  · norm_num [homophily, HomophilyDefined, hValue, hNumerator, hDenominator,
      graphDegree, adjacency, z, proposalStart, s, u]
  · norm_num [preferential, PreferentialDefined, pValue, pSum, susceptible,
      sameSusceptible, nonseeds, proposalData, proposalStart, s, u]

/-- Transient graph-update invariant: the augmented-graph rules and the
preserved recruitment graph, sampled vertices and traits (Definition 3,
p. 155). Isolated unsampled vertices and temporary degree deficits are allowed
until the corrected mechanism finishes its replacements and cleanup. -/
abbrev ProposalBase (D : Data) (H : State) : Prop :=
  Augmented D H ∧ sampledVertices D ⊆ H.vertices ∧
    recruitmentEdges D ⊆ H.edges ∧ ∀ i ∈ D.sampled, H.trait (s i) = D.trait i

/-- T2 finite incidence identity: deleting a present edge subtracts exactly
one degree unit at each of its endpoints. Web Appendix 2, line 4 or 24. -/
theorem degree_remove_step (H : State) (v w x : Vertex) (he : {v,w} ∈ H.edges) :
    graphDegree (removeEdge H v w) x + (if x ∈ ({v,w} : Finset Vertex) then 1 else 0) =
      graphDegree H x := by
  change ((H.edges.erase {v,w}).filter (fun e => x ∈ e)).card + _ = _
  rw [filter_erase]
  by_cases hx : x ∈ ({v,w} : Finset Vertex)
  · simp only [if_pos hx]
    exact card_erase_add_one (mem_filter.mpr ⟨he,hx⟩)
  · simp only [if_neg hx,Nat.add_zero]
    rw [erase_eq_of_notMem (by simp [hx])]
    rfl

/-- T2 finite incidence identity: adding an absent edge adds exactly one
degree unit at each endpoint. Web Appendix 2, lines 12, 22 or 25. -/
theorem degree_add_step (H : State) (v w x : Vertex) (he : {v,w} ∉ H.edges) :
    graphDegree (addEdge H v w) x = graphDegree H x +
      (if x ∈ ({v,w} : Finset Vertex) then 1 else 0) := by
  change ((insert {v,w} H.edges).filter (fun e => x ∈ e)).card = _
  rw [filter_insert]
  by_cases hx : x ∈ ({v,w} : Finset Vertex)
  · simp only [if_pos hx]
    exact card_insert_of_notMem (fun h => he (mem_filter.mp h).1)
  · simp only [if_neg hx,Nat.add_zero]
    rfl

/-- T2: removing an edge outside G_R preserves the recruitment graph,
sampled vertices and traits, and every remaining augmented edge. Line 4. -/
theorem remove_edge_base (D : Data) (H : State) (v w : Vertex)
    (hB : ProposalBase D H) (hr : {v,w} ∉ recruitmentEdges D) :
    ProposalBase D (removeEdge H v w) := by
  refine ⟨⟨?_,?_⟩,hB.2.1,?_,hB.2.2.2⟩
  · intro e he
    exact hB.1.1 e (mem_erase.mp he).2
  · intro e he
    exact hB.1.2 e (mem_erase.mp he).2
  · intro e he
    exact mem_erase.mpr ⟨(fun h => hr (h ▸ he)),hB.2.2.1 he⟩

/-- T2: a new simple edge with a sampled endpoint preserves the graph and
trait clauses not involving degrees or isolated unsampled vertices. Line 12. -/
theorem add_edge_base (D : Data) (H : State) (i : ℕ) (v : Vertex)
    (hB : ProposalBase D H) (hi : i ∈ D.sampled) (hv : v ∈ H.vertices)
    (hne : s i ≠ v) : ProposalBase D (addEdge H (s i) v) := by
  refine ⟨⟨?_,?_⟩,hB.2.1,?_,hB.2.2.2⟩
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · refine ⟨by simp [hne],?_⟩
      intro w hw
      rcases mem_insert.mp hw with rfl | hw
      · exact hB.2.1 (mem_image_of_mem s hi)
      · exact mem_singleton.mp hw ▸ hv
    · exact hB.1.1 e he
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact ⟨i,hi,by simp⟩
    · exact hB.1.2 e he
  · exact Subset.trans hB.2.2.1 (subset_insert _ _)

/-- T2: invention of a fresh unsampled vertex with either binary trait keeps
all sampled traits and the old edge set. Web Appendix 2, lines 9--10. -/
theorem add_vertex_base (D : Data) (H : State) (v : Vertex) (t : Bool)
    (hB : ProposalBase D H) (hv : v ∉ H.vertices) :
    ProposalBase D (addVertex H v t) := by
  refine ⟨⟨?_,hB.1.2⟩,?_,hB.2.2.1,?_⟩
  · intro e he
    exact ⟨(hB.1.1 e he).1,Subset.trans (hB.1.1 e he).2 (subset_insert _ _)⟩
  · exact Subset.trans hB.2.1 (subset_insert _ _)
  · intro i hi
    have hne : s i ≠ v := by
      intro h
      exact hv (h ▸ hB.2.1 (mem_image_of_mem s hi))
    simpa [addVertex,Function.update_of_ne hne] using hB.2.2.2 i hi

/-- T2: every possible existing or fresh replacement is unsampled, present
after invention, and still a nonneighbour of the designated sampled endpoint.
Its invention does not alter any degree. Web Appendix 2, lines 5--11,14--20. -/
theorem replacement_properties (D : Data) (H L P : State) (i : ℕ) (v : Vertex)
    (hH : Compatible D H) (hL : ProposalBase D L)
    (hverts : H.vertices ⊆ L.vertices)
    (hpool : ∀ w ∈ replacementPool D H i, {s i,w} ∉ L.edges)
    (hP : Replacement D H L i v P) :
    ProposalBase D P ∧ L.vertices ⊆ P.vertices ∧ v ∈ P.vertices ∧
      v ∉ sampledVertices D ∧ P.edges = L.edges ∧ {s i,v} ∉ P.edges := by
  cases hP with
  | existing hv =>
    obtain ⟨hv,hnot⟩ := mem_filter.mp hv
    obtain ⟨hvH,hvS⟩ := mem_sdiff.mp hv
    exact ⟨hL,Subset.refl _,hverts hvH,hvS,rfl,hpool v (mem_filter.mpr ⟨hv,hnot⟩)⟩
  | fresh hv t =>
    have hvS : v ∉ sampledVertices D := fun h => hv (hL.2.1 h)
    refine ⟨add_vertex_base D L v t hL hv,subset_insert _ _,by simp [addVertex],hvS,rfl,?_⟩
    intro he
    exact hv ((hL.1.1 {s i,v} he).2 (by simp))

/-- T2(v): corrected cleanup deletes only isolated unsampled vertices.
An edge's endpoints have positive degree, so no edge or degree changes.
Every surviving unsampled vertex has a sampled neighbour. Line 27. -/
theorem cleanup_compatible (D : Data) (H : State) (hB : ProposalBase D H)
    (hd : ∀ i ∈ D.sampled, graphDegree H (s i) = D.degree i) :
    Compatible D (cleanup D true H) := by
  have hpos : ∀ e ∈ H.edges, ∀ v ∈ e, graphDegree H v ≠ 0 := by
    intro e he v hv
    exact Nat.ne_of_gt (card_pos.mpr ⟨e,mem_filter.mpr ⟨he,hv⟩⟩)
  refine ⟨⟨?_,hB.1.2⟩,?_,hB.2.2.1,hB.2.2.2,?_,hd⟩
  · intro e he
    refine ⟨(hB.1.1 e he).1,?_⟩
    intro v hv
    exact mem_filter.mpr ⟨(hB.1.1 e he).2 hv,Or.inr (hpos e he v hv)⟩
  · intro v hv
    exact mem_filter.mpr ⟨hB.2.1 hv,Or.inl ⟨rfl,hv⟩⟩
  · intro v hv hvS
    have hvD : graphDegree H v ≠ 0 :=
      (mem_filter.mp hv).2.resolve_left (fun h => hvS h.2)
    obtain ⟨e,he⟩ := card_pos.mp (Nat.pos_of_ne_zero hvD)
    obtain ⟨he,hve⟩ := mem_filter.mp he
    obtain ⟨i,hi,hie⟩ := hB.1.2 e he
    have hne : s i ≠ v := fun h => hvS (h ▸ mem_image_of_mem s hi)
    have hpair : ({s i,v} : Finset Vertex) = e := eq_of_subset_of_card_le
      (by intro w hw; rcases mem_insert.mp hw with rfl | hw
          · exact hie
          · exact mem_singleton.mp hw ▸ hve)
      (by simp [(hB.1.1 e he).1,hne])
    exact ⟨i,hi,hpair ▸ he⟩

/-- T2(iii): every recruitment edge has only sampled endpoints, so an edge
with an unsampled endpoint can never be a recruitment edge. Definition 3. -/
theorem recruitment_edge_sampled (D : Data) (hD : Admissible D)
    (e : Finset Vertex) (he : e ∈ recruitmentEdges D) : e ⊆ sampledVertices D := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp he
  intro v hv
  rcases mem_insert.mp hv with rfl | hv
  · exact mem_image_of_mem s (hD.2.2.1 j hj).1
  · exact mem_singleton.mp hv ▸ mem_image_of_mem s (mem_sdiff.mp hj).1

/-- T2(i)--(v): every graph branch of the corrected mechanism preserves
compatibility, including reuse of the original replacement pools and a shared
unsampled vertex in the addition branch. Web Appendix 2, corrected listing. -/
theorem corrected_graph_preserves (D : Data) (H K : State)
    (hD : Admissible D) (hH : Compatible D H) (hP : GraphProposal D true H K) :
    Compatible D K := by
  have hB : ProposalBase D H := ⟨hH.1,hH.2.1,hH.2.2.1,hH.2.2.2.1⟩
  have hsampleNe : ∀ v, v ∉ sampledVertices D → ∀ k ∈ D.sampled, s k ≠ v := by
    intro v hv k hk h
    exact hv (h ▸ mem_image_of_mem s hk)
  cases hP with
  | deleteUnobserved i j v P hi hj hne he hr hju hp =>
    have hL := remove_edge_base D H (s i) j hB hr
    have hprops := replacement_properties D H (removeEdge H (s i) j) P i v hH hL
      (Subset.refl _) (by intro w hw; exact fun h =>
        (mem_filter.mp hw).2 (mem_erase.mp h).2) hp
    have hnv := hsampleNe v hprops.2.2.2.1 i hi
    have hA := add_edge_base D P i v hprops.1 hi hprops.2.2.1 hnv
    change Compatible D (cleanup D true (addEdge P (s i) v))
    apply cleanup_compatible D _ hA
    intro k hk
    have hrdeg := degree_remove_step H (s i) j (s k) he
    have hadeg := degree_add_step P (s i) v (s k) hprops.2.2.2.2.2
    have hpdeg : graphDegree P (s k) = graphDegree (removeEdge H (s i) j) (s k) := by
      simp only [graphDegree,hprops.2.2.2.2.1]
    rw [hpdeg] at hadeg
    rw [hH.2.2.2.2.2 k hk] at hrdeg
    have hkj := hsampleNe j hju k hk
    have hkv := hsampleNe v hprops.2.2.2.1 k hk
    simp only [mem_insert,mem_singleton,hkj,hkv,or_false] at hrdeg hadeg
    by_cases hki : k = i <;> simp [hki,s] at hrdeg hadeg ⊢ <;> omega
  | deleteObserved i j v w P Q hi hj hne he hr hp hq =>
    have hL := remove_edge_base D H (s i) (s j) hB hr
    have hp' := replacement_properties D H (removeEdge H (s i) (s j)) P i v hH hL
      (Subset.refl _) (by intro z hz; exact fun h =>
        (mem_filter.mp hz).2 (mem_erase.mp h).2) hp
    have hnv := hsampleNe v hp'.2.2.2.1 i hi
    have hA := add_edge_base D P i v hp'.1 hi hp'.2.2.1 hnv
    have hpool : ∀ z ∈ replacementPool D H j, {s j,z} ∉ (addEdge P (s i) v).edges := by
      intro z hz hez
      have hneq : ({s j,z} : Finset Vertex) ≠ {s i,v} := by
        intro h
        have hs : s j ∈ ({s i,v} : Finset Vertex) := h ▸ (by simp)
        rcases mem_insert.mp hs with hh | hh
        · exact hne (Sum.inl.inj hh.symm)
        · exact hsampleNe v hp'.2.2.2.1 j hj (mem_singleton.mp hh)
      rcases mem_insert.mp hez with heq | hez
      · exact hneq heq
      · rw [hp'.2.2.2.2.1] at hez
        exact (mem_filter.mp hz).2 (mem_erase.mp hez).2
    have hq' := replacement_properties D H (addEdge P (s i) v) Q j w hH hA
      hp'.2.1 hpool hq
    have hnw := hsampleNe w hq'.2.2.2.1 j hj
    apply cleanup_compatible D _ (add_edge_base D Q j w hq'.1 hj hq'.2.2.1 hnw)
    intro k hk
    have hd1 := degree_remove_step H (s i) (s j) (s k) he
    have hd2 := degree_add_step P (s i) v (s k) hp'.2.2.2.2.2
    have hd3 := degree_add_step Q (s j) w (s k) hq'.2.2.2.2.2
    have heP : graphDegree P (s k) = graphDegree (removeEdge H (s i) (s j)) (s k) := by
      simp only [graphDegree,hp'.2.2.2.2.1]
    have heQ : graphDegree Q (s k) = graphDegree (addEdge P (s i) v) (s k) := by
      simp only [graphDegree,hq'.2.2.2.2.1]
    rw [heP] at hd2
    rw [heQ] at hd3
    rw [hH.2.2.2.2.2 k hk] at hd1
    have hkv := hsampleNe v hp'.2.2.2.1 k hk
    have hkw := hsampleNe w hq'.2.2.2.1 k hk
    simp only [mem_insert,mem_singleton,hkv,hkw,or_false] at hd1 hd2 hd3
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [s,hki,hkj,hne,Ne.symm hne] at hd1 hd2 hd3 ⊢ <;> omega
  | addObserved i j v w hi hj hne he hv hw hiv hjw =>
    have hvS := (mem_sdiff.mp hv).2
    have hwS := (mem_sdiff.mp hw).2
    obtain ⟨l,hl,hjl⟩ := hH.1.2 {j,w} hjw
    have hjl' : s l = j := by
      rcases mem_insert.mp hjl with hjl | hjl
      · exact hjl
      · exact False.elim (hwS (mem_singleton.mp hjl ▸ mem_image_of_mem s hl))
    subst j
    have hil : i ≠ l := by simpa [s] using hne
    have hr1 : {s i,v} ∉ recruitmentEdges D := fun h =>
      hvS (recruitment_edge_sampled D hD _ h (by simp))
    have hr2 : {s l,w} ∉ recruitmentEdges D := fun h =>
      hwS (recruitment_edge_sampled D hD _ h (by simp))
    have hdiff : ({s l,w} : Finset Vertex) ≠ {s i,v} := by
      intro h
      have hs : s l ∈ ({s i,v} : Finset Vertex) := h ▸ (by simp)
      rcases mem_insert.mp hs with hh | hh
      · exact hil (Sum.inl.inj hh.symm)
      · exact hsampleNe v hvS l hl (mem_singleton.mp hh)
    have hjw' : {s l,w} ∈ (removeEdge H (s i) v).edges := mem_erase.mpr ⟨hdiff,hjw⟩
    have he' : {s i,s l} ∉ (removeEdge (removeEdge H (s i) v) (s l) w).edges :=
      fun h => he (mem_erase.mp (mem_erase.mp h).2).2
    have hL := remove_edge_base D (removeEdge H (s i) v) (s l) w
      (remove_edge_base D H (s i) v hB hr1) hr2
    apply cleanup_compatible D _ (add_edge_base D _ i (s l) hL hi
      (hB.2.1 (mem_image_of_mem s hl)) hne)
    intro k hk
    have hd1 := degree_remove_step H (s i) v (s k) hiv
    have hd2 := degree_remove_step (removeEdge H (s i) v) (s l) w (s k) hjw'
    have hd3 := degree_add_step (removeEdge (removeEdge H (s i) v) (s l) w)
      (s i) (s l) (s k) he'
    rw [hH.2.2.2.2.2 k hk] at hd1
    have hkv := hsampleNe v hvS k hk
    have hkw := hsampleNe w hwS k hk
    simp only [mem_insert,mem_singleton,hkv,hkw,or_false] at hd1 hd2 hd3
    by_cases hki : k = i <;> by_cases hkl : k = l <;>
      simp [s,hki,hkl,hil,Ne.symm hil] at hd1 hd2 hd3 ⊢ <;> omega
  | unchanged i j hi hj hne hdel hadd =>
    exact cleanup_compatible D H hB hH.2.2.2.2.2


/-- T2: every execution of both corrected mechanisms preserves Definition 3;
the pools are still those of the original state, and no new data assumption is
imposed. Web Appendix 2, pp. 2--3, as corrected for P012-E001. -/
theorem corrected_proposal_preserves (D : Data) (H K : State)
    (hD : Admissible D) (hH : Compatible D H) (hP : Proposal D true H K) :
    Compatible D K := by
  rcases hP with hP | hP
  · exact corrected_graph_preserves D H K hD hH hP
  · exact corrected_trait_preserves D H K hH hP

/- T19: the printed claim that every proposal stays in C is false, as
proposal_counterexample demonstrates. Web Appendix 2, pp. 2--3. -/


/-- Example T8-T9 data: "V_R={1,2,3}, E_R={(1,2),(2,3)}, d_R=(3,2,3), Z_R=(0,0,1)"; seed 1 and entry order 1,2,3. Appendix p. 160 counterexamples. -/
def proofStepData : Data :=
  ⟨{1,2,3}, {1}, fun j => if j = 3 then 2 else 1, id,
    fun i => if i = 2 then 2 else 3, fun i => i == 3⟩
/-- Example T8 starting graph: the sampled triangle and two edges from vertices 1 and 3 to shared unsampled vertex 4. Traits extend (0,0,1) with Z_4=0; Appendix p. 160. -/
def result1BadStart : State :=
  ⟨{s 1,s 2,s 3,u 4 0},
    {{s 1,s 2},{s 2,s 3},{s 1,s 3},{s 1,u 4 0},{s 3,u 4 0}},
    fun v => decide (v = s 3)⟩
/-- The T8 proof-step output: remove {1,4},{3,4}, add the already present {1,3}, and discard the isolated unsampled vertex. Counterexample to the Result 1 proof, p. 160. -/
def result1BadEnd : State :=
  cleanup proofStepData true
    (addEdge (removeEdge (removeEdge result1BadStart (s 1) (u 4 0))
      (s 3) (u 4 0)) (s 1) (s 3))

/-- T8: the "any compatible subgraph" step in the Result 1 proof fails when
the prospective new edge is already present. Both degree-surplus hypotheses
and the nonrecruitment premise hold, but the new graph is incompatible and
the two induced edge sets are identical. Appendix p. 160. -/
theorem result1_proof_counterexample :
    Admissible proofStepData ∧ Compatible proofStepData result1BadStart ∧
    1 < 3 ∧ 3 ∈ nonseeds proofStepData ∧ proofStepData.parent 3 ≠ 1 ∧
    recruitmentDegree proofStepData 1 < proofStepData.degree 1 ∧
    recruitmentDegree proofStepData 3 < proofStepData.degree 3 ∧
    {s 1,u 4 0} ∈ result1BadStart.edges ∧ {s 3,u 4 0} ∈ result1BadStart.edges ∧
    {s 1,s 3} ∈ result1BadStart.edges ∧
    ¬ Compatible proofStepData result1BadEnd ∧
    (induced proofStepData result1BadStart).edges =
      (induced proofStepData result1BadEnd).edges := by
  norm_num [Admissible, Compatible, Augmented, Simple, proofStepData,
    result1BadStart, result1BadEnd, cleanup, addEdge, removeEdge, induced,
    recruitmentDegree, recruitmentEdges, graphDegree, sampledVertices, nonseeds, s, u]
  decide

/-- Example T9 starting graph: recruitment edges and all four ties from sampled 1,3 to unsampled 4,5, with traits Z_4=0 and Z_5=1. The cross edges are already present; p. 160. -/
def result2BadStart : State :=
  ⟨{s 1,s 2,s 3,u 4 0,u 5 0},
    {{s 1,s 2},{s 2,s 3},{s 1,u 4 0},{s 3,u 5 0},{s 1,u 5 0},{s 3,u 4 0}},
    fun v => decide (v = s 3) || decide (v = u 5 0)⟩
/-- The literal T9 swap removes {1,4},{3,5} and attempts to add already present {1,5},{3,4}. Counterexample to the Result 2 proof, p. 160. -/
def result2BadEnd : State :=
  addEdge (addEdge (removeEdge (removeEdge result2BadStart (s 1) (u 4 0))
    (s 3) (u 5 0)) (s 1) (u 5 0)) (s 3) (u 4 0)

/-- T9: the Result 2 "any compatible" swap can fail because both cross edges
were already present. The initial pair satisfies all hypotheses, including
opposite sampled traits and positive spare degrees; the output fails the
sampled-degree condition. Appendix p. 160. -/
theorem result2_proof_counterexample :
    Admissible proofStepData ∧ Compatible proofStepData result2BadStart ∧
    recruitmentDegree proofStepData 1 < proofStepData.degree 1 ∧
    recruitmentDegree proofStepData 3 < proofStepData.degree 3 ∧
    proofStepData.trait 1 = false ∧ proofStepData.trait 3 = true ∧
    result2BadStart.trait (u 4 0) = false ∧ result2BadStart.trait (u 5 0) = true ∧
    {s 1,u 4 0} ∈ result2BadStart.edges ∧ {s 3,u 5 0} ∈ result2BadStart.edges ∧
    {s 1,u 5 0} ∈ result2BadStart.edges ∧ {s 3,u 4 0} ∈ result2BadStart.edges ∧
    ¬ Compatible proofStepData result2BadEnd := by
  norm_num [Admissible, Compatible, Augmented, Simple, proofStepData,
    result2BadStart, result2BadEnd, addEdge, removeEdge, recruitmentDegree,
    recruitmentEdges, graphDegree, sampledVertices, nonseeds, s, u]
  decide

/-- Example T12: "V_R={1,2,3}, M={1}, E_R={(1,2),(1,3)}, t_R=(0,1,2), d_R=(3,1,1), Z_R=(1,1,1)". Counterexample to (A2), Appendix p. 160. -/
def a2Data : Data :=
  ⟨{1,2,3}, {1}, fun _ => 1, fun i => i-1,
    fun i => if i = 1 then 3 else 1, fun _ => true⟩
/-- Example T12 graph: "E_SU={{1,2},{1,3},{1,4}}", with vertex 4 unsampled and its trait equal to t. The three sampled traits are all 1; Appendix p. 160, (A2). -/
def a2State (t : Bool) : State :=
  ⟨{s 1,s 2,s 3,u 4 0}, {{s 1,s 2},{s 1,s 3},{s 1,u 4 0}},
    fun v => match v with | Sum.inl _ => true | Sum.inr _ => t⟩

/-- T12: the pre-flip functional minus the post-flip functional is -5/12
in the admissible two-recruit example, whereas printed (A2) gives -1/6 or -1/4. The private neighbour
assumption, both compatibilities, the times and the spare degree are explicit.
Appendix p. 160, (A2), counterexample from P012-E002. -/
theorem a2_counterexample :
    Admissible a2Data ∧ Compatible a2Data (a2State true) ∧
    Compatible a2Data (a2State false) ∧
    recruitmentDegree a2Data 1 < a2Data.degree 1 ∧ a2Data.parent 2 = 1 ∧
    (∀ i ∈ a2Data.sampled, {s i,u 4 0} ∈ (a2State true).edges ↔ i = 1) ∧
    susceptible a2Data (a2State true) 1 2 = {s 2,s 3,u 4 0} ∧
    susceptible a2Data (a2State true) 1 3 = {s 3,u 4 0} ∧
    preferential a2Data (a2State true) = some 0 ∧
    preferential a2Data (a2State false) = some (5/12) ∧
    pValue a2Data (a2State true) - pValue a2Data (a2State false) = -5/12 ∧
    pValue a2Data (a2State true) - pValue a2Data (a2State false) ≠
      -1 / ((nonseeds a2Data).card *
        ((susceptible a2Data (a2State true) 1 2).card : ℝ)) ∧
    pValue a2Data (a2State true) - pValue a2Data (a2State false) ≠
      -1 / ((nonseeds a2Data).card *
        ((susceptible a2Data (a2State true) 1 3).card : ℝ)) := by
  norm_num [Admissible, Compatible, Augmented, Simple, a2Data, a2State,
    recruitmentDegree, recruitmentEdges, graphDegree, sampledVertices, nonseeds,
    susceptible, sameSusceptible, preferential, PreferentialDefined, pValue, pSum, s, u]
  decide

/-- Example T14(A): "V_R={1,2}, M={1}, E_R={(1,2)}, d_R=(1,1), Z_R=(0,0)". A zero-variance boundary of Definition 1, p. 155. -/
def domainA : Data :=
  ⟨{1,2},{1},fun _ => 1,fun i => i-1,fun _ => 1,fun _ => false⟩
/-- The simple two-vertex graph "E_SU={{1,2}}", with active traits t1,t2. Used in the domain and empty-unsampled-pool counterexamples to Definitions 1-2 and Web Appendix 2. -/
def dyad (t1 t2 : Bool) : State :=
  ⟨{s 1,s 2},{{s 1,s 2}},fun v => if v = s 1 then t1 else t2⟩
/-- Example T14(B): "V_R=M={1,2}, E_R=empty, d_R=(1,1), Z_R=(0,1)". Definition 2 has an empty average although the dyad homophily is defined; p. 155. -/
def domainB : Data := {domainA with seeds := {1,2}, trait := fun i => i == 2}
/-- Example T14(C): "V_R=M={1}, E_R=empty, d_1=0, Z_1=0". The edgeless boundary of Definitions 1-2, p. 155. -/
def domainC : Data := ⟨{1},{1},fun _ => 1,id,fun _ => 0,fun _ => false⟩
/-- The T14(C) graph has the single sampled seed, no edges and trait 0. Definitions 1-2, p. 155, edgeless counterexample. -/
def domainCState : State := ⟨{s 1},∅,fun _ => false⟩
/-- Example T14(D): "V_R={1,2}, M={1}, E_R={(1,2)}, d_R=(1,4), Z_R=(1,1)". Compatible states need not share the homophily domain; Definition 4, p. 155. -/
def domainD : Data :=
  ⟨{1,2},{1},fun _ => 1,fun i => i-1,fun i => if i = 1 then 1 else 4,fun _ => true⟩
/-- The T14(D) graph is the recruitment dyad plus three private leaves at vertex 2. The three independent unsampled traits are t3,t4,t5; Definitions 1 and 4, p. 155. -/
def domainDState (t3 t4 t5 : Bool) : State :=
  ⟨{s 1,s 2,u 3 0,u 4 0,u 5 0},
    {{s 1,s 2},{s 2,u 3 0},{s 2,u 4 0},{s 2,u 5 0}},
    fun v => if v = u 3 0 then t3 else if v = u 4 0 then t4
      else if v = u 5 0 then t5 else true⟩

/-- T14(A--D): explicit compatible data for a 0/0 correlation, an empty
recruitment average, an edgeless graph, and mixed defined/undefined compatible
states. Zero denominators are asserted; no fictitious value is assigned.
Definitions 1, 2, 4, p. 155, domain counterexamples from P012-E006. -/
theorem domain_counterexamples :
    (Admissible domainA ∧ Compatible domainA (dyad false false) ∧
      hNumerator (dyad false false) = 0 ∧ hDenominator (dyad false false) = 0 ∧
      homophily (dyad false false) = none ∧
      preferential domainA (dyad false false) = some 0) ∧
    (Admissible domainB ∧ Compatible domainB (dyad false true) ∧
      homophily (dyad false true) = some (-1) ∧ (nonseeds domainB).card = 0 ∧
      pSum domainB (dyad false true) = 0 ∧
      (∀ H, preferential domainB H = none)) ∧
    (Admissible domainC ∧ Compatible domainC domainCState ∧
      domainCState.edges.card = 0 ∧ homophily domainCState = none ∧
      preferential domainC domainCState = none) ∧
    (Admissible domainD ∧
      (∀ t3 t4 t5 : Bool, Compatible domainD (domainDState t3 t4 t5)) ∧
      hNumerator (domainDState true true true) = 0 ∧
      hDenominator (domainDState true true true) = 0 ∧
      homophily (domainDState true true true) = none ∧
      homophily (domainDState false false false) = some (-3/5) ∧
      homophily (domainDState true false false) = some (-1/3) ∧
      homophily (domainDState true true false) = some (-1/7) ∧
      (∀ t3 t4 t5 : Bool, preferential domainD (domainDState t3 t4 t5) = some 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
    all_goals norm_num [homophily, HomophilyDefined, hValue, hNumerator, hDenominator,
      graphDegree, adjacency, z, dyad, domainA, preferential, PreferentialDefined,
      pValue, pSum, susceptible, sameSusceptible, nonseeds, s, u]
  · refine ⟨by decide, by decide, ?_, by decide, ?_, ?_⟩
    · norm_num [homophily, HomophilyDefined, hValue, hNumerator, hDenominator,
        graphDegree, adjacency, z, dyad, s]
    · simp [pSum, nonseeds, domainB, domainA]
    · intro H
      simp [preferential, PreferentialDefined, nonseeds, domainB, domainA]
  · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · simp [homophily, HomophilyDefined, domainCState]
    · simp [preferential, PreferentialDefined, nonseeds, domainC]
  · refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t3 t4 t5
      cases t3 <;> cases t4 <;> cases t5 <;> decide
    · norm_num [hNumerator, graphDegree, adjacency, z, domainDState, s, u]
    · norm_num [hDenominator, graphDegree, z, domainDState, s, u]
    · norm_num [homophily, HomophilyDefined, hDenominator, graphDegree, z, domainDState, s, u]
    · norm_num [homophily, HomophilyDefined, hValue, hNumerator, hDenominator,
        graphDegree, adjacency, z, domainDState, s, u]
    · norm_num [homophily, HomophilyDefined, hValue, hNumerator, hDenominator,
        graphDegree, adjacency, z, domainDState, s, u]
    · norm_num [homophily, HomophilyDefined, hValue, hNumerator, hDenominator,
        graphDegree, adjacency, z, domainDState, s, u]
    · intro t3 t4 t5
      cases t3 <;> cases t4 <;> cases t5 <;>
        norm_num [preferential, PreferentialDefined, pValue, pSum, susceptible,
          sameSusceptible, nonseeds, domainD, domainDState, s, u]

/-- Example T1(b): "V_R={1,2,3}, E_R={(1,2),(2,3)}, M={1}, d_R=(1,3,1), Z_R=(0,1,0)". Entry order 1,2,3; Web Appendix 2 counterexample. -/
def proposalDataB : Data :=
  ⟨{1,2,3},{1},fun j => if j = 3 then 2 else 1,id,
    fun i => if i = 2 then 3 else 1,fun i => i == 2⟩
/-- Example T1(b): recruitment edges plus the private tie {2,4}, with Z_4=0. Vertex 4 is unsampled; Web Appendix 2 counterexample. -/
def proposalStartB : State :=
  ⟨{s 1,s 2,s 3,u 4 0}, {{s 1,s 2},{s 2,s 3},{s 2,u 4 0}}, fun v => decide (v = s 2)⟩
/-- The T1(b) printed output replaces {2,4} by {2,5} and also adds the forbidden {4,5}, for either new trait t. Web Appendix 2, line 22. -/
def proposalBadB (t : Bool) : State :=
  cleanup proposalDataB false (addEdge
    (addEdge (addVertex (removeEdge proposalStartB (s 2) (u 4 0)) (u 5 0) t)
      (s 2) (u 5 0)) (u 4 0) (u 5 0))

/-- T1(b): the explicit three-subject example returns
an incompatible graph for both choices of the fresh trait. Web Appendix 2. -/
theorem proposal_counterexample_b :
    Admissible proposalDataB ∧ Compatible proposalDataB proposalStartB ∧
    replacementPool proposalDataB proposalStartB 2 = ∅ ∧
    (∀ t : Bool, Proposal proposalDataB false proposalStartB (proposalBadB t) ∧
      ¬ Compatible proposalDataB (proposalBadB t)) := by
  refine ⟨by decide,by decide,by decide,?_⟩
  intro t
  constructor
  · left
    exact GraphProposal.deleteUnobserved 2 (u 4 0) (u 5 0)
      (addVertex (removeEdge proposalStartB (s 2) (u 4 0)) (u 5 0) t)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (Replacement.fresh (u 5 0) (by decide) t)
  · cases t <;> decide

/-- Example T1(c): "V_R={1,2,3}, M={1,3}, E_R={(1,2)}, d_R=(1,1,0), Z_R=(0,1,0)". Sampled vertex 3 is an isolated seed; Web Appendix 2, line 27. -/
def cleanupData : Data :=
  ⟨{1,2,3},{1,3},fun _ => 1,id,fun i => if i = 3 then 0 else 1,fun i => i == 2⟩
/-- The T1(c) compatible graph has three sampled vertices but only edge {1,2}; sampled seed 3 must remain in the graph. Web Appendix 2, line 27 counterexample. -/
def cleanupStart : State :=
  ⟨{s 1,s 2,s 3},{{s 1,s 2}},fun v => decide (v = s 2)⟩

/-- T1(c): selecting a recruitment edge leaves the edges untouched, but printed
line 27 deletes the isolated sampled seed 3 and destroys compatibility. -/
theorem cleanup_counterexample :
    Admissible cleanupData ∧ Compatible cleanupData cleanupStart ∧
    Proposal cleanupData false cleanupStart (cleanup cleanupData false cleanupStart) ∧
    ¬ Compatible cleanupData (cleanup cleanupData false cleanupStart) ∧
    homophily cleanupStart = some (-1) ∧ preferential cleanupData cleanupStart = some 0 := by
  refine ⟨by decide,by decide,?_,by decide,?_,?_⟩
  · left
    exact GraphProposal.unchanged 1 (s 2) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · norm_num [homophily, HomophilyDefined, hValue, hNumerator, hDenominator,
      graphDegree, adjacency, z, cleanupStart, s]
  · norm_num [preferential, PreferentialDefined, pValue, pSum, susceptible,
      sameSusceptible, nonseeds, cleanupData, cleanupStart, s]

/-- Example T1(d): "V_R={1,2}, M={1}, E_R={(1,2)}, d_R=(1,1), Z_R=(0,1)". The compatible dyad has no unsampled vertex; Web Appendix 2 trait mechanism. -/
def emptyPoolData : Data := {domainA with trait := fun i => i == 2}

/-- T1(d): the printed trait mechanism has no possible execution when there
is no unsampled vertex, even at a compatible nondegenerate recruited dyad. -/
theorem empty_trait_pool_counterexample :
    Admissible emptyPoolData ∧ Compatible emptyPoolData (dyad false true) ∧
    unsampled emptyPoolData (dyad false true) = ∅ ∧
    (¬ ∃ K, TraitProposal emptyPoolData false (dyad false true) K) ∧
    homophily (dyad false true) = some (-1) ∧
    preferential emptyPoolData (dyad false true) = some 0 := by
  refine ⟨by decide,by decide,by decide,?_,?_,?_⟩
  · rintro ⟨K,hK⟩
    cases hK with
    | flip v hv => simpa [unsampled,emptyPoolData,domainA,dyad,sampledVertices,s] using hv
    | empty hr _ => cases hr
  · norm_num [homophily, HomophilyDefined, hValue, hNumerator, hDenominator,
      graphDegree, adjacency, z, dyad, s]
  · norm_num [preferential, PreferentialDefined, pValue, pSum, susceptible,
      sameSusceptible, nonseeds, emptyPoolData,domainA,dyad,s]


/-- Children R_i in the repaired (A2) calculation (Appendix p. 160, T13). -/
def children (D : Data) (i : ℕ) : Finset ℕ :=
  (nonseeds D).filter (fun j => D.parent j = i)

/-- T15(b,c): p is defined at every compatible pair exactly when there is
at least one nonseed recruitment. Definitions 2 and 4, p. 155, corrected. -/
theorem full_p_domain_conditions (D : Data) (hD : Admissible D) :
    (∀ H, Compatible D H → PreferentialDefined D H) ↔
      D.seeds.card < D.sampled.card := by
  constructor
  · intro h
    have hN := (h (leafCompletion D true) (leafCompletion_compatible D hD true)).1
    rw [nonseeds, card_sdiff_of_subset hD.1] at hN
    omega
  · intro hN H hH
    constructor
    · rw [nonseeds, card_sdiff_of_subset hD.1]
      omega
    · intro j hj
      exact (recruit_is_susceptible D H hH j hj).2

/-- T17: deleting U gives the degree-upper-bound compatibility from the
opening of the proof, and gives degree-equality compatibility precisely when
there were no unsampled vertices. Appendix p. 160, corrected P012-N005. -/
theorem induced_compatibility (D : Data) (H : State) (hD : Admissible D)
    (hH : GraphCompatible D H) :
    InducedCompatible D (induced D H) ∧
    ((∀ i ∈ D.sampled, graphDegree (induced D H) (s i) = D.degree i) ↔
      H.vertices = sampledVertices D) := by
  have hsub : ∀ i, ((induced D H).edges.filter (fun e => s i ∈ e)) ⊆
      H.edges.filter (fun e => s i ∈ e) := by
    intro i e he
    obtain ⟨he,hi⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨(mem_filter.mp he).1,hi⟩
  have hI : InducedCompatible D (induced D H) := by
    refine ⟨?_,rfl,?_,?_⟩
    · intro e he
      obtain ⟨he,hsubE⟩ := mem_filter.mp he
      exact ⟨(hH.1.1 e he).1,hsubE⟩
    · intro e he
      refine mem_filter.mpr ⟨hH.2.2.1 he,?_⟩
      obtain ⟨j,hj,rfl⟩ := mem_image.mp he
      have hp := hD.2.2.1 j hj
      intro v hv
      simp only [mem_insert,mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact mem_image_of_mem s hp.1
      · exact mem_image_of_mem s (mem_sdiff.mp hj).1
    · intro i hi
      exact le_trans (card_le_card (hsub i)) (le_of_eq (hH.2.2.2.2 i hi))
  refine ⟨hI,?_⟩
  constructor
  · intro heq
    apply Subset.antisymm _ hH.2.1
    intro v hv
    by_contra hnot
    obtain ⟨i,hi,he⟩ := hH.2.2.2.1 v hv hnot
    have hstrict : ((induced D H).edges.filter (fun e => s i ∈ e)) ⊂
        H.edges.filter (fun e => s i ∈ e) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub i,?_⟩
      intro hsame
      have hin : {s i,v} ∈ (induced D H).edges.filter (fun e => s i ∈ e) := by
        rw [hsame]
        exact mem_filter.mpr ⟨he,by simp⟩
      have hpairSub := (mem_filter.mp (mem_filter.mp hin).1).2
      exact hnot (hpairSub (by simp))
    have hcard := card_lt_card hstrict
    change graphDegree (induced D H) (s i) < graphDegree H (s i) at hcard
    rw [heq i hi,hH.2.2.2.2 i hi] at hcard
    exact lt_irrefl _ hcard
  · intro hv
    have he : (induced D H).edges = H.edges := by
      apply filter_eq_self.mpr
      intro e he
      rw [← hv]
      exact (hH.1.1 e he).2
    intro i hi
    simpa only [graphDegree,he] using hH.2.2.2.2 i hi

/-- T18: homophily has only the augmented graph and its traits as inputs;
changing recruitment data cannot change it. This is the corrected two-argument
notation of equation (1), pp. 155, 160 (P012-N006). -/
theorem homophily_arguments (D₁ D₂ : Data) (H K : State)
    (hD₁ : Admissible D₁) (hD₂ : Admissible D₂)
    (hH : Compatible D₁ H) (hK : Compatible D₂ K)
    (hv : H.vertices = K.vertices) (he : H.edges = K.edges)
    (hz : ∀ v ∈ H.vertices, H.trait v = K.trait v) :
    homophily H = homophily K := by
  have hd : ∀ v, graphDegree H v = graphDegree K v := by
    intro v; simp only [graphDegree, he]
  have ha : ∀ v w, adjacency H v w = adjacency K v w := by
    intro v w; simp only [adjacency, he]
  have hnum : hNumerator H = hNumerator K := by
    unfold hNumerator
    rw [← hv, ← he]
    apply sum_congr rfl
    intro v hv'
    apply sum_congr rfl
    intro w hw'
    simp only [ha, hd, z, hz v hv', hz w hw']
  have hden : hDenominator H = hDenominator K := by
    unfold hDenominator
    rw [← hv, ← he]
    apply sum_congr rfl
    intro v hv'
    apply sum_congr rfl
    intro w hw'
    simp only [hd, z, hz v hv', hz w hw']
  simp only [homophily, HomophilyDefined, hValue, he, hnum, hden]

/-- Figure 1 panel A (p. 156): "V_R={1,...,5}, M={1}, d_R=(5,4,3,3,2), Z_R=(1,1,1,0,1)". Arrows are 1->2, 1->4, 2->3, 2->5; the vertex labels give entry-time order. -/
def figureData : Data :=
  ⟨{1,2,3,4,5},{1},fun j => if j = 3 ∨ j = 5 then 2 else 1,id,
    fun i => if i = 1 then 5 else if i = 2 then 4 else if i = 5 then 2 else 3,
    fun i => !(i == 4)⟩


/-- The pointwise Table 1 h-interval assertion at supplied study inputs,
p. 158. This is a proposition template, not a universally quantified theorem
about all data with the reported totals. The actual Hartford inputs are
unpublished, so the empirical T20 theorem cannot be instantiated here.
The tolerance 1/20000 represents four-decimal rounding. -/
def printed_table_intervals (Dsex Dcrack Dhome : Data) : Prop :=
    (∀ D ∈ [Dsex,Dcrack,Dhome], Admissible D ∧
      D.sampled.card = 527 ∧ D.seeds.card = 6 ∧
      (∑ i ∈ D.sampled, D.degree i) = 4487) ∧
    (Dsex.sampled = Dcrack.sampled ∧ Dsex.sampled = Dhome.sampled ∧
      Dsex.seeds = Dcrack.seeds ∧ Dsex.seeds = Dhome.seeds ∧
      (∀ j ∈ nonseeds Dsex, Dsex.parent j = Dcrack.parent j ∧ Dsex.parent j = Dhome.parent j) ∧
      (∀ i ∈ Dsex.sampled, Dsex.degree i = Dcrack.degree i ∧ Dsex.degree i = Dhome.degree i ∧
        Dsex.time i = Dcrack.time i ∧ Dsex.time i = Dhome.time i)) ∧
    ∃ Ls Us Lc Uc Lh Uh : ℝ,
      FullHomophilyRegion Dsex Ls Us ∧ FullHomophilyRegion Dcrack Lc Uc ∧
      FullHomophilyRegion Dhome Lh Uh ∧
      |Ls - (-7027/10000)| ≤ 1/20000 ∧ |Us - 8292/10000| ≤ 1/20000 ∧
      |Lc - (-6918/10000)| ≤ 1/20000 ∧ |Uc - 8231/10000| ≤ 1/20000 ∧
      |Lh - (-7179/10000)| ≤ 1/20000 ∧ |Uh - 8242/10000| ≤ 1/20000

/- Algebraic supporting lemmas for the graph theorems exact_h_region and exact_p_region. -/

/-- T6(i), finite algebra: the two forms of φ agree on the ordinary domain. -/
theorem phi_formula (x y c : ℝ) (hx : 2*x+c ≠ 0) (hy : 2*y+c ≠ 0) :
    phi x y c = (4*x*y-c^2)/((2*x+c)*(2*y+c)) := by
  unfold phi
  field_simp
  ring

/-- T6(iii), finite algebra: φ is nondecreasing in the 11 edge count. -/
theorem phi_mono_x (x X y c : ℝ) (hc : 0 ≤ c) (h : x ≤ X)
    (hx : 0 < 2*x+c) (hX : 0 < 2*X+c) : phi x y c ≤ phi X y c := by
  have hd : c / (2*X+c) ≤ c / (2*x+c) := by
    apply (div_le_div_iff₀ hX hx).2
    nlinarith [mul_nonneg hc (sub_nonneg.mpr h)]
  unfold phi
  linarith

/-- T6(iii), finite algebra: φ is nondecreasing in the 00 edge count. -/
theorem phi_mono_y (x y Y c : ℝ) (hc : 0 ≤ c) (h : y ≤ Y)
    (hy : 0 < 2*y+c) (hY : 0 < 2*Y+c) : phi x y c ≤ phi x Y c := by
  have hd : c / (2*Y+c) ≤ c / (2*y+c) := by
    apply (div_le_div_iff₀ hY hy).2
    nlinarith [mul_nonneg hc (sub_nonneg.mpr h)]
  unfold phi
  linarith

/-- T6(iii), finite algebra: φ is nonincreasing in the mixed edge count. -/
theorem phi_anti_c (x y c C : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : c ≤ C)
    (hxc : 0 < 2*x+c) (hxC : 0 < 2*x+C)
    (hyc : 0 < 2*y+c) (hyC : 0 < 2*y+C) : phi x y C ≤ phi x y c := by
  have h1 : c / (2*x+c) ≤ C / (2*x+C) := by
    apply (div_le_div_iff₀ hxc hxC).2
    nlinarith [mul_nonneg hx (sub_nonneg.mpr h)]
  have h2 : c / (2*y+c) ≤ C / (2*y+C) := by
    apply (div_le_div_iff₀ hyc hyC).2
    nlinarith [mul_nonneg hy (sub_nonneg.mpr h)]
  unfold phi
  linarith

/-- T6(ii) implies T6(iii): edge-count bounds yield both endpoint inequalities,
with explicitly positive intermediate denominators. Correction P012-N007. -/
theorem count_bounds_imply_h_bounds (a b A B cR C x y c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hcR : 0 ≤ cR)
    (hax : a ≤ x) (hxA : x ≤ A) (hby : b ≤ y) (hyB : y ≤ B)
    (hcRc : cR ≤ c) (hcC : c ≤ C)
    (hl1 : 0 < 2*a+C) (hl0 : 0 < 2*b+C)
    (hu1 : 0 < 2*A+cR) (hu0 : 0 < 2*B+cR)
    (h1 : 0 < 2*x+c) (h0 : 0 < 2*y+c) :
    phi a b C ≤ phi x y c ∧ phi x y c ≤ phi A B cR := by
  have hx : 0 ≤ x := le_trans ha hax
  have hy : 0 ≤ y := le_trans hb hby
  have hc : 0 ≤ c := le_trans hcR hcRc
  have hC : 0 ≤ C := le_trans hc hcC
  have hxC : 0 < 2*x+C := by linarith
  have hyC : 0 < 2*y+C := by linarith
  have hAc : 0 < 2*A+c := by linarith
  have hBc : 0 < 2*B+c := by linarith
  have hA : 0 ≤ A := le_trans hx hxA
  have hB : 0 ≤ B := le_trans hy hyB
  constructor
  · exact le_trans (phi_mono_x a x b C hC hax hl1 hxC)
      (le_trans (phi_mono_y x b y C hC hby hl0 hyC)
        (phi_anti_c x y c C hx hy hcC h1 hxC h0 hyC))
  · exact le_trans (phi_mono_x x A y c hc hxA h1 hAc)
      (le_trans (phi_mono_y A y B c hc hyB h0 hBc)
        (phi_anti_c A B cR c hA hB hcRc hu1 hAc hu0 hBc))

/-- T7(ii), finite algebra: obligatory and at most s extra susceptible neighbours
give the printed sharp bounds for a single recruitment baseline. P012-N007. -/
theorem susceptible_fraction_bounds (a b s q y : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b)
    (hy : 0 ≤ y) (hys : y ≤ s) (hq : 0 ≤ q) (hqy : q ≤ y) :
    a/(b+s) ≤ (a+q)/(b+y) ∧ (a+q)/(b+y) ≤ (a+s)/(b+s) := by
  have hs : 0 ≤ s := le_trans hy hys
  have hbs : 0 < b+s := by linarith
  have hby : 0 < b+y := by linarith
  have h1 : 0 ≤ a*(s-y) := mul_nonneg ha (sub_nonneg.mpr hys)
  have h2 : 0 ≤ q*(b+s) := mul_nonneg hq (le_of_lt hbs)
  have h3 : 0 ≤ (s-y)*(b-a) := mul_nonneg (sub_nonneg.mpr hys) (sub_nonneg.mpr hab)
  have h4 : 0 ≤ (y-q)*(b+s) := mul_nonneg (sub_nonneg.mpr hqy) (le_of_lt hbs)
  constructor
  · apply (div_le_div_iff₀ hbs hby).2
    nlinarith
  · apply (div_le_div_iff₀ hby hbs).2
    nlinarith

/-- T3(c), uniform real-valued certificate: for all nonnegative counts summing
to 521, the opposite-leaf value is at most -1462/1983. P012-N002, Table 1 p. 158. -/
theorem uniform_leaf_bound (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hsum : a+b+c = 521) :
    (4*a*b-(c+3445)^2)/((2*a+c+3445)*(2*b+c+3445)) ≤ -1462/1983 := by
  have hden : 0 < (2*a+c+3445)*(2*b+c+3445) := by positivity
  apply (div_le_iff₀ hden).2
  have hid : (-1462/1983 : ℝ)*((2*a+c+3445)*(2*b+c+3445)) -
      (4*a*b-(c+3445)^2) = 7932*c + (3445/1983)*(a-b)^2 := by
    have hce : c = 521-a-b := by linarith
    rw [hce]
    ring
  nlinarith [sq_nonneg (a-b)]

/-- T3(c)--T4, integer strengthening: the largest possible constructed value
is -178409/241987, attained at (a,b,c_R)=(260,261,0) or its trait exchange. -/
theorem uniform_integer_leaf_bound (a b c : ℕ) (hsum : a+b+c = 521) :
    (4*(a:ℝ)*b-((c:ℝ)+3445)^2)/
      ((2*(a:ℝ)+c+3445)*(2*(b:ℝ)+c+3445)) ≤ -178409/241987 := by
  have hsumR : (a:ℝ)+b+c = 521 := by exact_mod_cast hsum
  have hden : 0 < (2*(a:ℝ)+c+3445)*(2*(b:ℝ)+c+3445) := by positivity
  apply (div_le_iff₀ hden).2
  have hid : (-178409/241987 : ℝ)*
      ((2*(a:ℝ)+c+3445)*(2*(b:ℝ)+c+3445)) -
      (4*(a:ℝ)*b-((c:ℝ)+3445)^2) =
      7932*(c:ℝ) + (420396/241987)*(((a:ℝ)-b)^2-1) := by
    have hce : (c:ℝ) = 521-a-b := by linarith
    rw [hce]
    ring
  by_cases hc : c = 0
  · have hab : a+1 ≤ b ∨ b+1 ≤ a := by omega
    have habR : (a:ℝ)+1 ≤ b ∨ (b:ℝ)+1 ≤ a := by exact_mod_cast hab
    have hs : (1:ℝ) ≤ ((a:ℝ)-b)^2 := by
      rcases habR with h | h <;> nlinarith [sq_nonneg ((a:ℝ)-b+1),
        sq_nonneg ((a:ℝ)-b-1)]
    simp only [hc, Nat.cast_zero, mul_zero, zero_add] at hid
    nlinarith
  · have hc1 : (1:ℝ) ≤ c := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hc)
    nlinarith [sq_nonneg ((a:ℝ)-b)]

/-- T3(d)--T4: exact comparisons and gaps, unaffected by four-decimal rounding. -/
theorem table_numeric_gaps :
    (-1462/1983 : ℝ) < -7179/10000 ∧ (-7179/10000 : ℝ) < -7027/10000 ∧
    (-7027/10000 : ℝ) < -6918/10000 ∧
    (-7027/10000 : ℝ)+1462/1983 = 685459/19830000 ∧
    (-6918/10000 : ℝ)+1462/1983 = 450803/9915000 ∧
    (-7179/10000 : ℝ)+1462/1983 = 384043/19830000 ∧
    phi 260 261 3445 = -178409/241987 ∧ phi 261 260 3445 = -178409/241987 := by
  norm_num [phi]

/-- T23 finite arithmetic: the four endpoint formulas evaluated at Figure 1's
observed data give the four exact published extrema. This lemma by itself
does not assert that every compatible graph is between the endpoints. -/
theorem figure1_endpoint_arithmetic :
    Admissible figureData ∧ hLower figureData = -5/8 ∧ hUpper figureData = 79/105 ∧
    pLower figureData = -11/80 ∧ pUpper figureData = 49/120 := by
  norm_num [Admissible, figureData, recruitmentDegree, recruitmentEdges, nonseeds,
    hLower, hUpper, a, b, cR, recruitmentState, edgeCount, mixedCount, phi,
    traitSpare, totalSpare, spare, pLower, pUpper, observedMatch, childMatches,
    laterChildren, s]

open Filter
open scoped Topology

/-- J(h,p)=1/(1+ε+h) from Web Appendix 1, p. 1. Its second argument is inert. -/
def objective (ε h p : ℝ) : ℝ := 1/(1+ε+h)

/-- T24 finite display (1): the objective is positive and at most 1/ε on
[-1,1]^2, with equality at h=-1, for every ε>0 (no ε<1 restriction). -/
theorem objective_bounds (ε h p : ℝ) (hε : 0 < ε) (hh : -1 ≤ h) :
    0 < objective ε h p ∧ objective ε h p ≤ 1/ε ∧ objective ε (-1) p = 1/ε := by
  have hd : 0 < 1+ε+h := by linarith
  constructor
  · exact div_pos (by norm_num) hd
  constructor
  · unfold objective
    exact one_div_le_one_div_of_le hε (by linarith)
  · unfold objective
    congr 1
    ring

/-- T16(a): no positive nondecreasing temperature sequence tends to zero.
The index 0 represents printed t=1. Web Appendix p. 1, correction P012-E007. -/
theorem no_positive_nondecreasing_zero_limit (T : ℕ → ℝ)
    (hp : ∀ n, 0 < T n) (hm : Monotone T) :
    ¬ Tendsto T atTop (𝓝 0) := by
  intro hlim
  have hle : T 0 ≤ 0 := ge_of_tendsto hlim
    (Eventually.of_forall (fun n => hm (Nat.zero_le n)))
  linarith [hp 0]

/-- T16(a): log 1 has no finite multiplicative reciprocal; asserting x/0=0
would change the printed schedule rather than define its first temperature. -/
theorem printed_first_temperature_undefined (ε : ℝ) :
    ¬ ∃ T : ℝ, T*(ε*Real.log 1) = 1 := by
  simp

/-- Corrected schedule T_1 arbitrary ≥1/(ε log2); T_t=1/(ε log t) for t≥2,
Web Appendix pp. 1--2, T16(b). Lean index n denotes printed t=n+1. -/
def cooling (ε T₁ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then T₁ else 1/(ε*Real.log ((n:ℝ)+1))

/-- T16(b): full positivity, nonincrease, strict decrease from t=2 onwards,
and the limit zero for the repaired schedule, including its first value. -/
theorem cooling_properties (ε T₁ : ℝ) (hε : 0 < ε)
    (hfirst : 1/(ε*Real.log 2) ≤ T₁) :
    (∀ n, 0 < cooling ε T₁ n) ∧ Antitone (cooling ε T₁) ∧
    StrictAntiOn (cooling ε T₁) (Set.Ici 1) ∧ Tendsto (cooling ε T₁) atTop (𝓝 0) := by
  have hlog : ∀ n : ℕ, 1 ≤ n → 0 < Real.log ((n:ℝ)+1) := by
    intro n hn
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
    apply Real.log_pos
    linarith
  have htail : ∀ i j : ℕ, 1 ≤ i → i ≤ j →
      1/(ε*Real.log ((j:ℝ)+1)) ≤ 1/(ε*Real.log ((i:ℝ)+1)) := by
    intro i j hi hij
    apply one_div_le_one_div_of_le (mul_pos hε (hlog i hi))
    apply mul_le_mul_of_nonneg_left _ hε.le
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hp : ∀ n, 0 < cooling ε T₁ n := by
    intro n
    by_cases hn : n = 0
    · simp only [cooling, hn, if_pos rfl]
      exact lt_of_lt_of_le (div_pos (by norm_num) (mul_pos hε (Real.log_pos (by norm_num)))) hfirst
    · simp only [cooling, if_neg hn]
      exact div_pos (by norm_num) (mul_pos hε (hlog n (by omega)))
  refine ⟨hp, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j; exact le_rfl
      · simp only [cooling, if_pos rfl, if_neg hj]
        exact le_trans (by simpa only [Nat.cast_one,show (1:ℝ)+1=2 by norm_num] using htail 1 j (by omega) (by omega)) hfirst
    · have hj : j ≠ 0 := by omega
      simpa only [cooling, if_neg hi, if_neg hj] using htail i j (by omega) hij
  · intro i hi j hj hij
    simp only [Set.mem_Ici] at hi hj
    have hi0 : i ≠ 0 := by omega
    have hj0 : j ≠ 0 := by omega
    simp only [cooling, if_neg hi0, if_neg hj0]
    apply one_div_lt_one_div_of_lt (mul_pos hε (hlog i hi))
    apply mul_lt_mul_of_pos_left _ hε
    apply Real.log_lt_log (by positivity)
    exact_mod_cast Nat.add_lt_add_right hij 1
  · have hloglim : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+1)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).atTop_add
          (tendsto_const_nhds (x := (1:ℝ))))
    have hinv : Tendsto (fun n : ℕ => 1/(ε*Real.log ((n:ℝ)+1))) atTop (𝓝 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (hloglim.const_mul_atTop hε)
    apply hinv.congr'
    exact eventually_atTop.2 ⟨1, fun n hn => by simp [cooling, show n ≠ 0 by omega]⟩

/-- T16(c) and T24 display (2), for each fixed real t≥2: the exact exponential
and power identities and comparison with the harmonic term. -/
theorem cooling_term_bound (ε D t : ℝ) (hε : 0 < ε) (ht : 2 ≤ t)
    (hD : 0 ≤ D*ε) (hdepth : D*ε ≤ 1) :
    Real.exp (-D / (1/(ε*Real.log t))) = 1/(t^(D*ε)) ∧
    1/t ≤ Real.exp (-D / (1/(ε*Real.log t))) := by
  have ht0 : 0 < t := by linarith
  have heq : Real.exp (-D / (1/(ε*Real.log t))) = 1/(t^(D*ε)) := by
    simp only [div_eq_mul_inv,one_mul,inv_inv]
    rw [Real.rpow_def_of_pos ht0,← Real.exp_neg]
    congr 1
    ring
  constructor
  · exact heq
  · rw [heq]
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos ht0 _)
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ t) hdepth

/-- T16(c): the corrected comparison series, beginning at t=2, has partial
sums tending to +∞; adding any finite first term leaves this divergence.
This states divergence as a filter limit, not an equality to Mathlib's total tsum. -/
theorem cooling_series_diverges (ε D : ℝ) (hε : 0 < ε)
    (hD : 0 ≤ D*ε) (hdepth : D*ε ≤ 1) (first : ℝ) :
    Tendsto (fun N : ℕ => first + ∑ n ∈ range N,
      Real.exp (-D / (1/(ε*Real.log ((n:ℝ)+2))))) atTop atTop := by
  have hdiv : Tendsto (fun N : ℕ => ∑ n ∈ range N, 1/((n:ℝ)+2)) atTop atTop := by
    apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => by positivity)).mp
    intro h
    apply Real.not_summable_one_div_natCast
    exact (summable_nat_add_iff 2).mp (by simpa only [Nat.cast_add, Nat.cast_ofNat] using h)
  have hcomp : Tendsto (fun N : ℕ => ∑ n ∈ range N,
      Real.exp (-D / (1/(ε*Real.log ((n:ℝ)+2))))) atTop atTop := by
    apply tendsto_atTop_mono _ hdiv
    intro N
    apply sum_le_sum
    intro n hn
    exact (cooling_term_bound ε D ((n:ℝ)+2) hε (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) hD hdepth).2
  exact (tendsto_const_nhds (x := first)).add_atTop hcomp

/-- Renaming unsampled vertices in the model of Definition 3.
The permutation fixes every observed identity and carries both graph and traits. -/
def Relabeling (D : Data) (H K : State) : Prop :=
  ∃ e : Equiv.Perm Vertex,
    (∀ i ∈ D.sampled, e (s i) = s i) ∧ H.vertices.image e = K.vertices ∧
    H.edges.image (fun edge => edge.image e) = K.edges ∧
    ∀ v ∈ H.vertices, K.trait (e v) = H.trait v

/-- The finite compatible set C, up to renaming unsampled vertices (Definition
3, p. 155). A finite index type lists every class once, with no further
restriction on unsampled number, degree or trait. -/
def EnumeratesCompatible {X : Type*} (D : Data) (repr : X → State) : Prop :=
  (∀ x, Compatible D (repr x)) ∧
  (∀ H, Compatible D H → ∃ x, Relabeling D H (repr x)) ∧
  ∀ x y, Relabeling D (repr x) (repr y) → x = y

/-- Proposal support on C from the corrected graph and trait mechanisms,
Web Appendixes 1--2, with names of unobserved vertices quotiented out. -/
def QuotientProposal {X : Type*} (D : Data) (repr : X → State) (x y : X) : Prop :=
  ∃ H K, Relabeling D (repr x) H ∧ Relabeling D (repr y) K ∧ Proposal D true H K

/-- The fixed transition proposal K of Web Appendix 1, p. 1: finite stochastic
rows and full support for the corrected mechanisms, independent of temperature. -/
def ProposalKernel {X : Type*} [Fintype X] (D : Data) (repr : X → State)
    (K : X → X → ℝ) : Prop :=
  (∀ x y, 0 ≤ K x y) ∧ (∀ x, ∑ y, K x y = 1) ∧
  ∀ x y, 0 < K x y ↔ QuotientProposal D repr x y

/-- ρ_t=min{1,exp((J(y)-J(x))/T_t)} (Web Appendix 1, p. 1), with the usual
rejected mass retained at the current state. This is the transition matrix,
not a Metropolis-Hastings ratio or a silently symmetrized proposal. -/
def annealingTransition {X : Type*} [Fintype X] [DecidableEq X]
    (repr : X → State) (K : X → X → ℝ) (ε T : ℝ) (x y : X) : ℝ :=
  let accept := fun a b => min 1 (Real.exp
    ((objective ε (hValue (repr b)) 0 - objective ε (hValue (repr a)) 0)/T))
  K x y * accept x y + if y = x then (∑ b, K x b * (1-accept x b)) else 0

/-- μ_t, the law of the inhomogeneous finite-state chain in Web Appendix 1,
p. 1. Rows are probability distributions and obey the stated transition rule. -/
def ChainLaw {X : Type*} [Fintype X] [DecidableEq X] (repr : X → State)
    (K : X → X → ℝ) (ε T₁ : ℝ) (μ : ℕ → X → ℝ) : Prop :=
  (∀ n x, 0 ≤ μ n x) ∧ (∀ n, ∑ x, μ n x = 1) ∧
  ∀ n y, μ (n+1) y = ∑ x, μ n x *
    annealingTransition repr K ε (cooling ε T₁ n) x y

/-- M, the global-maximizer set for J (Web Appendix pp. 1--2). -/
noncomputable def optimumSet {X : Type*} [Fintype X] (repr : X → State) (ε : ℝ) : Finset X :=
  univ.filter (fun x => ∀ y, objective ε (hValue (repr y)) 0 ≤
    objective ε (hValue (repr x)) 0)


/-- Q=∑ d_i Z_i in the Appendix p. 160, (A1), and correction T15(a). -/
def degreeTraitSum (H : State) : ℝ := ∑ v ∈ H.vertices, (graphDegree H v : ℝ)*z H v

/-- T15(a), T11(c), finite identity: the exact ordered-pair denominator of
equation (1) is Q-Q²/(2m). This is an identity of the quotient expressions;
it does not assign a homophily value at a zero denominator. -/
theorem denominator_sum_identity (H : State) :
    hDenominator H = degreeTraitSum H - (degreeTraitSum H)^2/(2*(H.edges.card:ℝ)) := by
  have hzsq : ∀ v, z H v*z H v = z H v := by
    intro v
    unfold z
    split <;> norm_num
  have hterm : ∀ v w,
      ((if v=w then (graphDegree H v:ℝ) else 0) -
        (graphDegree H v:ℝ)*graphDegree H w/(2*(H.edges.card:ℝ)))*z H v*z H w =
      (if w=v then (graphDegree H v:ℝ)*z H v else 0) -
        ((graphDegree H v:ℝ)*z H v)*((graphDegree H w:ℝ)*z H w)/(2*(H.edges.card:ℝ)) := by
    intro v w
    by_cases hvw : v = w
    · subst w
      simp only [ite_true,sub_mul]
      rw [mul_assoc, hzsq]
      ring
    · simp only [if_neg hvw,if_neg (Ne.symm hvw)]
      ring
  have hdiag : (∑ v ∈ H.vertices, ∑ w ∈ H.vertices,
      if w=v then (graphDegree H v:ℝ)*z H v else 0) = degreeTraitSum H := by
    apply sum_congr rfl
    intro v hv
    simp [hv]
  have hnull : (∑ v ∈ H.vertices, ∑ w ∈ H.vertices,
      ((graphDegree H v:ℝ)*z H v)*((graphDegree H w:ℝ)*z H w)/(2*(H.edges.card:ℝ))) =
      (degreeTraitSum H)^2/(2*(H.edges.card:ℝ)) := by
    simp_rw [← sum_div, ← mul_sum]
    rw [← sum_mul]
    simp only [degreeTraitSum,pow_two]
  unfold hDenominator
  simp_rw [hterm,sum_sub_distrib]
  rw [hdiag,hnull]

/-- Finite incidence counting for Definition 1 (p. 155): every edge in a
simple graph contributes exactly two to the all-vertex degree sum. -/
theorem degree_sum_twice_edges (H : State) (hS : Simple H) :
    (∑ v ∈ H.vertices, graphDegree H v) = 2*H.edges.card := by
  have hg : ∀ v, graphDegree H v = ∑ e ∈ H.edges, if v ∈ e then (1:ℕ) else 0 := by
    intro v
    simp [graphDegree]
  simp_rw [hg]
  rw [sum_comm]
  have he : ∀ e ∈ H.edges, (∑ v ∈ H.vertices, if v ∈ e then (1:ℕ) else 0) = 2 := by
    intro e he
    have hfilter : H.vertices.filter (fun v => v ∈ e) = e := by
      ext v
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(hS e he).2 h,h⟩⟩
    simp only [sum_boole,Nat.cast_id,hfilter]
    exact (hS e he).1
  rw [sum_congr rfl he]
  simp [mul_comm]

/-- T15(a), the trait-specific degree sums partition the all-vertex sum. -/
theorem trait_degree_partition (H : State) :
    traitDegree H true + traitDegree H false = ∑ v ∈ H.vertices, graphDegree H v := by
  unfold traitDegree
  rw [sum_filter,sum_filter,← sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  cases hz : H.trait v <;> simp [hz]

/-- T15(a), binary Z converts Q exactly to the degree total of trait 1. -/
theorem degreeTraitSum_eq (H : State) : degreeTraitSum H = (traitDegree H true:ℝ) := by
  unfold degreeTraitSum traitDegree
  rw [Nat.cast_sum,sum_filter]
  apply sum_congr rfl
  intro v hv
  cases hz : H.trait v <;> simp [z,hz]

/-- T15(a), positive-denominator criterion of equation (1), together with
the exact D_1 D_0/(2m) identity, for a nonempty simple graph. -/
theorem denominator_domain_criterion (H : State) (hS : Simple H) (hm : 0 < H.edges.card) :
    hDenominator H = (traitDegree H true:ℝ)*traitDegree H false/(2*(H.edges.card:ℝ)) ∧
    (HomophilyDefined H ↔ 0 < traitDegree H false ∧ 0 < traitDegree H true) := by
  have htot : (traitDegree H true:ℝ)+traitDegree H false = 2*(H.edges.card:ℝ) := by
    exact_mod_cast ((trait_degree_partition H).trans (degree_sum_twice_edges H hS))
  have hmR : 0 < 2*(H.edges.card:ℝ) := by positivity
  have hid : hDenominator H =
      (traitDegree H true:ℝ)*traitDegree H false/(2*(H.edges.card:ℝ)) := by
    rw [denominator_sum_identity,degreeTraitSum_eq]
    apply (eq_div_iff (ne_of_gt hmR)).2
    field_simp
    nlinarith
  refine ⟨hid,?_⟩
  simp [HomophilyDefined,hm,hid,div_ne_zero_iff,mul_ne_zero_iff,
    ne_of_gt hmR,Nat.pos_iff_ne_zero,and_comm]

/-- T3--T6 finite incidence identity: the degree total of a trait equals the
number of edge endpoints of that trait. Definition 1, p. 155. -/
theorem trait_degree_edge_incidence (H : State) (hS : Simple H) (t : Bool) :
    traitDegree H t = ∑ e ∈ H.edges, (e.filter (fun v => H.trait v = t)).card := by
  have hg : ∀ v, graphDegree H v = ∑ e ∈ H.edges, if v ∈ e then (1:ℕ) else 0 := by
    intro v; simp [graphDegree]
  have ht : ∀ v,
      (if H.trait v = t then graphDegree H v else 0) =
      ∑ e ∈ H.edges, if v ∈ e ∧ H.trait v = t then (1:ℕ) else 0 := by
    intro v
    by_cases hz : H.trait v = t <;> simp [hz,hg]
  unfold traitDegree
  rw [sum_filter]
  simp_rw [ht]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  have hf : H.vertices.filter (fun v => v ∈ e ∧ H.trait v = t) =
      e.filter (fun v => H.trait v = t) := by
    ext v
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(hS e he).2 h.1,h⟩⟩
  simp only [sum_boole,Nat.cast_id,hf]

/-- T3--T6 finite binary-edge counts: D_1=2x+c, D_0=2y+c and m=x+y+c.
These are counts in the actual simple graph of Definition 1, p. 155. -/
theorem binary_edge_counts (H : State) (hS : Simple H) :
    traitDegree H true = 2*edgeCount H true+mixedCount H ∧
    traitDegree H false = 2*edgeCount H false+mixedCount H ∧
    H.edges.card = edgeCount H true+edgeCount H false+mixedCount H := by
  have he : ∀ e ∈ H.edges, ∀ t : Bool,
      (e.filter (fun v => H.trait v = t)).card =
      2*(if ∀ v ∈ e, H.trait v = t then (1:ℕ) else 0) +
        (if (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false) then 1 else 0) := by
    intro e he t
    obtain ⟨v,w,hne,rfl⟩ := card_eq_two.mp (hS e he).1
    cases hv : H.trait v <;> cases hw : H.trait w <;> cases t <;> simp [hv,hw,hne]
  have hc : ∀ e ∈ H.edges, (1:ℕ) =
      (if ∀ v ∈ e, H.trait v = true then 1 else 0) +
      (if ∀ v ∈ e, H.trait v = false then 1 else 0) +
      (if (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false) then 1 else 0) := by
    intro e he
    obtain ⟨v,w,hne,rfl⟩ := card_eq_two.mp (hS e he).1
    cases hv : H.trait v <;> cases hw : H.trait w <;> simp [hv,hw]
  have hdeg : ∀ t, traitDegree H t = 2*edgeCount H t+mixedCount H := by
    intro t
    rw [trait_degree_edge_incidence H hS t,sum_congr rfl (fun e he' => he e he' t)]
    rw [sum_add_distrib,← mul_sum]
    simp [edgeCount,mixedCount]
  refine ⟨hdeg true,hdeg false,?_⟩
  have hsum := sum_congr (s₁ := H.edges) rfl hc
  simpa [sum_add_distrib,edgeCount,mixedCount] using hsum

/-- T15(d): the hypotheses of Result 2 imply positive sampled degree in both
trait classes, and those of Result 3 imply a nonempty nonseed average.
Definitions 1--2 and Results 2--3, p. 155. -/
theorem result_domain_conditions (D : Data) (hD : Admissible D) :
    ((∃ i ∈ D.sampled, ∃ j ∈ D.sampled,
      recruitmentDegree D i < D.degree i ∧ recruitmentDegree D j < D.degree j ∧
      D.trait i ≠ D.trait j) →
      0 < sampledTraitDegree D false ∧ 0 < sampledTraitDegree D true) ∧
    ((∃ j ∈ nonseeds D, recruitmentDegree D (D.parent j) < D.degree (D.parent j)) →
      D.seeds.card < D.sampled.card) := by
  constructor
  · rintro ⟨i,hi,j,hj,hdi,hdj,hz⟩
    have hiP : 0 < D.degree i := lt_of_le_of_lt (Nat.zero_le _) hdi
    have hjP : 0 < D.degree j := lt_of_le_of_lt (Nat.zero_le _) hdj
    have hbound : ∀ k ∈ D.sampled, D.degree k ≤ sampledTraitDegree D (D.trait k) := by
      intro k hk
      apply single_le_sum (fun a ha => Nat.zero_le _)
      exact mem_filter.mpr ⟨hk,rfl⟩
    cases hiZ : D.trait i <;> cases hjZ : D.trait j
    · exact False.elim (hz (hiZ.trans hjZ.symm))
    · constructor
      · simpa [hiZ] using lt_of_lt_of_le hiP (hbound i hi)
      · simpa [hjZ] using lt_of_lt_of_le hjP (hbound j hj)
    · constructor
      · simpa [hjZ] using lt_of_lt_of_le hjP (hbound j hj)
      · simpa [hiZ] using lt_of_lt_of_le hiP (hbound i hi)
    · exact False.elim (hz (hiZ.trans hjZ.symm))
  · rintro ⟨j,hj,hspare⟩
    have hpos : 0 < (nonseeds D).card := card_pos.mpr ⟨j,hj⟩
    rw [nonseeds,card_sdiff_of_subset hD.1] at hpos
    omega

/-- T16(c), finite harmonic comparison: the sum from t=2 to N is at least
log((N+1)/2). This fixed-N inequality is the integral comparison behind the
display's unbounded harmonic tail (Web Appendix p. 2, corrected display (2)). -/
theorem harmonic_tail_log_bound (N : ℕ) (hN : 1 ≤ N) :
    Real.log (((N:ℝ)+1)/2) ≤ ∑ t ∈ Icc 2 N, 1/(t:ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    have hn : (0:ℝ) < (N:ℝ)+1 := by positivity
    have hn2 : (0:ℝ) < (N:ℝ)+2 := by positivity
    have hstep := Real.log_le_sub_one_of_pos (div_pos hn2 hn)
    have hratio : ((N:ℝ)+2)/((N:ℝ)+1)-1 = 1/((N:ℝ)+1) := by
      field_simp
      ring
    rw [hratio, Real.log_div (ne_of_gt hn2) (ne_of_gt hn)] at hstep
    have hlogN : Real.log (((N:ℝ)+1)/2) = Real.log ((N:ℝ)+1)-Real.log 2 :=
      Real.log_div (ne_of_gt hn) (by norm_num)
    have hlogN1 : Real.log (((N:ℝ)+2)/2) = Real.log ((N:ℝ)+2)-Real.log 2 :=
      Real.log_div (ne_of_gt hn2) (by norm_num)
    rw [hlogN] at ih
    rw [sum_Icc_succ_top (by omega : 2 ≤ N+1)]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show (N:ℝ)+1+1 = (N:ℝ)+2 by ring,hlogN1]
    linarith

/-- "The least value of J along the path is J(x) - D" (Web Appendix
p. 2, Proposition 1 proof). In addition to the lower bound, some path vertex
must attain that exact value; a singleton path has exact depth zero. -/
def CommunicatesAtDepth {X : Type*} [Fintype X] (repr : X → State)
    (K : X → X → ℝ) (ε : ℝ) (x : X) (d : ℝ) : Prop :=
  0 ≤ d ∧ ∃ path : List X, path.head? = some x ∧
    (∃ y ∈ optimumSet repr ε, path.getLast? = some y) ∧
    path.IsChain (fun a b => 0 < K a b) ∧
    (∀ y ∈ path, objective ε (hValue (repr x)) 0-d ≤ objective ε (hValue (repr y)) 0) ∧
    ∃ y ∈ path, objective ε (hValue (repr y)) 0 = objective ε (hValue (repr x)) 0-d

/-- "D* [is] the smallest number such that every [state] communicates with M
at depth D*" (Web Appendix p. 2, Proposition 1 proof), literally with a single
common exact depth. This partial object is `none` if no such least common
depth exists. It is not the conventional maximum of individual minimum
barriers, which is a different object. -/
noncomputable def criticalDepth {X : Type*} [Fintype X] (repr : X → State)
    (K : X → X → ℝ) (ε : ℝ) : Option ℝ := by
  classical
  exact if ∃ d, IsLeast {d | ∀ x, CommunicatesAtDepth repr K ε x d} d then
    some (sInf {d | ∀ x, CommunicatesAtDepth repr K ε x d}) else none

/-- T24, finite display (1), for the literal printed D*: if a least common
exact communication depth exists, it is nonnegative, bounded by max J and
1/ε, and satisfies εD*≤1. Existence is an explicit condition, not inferred
from existence of paths at possibly different depths. Web Appendix p. 2. -/
theorem critical_depth_bound {X : Type*} [Fintype X] [Nonempty X]
    (repr : X → State) (K : X → X → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hh : ∀ x, -1 ≤ hValue (repr x)) (d : ℝ)
    (hdepth : IsLeast {d | ∀ x, CommunicatesAtDepth repr K ε x d} d) :
    criticalDepth repr K ε = some d ∧ 0 ≤ d ∧
      d ≤ sSup (Set.range (fun x => objective ε (hValue (repr x)) 0)) ∧
      d ≤ 1/ε ∧ d*ε ≤ 1 := by
  let J := fun x => objective ε (hValue (repr x)) 0
  have hpos : ∀ x, 0 < J x := fun x => (objective_bounds ε _ 0 hε (hh x)).1
  have hupper : ∀ x, J x ≤ 1/ε := fun x => (objective_bounds ε _ 0 hε (hh x)).2.1
  let x₀ : X := Classical.choice inferInstance
  obtain ⟨hd0,path,hhead,hend,hchain,hlevel,y,hy,hmin⟩ := hdepth.1 x₀
  have hdx : d ≤ J x₀ := by
    have := hpos y
    change J y = J x₀-d at hmin
    linarith
  have hbd : BddAbove (Set.range J) := ⟨1/ε,by rintro r ⟨x,rfl⟩; exact hupper x⟩
  have hmaxJ : d ≤ sSup (Set.range J) :=
    le_trans hdx (le_csSup hbd (Set.mem_range_self x₀))
  have hmax : d ≤ 1/ε := le_trans hdx (hupper x₀)
  have hvalue : criticalDepth repr K ε = some d := by
    have hex : ∃ q, IsLeast {q | ∀ x, CommunicatesAtDepth repr K ε x q} q := ⟨d,hdepth⟩
    rw [criticalDepth,if_pos hex,hdepth.csInf_eq]
  exact ⟨hvalue,hd0,hmaxJ,hmax,(le_div_iff₀ hε).mp hmax⟩


/-- T24 finite path lemma: an optimum communicates with the optimum set at
exact depth zero using its singleton path. This verifies the exact minimum
clause of the printed definition, Web Appendix p. 2. -/
theorem optimum_exact_zero_depth {X : Type*} [Fintype X]
    (repr : X → State) (K : X → X → ℝ) (ε : ℝ) (x : X)
    (hx : x ∈ optimumSet repr ε) : CommunicatesAtDepth repr K ε x 0 := by
  refine ⟨le_rfl,[x],rfl,⟨x,hx,rfl⟩,by simp,?_,?_⟩
  · intro y hy
    simp only [List.mem_singleton] at hy
    subst y
    simp
  · exact ⟨x,by simp,by simp⟩

/-- T24 nonvacuity instance: on a one-state space the printed least common
exact depth exists and equals zero, independently of the proposal matrix.
This is a supporting finite instance, not the annealing limit theorem. -/
theorem critical_depth_singleton (repr : Unit → State) (K : Unit → Unit → ℝ)
    (ε : ℝ) : criticalDepth repr K ε = some 0 := by
  have hx : () ∈ optimumSet repr ε := by
    simp only [optimumSet,mem_filter,mem_univ,true_and]
    intro y
    cases y
    exact le_rfl
  have hleast : IsLeast {d | ∀ x, CommunicatesAtDepth repr K ε x d} 0 := by
    refine ⟨?_,?_⟩
    · intro x
      cases x
      exact optimum_exact_zero_depth repr K ε () hx
    · intro d hd
      exact (hd ()).1
  have hex : ∃ q, IsLeast {q | ∀ x, CommunicatesAtDepth repr K ε x q} q := ⟨0,hleast⟩
  rw [criticalDepth,if_pos hex,hleast.csInf_eq]


/-- T11 exact numerical instance of (A1), from P012-E003: both legal completions
have m=3, Q=3, D=3/2 and h1-h2=4/3=2/D. It permits i,j to be joined by a
recruitment edge, as the printed Result 2 does. Appendix p. 160. -/
theorem a1_exact_instance :
    let D : Data := ⟨{1,2},{1},fun _ => 1,id,fun _ => 2,fun i => i == 2⟩
    let H : State := ⟨{s 1,s 2,u 3 0,u 4 0},
      {{s 1,s 2},{s 1,u 3 0},{s 2,u 4 0}},fun v => decide (v = s 2) || decide (v = u 4 0)⟩
    let K := addEdge (addEdge (removeEdge (removeEdge H (s 1) (u 3 0))
      (s 2) (u 4 0)) (s 1) (u 4 0)) (s 2) (u 3 0)
    Admissible D ∧ Compatible D H ∧ Compatible D K ∧
    H.edges.card = 3 ∧ degreeTraitSum H = 3 ∧ hDenominator H = 3/2 ∧
    hDenominator K = 3/2 ∧ homophily H = some (1/3) ∧ homophily K = some (-1) ∧
    hValue H-hValue K = 4/3 ∧ hValue H-hValue K = 2/hDenominator H := by
  norm_num [Admissible,Compatible,Augmented,Simple,nonseeds,sampledVertices,
    recruitmentEdges,recruitmentDegree,graphDegree,addEdge,removeEdge,
    degreeTraitSum,homophily,HomophilyDefined,hValue,hNumerator,hDenominator,
    adjacency,z,s,u]
  decide

/-- Finite structure of the observed forest: G_R without directions is simple
and has n-|M| edges, since every nonseed has exactly one earlier recruiter.
Standing assumptions pp. 154--155; corrections T3--T7. -/
theorem recruitment_skeleton_counts (D : Data) (hD : Admissible D) :
    Simple (recruitmentState D) ∧
    (recruitmentEdges D).card = D.sampled.card-D.seeds.card := by
  have hs : Simple (recruitmentState D) := by
    intro e he
    obtain ⟨j,hj,rfl⟩ := mem_image.mp he
    have hp := hD.2.2.1 j hj
    have hne : s (D.parent j) ≠ s j := by
      intro heq
      have hjp : D.parent j = j := Sum.inl.inj heq
      rw [hjp] at hp
      exact lt_irrefl _ hp.2
    refine ⟨by simp [hne],?_⟩
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact mem_image_of_mem s hp.1
    · exact mem_image_of_mem s (mem_sdiff.mp hj).1
  have hi : Set.InjOn (fun j => ({s (D.parent j),s j} : Finset Vertex)) (nonseeds D) := by
    intro j hj k hk heq
    change ({s (D.parent j),s j} : Finset Vertex) = {s (D.parent k),s k} at heq
    have hjm : s j ∈ ({s (D.parent k),s k} : Finset Vertex) := by rw [← heq]; simp
    have hkm : s k ∈ ({s (D.parent j),s j} : Finset Vertex) := by rw [heq]; simp
    simp only [mem_insert,mem_singleton,s,Sum.inl.injEq] at hjm hkm
    rcases hjm with hjp | hjk
    · rcases hkm with hkp | hkj
      · have htj := (hD.2.2.1 j hj).2
        have htk := (hD.2.2.1 k hk).2
        rw [← hkp] at htj
        rw [← hjp] at htk
        omega
      · exact hkj.symm
    · exact hjk
  refine ⟨hs,?_⟩
  rw [recruitmentEdges,card_image_iff.mpr hi,nonseeds,card_sdiff_of_subset hD.1]

/-- Corrections T3--T7: spare edge ends total ∑d_i-2(n-|M|). Recruitment
degrees count both directions of incidence, rather than only outdegree. -/
theorem spare_total_identity (D : Data) (hD : Admissible D) :
    totalSpare D = (∑ i ∈ D.sampled, D.degree i)-2*(D.sampled.card-D.seeds.card) := by
  have hpoint : ∀ i ∈ D.sampled, D.degree i = recruitmentDegree D i+spare D i := by
    intro i hi
    exact (Nat.add_sub_of_le (hD.2.2.2 i hi)).symm
  have hsum : (∑ i ∈ D.sampled, D.degree i) =
      (∑ i ∈ D.sampled, recruitmentDegree D i)+totalSpare D := by
    rw [sum_congr rfl hpoint,sum_add_distrib]
    rfl
  have hdeg : (∑ i ∈ D.sampled, recruitmentDegree D i) = 2*(recruitmentEdges D).card := by
    have h := degree_sum_twice_edges (recruitmentState D) (recruitment_skeleton_counts D hD).1
    change (∑ v ∈ D.sampled.image s, graphDegree (recruitmentState D) v) = _ at h
    rw [sum_image (by intro i hi j hj h; exact Sum.inl.inj h)] at h
    exact h
  rw [(recruitment_skeleton_counts D hD).2] at hdeg
  omega

/-- The adjacency-row identity used in equation (1), p. 155: on a simple
graph the degree equals the number of its distinct neighbours. -/
theorem degree_eq_neighbor_card (H : State) (hS : Simple H) (v : Vertex) :
    graphDegree H v =
      (H.vertices.filter (fun w => v ≠ w ∧ {v,w} ∈ H.edges)).card := by
  symm
  unfold graphDegree
  apply card_bij (fun w _ => ({v,w} : Finset Vertex))
  · intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).2.2,by simp⟩
  · intro w hw x hx he
    have hwne := (mem_filter.mp hw).2.1
    rcases (pair_edge_eq v w v x).mp he with h | h
    · exact h.2
    · exact False.elim (hwne h.2.symm)
  · intro e he
    obtain ⟨he,hv⟩ := mem_filter.mp he
    obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp (hS e he).1
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl
    · refine ⟨y,mem_filter.mpr ⟨(hS _ he).2 (by simp),hxy,he⟩,rfl⟩
    · refine ⟨x,mem_filter.mpr ⟨(hS _ he).2 (by simp),hxy.symm,?_⟩,?_⟩
      · simpa [Finset.pair_comm] using he
      · exact Finset.pair_comm _ _

/-- Summing the adjacency matrix over a row gives d_i (equation (1), p. 155).
This finite identity retains the ordinary simple-graph hypotheses. -/
theorem adjacency_row_sum (H : State) (hS : Simple H) (v : Vertex) :
    (∑ w ∈ H.vertices, adjacency H v w) = (graphDegree H v : ℝ) := by
  unfold adjacency
  rw [sum_boole]
  exact_mod_cast (degree_eq_neighbor_card H hS v).symm

/-- A zero degree excludes an incident edge in equation (1), p. 155. -/
theorem zero_degree_no_edge (H : State) (v : Vertex) (hd : graphDegree H v = 0)
    (w : Vertex) : {v,w} ∉ H.edges := by
  intro he
  have hm : {v,w} ∈ H.edges.filter (fun e => v ∈ e) := mem_filter.mpr ⟨he,by simp⟩
  have hzero : H.edges.filter (fun e => v ∈ e) = ∅ := card_eq_zero.mp hd
  rw [hzero] at hm
  simp at hm

/-- A trait with degree total zero occurs only at isolated vertices
(Definition 1, p. 155; T15(a)'s correlation boundary). -/
theorem zero_trait_degree (H : State) (t : Bool) (ht : traitDegree H t = 0)
    (v : Vertex) (hv : v ∈ H.vertices) (hz : H.trait v = t) : graphDegree H v = 0 := by
  have hle : graphDegree H v ≤ traitDegree H t := by
    apply single_le_sum (fun w hw => Nat.zero_le _)
    exact mem_filter.mpr ⟨hv,hz⟩
  omega

/-- T15(a), zero-variance boundary: the numerator in (1) is zero whenever
one trait has no edge stubs. This concerns the numerator, not a totalized h. -/
theorem boundary_numerator_zero (H : State) (hS : Simple H) (hm : 0 < H.edges.card)
    (hz : traitDegree H true = 0 ∨ traitDegree H true = 2*H.edges.card) :
    hNumerator H = 0 := by
  rcases hz with hz | hz
  · unfold hNumerator
    apply sum_eq_zero
    intro v hv
    apply sum_eq_zero
    intro w hw
    cases htv : H.trait v
    · simp [z,htv]
    · have hd := zero_trait_degree H true hz v hv htv
      have he := zero_degree_no_edge H v hd w
      simp [adjacency,he,hd]
  · have hzero : traitDegree H false = 0 := by
      have hp := (trait_degree_partition H).trans (degree_sum_twice_edges H hS)
      omega
    have hterm : ∀ v ∈ H.vertices, ∀ w ∈ H.vertices,
        (adjacency H v w - (graphDegree H v:ℝ)*graphDegree H w/(2*(H.edges.card:ℝ))) *
          z H v * z H w =
        adjacency H v w - (graphDegree H v:ℝ)*graphDegree H w/(2*(H.edges.card:ℝ)) := by
      intro v hv w hw
      cases htv : H.trait v
      · have hd := zero_trait_degree H false hzero v hv htv
        have he := zero_degree_no_edge H v hd w
        simp [adjacency,he,hd,z,htv]
      · cases htw : H.trait w
        · have hd := zero_trait_degree H false hzero w hw htw
          have he : {v,w} ∉ H.edges := by
            simpa [Finset.pair_comm] using zero_degree_no_edge H w hd v
          simp [adjacency,he,hd,z,htv,htw]
        · simp [z,htv,htw]
    have htotal : (∑ v ∈ H.vertices, (graphDegree H v:ℝ)) = 2*(H.edges.card:ℝ) := by
      exact_mod_cast degree_sum_twice_edges H hS
    have hmR : (2*(H.edges.card:ℝ)) ≠ 0 := by positivity
    have hformula : hNumerator H = ∑ v ∈ H.vertices, ∑ w ∈ H.vertices,
        (adjacency H v w - (graphDegree H v:ℝ)*graphDegree H w/(2*(H.edges.card:ℝ))) := by
      unfold hNumerator
      apply sum_congr rfl
      intro v hv
      apply sum_congr rfl
      intro w hw
      exact hterm v hv w hw
    rw [hformula]
    simp_rw [sum_sub_distrib]
    have hrows : (∑ v ∈ H.vertices, ∑ w ∈ H.vertices, adjacency H v w) =
        ∑ v ∈ H.vertices, (graphDegree H v:ℝ) := by
      apply sum_congr rfl
      intro v hv
      exact adjacency_row_sum H hS v
    rw [hrows]
    simp_rw [← sum_div,← mul_sum,← sum_mul]
    rw [htotal]
    field_simp
    ring

/-- T15(a): the exact denominator identity, its positivity criterion, and the
0/0 boundary cases of Definition 1. m=0 is excluded from the identity.
Correction P012-E006, p. 155. -/
theorem homophily_domain (H : State) (hS : Simple H) (hm : 0 < H.edges.card) :
    hDenominator H = (traitDegree H true : ℝ) -
      (traitDegree H true : ℝ)^2 / (2*(H.edges.card : ℝ)) ∧
    hDenominator H = (traitDegree H true : ℝ) * traitDegree H false /
      (2*(H.edges.card : ℝ)) ∧
    (0 < hDenominator H ↔ 0 < traitDegree H false ∧ 0 < traitDegree H true) ∧
    (HomophilyDefined H ↔ 0 < traitDegree H false ∧ 0 < traitDegree H true) ∧
    (traitDegree H true = 0 ∨ traitDegree H true = 2*H.edges.card →
      hNumerator H = 0 ∧ hDenominator H = 0) := by
  have hfirst : hDenominator H = (traitDegree H true : ℝ) -
      (traitDegree H true : ℝ)^2 / (2*(H.edges.card : ℝ)) := by
    rw [denominator_sum_identity,degreeTraitSum_eq]
  have hid := denominator_domain_criterion H hS hm
  have hmR : 0 < 2*(H.edges.card:ℝ) := by positivity
  refine ⟨hfirst,hid.1,?_,hid.2,?_⟩
  · rw [hid.1,div_pos_iff_of_pos_right hmR,mul_pos_iff]
    have hnon0 : (0:ℝ) ≤ traitDegree H false := Nat.cast_nonneg _
    have hnon1 : (0:ℝ) ≤ traitDegree H true := Nat.cast_nonneg _
    simp only [Nat.cast_pos]
    constructor
    · rintro (⟨h1,h0⟩ | ⟨h1,h0⟩)
      · exact ⟨h0,h1⟩
      · exact False.elim (not_lt_of_ge hnon1 h1)
    · rintro ⟨h0,h1⟩
      exact Or.inl ⟨h1,h0⟩
  · intro hz
    refine ⟨boundary_numerator_zero H hS hm hz,?_⟩
    rw [hfirst]
    rcases hz with hz | hz
    · simp [hz]
    · simp only [hz,Nat.cast_mul,Nat.cast_ofNat]
      field_simp
      ring


/-- T15(c): positive observed stub total for a trait supplies a positive
stub total for that trait in every compatible graph (Definition 3, p. 155). -/
theorem sampled_trait_positive_transfer (D : Data) (H : State)
    (hH : Compatible D H) (t : Bool) (ht : 0 < sampledTraitDegree D t) :
    0 < traitDegree H t := by
  have hw : ∃ i ∈ D.sampled, D.trait i = t ∧ 0 < D.degree i := by
    by_contra hw
    push_neg at hw
    have hzero : sampledTraitDegree D t = 0 := by
      apply sum_eq_zero
      intro i hi
      obtain ⟨hi,hz⟩ := mem_filter.mp hi
      have hi0 := hw i hi hz
      omega
    omega
  obtain ⟨i,hi,hz,hd⟩ := hw
  apply lt_of_lt_of_le hd
  rw [← hH.2.2.2.2.2 i hi]
  apply single_le_sum (fun v hv => Nat.zero_le _)
  exact mem_filter.mpr ⟨hH.2.1 (mem_image_of_mem s hi),(hH.2.2.2.1 i hi).trans hz⟩

/-- T15(c), necessary-domain witness: if an observed trait has zero stub
total, the same-trait private-leaf completion has zero total for that trait.
This includes isolated sampled vertices and never assumes both traits occur. -/
theorem leaf_same_zero_trait (D : Data) (hD : Admissible D) (t : Bool)
    (ht : sampledTraitDegree D t = 0) : traitDegree (leafCompletion D true) t = 0 := by
  have howner : ∀ i ∈ D.sampled, D.trait i = t → D.degree i = 0 := by
    intro i hi hz
    have hle : D.degree i ≤ sampledTraitDegree D t := by
      apply single_le_sum (fun j hj => Nat.zero_le _)
      exact mem_filter.mpr ⟨hi,hz⟩
    omega
  apply sum_eq_zero
  intro v hv
  obtain ⟨hv,hz⟩ := mem_filter.mp hv
  cases v with
  | inl i =>
    have hn : Sum.inl i ∉ leafVertices D := by simp [leafVertices,u]
    have hs : Sum.inl i ∈ sampledVertices D := (mem_union.mp hv).resolve_right hn
    have hi : i ∈ D.sampled := by simpa [sampledVertices,s] using hs
    have htrait : D.trait i = t := hz
    exact ((leafCompletion_compatible D hD true).2.2.2.2.2 i hi).trans (howner i hi htrait)
  | inr q =>
    obtain ⟨i,k⟩ := q
    have hn : u i k ∉ sampledVertices D := by simp [sampledVertices,s,u]
    have hs : u i k ∈ leafVertices D := (mem_union.mp hv).resolve_left hn
    obtain ⟨j,hj,hjv⟩ := mem_biUnion.mp hs
    obtain ⟨l,hl,heq⟩ := mem_image.mp hjv
    have hij : j = i ∧ l = k := by simpa [u] using heq
    rcases hij with ⟨hji,hlk⟩
    subst j
    subst l
    have htrait : D.trait i = t := hz
    have hdeg := howner i hj htrait
    simp [spare,hdeg] at hl

/-- T15(b--d): exact observable regularity conditions for Definitions 1, 2 and
4 over the full compatible set. The sets for h and p are qualified separately;
the Result 2 and Result 3 premises supply the respective conditions. p. 155,
correction P012-E006. -/
theorem full_domain_conditions (D : Data) (hD : Admissible D) :
    (∀ H, Compatible D H → HomophilyDefined H) ↔
      0 < sampledTraitDegree D false ∧ 0 < sampledTraitDegree D true := by
  constructor
  · intro h
    have hleaf := leafCompletion_compatible D hD true
    have hd := h (leafCompletion D true) hleaf
    have hstubs := (denominator_domain_criterion (leafCompletion D true) hleaf.1.1 hd.1).2.mp hd
    have hpos : ∀ t : Bool, 0 < sampledTraitDegree D t := by
      intro t
      by_contra ht
      have hzero : sampledTraitDegree D t = 0 := by omega
      have hz := leaf_same_zero_trait D hD t hzero
      cases t
      · rw [hz] at hstubs
        omega
      · rw [hz] at hstubs
        omega
    exact ⟨hpos false,hpos true⟩
  · rintro ⟨h0,h1⟩ H hH
    have h0H := sampled_trait_positive_transfer D H hH false h0
    have h1H := sampled_trait_positive_transfer D H hH true h1
    have hm : 0 < H.edges.card := by
      by_contra hm
      have hcard : H.edges.card = 0 := by omega
      have he : H.edges = ∅ := card_eq_zero.mp hcard
      have hz : traitDegree H true = 0 := by simp [traitDegree,graphDegree,he]
      omega
    exact (denominator_domain_criterion H hH.1.1 hm).2.mpr ⟨h0H,h1H⟩


/-- T24 finite lemma (iii): every compatible graph has at most S unsampled
vertices. This is the incidence bound underlying finiteness up to names;
it is not a finiteness assertion for the infinite set of all labelings. -/
theorem unsampled_card_bound (D : Data) (H : State) (hD : Admissible D)
    (hH : Compatible D H) : (unsampled D H).card ≤ totalSpare D := by
  let N : ℕ → Finset Vertex := fun i =>
    (unsampled D H).filter (fun v => {s i,v} ∈ H.edges)
  let F : ℕ → Finset (Finset Vertex) := fun i =>
    (H.edges \ recruitmentEdges D).filter (fun e => s i ∈ e)
  have hF : ∀ i ∈ D.sampled, (F i).card = spare D i := by
    intro i hi
    have hsub : (recruitmentEdges D).filter (fun e => s i ∈ e) ⊆
        H.edges.filter (fun e => s i ∈ e) := by
      intro e he
      obtain ⟨he,hiE⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨hH.2.2.1 he,hiE⟩
    dsimp [F]
    have hfilter : (H.edges \ recruitmentEdges D).filter (fun e => s i ∈ e) =
        H.edges.filter (fun e => s i ∈ e) \ (recruitmentEdges D).filter (fun e => s i ∈ e) := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_sdiff]
      tauto
    rw [hfilter,card_sdiff_of_subset hsub]
    change graphDegree H (s i)-recruitmentDegree D i = spare D i
    rw [hH.2.2.2.2.2 i hi]
    rfl
  have hN : ∀ i ∈ D.sampled, (N i).card ≤ spare D i := by
    intro i hi
    rw [← hF i hi]
    apply card_le_card_of_injOn (fun v => ({s i,v} : Finset Vertex))
    · intro v hv
      obtain ⟨hv,he⟩ := mem_filter.mp hv
      refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨he,?_⟩,by simp⟩
      intro hr
      have hs : {s i,v} ⊆ sampledVertices D :=
        ((recruitment_skeleton_counts D hD).1 _ hr).2
      exact (mem_sdiff.mp hv).2 (hs (by simp))
    · intro v hv w hw he
      rcases (pair_edge_eq (s i) v (s i) w).mp he with h | h
      · exact h.2
      · exfalso
        apply (mem_sdiff.mp (mem_filter.mp hv).1).2
        rw [h.2]
        exact mem_image_of_mem s hi
  have hcover : unsampled D H ⊆ D.sampled.biUnion N := by
    intro v hv
    obtain ⟨hvV,hvNot⟩ := mem_sdiff.mp hv
    obtain ⟨i,hi,he⟩ := hH.2.2.2.2.1 v hvV hvNot
    exact mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨hv,he⟩⟩
  calc
    (unsampled D H).card ≤ (D.sampled.biUnion N).card := card_le_card hcover
    _ ≤ ∑ i ∈ D.sampled, (N i).card := card_biUnion_le
    _ ≤ totalSpare D := sum_le_sum hN


/-- T3--T6: each trait-1 edge contributes two to the ordered adjacency sum
in (1). This counts the actual graph, rather than assuming the reduction.
Definition 1, p. 155; Appendix p. 160 (A1). -/
theorem ordered_trait_adjacency (H : State) (hS : Simple H) :
    (∑ v ∈ H.vertices, ∑ w ∈ H.vertices, adjacency H v w*z H v*z H w) =
      2*(edgeCount H true : ℝ) := by
  let F : State := ⟨H.vertices.filter (fun v => H.trait v = true),
    H.edges.filter (fun e => ∀ v ∈ e, H.trait v = true),H.trait⟩
  have hF : Simple F := by
    intro e he
    obtain ⟨he,hze⟩ := mem_filter.mp he
    refine ⟨(hS e he).1,?_⟩
    intro v hv
    exact mem_filter.mpr ⟨(hS e he).2 hv,hze v hv⟩
  have hA : ∀ v ∈ F.vertices, ∀ w ∈ F.vertices, adjacency F v w = adjacency H v w := by
    intro v hv w hw
    have hp : ∀ a ∈ ({v,w} : Finset Vertex), H.trait a = true := by
      intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · exact (mem_filter.mp hv).2
      · exact mem_singleton.mp ha ▸ (mem_filter.mp hw).2
    simp [adjacency,F,hp]
  have hfiltered : (∑ v ∈ H.vertices, ∑ w ∈ H.vertices, adjacency H v w*z H v*z H w) =
      ∑ v ∈ F.vertices, ∑ w ∈ F.vertices, adjacency H v w := by
    change _ = ∑ v ∈ H.vertices.filter (fun v => H.trait v = true),
      ∑ w ∈ H.vertices.filter (fun w => H.trait w = true), adjacency H v w
    simp only [sum_filter]
    apply sum_congr rfl
    intro v hv
    cases hzv : H.trait v
    · simp [z,hzv]
    · simp only [hzv,ite_true,z]
      apply sum_congr rfl
      intro w hw
      cases hzw : H.trait w <;> simp [hzw]
  rw [hfiltered]
  have hsum : (∑ v ∈ F.vertices, ∑ w ∈ F.vertices, adjacency H v w) =
      ∑ v ∈ F.vertices, (graphDegree F v : ℝ) := by
    apply sum_congr rfl
    intro v hv
    rw [← adjacency_row_sum F hF v]
    apply sum_congr rfl
    intro w hw
    exact (hA v hv w hw).symm
  rw [hsum]
  exact_mod_cast degree_sum_twice_edges F hF

/-- T3--T6: reduction of the full ordered numerator to 2x-Q²/(2m).
Equation (1), p. 155, with the ordered-pair convention. -/
theorem numerator_edge_identity (H : State) (hS : Simple H) :
    hNumerator H = 2*(edgeCount H true : ℝ) -
      (degreeTraitSum H)^2/(2*(H.edges.card:ℝ)) := by
  have hterm : ∀ v w, (adjacency H v w-
      (graphDegree H v:ℝ)*graphDegree H w/(2*(H.edges.card:ℝ)))*z H v*z H w =
      adjacency H v w*z H v*z H w -
      ((graphDegree H v:ℝ)*z H v)*((graphDegree H w:ℝ)*z H w)/(2*(H.edges.card:ℝ)) := by
    intro v w; ring
  have hnull : (∑ v ∈ H.vertices, ∑ w ∈ H.vertices,
      ((graphDegree H v:ℝ)*z H v)*((graphDegree H w:ℝ)*z H w)/(2*(H.edges.card:ℝ))) =
      (degreeTraitSum H)^2/(2*(H.edges.card:ℝ)) := by
    simp_rw [← sum_div,← mul_sum]
    rw [← sum_mul]
    simp only [degreeTraitSum,pow_two]
  unfold hNumerator
  simp_rw [hterm,sum_sub_distrib]
  rw [ordered_trait_adjacency H hS,hnull]

/-- T6(i): equation (1) equals φ(x,y,c), with the exact positive denominator,
for every simple graph with positive degree totals of both binary traits.
This is the graph-level identity used in the corrected homophily bounds. -/
theorem graph_homophily_formula (H : State) (hS : Simple H)
    (h0 : 0 < traitDegree H false) (h1 : 0 < traitDegree H true) :
    0 < H.edges.card ∧
    hDenominator H = ((2*(edgeCount H true:ℝ)+mixedCount H)*
      (2*(edgeCount H false:ℝ)+mixedCount H))/(2*(H.edges.card:ℝ)) ∧
    0 < hDenominator H ∧
    hValue H = phi (edgeCount H true) (edgeCount H false) (mixedCount H) := by
  obtain ⟨hD1,hD0,hm⟩ := binary_edge_counts H hS
  have hm0 : 0 < H.edges.card := by omega
  have hmR : (2*(H.edges.card:ℝ)) ≠ 0 := by positivity
  have hs1 : (traitDegree H true:ℝ) = 2*(edgeCount H true:ℝ)+mixedCount H := by exact_mod_cast hD1
  have hs0 : (traitDegree H false:ℝ) = 2*(edgeCount H false:ℝ)+mixedCount H := by exact_mod_cast hD0
  have hs : (H.edges.card:ℝ) = (edgeCount H true:ℝ)+edgeCount H false+mixedCount H := by exact_mod_cast hm
  have hd := (denominator_domain_criterion H hS hm0).1
  have hdpos : 0 < hDenominator H := by rw [hd]; positivity
  have hq : hDenominator H = ((2*(edgeCount H true:ℝ)+mixedCount H)*
      (2*(edgeCount H false:ℝ)+mixedCount H))/(2*(H.edges.card:ℝ)) := by rw [hd,hs1,hs0]
  refine ⟨hm0,hq,hdpos,?_⟩
  have hp1 : 2*(edgeCount H true:ℝ)+mixedCount H ≠ 0 := by rw [← hs1]; positivity
  have hp0 : 2*(edgeCount H false:ℝ)+mixedCount H ≠ 0 := by rw [← hs0]; positivity
  rw [hValue,numerator_edge_identity H hS,degreeTraitSum_eq,hs1,hq,
    phi_formula _ _ _ hp1 hp0]
  field_simp
  rw [hs]
  ring


/-- T5--T6 finite degree budget: a family of nonrecruitment edges, each
covered by a sampled endpoint in I, has at most the spare degree total of I.
Shared unsampled vertices are allowed. Definition 3(4), p. 155. -/
theorem extra_edge_budget (D : Data) (H : State) (hH : Compatible D H)
    (I : Finset ℕ) (hI : I ⊆ D.sampled) (F : Finset (Finset Vertex))
    (hF : F ⊆ H.edges \ recruitmentEdges D)
    (hcover : ∀ e ∈ F, ∃ i ∈ I, s i ∈ e) : F.card ≤ ∑ i ∈ I, spare D i := by
  let N := fun i => (H.edges \ recruitmentEdges D).filter (fun e => s i ∈ e)
  have hN : ∀ i ∈ I, (N i).card = spare D i := by
    intro i hi
    have hsub : (recruitmentEdges D).filter (fun e => s i ∈ e) ⊆
        H.edges.filter (fun e => s i ∈ e) := fun e he =>
      mem_filter.mpr ⟨hH.2.2.1 (mem_filter.mp he).1,(mem_filter.mp he).2⟩
    have hfilter : N i = (H.edges.filter (fun e => s i ∈ e)) \
        ((recruitmentEdges D).filter (fun e => s i ∈ e)) := by
      ext e
      simp only [N,Finset.mem_filter,Finset.mem_sdiff]
      tauto
    rw [hfilter,card_sdiff_of_subset hsub]
    change graphDegree H (s i)-recruitmentDegree D i = spare D i
    rw [hH.2.2.2.2.2 i (hI hi)]
    rfl
  have hc : F ⊆ I.biUnion N := by
    intro e he
    obtain ⟨i,hi,hie⟩ := hcover e he
    exact mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨hF he,hie⟩⟩
  calc
    F.card ≤ (I.biUnion N).card := card_le_card hc
    _ ≤ ∑ i ∈ I, (N i).card := card_biUnion_le
    _ = ∑ i ∈ I, spare D i := sum_congr rfl hN

/-- T5--T6: recruitment edges of any selected type are compulsory; every
additional edge of that type spends a sampled spare degree. This is the
finite counting argument behind the corrected homophily inequalities. -/
theorem compatible_filtered_edge_bounds (D : Data) (H : State)
    (hH : Compatible D H) (I : Finset ℕ) (hI : I ⊆ D.sampled)
    (P : Finset Vertex → Prop) [DecidablePred P]
    (hcover : ∀ e ∈ H.edges, P e → ∃ i ∈ I, s i ∈ e) :
    ((recruitmentEdges D).filter P).card ≤ (H.edges.filter P).card ∧
    (H.edges.filter P).card ≤ ((recruitmentEdges D).filter P).card + ∑ i ∈ I, spare D i := by
  have hsub : (recruitmentEdges D).filter P ⊆ H.edges.filter P := by
    intro e he
    exact mem_filter.mpr ⟨hH.2.2.1 (mem_filter.mp he).1,(mem_filter.mp he).2⟩
  let F := (H.edges.filter P) \ (recruitmentEdges D).filter P
  have hF : F ⊆ H.edges \ recruitmentEdges D := by
    intro e he
    obtain ⟨he,hr⟩ := mem_sdiff.mp he
    obtain ⟨he,hp⟩ := mem_filter.mp he
    exact mem_sdiff.mpr ⟨he,fun h => hr (mem_filter.mpr ⟨h,hp⟩)⟩
  have hc : ∀ e ∈ F, ∃ i ∈ I, s i ∈ e := by
    intro e he
    obtain ⟨he,hp⟩ := mem_filter.mp (mem_sdiff.mp he).1
    exact hcover e he hp
  have hb := extra_edge_budget D H hH I hI F hF hc
  have hcard : F.card = (H.edges.filter P).card-((recruitmentEdges D).filter P).card :=
    card_sdiff_of_subset hsub
  have hle := card_le_card hsub
  exact ⟨hle,by omega⟩

/-- T6(ii): the actual counts of any compatible graph satisfy a≤x≤a+S_1,
b≤y≤b+S_0 and c_R≤c≤c_R+S. These bounds quantify over all augmented graphs,
without fixing unsampled number, labels, degree or trait. Definition 3 p. 155. -/
theorem compatible_edge_counts (D : Data) (H : State) (hD : Admissible D)
    (hH : Compatible D H) :
    a D ≤ edgeCount H true ∧ edgeCount H true ≤ a D+traitSpare D true ∧
    b D ≤ edgeCount H false ∧ edgeCount H false ≤ b D+traitSpare D false ∧
    cR D ≤ mixedCount H ∧ mixedCount H ≤ cR D+totalSpare D := by
  have hAgree : ∀ e ∈ recruitmentEdges D, ∀ v ∈ e,
      H.trait v = (recruitmentState D).trait v := by
    intro e he v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp (recruitment_edge_sampled D hD e he hv)
    exact hH.2.2.2.1 i hi
  have hmono : ∀ t : Bool,
      (recruitmentEdges D).filter (fun e => ∀ v ∈ e, H.trait v = t) =
      (recruitmentEdges D).filter (fun e => ∀ v ∈ e, (recruitmentState D).trait v = t) := by
    intro t
    ext e
    simp only [mem_filter]
    constructor
    · intro ⟨he,hz⟩
      exact ⟨he,fun v hv => (hAgree e he v hv).symm.trans (hz v hv)⟩
    · intro ⟨he,hz⟩
      exact ⟨he,fun v hv => (hAgree e he v hv).trans (hz v hv)⟩
  have ht : ∀ t, edgeCount (recruitmentState D) t ≤ edgeCount H t ∧
      edgeCount H t ≤ edgeCount (recruitmentState D) t+traitSpare D t := by
    intro t
    have hcover : ∀ e ∈ H.edges, (∀ v ∈ e, H.trait v = t) →
        ∃ i ∈ D.sampled.filter (fun i => D.trait i = t), s i ∈ e := by
      intro e he hp
      obtain ⟨i,hi,hie⟩ := hH.1.2 e he
      exact ⟨i,mem_filter.mpr ⟨hi,(hH.2.2.2.1 i hi).symm.trans (hp (s i) hie)⟩,hie⟩
    have hb := compatible_filtered_edge_bounds D H hH
      (D.sampled.filter (fun i => D.trait i = t)) (filter_subset _ _)
      (fun e => ∀ v ∈ e, H.trait v = t) hcover
    rw [hmono t] at hb
    exact hb
  have hmix : (recruitmentEdges D).filter (fun e =>
      (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false)) =
      (recruitmentEdges D).filter (fun e =>
      (∃ v ∈ e, (recruitmentState D).trait v = true) ∧
      (∃ v ∈ e, (recruitmentState D).trait v = false)) := by
    ext e
    simp only [mem_filter]
    constructor <;> rintro ⟨he,⟨v,hv,hzv⟩,⟨w,hw,hzw⟩⟩
    · exact ⟨he,⟨v,hv,(hAgree e he v hv).symm.trans hzv⟩,
        ⟨w,hw,(hAgree e he w hw).symm.trans hzw⟩⟩
    · exact ⟨he,⟨v,hv,(hAgree e he v hv).trans hzv⟩,
        ⟨w,hw,(hAgree e he w hw).trans hzw⟩⟩
  have hm := compatible_filtered_edge_bounds D H hH D.sampled (Subset.refl _)
    (fun e => (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false))
    (fun e he _ => hH.1.2 e he)
  rw [hmix] at hm
  exact ⟨(ht true).1,(ht true).2,(ht false).1,(ht false).2,hm.1,hm.2⟩


/-- T3 and T6: the number of private leaf edges is the sum of sampled spare
degrees; their distinct owners and indices prevent duplicates. Corrections
P012-N002–P012-N007, Definition 3 p. 155. -/
theorem leaf_edge_card (D : Data) : (leafEdges D).card = totalSpare D := by
  have hdis : (D.sampled : Set ℕ).PairwiseDisjoint
      (fun i => (range (spare D i)).image (fun k => ({s i,u i k} : Finset Vertex))) := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro e hei hej
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hei
    obtain ⟨l,hl,heq⟩ := mem_image.mp hej
    have hij' : i = j := by
      have h : i = j ∧ k = l := by simpa [pair_edge_eq,s,u] using heq.symm
      exact h.1
    exact hij hij'
  have hinj : ∀ i, Function.Injective (fun k : ℕ => ({s i,u i k} : Finset Vertex)) := by
    intro i k l h
    change ({s i,u i k} : Finset Vertex) = {s i,u i l} at h
    have hu : u i k ∈ ({s i,u i l} : Finset Vertex) := by rw [← h]; simp
    simpa [s,u] using hu
  unfold leafEdges totalSpare
  rw [card_biUnion hdis]
  apply sum_congr rfl
  intro i hi
  rw [card_image_of_injective _ (hinj i),card_range]

/-- T3(b): in the opposite-trait private-leaf completion, the recruitment
same-trait counts stay a,b and every new edge is mixed, so c=c_R+S.
This proves the graph construction's counts, not just a scalar certificate.
Corrections P012-N002–P012-N003; Table 1 p. 158. -/
theorem opposite_leaf_counts (D : Data) (hD : Admissible D) :
    edgeCount (leafCompletion D false) true = a D ∧
    edgeCount (leafCompletion D false) false = b D ∧
    mixedCount (leafCompletion D false) = cR D+totalSpare D := by
  let H := leafCompletion D false
  have hE : ∀ e ∈ leafEdges D, ∃ i ∈ D.sampled, ∃ k ∈ range (spare D i),
      e = {s i,u i k} := by
    intro e he
    obtain ⟨i,hi,hie⟩ := mem_biUnion.mp he
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hie
    exact ⟨i,hi,k,hk,rfl⟩
  have hAgree : ∀ e ∈ recruitmentEdges D, ∀ v ∈ e, H.trait v = (recruitmentState D).trait v := by
    intro e he v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp (recruitment_edge_sampled D hD e he hv)
    rfl
  have hmono : ∀ t : Bool,
      (recruitmentEdges D).filter (fun e => ∀ v ∈ e, H.trait v = t) =
      (recruitmentEdges D).filter (fun e => ∀ v ∈ e, (recruitmentState D).trait v = t) := by
    intro t
    ext e
    simp only [mem_filter]
    constructor
    · intro ⟨he,hz⟩
      exact ⟨he,fun v hv => (hAgree e he v hv).symm.trans (hz v hv)⟩
    · intro ⟨he,hz⟩
      exact ⟨he,fun v hv => (hAgree e he v hv).trans (hz v hv)⟩
  have hmix : (recruitmentEdges D).filter (fun e =>
      (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false)) =
      (recruitmentEdges D).filter (fun e =>
      (∃ v ∈ e, (recruitmentState D).trait v = true) ∧
      (∃ v ∈ e, (recruitmentState D).trait v = false)) := by
    ext e
    simp only [mem_filter]
    constructor <;> rintro ⟨he,⟨v,hv,hzv⟩,⟨w,hw,hzw⟩⟩
    · exact ⟨he,⟨v,hv,(hAgree e he v hv).symm.trans hzv⟩,
        ⟨w,hw,(hAgree e he w hw).symm.trans hzw⟩⟩
    · exact ⟨he,⟨v,hv,(hAgree e he v hv).trans hzv⟩,
        ⟨w,hw,(hAgree e he w hw).trans hzw⟩⟩
  have hleafmono : ∀ t : Bool, (leafEdges D).filter (fun e => ∀ v ∈ e, H.trait v = t) = ∅ := by
    intro t
    apply filter_eq_empty_iff.mpr
    intro e he hz
    obtain ⟨i,hi,k,hk,rfl⟩ := hE e he
    have hz1 := hz (s i) (by simp)
    have hz2 := hz (u i k) (by simp)
    cases hzi : D.trait i <;> cases t <;> simp [H,leafCompletion,s,u,hzi] at hz1 hz2
  have hleafmix : (leafEdges D).filter (fun e =>
      (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false)) = leafEdges D := by
    apply filter_eq_self.mpr
    intro e he
    obtain ⟨i,hi,k,hk,rfl⟩ := hE e he
    cases hzi : D.trait i
    · exact ⟨⟨u i k,by simp,by simp [H,leafCompletion,s,u,hzi]⟩,
        ⟨s i,by simp,by simp [H,leafCompletion,s,hzi]⟩⟩
    · exact ⟨⟨s i,by simp,by simp [H,leafCompletion,s,hzi]⟩,
        ⟨u i k,by simp,by simp [H,leafCompletion,u,hzi]⟩⟩
  have hdis : Disjoint (recruitmentEdges D) (leafEdges D) := by
    apply disjoint_left.mpr
    intro e he hl
    obtain ⟨i,hi,k,hk,rfl⟩ := hE e hl
    have hu := recruitment_edge_sampled D hD _ he (by simp : u i k ∈ ({s i,u i k}:Finset Vertex))
    simpa [sampledVertices,s,u] using hu
  have ht : ∀ t, edgeCount H t = edgeCount (recruitmentState D) t := by
    intro t
    change ((recruitmentEdges D ∪ leafEdges D).filter (fun e => ∀ v ∈ e, H.trait v = t)).card = _
    rw [filter_union,hleafmono t,union_empty,hmono t]
    rfl
  refine ⟨ht true,ht false,?_⟩
  change ((recruitmentEdges D ∪ leafEdges D).filter (fun e =>
      (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false))).card = _
  rw [filter_union,hleafmix,hmix,card_union_of_disjoint
    (hdis.mono_left (filter_subset _ _)),leaf_edge_card]
  rfl


/-- T3: for every admissible RDS data set with the published counts, the
opposite-private-leaf completion is compatible and its defined homophily is
below each printed Table 1 lower endpoint. This is a uniform counterexample
family with explicit n, |M|, degree total and spare total, not guessed Hartford
microdata. Table 1 p. 158; network counts p. 156. -/
theorem table_counterexample (D : Data) (hD : Admissible D)
    (hn : D.sampled.card = 527) (hM : D.seeds.card = 6)
    (hd : ∑ i ∈ D.sampled, D.degree i = 4487) :
    Compatible D (leafCompletion D false) ∧ totalSpare D = 3445 ∧
    a D + b D + cR D = 521 ∧ HomophilyDefined (leafCompletion D false) ∧
    hValue (leafCompletion D false) = hLower D ∧
    hValue (leafCompletion D false) ≤ -1462/1983 ∧
    hValue (leafCompletion D false) ≤ -178409/241987 ∧
    hValue (leafCompletion D false) < -7027/10000 ∧
    hValue (leafCompletion D false) < -6918/10000 ∧
    hValue (leafCompletion D false) < -7179/10000 := by
  let H := leafCompletion D false
  have hH : Compatible D H := leafCompletion_compatible D hD false
  have hS : totalSpare D = 3445 := by
    rw [spare_total_identity D hD,hd,hn,hM]
  have hcounts : a D+b D+cR D = 521 := by
    have h := (binary_edge_counts (recruitmentState D)
      (recruitment_skeleton_counts D hD).1).2.2
    change (recruitmentEdges D).card = a D+b D+cR D at h
    rw [(recruitment_skeleton_counts D hD).2,hn,hM] at h
    omega
  obtain ⟨hx,hy,hc⟩ := opposite_leaf_counts D hD
  obtain ⟨hD1,hD0,hm⟩ := binary_edge_counts H hH.1.1
  have h0 : 0 < traitDegree H false := by
    rw [hD0]
    change 0 < 2*edgeCount (leafCompletion D false) false+mixedCount (leafCompletion D false)
    rw [hy,hc,hS]
    omega
  have h1 : 0 < traitDegree H true := by
    rw [hD1]
    change 0 < 2*edgeCount (leafCompletion D false) true+mixedCount (leafCompletion D false)
    rw [hx,hc,hS]
    omega
  obtain ⟨hm0,hden,hdenpos,hval⟩ := graph_homophily_formula H hH.1.1 h0 h1
  have hdef : HomophilyDefined H := ⟨hm0,ne_of_gt hdenpos⟩
  have hvalue : hValue H = hLower D := by
    simpa only [H,hx,hy,hc,hLower,Nat.cast_add] using hval
  have hv : hValue H = phi (a D) (b D) ((cR D:ℝ)+3445) := by
    simpa only [H,hx,hy,hc,Nat.cast_add,hS,Nat.cast_ofNat] using hval
  have hreal : (a D:ℝ)+(b D:ℝ)+cR D = 521 := by exact_mod_cast hcounts
  have hbound : hValue H ≤ -1462/1983 := by
    rw [hv,phi_formula _ _ _ (by positivity) (by positivity)]
    simpa only [add_assoc] using uniform_leaf_bound _ _ _
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hreal
  have hint : hValue H ≤ -178409/241987 := by
    rw [hv,phi_formula _ _ _ (by positivity) (by positivity)]
    simpa only [add_assoc] using uniform_integer_leaf_bound _ _ _ hcounts
  refine ⟨hH,hS,hcounts,hdef,hvalue,hbound,hint,?_,?_,?_⟩ <;>
    linarith [table_numeric_gaps]


/-- T4: the true lower h endpoint is at most both certified bounds, and has
the specified gaps below the three printed endpoints. A different degree
vector yielding a printed endpoint cannot have degree total 4487. Table 1
p. 158, correction P012-N002; the bound is not asserted to be the exact endpoint. -/
theorem corrected_table_bound (D : Data) (hD : Admissible D)
    (hn : D.sampled.card = 527) (hM : D.seeds.card = 6)
    (hd : ∑ i ∈ D.sampled, D.degree i = 4487)
    (L : ℝ) (hL : IsGLB (hValues D) L) :
    L ≤ -1462/1983 ∧ L ≤ -178409/241987 ∧
    -7027/10000 - L ≥ 685459/19830000 ∧
    -6918/10000 - L ≥ 450803/9915000 ∧
    -7179/10000 - L ≥ 384043/19830000 := by
  obtain ⟨hH,hS,hcounts,hdef,hvalue,hbound,hint,hsex,hcrack,hhome⟩ :=
    table_counterexample D hD hn hM hd
  have hmem : hValue (leafCompletion D false) ∈ hValues D :=
    ⟨leafCompletion D false,hH,by simp [homophily,hdef]⟩
  have hle := hL.1 hmem
  refine ⟨le_trans hle hbound,le_trans hle hint,?_,?_,?_⟩ <;>
    linarith [table_numeric_gaps]


/-- T4's converse: a degree vector whose true lower bound rounds to a printed
Table 1 lower endpoint cannot have total 4487. Therefore it differs at some
sampled vertex from the nomination-network degree vector, and that graph
fails Definition 3's degree-preservation condition. Correction P012-N002. -/
theorem table_degree_converse (D : Data) (Hnom : State) (hD : Admissible D)
    (hn : D.sampled.card = 527) (hM : D.seeds.card = 6)
    (hNom : (∑ i ∈ D.sampled, graphDegree Hnom (s i)) = 4487)
    (L : ℝ) (hL : IsGLB (hValues D) L)
    (hround : ∃ q ∈ ({-7027/10000,-6918/10000,-7179/10000} : Finset ℝ),
      |L-q| ≤ 1/20000) :
    (∑ i ∈ D.sampled, D.degree i) ≠ 4487 ∧
    (∃ i ∈ D.sampled, D.degree i ≠ graphDegree Hnom (s i)) ∧
    ¬ Compatible D Hnom := by
  have htotal : (∑ i ∈ D.sampled, D.degree i) ≠ 4487 := by
    intro hsum
    have hbound := (corrected_table_bound D hD hn hM hsum L hL).1
    obtain ⟨q,hq,hround⟩ := hround
    have hr := (abs_le.mp hround).1
    simp only [mem_insert,mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> linarith
  have hdiff : ∃ i ∈ D.sampled, D.degree i ≠ graphDegree Hnom (s i) := by
    by_contra h
    push_neg at h
    have heq := sum_congr (s₁ := D.sampled) rfl h
    exact htotal (heq.trans hNom)
  refine ⟨htotal,hdiff,?_⟩
  intro hH
  have heq := sum_congr (s₁ := D.sampled) rfl (fun i hi => (hH.2.2.2.2.2 i hi).symm)
  exact htotal (heq.trans hNom)


/-- T6 finite cardinality: private edges indexed by any finite set of sampled
owners have cardinality equal to their spare-degree sum. Private-leaf
construction, corrections P012-N003 and P012-N007, Definition 3 p. 155. -/
theorem private_edge_card (D : Data) (I : Finset ℕ) :
    (I.biUnion (fun i => (range (spare D i)).image
      (fun k => ({s i,u i k} : Finset Vertex)))).card = ∑ i ∈ I, spare D i := by
  have hdis : (I : Set ℕ).PairwiseDisjoint
      (fun i => (range (spare D i)).image (fun k => ({s i,u i k} : Finset Vertex))) := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro e hei hej
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hei
    obtain ⟨l,hl,heq⟩ := mem_image.mp hej
    have h : i = j ∧ k = l := by simpa [pair_edge_eq,s,u] using heq.symm
    exact hij h.1
  have hinj : ∀ i, Function.Injective (fun k : ℕ => ({s i,u i k} : Finset Vertex)) := by
    intro i k l h
    change ({s i,u i k} : Finset Vertex) = {s i,u i l} at h
    have hu : u i k ∈ ({s i,u i l} : Finset Vertex) := by rw [← h]; simp
    simpa [s,u] using hu
  rw [card_biUnion hdis]
  apply sum_congr rfl
  intro i hi
  rw [card_image_of_injective _ (hinj i),card_range]

/-- T6(iv): the same-trait private-leaf completion has counts a+S_1,b+S_0,c_R.
Together with the opposite-trait counts, these are the actual endpoint
witnesses for the corrected homophily bounds. Correction P012-N007. -/
theorem same_leaf_counts (D : Data) (hD : Admissible D) :
    edgeCount (leafCompletion D true) true = a D+traitSpare D true ∧
    edgeCount (leafCompletion D true) false = b D+traitSpare D false ∧
    mixedCount (leafCompletion D true) = cR D := by
  let H := leafCompletion D true
  have hE : ∀ e ∈ leafEdges D, ∃ i ∈ D.sampled, ∃ k ∈ range (spare D i),
      e = {s i,u i k} := by
    intro e he
    obtain ⟨i,hi,hie⟩ := mem_biUnion.mp he
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hie
    exact ⟨i,hi,k,hk,rfl⟩
  have hAgree : ∀ e ∈ recruitmentEdges D, ∀ v ∈ e, H.trait v = (recruitmentState D).trait v := by
    intro e he v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp (recruitment_edge_sampled D hD e he hv)
    rfl
  have hmono : ∀ t : Bool,
      (recruitmentEdges D).filter (fun e => ∀ v ∈ e, H.trait v = t) =
      (recruitmentEdges D).filter (fun e => ∀ v ∈ e, (recruitmentState D).trait v = t) := by
    intro t
    ext e
    simp only [mem_filter]
    constructor
    · intro ⟨he,hz⟩
      exact ⟨he,fun v hv => (hAgree e he v hv).symm.trans (hz v hv)⟩
    · intro ⟨he,hz⟩
      exact ⟨he,fun v hv => (hAgree e he v hv).trans (hz v hv)⟩
  have hmix : (recruitmentEdges D).filter (fun e =>
      (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false)) =
      (recruitmentEdges D).filter (fun e =>
      (∃ v ∈ e, (recruitmentState D).trait v = true) ∧
      (∃ v ∈ e, (recruitmentState D).trait v = false)) := by
    ext e
    simp only [mem_filter]
    constructor <;> rintro ⟨he,⟨v,hv,hzv⟩,⟨w,hw,hzw⟩⟩
    · exact ⟨he,⟨v,hv,(hAgree e he v hv).symm.trans hzv⟩,
        ⟨w,hw,(hAgree e he w hw).symm.trans hzw⟩⟩
    · exact ⟨he,⟨v,hv,(hAgree e he v hv).trans hzv⟩,
        ⟨w,hw,(hAgree e he w hw).trans hzw⟩⟩
  have hleafmono : ∀ t : Bool, (leafEdges D).filter (fun e => ∀ v ∈ e, H.trait v = t) =
      (D.sampled.filter (fun i => D.trait i = t)).biUnion
        (fun i => (range (spare D i)).image (fun k => ({s i,u i k}:Finset Vertex))) := by
    intro t
    ext e
    constructor
    · intro he
      obtain ⟨he,hz⟩ := mem_filter.mp he
      obtain ⟨i,hi,k,hk,rfl⟩ := hE e he
      have hzi : D.trait i = t := hz (s i) (by simp)
      exact mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨hi,hzi⟩,mem_image.mpr ⟨k,hk,rfl⟩⟩
    · intro he
      obtain ⟨i,hi,hie⟩ := mem_biUnion.mp he
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hie
      refine mem_filter.mpr ⟨mem_biUnion.mpr
        ⟨i,(mem_filter.mp hi).1,mem_image.mpr ⟨k,hk,rfl⟩⟩,?_⟩
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact (mem_filter.mp hi).2
      · rw [mem_singleton.mp hv]
        simpa [H,leafCompletion,u] using (mem_filter.mp hi).2
  have hleafmix : (leafEdges D).filter (fun e =>
      (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false)) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro e he hz
    obtain ⟨i,hi,k,hk,rfl⟩ := hE e he
    cases hzi : D.trait i <;> simp [H,leafCompletion,s,u,hzi] at hz
  have hdis : Disjoint (recruitmentEdges D) (leafEdges D) := by
    apply disjoint_left.mpr
    intro e he hl
    obtain ⟨i,hi,k,hk,rfl⟩ := hE e hl
    have hu := recruitment_edge_sampled D hD _ he (by simp : u i k ∈ ({s i,u i k}:Finset Vertex))
    simpa [sampledVertices,s,u] using hu
  have ht : ∀ t, edgeCount H t = edgeCount (recruitmentState D) t+traitSpare D t := by
    intro t
    change ((recruitmentEdges D ∪ leafEdges D).filter (fun e => ∀ v ∈ e, H.trait v = t)).card = _
    rw [filter_union,card_union_of_disjoint (hdis.mono (filter_subset _ _) (filter_subset _ _)),
      hleafmono t,hmono t,private_edge_card]
    rfl
  refine ⟨ht true,ht false,?_⟩
  change ((recruitmentEdges D ∪ leafEdges D).filter (fun e =>
      (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false))).card = _
  rw [filter_union,hleafmix,union_empty,hmix]
  rfl


/-- T5: the corrected lower h bound for general admissible data is sharp,
including when only the attaining completion is nondegenerate. It specializes
to c_R+3445 for the Hartford totals. Correction P012-N003, Table 1 p. 158. -/
theorem exact_h_lower (D : Data) (hD : Admissible D)
    (hreg : 0 < totalSpare D ∨
      (0 < 2*a D + cR D ∧ 0 < 2*b D + cR D)) :
    IsLeast (hValues D) (hLower D) ∧
    Compatible D (leafCompletion D false) ∧
    homophily (leafCompletion D false) = some (hLower D) := by
  let H₀ := leafCompletion D false
  have hH₀ : Compatible D H₀ := leafCompletion_compatible D hD false
  obtain ⟨hx,hy,hc⟩ := opposite_leaf_counts D hD
  obtain ⟨hD1,hD0,hm⟩ := binary_edge_counts H₀ hH₀.1.1
  have hstub1 : 0 < 2*a D+cR D+totalSpare D := by rcases hreg with hs | ⟨hs1,hs0⟩ <;> omega
  have hstub0 : 0 < 2*b D+cR D+totalSpare D := by rcases hreg with hs | ⟨hs1,hs0⟩ <;> omega
  have ht1 : 0 < traitDegree H₀ true := by
    rw [hD1]
    change 0 < 2*edgeCount (leafCompletion D false) true+mixedCount (leafCompletion D false)
    rw [hx,hc]
    omega
  have ht0 : 0 < traitDegree H₀ false := by
    rw [hD0]
    change 0 < 2*edgeCount (leafCompletion D false) false+mixedCount (leafCompletion D false)
    rw [hy,hc]
    omega
  obtain ⟨hm0,hden,hdenpos,hval⟩ := graph_homophily_formula H₀ hH₀.1.1 ht0 ht1
  have hdef : HomophilyDefined H₀ := ⟨hm0,ne_of_gt hdenpos⟩
  have hvalue : hValue H₀ = hLower D := by
    simpa only [H₀,hx,hy,hc,hLower,Nat.cast_add] using hval
  have hsome : homophily H₀ = some (hLower D) := by simp [homophily,hdef,hvalue]
  refine ⟨⟨⟨H₀,hH₀,hsome⟩,?_⟩,hH₀,hsome⟩
  intro r hr
  obtain ⟨H,hH,hhom⟩ := hr
  have hdefH : HomophilyDefined H := by
    by_contra h
    simp [homophily,h] at hhom
  have hvr : hValue H = r := (show HomophilyDefined H ∧ hValue H = r by simpa [homophily] using hhom).2
  obtain ⟨ht0,ht1⟩ := (denominator_domain_criterion H hH.1.1 hdefH.1).2.mp hdefH
  have hvalH := (graph_homophily_formula H hH.1.1 ht0 ht1).2.2.2
  obtain ⟨ha,hA,hb,hB,hcr,hC⟩ := compatible_edge_counts D H hD hH
  have haR : (a D:ℝ) ≤ edgeCount H true := by exact_mod_cast ha
  have hbR : (b D:ℝ) ≤ edgeCount H false := by exact_mod_cast hb
  have hcR : (mixedCount H:ℝ) ≤ (cR D:ℝ)+totalSpare D := by exact_mod_cast hC
  have hs1 : (0:ℝ) < 2*(a D:ℝ)+cR D+totalSpare D := by exact_mod_cast hstub1
  have hs0 : (0:ℝ) < 2*(b D:ℝ)+cR D+totalSpare D := by exact_mod_cast hstub0
  have hxpos : (0:ℝ) < 2*(edgeCount H true:ℝ)+mixedCount H := by
    have h := (binary_edge_counts H hH.1.1).1
    exact_mod_cast (h ▸ ht1)
  have hypos : (0:ℝ) < 2*(edgeCount H false:ℝ)+mixedCount H := by
    have h := (binary_edge_counts H hH.1.1).2.1
    exact_mod_cast (h ▸ ht0)
  rw [← hvr,hvalH]
  unfold hLower
  calc
    phi (a D) (b D) ((cR D:ℝ)+totalSpare D) ≤
        phi (a D) (edgeCount H false) ((cR D:ℝ)+totalSpare D) :=
      phi_mono_y _ _ _ _ (by positivity) hbR (by linarith) (by linarith)
    _ ≤ phi (edgeCount H true) (edgeCount H false) ((cR D:ℝ)+totalSpare D) :=
      phi_mono_x _ _ _ _ (by positivity) haR (by linarith) (by linarith)
    _ ≤ phi (edgeCount H true) (edgeCount H false) (mixedCount H) :=
      phi_anti_c _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) hcR hxpos (by linarith) hypos (by linarith)


/-- T6: every defined compatible pair has the printed assortativity formula
reduced to φ, the edge-count bounds, the two sharp endpoint bounds, and the
private-leaf attainments. Correction P012-N007 of Web Appendix p. 1. -/
theorem exact_h_region (D : Data) (hD : Admissible D)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true) :
    (∀ H, Compatible D H →
      hDenominator H =
        ((2*(edgeCount H true : ℝ)+mixedCount H)*
          (2*(edgeCount H false : ℝ)+mixedCount H)) /
          (2*((edgeCount H true : ℝ)+edgeCount H false+mixedCount H)) ∧
      0 < hDenominator H ∧
      hValue H = phi (edgeCount H true) (edgeCount H false) (mixedCount H) ∧
      a D ≤ edgeCount H true ∧ edgeCount H true ≤ a D + traitSpare D true ∧
      b D ≤ edgeCount H false ∧ edgeCount H false ≤ b D + traitSpare D false ∧
      cR D ≤ mixedCount H ∧ mixedCount H ≤ cR D + totalSpare D ∧
      hLower D ≤ hValue H ∧ hValue H ≤ hUpper D) ∧
    Compatible D (leafCompletion D false) ∧ Compatible D (leafCompletion D true) ∧
    homophily (leafCompletion D false) = some (hLower D) ∧
    homophily (leafCompletion D true) = some (hUpper D) ∧
    FullHomophilyRegion D (hLower D) (hUpper D) := by
  have hdom : ∀ H, Compatible D H → HomophilyDefined H :=
    (full_domain_conditions D hD).2 ⟨h0,h1⟩
  have hO := leafCompletion_compatible D hD false
  have hS := leafCompletion_compatible D hD true
  obtain ⟨hOx,hOy,hOc⟩ := opposite_leaf_counts D hD
  obtain ⟨hSx,hSy,hSc⟩ := same_leaf_counts D hD
  have hO1 := sampled_trait_positive_transfer D _ hO true h1
  have hO0 := sampled_trait_positive_transfer D _ hO false h0
  have hS1 := sampled_trait_positive_transfer D _ hS true h1
  have hS0 := sampled_trait_positive_transfer D _ hS false h0
  obtain ⟨hOD1,hOD0,hmO⟩ := binary_edge_counts _ hO.1.1
  obtain ⟨hSD1,hSD0,hmS⟩ := binary_edge_counts _ hS.1.1
  rw [hOx,hOc] at hOD1
  rw [hOy,hOc] at hOD0
  rw [hSx,hSc] at hSD1
  rw [hSy,hSc] at hSD0
  have hreg : 0 < totalSpare D ∨ (0 < 2*a D+cR D ∧ 0 < 2*b D+cR D) := by
    by_cases hs : 0 < totalSpare D
    · exact Or.inl hs
    · exact Or.inr ⟨by omega,by omega⟩
  obtain ⟨hleast,hO',hOvalue⟩ := exact_h_lower D hD hreg
  have hvalueS : hValue (leafCompletion D true) = hUpper D := by
    have hf := (graph_homophily_formula _ hS.1.1 hS0 hS1).2.2.2
    simpa only [hSx,hSy,hSc,hUpper,Nat.cast_add] using hf
  have hSvalue : homophily (leafCompletion D true) = some (hUpper D) := by
    simp [homophily,hdom _ hS,hvalueS]
  have hstubO1 : (0:ℝ) < 2*(a D:ℝ)+cR D+totalSpare D := by
    have hn : 0 < 2*a D+cR D+totalSpare D := by omega
    exact_mod_cast hn
  have hstubO0 : (0:ℝ) < 2*(b D:ℝ)+cR D+totalSpare D := by
    have hn : 0 < 2*b D+cR D+totalSpare D := by omega
    exact_mod_cast hn
  have hstubS1 : (0:ℝ) < 2*((a D:ℝ)+traitSpare D true)+cR D := by
    have hn : 0 < 2*(a D+traitSpare D true)+cR D := by omega
    exact_mod_cast hn
  have hstubS0 : (0:ℝ) < 2*((b D:ℝ)+traitSpare D false)+cR D := by
    have hn : 0 < 2*(b D+traitSpare D false)+cR D := by omega
    exact_mod_cast hn
  have hbds : ∀ H, Compatible D H → hLower D ≤ hValue H ∧ hValue H ≤ hUpper D := by
    intro H hH
    have ht1 := sampled_trait_positive_transfer D H hH true h1
    have ht0 := sampled_trait_positive_transfer D H hH false h0
    have hf := (graph_homophily_formula H hH.1.1 ht0 ht1).2.2.2
    obtain ⟨ha,hA,hb,hB,hcr,hC⟩ := compatible_edge_counts D H hD hH
    have hc1 : (0:ℝ) < 2*(edgeCount H true:ℝ)+mixedCount H := by
      exact_mod_cast ((binary_edge_counts H hH.1.1).1 ▸ ht1)
    have hc0 : (0:ℝ) < 2*(edgeCount H false:ℝ)+mixedCount H := by
      exact_mod_cast ((binary_edge_counts H hH.1.1).2.1 ▸ ht0)
    have hbound := count_bounds_imply_h_bounds (a D) (b D)
      ((a D:ℝ)+traitSpare D true) ((b D:ℝ)+traitSpare D false)
      (cR D) ((cR D:ℝ)+totalSpare D) (edgeCount H true) (edgeCount H false) (mixedCount H)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast ha) (by exact_mod_cast hA) (by exact_mod_cast hb) (by exact_mod_cast hB)
      (by exact_mod_cast hcr) (by exact_mod_cast hC)
      (by linarith) (by linarith) hstubS1 hstubS0 hc1 hc0
    simpa only [← hf,hLower,hUpper,Nat.cast_add] using hbound
  refine ⟨?_,hO,hS,hOvalue,hSvalue,⟨hdom,hleast,?_⟩⟩
  · intro H hH
    have ht1 := sampled_trait_positive_transfer D H hH true h1
    have ht0 := sampled_trait_positive_transfer D H hH false h0
    obtain ⟨hm,hd,hpos,hval⟩ := graph_homophily_formula H hH.1.1 ht0 ht1
    have hmc : (H.edges.card:ℝ) = (edgeCount H true:ℝ)+edgeCount H false+mixedCount H := by
      exact_mod_cast (binary_edge_counts H hH.1.1).2.2
    rw [hmc] at hd
    obtain ⟨ha,hA,hb,hB,hcr,hC⟩ := compatible_edge_counts D H hD hH
    exact ⟨hd,hpos,hval,ha,hA,hb,hB,hcr,hC,(hbds H hH).1,(hbds H hH).2⟩
  · refine ⟨⟨leafCompletion D true,hS,hSvalue⟩,?_⟩
    intro r hr
    obtain ⟨H,hH,hhom⟩ := hr
    have hvr : hValue H = r := (show HomophilyDefined H ∧ hValue H = r by simpa [homophily] using hhom).2
    rw [← hvr]
    exact (hbds H hH).2


/-- T7(i): all not-yet-entered children are mandatory susceptible neighbours;
j itself is one, and the matching-child count is at most the child count.
Definition 2, p. 155; corrected closed forms P012-N007. -/
theorem later_children_susceptible (D : Data) (H : State) (hH : Compatible D H)
    (j : ℕ) (hj : j ∈ nonseeds D) :
    (laterChildren D j).image s ⊆ susceptible D H (D.parent j) j ∧
    0 < (laterChildren D j).card ∧ childMatches D j ≤ (laterChildren D j).card := by
  refine ⟨?_,card_pos.mpr ⟨j,mem_filter.mpr ⟨hj,rfl,le_rfl⟩⟩,card_filter_le _ _⟩
  intro v hv
  obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
  obtain ⟨hk,hr,ht⟩ := mem_filter.mp hk
  have he := hH.2.2.1 (mem_image_of_mem (fun k => {s (D.parent k),s k}) hk)
  rw [hr] at he
  refine mem_filter.mpr ⟨hH.2.1 (mem_image_of_mem s (mem_sdiff.mp hk).1),he,?_⟩
  simp [notYetSampled,s,ht]

/-- T7(i): among susceptible neighbours, the recruitment edges fix exactly
the not-yet-entered children. A recruiter's parent entered earlier and cannot
be susceptible at a child's recruitment time. Definition 2, p. 155. -/
theorem susceptible_recruitment_edges (D : Data) (H : State) (hD : Admissible D)
    (hH : Compatible D H) (j : ℕ) (hj : j ∈ nonseeds D) :
    (susceptible D H (D.parent j) j).filter (fun v => {s (D.parent j),v} ∈ recruitmentEdges D) =
      (laterChildren D j).image s := by
  ext v
  constructor
  · intro hv
    obtain ⟨hv,he⟩ := mem_filter.mp hv
    obtain ⟨k,hk,heq⟩ := mem_image.mp he
    have hks := (mem_sdiff.mp hk).1
    have hny := (mem_filter.mp hv).2.2
    rcases (pair_edge_eq _ _ _ _).mp heq with ⟨hp,hv⟩ | ⟨hp,hv⟩
    · have hr : D.parent k = D.parent j := Sum.inl.inj hp
      have ht : D.time j ≤ D.time k := by
        rw [← hv] at hny
        simpa [notYetSampled,s,hks] using hny
      exact mem_image.mpr ⟨k,mem_filter.mpr ⟨hk,hr,ht⟩,hv⟩
    · have hr : k = D.parent j := Sum.inl.inj hv
      have hpk := hD.2.2.1 k hk
      have hpj := hD.2.2.1 j hj
      have ht : D.time (D.parent k) < D.time j := by
        exact lt_trans hpk.2 (by simpa only [hr] using hpj.2)
      rw [← hp] at hny
      have hlate : D.time j ≤ D.time (D.parent k) := by
        simpa [notYetSampled,s,hpk.1] using hny
      omega
  · intro hv
    have hs := (later_children_susceptible D H hH j hj).1 hv
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
    obtain ⟨hk,hr,ht⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hs,?_⟩
    rw [← hr]
    exact mem_image_of_mem _ hk

/-- T7(i): the same-trait count within the compulsory child neighbours is
the observed count a_j; no unsampled trait enters this identity. P012-N007. -/
theorem matching_child_card (D : Data) (H : State) (hD : Admissible D)
    (hH : Compatible D H) (j : ℕ) (hj : j ∈ nonseeds D) :
    (((laterChildren D j).image s).filter
      (fun v => H.trait v = H.trait (s (D.parent j)))).card = childMatches D j := by
  have hr := (hD.2.2.1 j hj).1
  have hfilter : ((laterChildren D j).image s).filter
      (fun v => H.trait v = H.trait (s (D.parent j))) =
      ((laterChildren D j).filter (fun k => D.trait k = D.trait (D.parent j))).image s := by
    rw [filter_image]
    congr 1
    apply filter_congr
    intro k hk
    have hks := (mem_sdiff.mp (mem_filter.mp hk).1).1
    rw [hH.2.2.2.1 k hks,hH.2.2.2.1 (D.parent j) hr]
  rw [hfilter,card_image_of_injective _ (by intro i k h; exact Sum.inl.inj h)]
  rfl

/-- T7(i)--(ii): the susceptible set decomposes into b_j compulsory children
and y_j≤s_r extra neighbours, with q_j≤y_j matching extras. The two sharp
baseline fraction inequalities follow from those actual finite sets. P012-N007. -/
theorem susceptible_decomposition (D : Data) (H : State) (hD : Admissible D)
    (hH : Compatible D H) (j : ℕ) (hj : j ∈ nonseeds D) :
    (laterChildren D j).image s ⊆ susceptible D H (D.parent j) j ∧
    ∃ y q : ℕ, y ≤ spare D (D.parent j) ∧ q ≤ y ∧
      (susceptible D H (D.parent j) j).card = (laterChildren D j).card+y ∧
      (sameSusceptible D H (D.parent j) j).card = childMatches D j+q ∧
      (childMatches D j:ℝ)/((laterChildren D j).card+(spare D (D.parent j):ℝ)) ≤
        ((childMatches D j:ℝ)+q)/((laterChildren D j).card+(y:ℝ)) ∧
      ((childMatches D j:ℝ)+q)/((laterChildren D j).card+(y:ℝ)) ≤
        ((childMatches D j:ℝ)+spare D (D.parent j))/
          ((laterChildren D j).card+(spare D (D.parent j):ℝ)) := by
  let B := (laterChildren D j).image s
  let S := susceptible D H (D.parent j) j
  let E := S \ B
  let P := fun v => H.trait v = H.trait (s (D.parent j))
  have hB := (later_children_susceptible D H hH j hj).1
  have hBc : B.card = (laterChildren D j).card := card_image_of_injective _ (by intro i k h; exact Sum.inl.inj h)
  have hEc : E.card+ B.card = S.card := card_sdiff_add_card_eq_card hB
  have hny : ∀ v ∈ E, {s (D.parent j),v} ∉ recruitmentEdges D := by
    intro v hv he
    have hs := (mem_sdiff.mp hv).1
    have hin : v ∈ S.filter (fun v => {s (D.parent j),v} ∈ recruitmentEdges D) := mem_filter.mpr ⟨hs,he⟩
    rw [susceptible_recruitment_edges D H hD hH j hj] at hin
    exact (mem_sdiff.mp hv).2 hin
  let F := E.image (fun v => ({s (D.parent j),v}:Finset Vertex))
  have hinj : Function.Injective (fun v => ({s (D.parent j),v}:Finset Vertex)) := by
    intro v w h
    rcases (pair_edge_eq _ _ _ _).mp h with h | h
    · exact h.2
    · exact h.2.trans h.1
  have hF : F ⊆ H.edges \ recruitmentEdges D := by
    intro e he
    obtain ⟨v,hv,rfl⟩ := mem_image.mp he
    exact Finset.mem_sdiff.mpr ⟨(mem_filter.mp (Finset.mem_sdiff.mp hv).1).2.1,hny v hv⟩
  have hcover : ∀ e ∈ F, ∃ i ∈ ({D.parent j}:Finset ℕ), s i ∈ e := by
    intro e he
    obtain ⟨v,hv,rfl⟩ := mem_image.mp he
    exact ⟨D.parent j,by simp,by simp⟩
  have hy : E.card ≤ spare D (D.parent j) := by
    have hb := extra_edge_budget D H hH {D.parent j}
      (by intro i hi; rw [mem_singleton.mp hi]; exact (hD.2.2.1 j hj).1) F hF hcover
    simpa [F,card_image_of_injective _ hinj] using hb
  have hq : (E.filter P).card ≤ E.card := card_filter_le _ _
  have hSc : (sameSusceptible D H (D.parent j) j).card = childMatches D j+(E.filter P).card := by
    have hU : B ∪ E = S := union_sdiff_of_subset hB
    have hd : Disjoint (B.filter P) (E.filter P) :=
      disjoint_sdiff_self_right.mono (filter_subset _ _) (filter_subset _ _)
    change (S.filter P).card = _
    rw [← hU,filter_union,card_union_of_disjoint hd]
    rw [matching_child_card D H hD hH j hj]
  have hbpos := (later_children_susceptible D H hH j hj).2.1
  have hab := (later_children_susceptible D H hH j hj).2.2
  have hfrac := susceptible_fraction_bounds (childMatches D j) (laterChildren D j).card
    (spare D (D.parent j)) (E.filter P).card E.card
    (Nat.cast_nonneg _) (by exact_mod_cast hab) (by exact_mod_cast hbpos)
    (Nat.cast_nonneg _) (by exact_mod_cast hy) (Nat.cast_nonneg _) (by exact_mod_cast hq)
  exact ⟨hB,E.card,(E.filter P).card,hy,hq,by change S.card = _; omega,hSc,hfrac⟩


/-- T7(iv): at every recruitment event, the private-leaf construction has
b_j+s_r susceptible neighbours and a_j+s_r matches for same-trait leaves,
or a_j matches for opposite-trait leaves. All events are covered at once.
Definition 2 p. 155; correction P012-N007. -/
theorem leaf_susceptible_counts (D : Data) (hD : Admissible D) (same : Bool)
    (j : ℕ) (hj : j ∈ nonseeds D) :
    (susceptible D (leafCompletion D same) (D.parent j) j).card =
      (laterChildren D j).card+spare D (D.parent j) ∧
    (sameSusceptible D (leafCompletion D same) (D.parent j) j).card =
      childMatches D j+(if same then spare D (D.parent j) else 0) := by
  let H := leafCompletion D same
  let B := (laterChildren D j).image s
  let L := (range (spare D (D.parent j))).image (u (D.parent j))
  let P := fun v => H.trait v = H.trait (s (D.parent j))
  have hH : Compatible D H := leafCompletion_compatible D hD same
  have hr := (hD.2.2.1 j hj).1
  have hS : susceptible D H (D.parent j) j = B ∪ L := by
    ext v
    constructor
    · intro hv
      have he := (mem_filter.mp hv).2.1
      change {s (D.parent j),v} ∈ recruitmentEdges D ∪ leafEdges D at he
      rcases mem_union.mp he with he | he
      · apply mem_union_left
        have hb : v ∈ (susceptible D H (D.parent j) j).filter
            (fun v => {s (D.parent j),v} ∈ recruitmentEdges D) := mem_filter.mpr ⟨hv,he⟩
        rw [susceptible_recruitment_edges D H hD hH j hj] at hb
        exact hb
      · obtain ⟨i,hi,hie⟩ := mem_biUnion.mp he
        obtain ⟨k,hk,hpair⟩ := mem_image.mp hie
        rcases (pair_edge_eq _ _ _ _).mp hpair with ⟨hi,hv⟩ | ⟨hi,hv⟩
        · have hi' : i = D.parent j := Sum.inl.inj hi
          subst i
          exact mem_union_right _ (mem_image.mpr ⟨k,hk,hv⟩)
        · simp [s,u] at hv
    · intro hv
      rcases mem_union.mp hv with hv | hv
      · exact (later_children_susceptible D H hH j hj).1 hv
      · obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
        refine mem_filter.mpr ⟨mem_union_right _
          (mem_biUnion.mpr ⟨D.parent j,hr,mem_image.mpr ⟨k,hk,rfl⟩⟩),?_,?_⟩
        · exact mem_union_right _ (mem_biUnion.mpr ⟨D.parent j,hr,mem_image.mpr ⟨k,hk,rfl⟩⟩)
        · simp [notYetSampled,u]
  have hdis : Disjoint B L := by
    apply disjoint_left.mpr
    intro v hv hl
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    simpa [L,s,u] using hl
  have hBc : B.card = (laterChildren D j).card := card_image_of_injective _ (by intro i k h; exact Sum.inl.inj h)
  have hLc : L.card = spare D (D.parent j) := by
    rw [card_image_of_injective _ (by intro k l h; simpa [u] using h),card_range]
  have hfilter : L.filter P = if same then L else ∅ := by
    cases same
    · change L.filter P = ∅
      apply filter_eq_empty_iff.mpr
      intro v hv hz
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
      cases ht : D.trait (D.parent j) <;> simp [P,H,leafCompletion,s,u,ht] at hz
    · change L.filter P = L
      apply filter_eq_self.mpr
      intro v hv
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
      simp [P,H,leafCompletion,s,u]
  constructor
  · rw [hS,card_union_of_disjoint hdis,hBc,hLc]
  · change ((susceptible D H (D.parent j) j).filter P).card = _
    rw [hS,filter_union,card_union_of_disjoint (hdis.mono (filter_subset _ _) (filter_subset _ _))]
    rw [matching_child_card D H hD hH j hj,hfilter]
    cases same <;> simp [hLc]

/-- T7(iv): both exact closed-form preferential endpoints are attained by
the two compatible private-leaf trait assignments, under n>|M|. P012-N007. -/
theorem leaf_preferential_endpoints (D : Data) (hD : Admissible D)
    (hN : D.seeds.card < D.sampled.card) :
    preferential D (leafCompletion D true) = some (pLower D) ∧
    preferential D (leafCompletion D false) = some (pUpper D) := by
  have hdom := (full_p_domain_conditions D hD).2 hN
  have hterm : ∀ same : Bool, ∀ j ∈ nonseeds D,
      (if (leafCompletion D same).trait (s j) =
        (leafCompletion D same).trait (s (D.parent j)) then (1:ℝ) else 0) -
      (sameSusceptible D (leafCompletion D same) (D.parent j) j).card /
        ((susceptible D (leafCompletion D same) (D.parent j) j).card:ℝ) =
      observedMatch D j - ((childMatches D j:ℝ)+(if same then (spare D (D.parent j):ℝ) else 0))/
        ((laterChildren D j).card+(spare D (D.parent j):ℝ)) := by
    intro same j hj
    obtain ⟨hs,hm⟩ := leaf_susceptible_counts D hD same j hj
    rw [hs,hm,Nat.cast_add,Nat.cast_add]
    cases same <;> simp [leafCompletion,s,observedMatch]
  have hvl : pValue D (leafCompletion D true) = pLower D := by
    unfold pValue pSum pLower
    congr 1
    exact sum_congr rfl (fun j hj => by simpa using hterm true j hj)
  have hvu : pValue D (leafCompletion D false) = pUpper D := by
    unfold pValue pSum pUpper
    congr 1
    exact sum_congr rfl (fun j hj => by simpa using hterm false j hj)
  constructor
  · rw [preferential,if_pos (hdom _ (leafCompletion_compatible D hD true)),hvl]
  · rw [preferential,if_pos (hdom _ (leafCompletion_compatible D hD false)),hvu]


/-- T7: closed-form sharp p bounds and simultaneous private-leaf attainment;
the susceptible decomposition has at most s_r extra neighbours. Correction
P012-N007 of Web Appendix p. 1; equation (2), p. 155. -/
theorem exact_p_region (D : Data) (hD : Admissible D)
    (hN : D.seeds.card < D.sampled.card) :
    (∀ H, Compatible D H → ∀ j ∈ nonseeds D,
      (laterChildren D j).image s ⊆ susceptible D H (D.parent j) j ∧
      ∃ y q : ℕ, y ≤ spare D (D.parent j) ∧ q ≤ y ∧
        (susceptible D H (D.parent j) j).card = (laterChildren D j).card + y ∧
        (sameSusceptible D H (D.parent j) j).card = childMatches D j + q ∧
        (childMatches D j : ℝ) /
          ((laterChildren D j).card + (spare D (D.parent j) : ℝ)) ≤
          ((childMatches D j : ℝ)+q) / ((laterChildren D j).card+(y : ℝ)) ∧
        ((childMatches D j : ℝ)+q) / ((laterChildren D j).card+(y : ℝ)) ≤
          ((childMatches D j : ℝ)+spare D (D.parent j)) /
          ((laterChildren D j).card+(spare D (D.parent j) : ℝ))) ∧
    Compatible D (leafCompletion D true) ∧ Compatible D (leafCompletion D false) ∧
    preferential D (leafCompletion D true) = some (pLower D) ∧
    preferential D (leafCompletion D false) = some (pUpper D) ∧
    FullPreferentialRegion D (pLower D) (pUpper D) := by
  have hdom := (full_p_domain_conditions D hD).2 hN
  have hL := leafCompletion_compatible D hD true
  have hU := leafCompletion_compatible D hD false
  obtain ⟨hl,hu⟩ := leaf_preferential_endpoints D hD hN
  have hcount : 0 < ((nonseeds D).card:ℝ) := by
    exact_mod_cast (hdom _ hL).1
  have hbounds : ∀ H, Compatible D H → pLower D ≤ pValue D H ∧ pValue D H ≤ pUpper D := by
    intro H hH
    have hterms : ∀ j ∈ nonseeds D,
        observedMatch D j-((childMatches D j:ℝ)+spare D (D.parent j))/
          ((laterChildren D j).card+(spare D (D.parent j):ℝ)) ≤
          (if H.trait (s j) = H.trait (s (D.parent j)) then (1:ℝ) else 0) -
          (sameSusceptible D H (D.parent j) j).card/((susceptible D H (D.parent j) j).card:ℝ) ∧
        (if H.trait (s j) = H.trait (s (D.parent j)) then (1:ℝ) else 0) -
          (sameSusceptible D H (D.parent j) j).card/((susceptible D H (D.parent j) j).card:ℝ) ≤
        observedMatch D j-(childMatches D j:ℝ)/
          ((laterChildren D j).card+(spare D (D.parent j):ℝ)) := by
      intro j hj
      obtain ⟨_,y,q,hy,hq,hsc,hmc,hmin,hmax⟩ := susceptible_decomposition D H hD hH j hj
      rw [hsc,hmc,Nat.cast_add,Nat.cast_add,hH.2.2.2.1 j (mem_sdiff.mp hj).1,
        hH.2.2.2.1 (D.parent j) (hD.2.2.1 j hj).1]
      change _ ≤ observedMatch D j-_ ∧ observedMatch D j-_ ≤ _
      exact ⟨sub_le_sub_left hmax _,sub_le_sub_left hmin _⟩
    constructor
    · unfold pLower pValue pSum
      exact div_le_div_of_nonneg_right (sum_le_sum (fun j hj => (hterms j hj).1)) hcount.le
    · unfold pUpper pValue pSum
      exact div_le_div_of_nonneg_right (sum_le_sum (fun j hj => (hterms j hj).2)) hcount.le
  refine ⟨fun H hH j hj => susceptible_decomposition D H hD hH j hj,
    hL,hU,hl,hu,⟨hdom,?_,?_⟩⟩
  · refine ⟨⟨leafCompletion D true,hL,hl⟩,?_⟩
    intro r hr
    obtain ⟨H,hH,hp⟩ := hr
    have hvr : pValue D H = r :=
      (show PreferentialDefined D H ∧ pValue D H = r by simpa [preferential] using hp).2
    rw [← hvr]
    exact (hbounds H hH).1
  · refine ⟨⟨leafCompletion D false,hU,hu⟩,?_⟩
    intro r hr
    obtain ⟨H,hH,hp⟩ := hr
    have hvr : pValue D H = r :=
      (show PreferentialDefined D H ∧ pValue D H = r by simpa [preferential] using hp).2
    rw [← hvr]
    exact (hbounds H hH).2


/-- T23: Figure 1's four exact extrema, each attained; the rectangle contains
all compatible h,p values. Figure 1, p. 156; three-decimal labels are the
roundings of these exact fractions. -/
theorem figure1_extrema :
    Admissible figureData ∧
    FullHomophilyRegion figureData (-5/8) (79/105) ∧
    FullPreferentialRegion figureData (-11/80) (49/120) := by
  obtain ⟨hD,hhl,hhu,hpl,hpu⟩ := figure1_endpoint_arithmetic
  have h0 : 0 < sampledTraitDegree figureData false := by norm_num [sampledTraitDegree,figureData]
  have h1 : 0 < sampledTraitDegree figureData true := by norm_num [sampledTraitDegree,figureData]
  have hN : figureData.seeds.card < figureData.sampled.card := by norm_num [figureData]
  have hhr := (exact_h_region figureData hD h0 h1).2.2.2.2.2
  have hpr := (exact_p_region figureData hD hN).2.2.2.2.2
  exact ⟨hD,by simpa only [hhl,hhu] using hhr,by simpa only [hpl,hpu] using hpr⟩


/-- Definition 4, p. 155: a nonempty set with attained smallest and largest
values is point identified exactly when those two values agree. -/
theorem point_identified_iff_equal_extrema (S : Set ℝ) (L U : ℝ)
    (hL : IsLeast S L) (hU : IsGreatest S U) :
    PointIdentified S ↔ L = U := by
  constructor
  · rintro ⟨r,hr⟩
    have hl : L = r := by simpa only [hr,Set.mem_singleton_iff] using hL.1
    have hu : U = r := by simpa only [hr,Set.mem_singleton_iff] using hU.1
    exact hl.trans hu.symm
  · intro h
    refine ⟨L,?_⟩
    ext x
    rw [Set.mem_singleton_iff]
    constructor
    · intro hx
      have hu := hU.2 hx
      rw [← h] at hu
      exact le_antisymm hu (hL.2 hx)
    · rintro rfl
      exact hL.1

/-- T7 and T22(iv): the preferential interval width is the average of the
nonnegative recruiter spare-degree fractions s_r/(b_j+s_r). Correction P012-N007
and identification criterion P012-E005; equation (2), p. 155. -/
theorem preferential_endpoint_gap (D : Data) :
    pUpper D-pLower D =
      (∑ j ∈ nonseeds D, (spare D (D.parent j):ℝ)/
        ((laterChildren D j).card+(spare D (D.parent j):ℝ))) / (nonseeds D).card := by
  unfold pUpper pLower
  rw [← sub_div,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro j hj
  ring

/-- T22(iv): under a nonempty recruitment sample, the sharp preferential
endpoints agree exactly when every actual recruitment event's recruiter has
zero spare degree. Identification criterion P012-E005, pp. 154--156. -/
theorem preferential_endpoints_equal_iff (D : Data) (hD : Admissible D)
    (hN : D.seeds.card < D.sampled.card) :
    pLower D = pUpper D ↔ ∀ j ∈ nonseeds D, spare D (D.parent j) = 0 := by
  have hL := leafCompletion_compatible D hD true
  have hn : 0 < ((nonseeds D).card:ℝ) := by
    exact_mod_cast (((full_p_domain_conditions D hD).2 hN) _ hL).1
  have hb : ∀ j ∈ nonseeds D,
      (0:ℝ) < (laterChildren D j).card+(spare D (D.parent j):ℝ) := by
    intro j hj
    have hp : (0:ℝ) < (laterChildren D j).card := by
      exact_mod_cast (later_children_susceptible D _ hL j hj).2.1
    exact add_pos_of_pos_of_nonneg hp (Nat.cast_nonneg _)
  constructor
  · intro he j hj
    have hg : pUpper D-pLower D = 0 := by rw [he]; ring
    rw [preferential_endpoint_gap] at hg
    have hs := (div_eq_zero_iff.mp hg).resolve_right hn.ne'
    have hz := (sum_eq_zero_iff_of_nonneg
      (fun k hk => div_nonneg (Nat.cast_nonneg _) (hb k hk).le)).1 hs j hj
    have hs0 := (div_eq_zero_iff.mp hz).resolve_right (hb j hj).ne'
    exact_mod_cast hs0
  · intro hz
    have hg : pUpper D-pLower D = 0 := by
      rw [preferential_endpoint_gap]
      have hs : (∑ j ∈ nonseeds D, (spare D (D.parent j):ℝ)/
          ((laterChildren D j).card+(spare D (D.parent j):ℝ))) = 0 := by
        apply sum_eq_zero
        intro j hj
        rw [hz j hj]
        simp
      rw [hs,zero_div]
    linarith


/-- T22(iv): p alone is point identified exactly when every actual recruiter
has no spare degree. Vertices that never recruit can have spare degree.
Identification headline pp. 154--156, P012-E005. -/
theorem preferential_identification (D : Data) (hD : Admissible D)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (hN : D.seeds.card < D.sampled.card) :
    PointIdentified (pValues D) ↔
      ∀ i ∈ D.sampled, (children D i).Nonempty → D.degree i = recruitmentDegree D i := by
  have hr := (exact_p_region D hD hN).2.2.2.2.2
  rw [point_identified_iff_equal_extrema _ _ _ hr.2.1 hr.2.2,
    preferential_endpoints_equal_iff D hD hN]
  constructor
  · intro hz i hi hc
    obtain ⟨j,hj⟩ := hc
    obtain ⟨hj,hji⟩ := mem_filter.mp hj
    have hs := hz j hj
    rw [hji,spare] at hs
    have hd := hD.2.2.2 i hi
    omega
  · intro he j hj
    have hparent := (hD.2.2.1 j hj).1
    have hc : (children D (D.parent j)).Nonempty :=
      ⟨j,mem_filter.mpr ⟨hj,rfl⟩⟩
    simp only [spare,he (D.parent j) hparent hc,Nat.sub_self]


/-- T22: the binary-trait spare totals partition the full sampled spare total.
Definitions 3--4, p. 155; P012-E005. -/
theorem trait_spare_partition (D : Data) :
    traitSpare D true+traitSpare D false = totalSpare D := by
  unfold traitSpare totalSpare
  rw [sum_filter,sum_filter,← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  cases D.trait i <;> simp

/-- T22: with no observed spare degree, compatibility forces precisely the
recruitment skeleton, with no unsampled vertices or additional edges.
Definition 3(1),(3),(4), p. 155; identification headline pp. 153--156. -/
theorem zero_spare_compatible_unique (D : Data) (hD : Admissible D)
    (hz : ∀ i ∈ D.sampled, D.degree i = recruitmentDegree D i)
    (H : State) (hH : Compatible D H) :
    H.vertices = sampledVertices D ∧ H.edges = recruitmentEdges D ∧
      ∀ v ∈ H.vertices, H.trait v = (recruitmentState D).trait v := by
  have hs : totalSpare D = 0 := by
    unfold totalSpare
    apply sum_eq_zero
    intro i hi
    simp only [spare,hz i hi,Nat.sub_self]
  have hb := extra_edge_budget D H hH D.sampled (Subset.refl _) (H.edges \ recruitmentEdges D)
    (Subset.refl _) (fun e he => hH.1.2 e (mem_sdiff.mp he).1)
  change (H.edges \ recruitmentEdges D).card ≤ totalSpare D at hb
  rw [hs] at hb
  have he : H.edges = recruitmentEdges D :=
    Subset.antisymm (sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (by omega))) hH.2.2.1
  have hv : H.vertices = sampledVertices D := by
    apply Subset.antisymm _ hH.2.1
    intro v hv
    by_contra hn
    obtain ⟨i,hi,hiv⟩ := hH.2.2.2.2.1 v hv hn
    rw [he] at hiv
    exact hn (recruitment_edge_sampled D hD _ hiv (by simp))
  refine ⟨hv,he,?_⟩
  intro v hvm
  rw [hv] at hvm
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hvm
  simpa only [recruitmentState,s] using hH.2.2.2.1 i hi

/-- T22: whenever any sampled spare degree is positive, the sharp homophily
interval has strictly positive width on the full homophily domain. This uses
both endpoint constructions, not a restricted compatible-graph class.
Identification headline pp. 153--156; P012-E005. -/
theorem homophily_endpoints_strict (D : Data) (hD : Admissible D)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (hs : 0 < totalSpare D) : hLower D < hUpper D := by
  have hH := leafCompletion_compatible D hD true
  obtain ⟨hc1,hc0,hcr⟩ := same_leaf_counts D hD
  have hb1 := (binary_edge_counts _ hH.1.1).1
  have hb0 := (binary_edge_counts _ hH.1.1).2.1
  rw [hc1,hcr] at hb1
  rw [hc0,hcr] at hb0
  have hu1 : (0:ℝ) < 2*((a D:ℝ)+traitSpare D true)+cR D := by
    have hn : 0 < 2*(a D+traitSpare D true)+cR D := by
      rw [← hb1]
      exact sampled_trait_positive_transfer D _ hH true h1
    exact_mod_cast hn
  have hu0 : (0:ℝ) < 2*((b D:ℝ)+traitSpare D false)+cR D := by
    have hn : 0 < 2*(b D+traitSpare D false)+cR D := by
      rw [← hb0]
      exact sampled_trait_positive_transfer D _ hH false h0
    exact_mod_cast hn
  have hC : (0:ℝ) < (cR D:ℝ)+totalSpare D := by
    have hp : (0:ℝ) < totalSpare D := by exact_mod_cast hs
    positivity
  have hx : (0:ℝ) < 2*(a D:ℝ)+((cR D:ℝ)+totalSpare D) := by positivity
  have hX : (0:ℝ) < 2*((a D:ℝ)+traitSpare D true)+((cR D:ℝ)+totalSpare D) := by positivity
  have hy : (0:ℝ) < 2*(b D:ℝ)+((cR D:ℝ)+totalSpare D) := by positivity
  have hY : (0:ℝ) < 2*((b D:ℝ)+traitSpare D false)+((cR D:ℝ)+totalSpare D) := by positivity
  have htail := phi_anti_c ((a D:ℝ)+traitSpare D true) ((b D:ℝ)+traitSpare D false)
    (cR D) ((cR D:ℝ)+totalSpare D) (by positivity) (by positivity)
    (le_add_of_nonneg_right (Nat.cast_nonneg _))
    hu1 hX hu0 hY
  have hsplit : 0 < traitSpare D true ∨ 0 < traitSpare D false := by
    have hp := trait_spare_partition D
    omega
  have hstrict : phi (a D) (b D) ((cR D:ℝ)+totalSpare D) <
      phi ((a D:ℝ)+traitSpare D true) ((b D:ℝ)+traitSpare D false)
        ((cR D:ℝ)+totalSpare D) := by
    rcases hsplit with hp | hp
    · have hpR : (0:ℝ) < traitSpare D true := by exact_mod_cast hp
      have hd : ((cR D:ℝ)+totalSpare D)/(2*((a D:ℝ)+traitSpare D true)+((cR D:ℝ)+totalSpare D)) <
          ((cR D:ℝ)+totalSpare D)/(2*(a D:ℝ)+((cR D:ℝ)+totalSpare D)) := by
        apply (div_lt_div_iff₀ hX hx).2
        nlinarith [mul_pos hC hpR]
      have hstep : phi (a D) (b D) ((cR D:ℝ)+totalSpare D) <
          phi ((a D:ℝ)+traitSpare D true) (b D) ((cR D:ℝ)+totalSpare D) := by
        unfold phi
        linarith
      exact lt_of_lt_of_le hstep (phi_mono_y _ _ _ _ hC.le
        (le_add_of_nonneg_right (Nat.cast_nonneg _)) hy hY)
    · have hpR : (0:ℝ) < traitSpare D false := by exact_mod_cast hp
      have hd : ((cR D:ℝ)+totalSpare D)/(2*((b D:ℝ)+traitSpare D false)+((cR D:ℝ)+totalSpare D)) <
          ((cR D:ℝ)+totalSpare D)/(2*(b D:ℝ)+((cR D:ℝ)+totalSpare D)) := by
        apply (div_lt_div_iff₀ hY hy).2
        nlinarith [mul_pos hC hpR]
      have hstep : phi (a D) (b D) ((cR D:ℝ)+totalSpare D) <
          phi (a D) ((b D:ℝ)+traitSpare D false) ((cR D:ℝ)+totalSpare D) := by
        unfold phi
        linarith
      exact lt_of_lt_of_le hstep (phi_mono_x _ _ _ _ hC.le
        (le_add_of_nonneg_right (Nat.cast_nonneg _)) hx hX)
  simpa only [hLower,hUpper,Nat.cast_add] using lt_of_lt_of_le hstrict htail


/-- T22(i--iii): the intended joint identification headline, on the full
defined domain. Both scalar functionals are point identified exactly when
every sampled degree equals its recruitment degree, equivalently when all
compatible graphs are the undirected recruitment skeleton. pp. 153--156. -/
theorem joint_identification (D : Data) (hD : Admissible D)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (hN : D.seeds.card < D.sampled.card) :
    ((PointIdentified (hValues D) ∧ PointIdentified (pValues D)) ↔
      ∀ i ∈ D.sampled, D.degree i = recruitmentDegree D i) ∧
    ((∀ i ∈ D.sampled, D.degree i = recruitmentDegree D i) ↔
      ∀ H, Compatible D H → H.vertices = sampledVertices D ∧
        H.edges = recruitmentEdges D) ∧
    ((∃ i ∈ D.sampled, recruitmentDegree D i < D.degree i) →
      ¬ PointIdentified (hValues D)) ∧
    ((∀ i ∈ D.sampled, D.degree i = recruitmentDegree D i) →
      ∀ H, Compatible D H → H.vertices = (recruitmentState D).vertices ∧
        H.edges = (recruitmentState D).edges ∧
        (∀ v ∈ H.vertices, H.trait v = (recruitmentState D).trait v)) := by
  have hh := (exact_h_region D hD h0 h1).2.2.2.2.2
  have hp := (exact_p_region D hD hN).2.2.2.2.2
  have hnon : (∃ i ∈ D.sampled, recruitmentDegree D i < D.degree i) →
      ¬ PointIdentified (hValues D) := by
    rintro ⟨i,hi,hs⟩ hid
    have hsp : 0 < spare D i := by unfold spare; omega
    have hle : spare D i ≤ totalSpare D := single_le_sum (fun k hk => Nat.zero_le _) hi
    have hstrict := homophily_endpoints_strict D hD h0 h1 (by omega)
    have he := (point_identified_iff_equal_extrema _ _ _ hh.2.1 hh.2.2).1 hid
    linarith
  have huniq : (∀ i ∈ D.sampled, D.degree i = recruitmentDegree D i) ↔
      ∀ H, Compatible D H → H.vertices = sampledVertices D ∧ H.edges = recruitmentEdges D := by
    constructor
    · intro hz H hH
      exact (zero_spare_compatible_unique D hD hz H hH).imp_right (fun h => h.1)
    · intro hall i hi
      have hH := leafCompletion_compatible D hD true
      have he := (hall _ hH).2
      have hd := hH.2.2.2.2.2 i hi
      rw [graphDegree,he] at hd
      exact hd.symm
  refine ⟨?_,huniq,hnon,?_⟩
  · constructor
    · rintro ⟨hid,_⟩
      intro i hi
      have hd := hD.2.2.2 i hi
      by_contra hn
      exact hnon ⟨i,hi,by omega⟩ hid
    · intro hz
      have hs : totalSpare D = 0 := by
        unfold totalSpare
        apply sum_eq_zero
        intro i hi
        simp only [spare,hz i hi,Nat.sub_self]
      have hs1 : traitSpare D true = 0 := by have ht := trait_spare_partition D; omega
      have hs0 : traitSpare D false = 0 := by have ht := trait_spare_partition D; omega
      have heh : hLower D = hUpper D := by simp [hLower,hUpper,hs,hs0,hs1]
      have hep : pLower D = pUpper D := (preferential_endpoints_equal_iff D hD hN).2 (by
        intro j hj
        simp only [spare,hz (D.parent j) (hD.2.2.1 j hj).1,Nat.sub_self])
      exact ⟨(point_identified_iff_equal_extrema _ _ _ hh.2.1 hh.2.2).2 heh,
        (point_identified_iff_equal_extrema _ _ _ hp.2.1 hp.2.2).2 hep⟩
  · intro hz H hH
    exact zero_spare_compatible_unique D hD hz H hH


/-- Definition 2, p. 155: every genuinely unsampled vertex remains susceptible
by entry status, including an unused observed-namespace name. -/
theorem unsampled_not_yet (D : Data) (H : State) (v : Vertex)
    (hv : v ∈ unsampled D H) (j : ℕ) : notYetSampled D j v = true := by
  cases v with
  | inl k =>
    have hk : k ∉ D.sampled := by
      intro hk
      exact (mem_sdiff.mp hv).2 (mem_image_of_mem s hk)
    simp [notYetSampled,hk]
  | inr k => rfl

/-- T13: flipping an unsampled trait changes no susceptible-neighbour set.
Definition 2 and corrected (A2), Appendix p. 160. -/
theorem flip_susceptible (D : Data) (H : State) (v : Vertex) (i j : ℕ) :
    susceptible D (flipTrait H v) i j = susceptible D H i j := rfl

/-- T13: a private unsampled neighbour of i is susceptible at exactly the
recruitment events whose recruiter is i. Corrected (A2), Appendix p. 160. -/
theorem private_susceptible_iff (D : Data) (H : State) (hD : Admissible D)
    (i : ℕ) (v : Vertex) (hv : v ∈ unsampled D H)
    (hprivate : ∀ k ∈ D.sampled, {s k,v} ∈ H.edges ↔ k = i)
    (j : ℕ) (hj : j ∈ nonseeds D) :
    v ∈ susceptible D H (D.parent j) j ↔ D.parent j = i := by
  have hr := (hD.2.2.1 j hj).1
  constructor
  · intro hs
    exact (hprivate _ hr).1 (mem_filter.mp hs).2.1
  · intro he
    exact mem_filter.mpr ⟨(mem_sdiff.mp hv).1,(hprivate _ hr).2 he,
      unsampled_not_yet D H v hv j⟩

/-- T13 counting identity: a 1-to-0 flip erases that vertex from the trait-1
filter of every finite set. Corrected (A2), Appendix p. 160. -/
theorem flip_true_filter (H : State) (S : Finset Vertex) (v : Vertex)
    (hz : H.trait v = true) :
    S.filter (fun w => (flipTrait H v).trait w = true) =
      (S.filter (fun w => H.trait w = true)).erase v := by
  ext w
  by_cases hw : w = v
  · subst w
    simp [flipTrait,hz]
  · have ht : (flipTrait H v).trait w = H.trait w := by simp [flipTrait,Function.update_of_ne hw]
    constructor
    · intro h
      obtain ⟨hs,hz'⟩ := mem_filter.mp h
      exact mem_erase.mpr ⟨hw,mem_filter.mpr ⟨hs,by rwa [ht] at hz'⟩⟩
    · intro h
      obtain ⟨_,hin⟩ := mem_erase.mp h
      obtain ⟨hs,hz'⟩ := mem_filter.mp hin
      exact mem_filter.mpr ⟨hs,by rw [ht]; exact hz'⟩

/-- T13 counting identity: when the flipped vertex belongs to a finite set,
a 1-to-0 flip inserts it into the trait-0 filter. Corrected (A2), p. 160. -/
theorem flip_false_filter (H : State) (S : Finset Vertex) (v : Vertex)
    (hv : v ∈ S) (hz : H.trait v = true) :
    S.filter (fun w => (flipTrait H v).trait w = false) =
      insert v (S.filter (fun w => H.trait w = false)) := by
  ext w
  by_cases hw : w = v
  · subst w
    simp [flipTrait,hz,hv]
  · have ht : (flipTrait H v).trait w = H.trait w := by simp [flipTrait,Function.update_of_ne hw]
    constructor
    · intro h
      obtain ⟨hs,hz'⟩ := mem_filter.mp h
      exact mem_insert_of_mem (mem_filter.mpr ⟨hs,by rwa [ht] at hz'⟩)
    · intro h
      have hin := (mem_insert.mp h).resolve_left hw
      obtain ⟨hs,hz'⟩ := mem_filter.mp hin
      exact mem_filter.mpr ⟨hs,by rw [ht]; exact hz'⟩

/-- T13 finite identity: the contribution before the 1-to-0 flip minus its
contribution after the flip is (1-2Z_i)/|S_i(t)| for a child of the private
neighbour’s owner, and zero at every other recruitment. Corrected (A2),
Appendix p. 160. -/
theorem private_flip_event_difference (D : Data) (H : State) (hD : Admissible D)
    (hH : Compatible D H) (i : ℕ) (hi : i ∈ D.sampled)
    (v : Vertex) (hv : v ∈ unsampled D H)
    (hprivate : ∀ k ∈ D.sampled, {s k,v} ∈ H.edges ↔ k = i)
    (hz : H.trait v = true) (j : ℕ) (hj : j ∈ nonseeds D) :
    ((if H.trait (s j) = H.trait (s (D.parent j)) then (1:ℝ) else 0) -
      (sameSusceptible D H (D.parent j) j).card /
        ((susceptible D H (D.parent j) j).card:ℝ)) -
    ((if (flipTrait H v).trait (s j) = (flipTrait H v).trait (s (D.parent j)) then (1:ℝ) else 0) -
      (sameSusceptible D (flipTrait H v) (D.parent j) j).card /
        ((susceptible D (flipTrait H v) (D.parent j) j).card:ℝ)) =
    if D.parent j = i then (if D.trait i then (-1:ℝ) else 1) /
      ((susceptible D H i j).card:ℝ) else 0 := by
  have hK := corrected_trait_preserves D H _ hH (TraitProposal.flip v hv)
  have hr := (hD.2.2.1 j hj).1
  have hobs : (flipTrait H v).trait (s j) = H.trait (s j) :=
    (hK.2.2.2.1 j (mem_sdiff.mp hj).1).trans (hH.2.2.2.1 j (mem_sdiff.mp hj).1).symm
  have hrt : (flipTrait H v).trait (s (D.parent j)) = H.trait (s (D.parent j)) :=
    (hK.2.2.2.1 _ hr).trans (hH.2.2.2.1 _ hr).symm
  rw [hobs,hrt,flip_susceptible]
  by_cases hri : D.parent j = i
  · rw [if_pos hri,hri]
    have hvi := (private_susceptible_iff D H hD i v hv hprivate j hj).2 hri
    rw [hri] at hvi
    cases hti : D.trait i
    · have hfalse : sameSusceptible D (flipTrait H v) i j =
          insert v (sameSusceptible D H i j) := by
        unfold sameSusceptible
        rw [flip_susceptible,hK.2.2.2.1 i hi,hH.2.2.2.1 i hi,hti]
        exact flip_false_filter H _ v hvi hz
      have hnot : v ∉ sameSusceptible D H i j := by
        simp [sameSusceptible,hH.2.2.2.1 i hi,hti,hz]
      have hc : (sameSusceptible D (flipTrait H v) i j).card =
          (sameSusceptible D H i j).card+1 := by rw [hfalse,card_insert_of_notMem hnot]
      rw [hc,Nat.cast_add,Nat.cast_one]
      simp [hti] <;> ring
    · have htrue : sameSusceptible D (flipTrait H v) i j =
          (sameSusceptible D H i j).erase v := by
        unfold sameSusceptible
        rw [flip_susceptible,hK.2.2.2.1 i hi,hH.2.2.2.1 i hi,hti]
        exact flip_true_filter H _ v hz
      have hin : v ∈ sameSusceptible D H i j :=
        mem_filter.mpr ⟨hvi,by rw [hz,hH.2.2.2.1 i hi,hti]⟩
      have hc : (sameSusceptible D H i j).card =
          (sameSusceptible D (flipTrait H v) i j).card+1 := by
        rw [htrue]
        exact (card_erase_add_one hin).symm
      rw [hc,Nat.cast_add,Nat.cast_one]
      simp [hti] <;> ring
  · have hvS : v ∉ susceptible D H (D.parent j) j := fun h =>
      hri ((private_susceptible_iff D H hD i v hv hprivate j hj).1 h)
    have he : sameSusceptible D (flipTrait H v) (D.parent j) j =
        sameSusceptible D H (D.parent j) j := by
      unfold sameSusceptible
      rw [flip_susceptible,hrt]
      apply filter_congr
      intro w hw
      have hne : w ≠ v := by rintro rfl; exact hvS hw
      simp [flipTrait,Function.update_of_ne hne]
    rw [he,if_neg hri]
    ring

/-- T13 finite identity: the pre-flip preferential value minus the post-flip
value is the signed sum of reciprocals over every child of the private
neighbour's owner, including later children. Corrected (A2), Appendix p. 160. -/
theorem private_flip_full_sum (D : Data) (H : State) (hD : Admissible D)
    (hH : Compatible D H) (i : ℕ) (hi : i ∈ D.sampled)
    (v : Vertex) (hv : v ∈ unsampled D H)
    (hprivate : ∀ k ∈ D.sampled, {s k,v} ∈ H.edges ↔ k = i)
    (hz : H.trait v = true) :
    pValue D H-pValue D (flipTrait H v) =
      ((if D.trait i then (-1:ℝ) else 1)/(nonseeds D).card) *
        (∑ j ∈ children D i, 1/((susceptible D H i j).card:ℝ)) := by
  unfold pValue pSum
  rw [← sub_div,← sum_sub_distrib]
  have ht : (∑ j ∈ nonseeds D,
      (((if H.trait (s j) = H.trait (s (D.parent j)) then (1:ℝ) else 0) -
        (sameSusceptible D H (D.parent j) j).card/((susceptible D H (D.parent j) j).card:ℝ)) -
      ((if (flipTrait H v).trait (s j) = (flipTrait H v).trait (s (D.parent j)) then (1:ℝ) else 0) -
        (sameSusceptible D (flipTrait H v) (D.parent j) j).card/
          ((susceptible D (flipTrait H v) (D.parent j) j).card:ℝ))) =
      ∑ j ∈ nonseeds D, if D.parent j = i then
        (if D.trait i then (-1:ℝ) else 1)/((susceptible D H i j).card:ℝ) else 0) := by
    apply sum_congr rfl
    intro j hj
    exact private_flip_event_difference D H hD hH i hi v hv hprivate hz j hj
  rw [ht]
  have hs : (∑ j ∈ nonseeds D, if D.parent j = i then
      (if D.trait i then (-1:ℝ) else 1)/((susceptible D H i j).card:ℝ) else 0) =
      (if D.trait i then (-1:ℝ) else 1)*
        (∑ j ∈ children D i, 1/((susceptible D H i j).card:ℝ)) := by
    rw [children,sum_filter,mul_sum]
    apply sum_congr rfl
    intro j hj
    by_cases hp : D.parent j = i <;> simp [hp,div_eq_mul_inv]
  rw [hs]
  ring

/-- T13: every child contributes a positive reciprocal; the whole child sum
is at least any one child's term, with equality exactly for a sole child.
Corrected (A2), Appendix p. 160. -/
theorem child_reciprocal_sum (D : Data) (H : State) (hH : Compatible D H)
    (i j : ℕ) (hj : j ∈ nonseeds D) (hr : D.parent j = i) :
    (0:ℝ) < (∑ k ∈ children D i, 1/((susceptible D H i k).card:ℝ)) ∧
    1/((susceptible D H i j).card:ℝ) ≤
      (∑ k ∈ children D i, 1/((susceptible D H i k).card:ℝ)) ∧
    ((∑ k ∈ children D i, 1/((susceptible D H i k).card:ℝ)) =
      1/((susceptible D H i j).card:ℝ) ↔ children D i = {j}) := by
  let f := fun k => 1/((susceptible D H i k).card:ℝ)
  have hjC : j ∈ children D i := mem_filter.mpr ⟨hj,hr⟩
  have hp : ∀ k ∈ children D i, 0 < f k := by
    intro k hk
    obtain ⟨hk,hri⟩ := mem_filter.mp hk
    have hs := (recruit_is_susceptible D H hH k hk).2
    rw [hri] at hs
    have hsR : (0:ℝ) < (susceptible D H i k).card := by exact_mod_cast hs
    exact one_div_pos.mpr hsR
  have hle : f j ≤ ∑ k ∈ children D i, f k := single_le_sum (fun k hk => (hp k hk).le) hjC
  refine ⟨lt_of_lt_of_le (hp j hjC) hle,hle,?_⟩
  constructor
  · intro he
    apply Subset.antisymm _ (singleton_subset_iff.mpr hjC)
    intro k hk
    by_contra hn
    have hkj : k ≠ j := by simpa using hn
    have hke : k ∈ (children D i).erase j := mem_erase.mpr ⟨hkj,hk⟩
    have hse : (0:ℝ) < ∑ l ∈ (children D i).erase j, f l :=
      lt_of_lt_of_le (hp k hk) (single_le_sum (fun l hl => (hp l (mem_of_mem_erase hl)).le) hke)
    have hsum := sum_erase_add (children D i) f hjC
    change (∑ k ∈ children D i, f k) = f j at he
    linarith
  · intro he
    rw [he,sum_singleton]

/-- T13 supporting compatibility fact: an arbitrary binary reassignment at
an unsampled vertex preserves all compatibility clauses. Definition 3, p. 155. -/
theorem unsampled_trait_update_preserves (D : Data) (H : State)
    (hH : Compatible D H) (v : Vertex) (hv : v ∈ unsampled D H) (t : Bool) :
    Compatible D {H with trait := Function.update H.trait v t} := by
  refine ⟨hH.1,hH.2.1,hH.2.2.1,?_,hH.2.2.2.2.1,hH.2.2.2.2.2⟩
  intro i hi
  have hn : s i ≠ v := by
    intro he
    exact (mem_sdiff.mp hv).2 (he ▸ mem_image_of_mem s hi)
  simpa only [Function.update_of_ne hn] using hH.2.2.2.1 i hi

/-- T10--T13 and T22: each constructed leaf is genuinely unsampled and has
exactly its owner as a sampled neighbour. It may have either binary trait.
Private-leaf construction, Appendix p. 160 and corrections P012-E001/P012-E003/P012-E005. -/
theorem private_leaf_member (D : Data) (hD : Admissible D) (same : Bool)
    (i k : ℕ) (hi : i ∈ D.sampled) (hk : k < spare D i) :
    u i k ∈ unsampled D (leafCompletion D same) ∧
    ∀ j ∈ D.sampled, {s j,u i k} ∈ (leafCompletion D same).edges ↔ j = i := by
  have hv : u i k ∈ leafVertices D :=
    mem_biUnion.mpr ⟨i,hi,mem_image.mpr ⟨k,mem_range.mpr hk,rfl⟩⟩
  refine ⟨mem_sdiff.mpr ⟨mem_union_right _ hv,by simp [sampledVertices,s,u]⟩,?_⟩
  intro j hj
  constructor
  · intro he
    rcases mem_union.mp he with he | he
    · have hm := recruitment_edge_sampled D hD _ he (show u i k ∈ ({s j,u i k}:Finset Vertex) by simp)
      simp [sampledVertices,s,u] at hm
    · obtain ⟨l,hl,he⟩ := mem_biUnion.mp he
      obtain ⟨q,hq,hpair⟩ := mem_image.mp he
      rcases (pair_edge_eq _ _ _ _).mp hpair with ⟨hs,hu⟩ | ⟨hs,hu⟩
      · have hlj : l = j := Sum.inl.inj hs
        have hli : l = i := congrArg Prod.fst (Sum.inr.inj hu)
        exact hlj.symm.trans hli
      · simp [s,u] at hs
  · intro hji
    subst j
    exact mem_union_right _ (mem_biUnion.mpr ⟨i,hi,mem_image.mpr ⟨k,mem_range.mpr hk,rfl⟩⟩)


/-- T13(b--d), corrected (A2) at any compatible starting pair with the stated
private unsampled neighbour, irrespective of all other traits and edges.
The difference p(H)-p(flipTrait H v) has sign 1-2Z_i. Appendix p. 160. -/
theorem private_trait_flip_difference (D : Data) (hD : Admissible D)
    (H : State) (hH : Compatible D H) (i j : ℕ) (hi : i ∈ D.sampled)
    (hj : j ∈ nonseeds D) (hr : D.parent j = i)
    (v : Vertex) (hv : v ∈ unsampled D H)
    (hprivate : ∀ k ∈ D.sampled, {s k,v} ∈ H.edges ↔ k = i)
    (htrait : H.trait v = true) :
    let K := flipTrait H v
    Compatible D K ∧
    (∀ ℓ ∈ nonseeds D, susceptible D H (D.parent ℓ) ℓ = susceptible D K (D.parent ℓ) ℓ) ∧
    (∀ ℓ ∈ nonseeds D, v ∈ susceptible D H (D.parent ℓ) ℓ ↔ D.parent ℓ = i) ∧
    pValue D H-pValue D K =
      ((if D.trait i then (-1:ℝ) else 1)/(nonseeds D).card) *
        (∑ ℓ ∈ children D i, 1/((susceptible D H i ℓ).card:ℝ)) ∧
    pValue D H ≠ pValue D K ∧
    (D.trait i = true →
      pValue D H-pValue D K ≤ -1/((nonseeds D).card*((susceptible D H i j).card:ℝ)) ∧
      -1/((nonseeds D).card*((susceptible D H i j).card:ℝ)) < 0 ∧
      (pValue D H-pValue D K = -1/((nonseeds D).card*((susceptible D H i j).card:ℝ)) ↔
        children D i = {j})) := by
  dsimp only
  have hK := corrected_trait_preserves D H _ hH (TraitProposal.flip v hv)
  have hdf := private_flip_full_sum D H hD hH i hi v hv hprivate htrait
  obtain ⟨hpos,hle,heq⟩ := child_reciprocal_sum D H hH i j hj hr
  have hN : (0:ℝ) < (nonseeds D).card := by
    exact_mod_cast (card_pos.mpr ⟨j,hj⟩)
  have hS : (0:ℝ) < (susceptible D H i j).card := by
    have hp := (recruit_is_susceptible D H hH j hj).2
    rw [hr] at hp
    exact_mod_cast hp
  have hne : pValue D H ≠ pValue D (flipTrait H v) := by
    intro he
    have hz : pValue D H-pValue D (flipTrait H v) = 0 := sub_eq_zero.mpr he
    rw [hdf] at hz
    cases hti : D.trait i
    · have hc : (0:ℝ) < 1/(nonseeds D).card := one_div_pos.mpr hN
      have hp := mul_pos hc hpos
      rw [hti] at hz
      change ((1:ℝ)/(nonseeds D).card)*(∑ k ∈ children D i, 1/((susceptible D H i k).card:ℝ)) = 0 at hz
      linarith
    · have hc : (-1:ℝ)/(nonseeds D).card < 0 := div_neg_of_neg_of_pos (by norm_num) hN
      have hp := mul_neg_of_neg_of_pos hc hpos
      simp only [hti,if_true] at hz
      linarith
  refine ⟨hK,?_,?_,hdf,hne,?_⟩
  · intro l hl
    exact (flip_susceptible D H v _ _).symm
  · intro l hl
    exact private_susceptible_iff D H hD i v hv hprivate l hl
  · intro hti
    have hc : (-1:ℝ)/(nonseeds D).card < 0 := div_neg_of_neg_of_pos (by norm_num) hN
    have hsingle : -1/((nonseeds D).card*((susceptible D H i j).card:ℝ)) =
        ((-1:ℝ)/(nonseeds D).card)*(1/((susceptible D H i j).card:ℝ)) := by
      field_simp
    have hdf' : pValue D H-pValue D (flipTrait H v) =
        ((-1:ℝ)/(nonseeds D).card)*(∑ l ∈ children D i, 1/((susceptible D H i l).card:ℝ)) := by
      simpa only [hti,if_true] using hdf
    rw [hdf',hsingle]
    refine ⟨mul_le_mul_of_nonpos_left hle hc.le,mul_neg_of_neg_of_pos hc (one_div_pos.mpr hS),?_⟩
    constructor
    · intro he
      exact heq.mp (mul_left_cancel₀ hc.ne he)
    · intro he
      rw [heq.mpr he]


/-- T13: Result 3, unchanged, with the corrected full difference. For the
pre-flip value minus the post-flip value, the sign is 1-2 Z_i and every child
contributes. Under Z_i=1 this difference is negative, at most the printed
one-child value, with equality exactly for a sole child. Appendix p. 160, corrected (A2). -/
theorem result3 (D : Data) (hD : Admissible D) (i j : ℕ)
    (hi : i ∈ D.sampled) (hj : j ∈ nonseeds D) (hr : D.parent j = i)
    (hdi : recruitmentDegree D i < D.degree i) :
    ∃ H K : State, ∃ v ∈ unsampled D H,
      Compatible D H ∧ Compatible D K ∧
      v = u i 0 ∧ H.vertices = (leafCompletion D true).vertices ∧
      H.edges = (leafCompletion D true).edges ∧
      (∀ k ∈ D.sampled, {s k,v} ∈ H.edges ↔ k = i) ∧
      H.trait v = true ∧ K = flipTrait H v ∧
      (∀ ℓ ∈ nonseeds D, susceptible D H (D.parent ℓ) ℓ =
        susceptible D K (D.parent ℓ) ℓ) ∧
      (∀ ℓ ∈ nonseeds D, v ∈ susceptible D H (D.parent ℓ) ℓ ↔ D.parent ℓ = i) ∧
      pValue D H - pValue D K =
        ((if D.trait i then (-1 : ℝ) else 1) / (nonseeds D).card) *
          (∑ ℓ ∈ children D i, 1 / ((susceptible D H i ℓ).card : ℝ)) ∧
      pValue D H ≠ pValue D K ∧ ¬ PointIdentified (pValues D) ∧
      (D.trait i = true →
        pValue D H - pValue D K ≤
          -1 / ((nonseeds D).card * ((susceptible D H i j).card : ℝ)) ∧
        -1 / ((nonseeds D).card * ((susceptible D H i j).card : ℝ)) < 0 ∧
        (pValue D H - pValue D K =
          -1 / ((nonseeds D).card * ((susceptible D H i j).card : ℝ)) ↔
          children D i = {j})) := by
  let L := leafCompletion D true
  let v := u i 0
  have hL : Compatible D L := leafCompletion_compatible D hD true
  have hsp : 0 < spare D i := by unfold spare; omega
  obtain ⟨hv,hprivate⟩ := private_leaf_member D hD true i 0 hi hsp
  let H : State := {L with trait := Function.update L.trait v true}
  let K := flipTrait H v
  have hH : Compatible D H := unsampled_trait_update_preserves D L hL v hv true
  have hvH : v ∈ unsampled D H := hv
  have hpH : ∀ k ∈ D.sampled, {s k,v} ∈ H.edges ↔ k = i := hprivate
  have hzH : H.trait v = true := by simp [H]
  obtain ⟨hK,hsus,hviff,hdf,hne,hnegative⟩ :=
    private_trait_flip_difference D hD H hH i j hi hj hr v hvH hpH hzH
  have hN : D.seeds.card < D.sampled.card := by
    have hn : 0 < (nonseeds D).card := card_pos.mpr ⟨j,hj⟩
    rw [nonseeds,card_sdiff_of_subset hD.1] at hn
    omega
  have hdom := (full_p_domain_conditions D hD).2 hN
  have hnot : ¬ PointIdentified (pValues D) := by
    rintro ⟨r,he⟩
    have hmemH : pValue D H ∈ pValues D := ⟨H,hH,by rw [preferential,if_pos (hdom H hH)]⟩
    have hmemK : pValue D K ∈ pValues D := ⟨K,hK,by rw [preferential,if_pos (hdom K hK)]⟩
    rw [he,Set.mem_singleton_iff] at hmemH hmemK
    exact hne (hmemH.trans hmemK.symm)
  exact ⟨H,K,v,hvH,hH,hK,rfl,rfl,rfl,hpH,hzH,rfl,hsus,hviff,hdf,hne,hnot,hnegative⟩


/-- T10, printed Result 1 unchanged (p. 155): two compatible completions have
different induced edge sets, under the earlier/later, nonrecruitment, two-spare-
degrees premises. Witnesses also exhibit the repaired common-neighbour move
from the Appendix proof (p. 160). -/
theorem result1 (D : Data) (hD : Admissible D) (i j : ℕ)
    (hi : i ∈ D.sampled) (hj : j ∈ D.sampled) (ht : D.time i < D.time j)
    (hr : ¬ (j ∈ nonseeds D ∧ D.parent j = i))
    (hdi : recruitmentDegree D i < D.degree i)
    (hdj : recruitmentDegree D j < D.degree j) :
    ∃ H K : State, Compatible D H ∧ Compatible D K ∧
      {s i,s j} ∉ H.edges ∧ {s i,s j} ∈ K.edges ∧
      (induced D H).edges = recruitmentEdges D ∧
      (induced D K).edges = insert {s i,s j} (recruitmentEdges D) ∧
      InducedCompatible D (induced D H) ∧ InducedCompatible D (induced D K) ∧
      ∃ v ∈ unsampled D H, {s i,v} ∈ H.edges ∧ {s j,v} ∈ H.edges ∧
        K = cleanup D true (addEdge (removeEdge (removeEdge H (s i) v) (s j) v)
          (s i) (s j)) := by
  let L := leafCompletion D true
  let v := u i 0
  let w := u j 0
  have hL : Compatible D L := leafCompletion_compatible D hD true
  have hiSp : 0 < spare D i := by unfold spare; omega
  have hjSp : 0 < spare D j := by unfold spare; omega
  obtain ⟨hv,hvi⟩ := private_leaf_member D hD true i 0 hi hiSp
  obtain ⟨hw,hwj⟩ := private_leaf_member D hD true j 0 hj hjSp
  have hij : i ≠ j := by rintro rfl; exact lt_irrefl _ ht
  have hvw : v ≠ w := by simpa [v,w,u] using hij
  have hne : s i ≠ s j := by simpa [s] using hij
  have hjsw : s j ≠ w := by simp [w,s,u]
  have hjw : {s j,w} ∈ L.edges := (hwj j hj).2 rfl
  have hiv : {s i,v} ∈ L.edges := (hvi i hi).2 rfl
  have hjv : {s j,v} ∉ L.edges := fun he => hij ((hvi j hj).1 he).symm
  have hrw : {s j,w} ∉ recruitmentEdges D := fun he =>
    (mem_sdiff.mp hw).2 (recruitment_edge_sampled D hD _ he (by simp [w]))
  have hp : v ∈ replacementPool D L j := mem_filter.mpr ⟨hv,hjv⟩
  let H := cleanup D true (addEdge (removeEdge L (s j) w) (s j) v)
  have hPH : GraphProposal D true L H :=
    GraphProposal.deleteUnobserved j w v (removeEdge L (s j) w) hj
      (mem_sdiff.mp hw).1 hjsw hjw hrw (mem_sdiff.mp hw).2 (Replacement.existing v hp)
  have hH : Compatible D H := corrected_graph_preserves D L H hD hL hPH
  have hevw : ({s i,v}:Finset Vertex) ≠ {s j,w} := by
    intro he
    rcases (pair_edge_eq _ _ _ _).mp he with he | he
    · exact hvw he.2
    · simp [v,w,s,u] at he
  have hivH : {s i,v} ∈ H.edges := mem_insert_of_mem (mem_erase.mpr ⟨hevw,hiv⟩)
  have hjvH : {s j,v} ∈ H.edges := mem_insert_self _ _
  have hvH : v ∈ unsampled D H := by
    have hvV := (hH.1.1 _ hivH).2 (show v ∈ ({s i,v}:Finset Vertex) by simp)
    exact mem_sdiff.mpr ⟨hvV,(mem_sdiff.mp hv).2⟩
  have hrpair : {s i,s j} ∉ recruitmentEdges D := by
    intro he
    obtain ⟨k,hk,hpair⟩ := mem_image.mp he
    rcases (pair_edge_eq _ _ _ _).mp hpair with ⟨hp,hk'⟩ | ⟨hp,hk'⟩
    · have hki : D.parent k = i := Sum.inl.inj hp
      have hkj : k = j := Sum.inl.inj hk'
      subst k
      exact hr ⟨hk,hki⟩
    · have hkj : D.parent k = j := Sum.inl.inj hp
      have hki : k = i := Sum.inl.inj hk'
      subst k
      have htime := (hD.2.2.1 i hk).2
      rw [hkj] at htime
      omega
  have hleafnot : ∀ e ∈ leafEdges D, ¬ e ⊆ sampledVertices D := by
    intro e he hs
    obtain ⟨k,hk,he⟩ := mem_biUnion.mp he
    obtain ⟨q,hq,rfl⟩ := mem_image.mp he
    have hm := hs (show u k q ∈ ({s k,u k q}:Finset Vertex) by simp)
    simp [sampledVertices,s,u] at hm
  have hHfilter : (induced D H).edges = recruitmentEdges D := by
    apply Subset.antisymm
    · intro e he
      obtain ⟨he,hs⟩ := mem_filter.mp he
      rcases mem_insert.mp he with he | he
      · subst e
        exact False.elim ((mem_sdiff.mp hv).2 (hs (by simp [v])))
      · have heL := (mem_erase.mp he).2
        exact (mem_union.mp heL).resolve_right (fun hl => hleafnot e hl hs)
    · intro e he
      exact mem_filter.mpr ⟨hH.2.2.1 he,recruitment_edge_sampled D hD _ he⟩
  have hijH : {s i,s j} ∉ H.edges := by
    intro he
    have hs : ({s i,s j}:Finset Vertex) ⊆ sampledVertices D := by
      simp only [insert_subset_iff,singleton_subset_iff]
      exact ⟨mem_image_of_mem s hi,mem_image_of_mem s hj⟩
    have hm : {s i,s j} ∈ (induced D H).edges := mem_filter.mpr ⟨he,hs⟩
    rw [hHfilter] at hm
    exact hrpair hm
  let K := cleanup D true (addEdge (removeEdge (removeEdge H (s i) v) (s j) v) (s i) (s j))
  have hPK : GraphProposal D true H K := GraphProposal.addObserved i (s j) v v hi
    (hH.2.1 (mem_image_of_mem s hj)) hne hijH hvH hvH hivH hjvH
  have hK : Compatible D K := corrected_graph_preserves D H K hD hH hPK
  have hijK : {s i,s j} ∈ K.edges := mem_insert_self _ _
  have hKfilter : (induced D K).edges = insert {s i,s j} (recruitmentEdges D) := by
    apply Subset.antisymm
    · intro e he
      obtain ⟨he,hs⟩ := mem_filter.mp he
      rcases mem_insert.mp he with he | he
      · exact mem_insert.mpr (Or.inl he)
      · have heH := (mem_erase.mp (mem_erase.mp he).2).2
        have hm : e ∈ (induced D H).edges := mem_filter.mpr ⟨heH,hs⟩
        rw [hHfilter] at hm
        exact mem_insert_of_mem hm
    · intro e he
      rcases mem_insert.mp he with he | he
      · subst e
        refine mem_filter.mpr ⟨hijK,?_⟩
        simp only [insert_subset_iff,singleton_subset_iff]
        exact ⟨mem_image_of_mem s hi,mem_image_of_mem s hj⟩
      · exact mem_filter.mpr ⟨hK.2.2.1 he,recruitment_edge_sampled D hD _ he⟩
  have hGH : GraphCompatible D H := ⟨hH.1,hH.2.1,hH.2.2.1,hH.2.2.2.2.1,hH.2.2.2.2.2⟩
  have hGK : GraphCompatible D K := ⟨hK.1,hK.2.1,hK.2.2.1,hK.2.2.2.2.1,hK.2.2.2.2.2⟩
  exact ⟨H,K,hH,hK,hijH,hijK,hHfilter,hKfilter,
    (induced_compatibility D H hD hGH).1,(induced_compatibility D K hD hGK).1,
    v,hvH,hivH,hjvH,rfl⟩


/-- T11: all compatible graph clauses transfer across equal vertex and edge
sets when the observed traits are preserved; unobserved traits remain free.
Definition 3, p. 155; repaired (A1), Appendix p. 160. -/
theorem compatible_same_graph (D : Data) (L H : State) (hL : Compatible D L)
    (hv : H.vertices = L.vertices) (he : H.edges = L.edges)
    (ht : ∀ i ∈ D.sampled, H.trait (s i) = D.trait i) : Compatible D H := by
  refine ⟨?_,?_,?_,ht,?_,?_⟩
  · simpa only [Augmented,Simple,hv,he] using hL.1
  · simpa only [hv] using hL.2.1
  · simpa only [he] using hL.2.2.1
  · simpa only [hv,he] using hL.2.2.2.2.1
  · simpa only [graphDegree,he] using hL.2.2.2.2.2

/-- T11: the legal exchange of two distinct owners' private leaves keeps
all vertex identities, every degree, every trait, and the total edge count.
No nonrecruitment premise between the owners is required. Repaired Result 2
construction, Appendix p. 160. -/
theorem private_leaf_swap_graph (D : Data) (hD : Admissible D) (H : State)
    (hv : H.vertices = (leafCompletion D true).vertices)
    (he : H.edges = (leafCompletion D true).edges)
    (ht : ∀ k ∈ D.sampled, H.trait (s k) = D.trait k)
    (i j : ℕ) (hi : i ∈ D.sampled) (hj : j ∈ D.sampled)
    (hdi : recruitmentDegree D i < D.degree i)
    (hdj : recruitmentDegree D j < D.degree j) (hij : i ≠ j) :
    let K := addEdge (addEdge (removeEdge (removeEdge H (s i) (u i 0))
      (s j) (u j 0)) (s i) (u j 0)) (s j) (u i 0)
    Compatible D H ∧ Compatible D K ∧
    {s i,u i 0} ∈ H.edges ∧ {s j,u j 0} ∈ H.edges ∧
    {s i,u j 0} ∉ H.edges ∧ {s j,u i 0} ∉ H.edges ∧
    H.vertices = K.vertices ∧ H.trait = K.trait ∧ H.edges.card = K.edges.card ∧
    (∀ v, graphDegree H v = graphDegree K v) := by
  dsimp only
  let A := removeEdge H (s i) (u i 0)
  let B := removeEdge A (s j) (u j 0)
  let C := addEdge B (s i) (u j 0)
  let K := addEdge C (s j) (u i 0)
  have hH := compatible_same_graph D _ H (leafCompletion_compatible D hD true) hv he ht
  have hiSp : 0 < spare D i := by unfold spare; omega
  have hjSp : 0 < spare D j := by unfold spare; omega
  obtain ⟨hvi,hpi⟩ := private_leaf_member D hD true i 0 hi hiSp
  obtain ⟨hvj,hpj⟩ := private_leaf_member D hD true j 0 hj hjSp
  have hviH : u i 0 ∈ unsampled D H := by simpa only [unsampled,hv] using hvi
  have hvjH : u j 0 ∈ unsampled D H := by simpa only [unsampled,hv] using hvj
  have hE1 : {s i,u i 0} ∈ H.edges := by rw [he]; exact (hpi i hi).2 rfl
  have hE2 : {s j,u j 0} ∈ H.edges := by rw [he]; exact (hpj j hj).2 rfl
  have hE3 : {s i,u j 0} ∉ H.edges := by rw [he]; exact fun h => hij ((hpj i hi).1 h)
  have hE4 : {s j,u i 0} ∉ H.edges := by rw [he]; exact fun h => hij ((hpi j hj).1 h).symm
  have hn12 : ({s j,u j 0}:Finset Vertex) ≠ {s i,u i 0} := by simp [s,u,hij,Ne.symm hij]
  have hn34 : ({s j,u i 0}:Finset Vertex) ≠ {s i,u j 0} := by simp [s,u,hij,Ne.symm hij]
  have hE2A : {s j,u j 0} ∈ A.edges := mem_erase.mpr ⟨hn12,hE2⟩
  have hE3B : {s i,u j 0} ∉ B.edges := fun h => hE3 ((mem_erase.mp (mem_erase.mp h).2).2)
  have hE4C : {s j,u i 0} ∉ C.edges := by
    intro h
    rcases mem_insert.mp h with h | h
    · exact hn34 h
    · exact hE4 ((mem_erase.mp (mem_erase.mp h).2).2)
  have hbase : ProposalBase D H := ⟨hH.1,hH.2.1,hH.2.2.1,hH.2.2.2.1⟩
  have hr1 : {s i,u i 0} ∉ recruitmentEdges D := fun h =>
    (mem_sdiff.mp hviH).2 (recruitment_edge_sampled D hD _ h (by simp))
  have hr2 : {s j,u j 0} ∉ recruitmentEdges D := fun h =>
    (mem_sdiff.mp hvjH).2 (recruitment_edge_sampled D hD _ h (by simp))
  have hA : ProposalBase D A := remove_edge_base D H _ _ hbase hr1
  have hB : ProposalBase D B := remove_edge_base D A _ _ hA hr2
  have hC : ProposalBase D C := add_edge_base D B i (u j 0) hB hi
    (mem_sdiff.mp hvjH).1 (by simp [s,u])
  have hbaseK : ProposalBase D K := add_edge_base D C j (u i 0) hC hj
    (mem_sdiff.mp hviH).1 (by simp [s,u])
  have hdeg : ∀ w, graphDegree H w = graphDegree K w := by
    intro w
    have h1 := degree_remove_step H (s i) (u i 0) w hE1
    have h2 := degree_remove_step A (s j) (u j 0) w hE2A
    have h3 := degree_add_step B (s i) (u j 0) w hE3B
    have h4 := degree_add_step C (s j) (u i 0) w hE4C
    change graphDegree A w+_ = graphDegree H w at h1
    change graphDegree B w+_ = graphDegree A w at h2
    change graphDegree C w = graphDegree B w+_ at h3
    change graphDegree K w = graphDegree C w+_ at h4
    simp only [mem_insert,mem_singleton] at h1 h2 h3 h4
    by_cases ha : w = s i <;> by_cases hb : w = s j <;>
      by_cases hc : w = u i 0 <;> by_cases hd : w = u j 0 <;>
      simp only [ha,hb,hc,hd,or_true,true_or,false_or,or_false,if_true,if_false] at h1 h2 h3 h4 ⊢ <;>
      simp [s,u,hij,Ne.symm hij] at h1 h2 h3 h4 ⊢ <;> omega
  have hclean : cleanup D true K = K := by
    have hf : K.vertices.filter (fun v =>
        (true = true ∧ v ∈ sampledVertices D) ∨ graphDegree K v ≠ 0) = K.vertices := by
      apply filter_eq_self.mpr
      intro v hvK
      by_cases hs : v ∈ sampledVertices D
      · exact Or.inl ⟨rfl,hs⟩
      · right
        have hvH : v ∈ H.vertices := hvK
        obtain ⟨k,hk,hkv⟩ := hH.2.2.2.2.1 v hvH hs
        have hpos : 0 < graphDegree H v := card_pos.mpr ⟨{s k,v},mem_filter.mpr ⟨hkv,by simp⟩⟩
        rw [hdeg] at hpos
        omega
    exact congrArg (fun V => {K with vertices := V}) hf
  have hK : Compatible D K := by
    rw [← hclean]
    apply cleanup_compatible D K hbaseK
    intro k hk
    rw [← hdeg]
    exact hH.2.2.2.2.2 k hk
  have hm : H.edges.card = K.edges.card := by
    have h1 := degree_sum_twice_edges H hH.1.1
    have h2 := degree_sum_twice_edges K hK.1.1
    have hs : (∑ v ∈ H.vertices, graphDegree H v) =
        ∑ v ∈ K.vertices, graphDegree K v := sum_congr rfl (fun v hv => hdeg v)
    omega
  exact ⟨hH,hK,hE1,hE2,hE3,hE4,rfl,rfl,hm,hdeg⟩

/-- T11: preserving all vertex degrees, traits, vertex names and edge count
preserves Q and the full homophily denominator. Repaired (A1), p. 160. -/
theorem same_degree_h_denominator (H K : State)
    (hv : H.vertices = K.vertices) (ht : H.trait = K.trait)
    (hm : H.edges.card = K.edges.card) (hd : ∀ v, graphDegree H v = graphDegree K v) :
    degreeTraitSum H = degreeTraitSum K ∧ hDenominator H = hDenominator K := by
  have hQ : degreeTraitSum H = degreeTraitSum K := by
    unfold degreeTraitSum
    rw [hv]
    apply sum_congr rfl
    intro v hv
    simp only [hd v,z,ht]
  exact ⟨hQ,by rw [denominator_sum_identity,denominator_sum_identity,hQ,hm]⟩

/-- T11: the two-private-leaf exchange loses exactly one trait-1 edge.
The other leaf traits and all other edges are unrestricted in this identity.
Repaired (A1), Appendix p. 160. -/
theorem private_swap_true_edge_count (H : State) (i j : ℕ)
    (hE : {s j,u j 0} ∈ H.edges)
    (hzi : H.trait (s i) = false) (hzj : H.trait (s j) = true)
    (hu1 : H.trait (u i 0) = false) (hu2 : H.trait (u j 0) = true) :
    let K := addEdge (addEdge (removeEdge (removeEdge H (s i) (u i 0))
      (s j) (u j 0)) (s i) (u j 0)) (s j) (u i 0)
    edgeCount K true+1 = edgeCount H true := by
  dsimp only
  let P := fun e : Finset Vertex => ∀ v ∈ e, H.trait v = true
  have hp1 : ¬ P {s i,u i 0} := by
    intro h
    have hh := h (s i) (by simp)
    rw [hzi] at hh
    cases hh
  have hp2 : P {s j,u j 0} := by
    intro v hv
    rcases mem_insert.mp hv with hv | hv
    · rw [hv]; exact hzj
    · rw [mem_singleton.mp hv]; exact hu2
  have hp3 : ¬ P {s i,u j 0} := by
    intro h
    have hh := h (s i) (by simp)
    rw [hzi] at hh
    cases hh
  have hp4 : ¬ P {s j,u i 0} := by
    intro h
    have hh := h (u i 0) (by simp)
    rw [hu1] at hh
    cases hh
  have hn : {s i,u i 0} ∉ H.edges.filter P := fun h => hp1 (mem_filter.mp h).2
  have hin : {s j,u j 0} ∈ H.edges.filter P := mem_filter.mpr ⟨hE,hp2⟩
  change ((insert {s j,u i 0} (insert {s i,u j 0}
    ((H.edges.erase {s i,u i 0}).erase {s j,u j 0}))).filter P).card+1 = (H.edges.filter P).card
  rw [filter_insert,if_neg hp4,filter_insert,if_neg hp3,filter_erase,filter_erase,
    erase_eq_of_notMem hn]
  exact card_erase_add_one hin

/-- T11: swapping the two selected 0- and 1-trait private leaves changes
homophily by exactly 2/D, with a positive unchanged denominator. Every other
unsampled trait is arbitrary. Repaired Result 2 and (A1), p. 160. -/
theorem private_leaf_swap_value (D : Data) (hD : Admissible D) (H : State)
    (hv : H.vertices = (leafCompletion D true).vertices)
    (he : H.edges = (leafCompletion D true).edges)
    (ht : ∀ k ∈ D.sampled, H.trait (s k) = D.trait k)
    (i j : ℕ) (hi : i ∈ D.sampled) (hj : j ∈ D.sampled)
    (hdi : recruitmentDegree D i < D.degree i)
    (hdj : recruitmentDegree D j < D.degree j)
    (hzi : D.trait i = false) (hzj : D.trait j = true)
    (hu1 : H.trait (u i 0) = false) (hu2 : H.trait (u j 0) = true) :
    let K := addEdge (addEdge (removeEdge (removeEdge H (s i) (u i 0))
      (s j) (u j 0)) (s i) (u j 0)) (s j) (u i 0)
    0 < hDenominator H ∧ hDenominator H = hDenominator K ∧
    hValue H-hValue K = 2/hDenominator H ∧ hValue H ≠ hValue K := by
  dsimp only
  let K := addEdge (addEdge (removeEdge (removeEdge H (s i) (u i 0))
      (s j) (u j 0)) (s i) (u j 0)) (s j) (u i 0)
  have hij : i ≠ j := by intro he; rw [he,hzj] at hzi; cases hzi
  obtain ⟨hH,hK,hE1,hE2,hE3,hE4,hV,hT,hM,hG⟩ :=
    private_leaf_swap_graph D hD H hv he ht i j hi hj hdi hdj hij
  have ht0 : 0 < traitDegree H false := by
    have hd : graphDegree H (s i) ≤ traitDegree H false :=
      single_le_sum (fun v hv => Nat.zero_le _) (mem_filter.mpr
        ⟨hH.2.1 (mem_image_of_mem s hi),by rw [ht i hi,hzi]⟩)
    rw [hH.2.2.2.2.2 i hi] at hd
    omega
  have ht1 : 0 < traitDegree H true := by
    have hd : graphDegree H (s j) ≤ traitDegree H true :=
      single_le_sum (fun v hv => Nat.zero_le _) (mem_filter.mpr
        ⟨hH.2.1 (mem_image_of_mem s hj),by rw [ht j hj,hzj]⟩)
    rw [hH.2.2.2.2.2 j hj] at hd
    omega
  have hpos := (graph_homophily_formula H hH.1.1 ht0 ht1).2.2.1
  obtain ⟨hQ,hden⟩ := same_degree_h_denominator H K hV hT hM hG
  have hcount := private_swap_true_edge_count H i j hE2 ((ht i hi).trans hzi) ((ht j hj).trans hzj) hu1 hu2
  have hcountR : (edgeCount K true:ℝ)+1 = (edgeCount H true:ℝ) := by exact_mod_cast hcount
  have hnum : hNumerator H-hNumerator K = 2 := by
    rw [numerator_edge_identity H hH.1.1,numerator_edge_identity K hK.1.1,
      hQ,hM]
    linarith
  have hdiff : hValue H-hValue K = 2/hDenominator H := by
    unfold hValue
    rw [← hden,← sub_div,hnum]
  refine ⟨hpos,hden,hdiff,?_⟩
  intro heq
  have hh : hValue H-hValue K = 0 := sub_eq_zero.mpr heq
  have hp : (0:ℝ) < 2/hDenominator H := div_pos (by norm_num) hpos
  rw [← hdiff,hh] at hp
  exact lt_irrefl _ hp


/-- T11(a--d), the repaired proof of Result 2 for every assignment of the
other private-leaf traits, rather than just the same-trait example. The two
selected leaves have traits 0 and 1; the absent cross edges and legal swap,
both denominator formulas, and the whole (A1) difference are conclusions.
Appendix p. 160, corrected Result 2 proof. -/
theorem result2_swap_formula (D : Data) (hD : Admissible D) (i j : ℕ)
    (hi : i ∈ D.sampled) (hj : j ∈ D.sampled)
    (hdi : recruitmentDegree D i < D.degree i)
    (hdj : recruitmentDegree D j < D.degree j)
    (hzi : D.trait i = false) (hzj : D.trait j = true)
    (H : State) (hv : H.vertices = (leafCompletion D true).vertices)
    (he : H.edges = (leafCompletion D true).edges)
    (htraits : ∀ k ∈ D.sampled, H.trait (s k) = D.trait k)
    (hu1 : H.trait (u i 0) = false) (hu2 : H.trait (u j 0) = true) :
    let K := addEdge (addEdge (removeEdge (removeEdge H (s i) (u i 0))
      (s j) (u j 0)) (s i) (u j 0)) (s j) (u i 0)
    let Q := ∑ v ∈ H.vertices, (graphDegree H v:ℝ)*z H v
    Compatible D H ∧ Compatible D K ∧
    {s i,u i 0} ∈ H.edges ∧ {s j,u j 0} ∈ H.edges ∧
    {s i,u j 0} ∉ H.edges ∧ {s j,u i 0} ∉ H.edges ∧
    H.vertices = K.vertices ∧ H.trait = K.trait ∧ H.edges.card = K.edges.card ∧
    (∀ v, graphDegree H v = graphDegree K v) ∧
    hDenominator H = Q-Q^2/(2*(H.edges.card:ℝ)) ∧
    hDenominator H = Q*(2*(H.edges.card:ℝ)-Q)/(2*(H.edges.card:ℝ)) ∧
    hDenominator H = hDenominator K ∧ 0 < hDenominator H ∧
    hValue H-hValue K =
      (2*(1-(graphDegree H (s j):ℝ)*graphDegree H (u j 0)/(2*(H.edges.card:ℝ))) -
        2*(0-(graphDegree H (s j):ℝ)*graphDegree H (u j 0)/(2*(H.edges.card:ℝ)))) /
        hDenominator H ∧
    hValue H-hValue K = 2/hDenominator H ∧ hValue H ≠ hValue K := by
  dsimp only
  let K := addEdge (addEdge (removeEdge (removeEdge H (s i) (u i 0))
    (s j) (u j 0)) (s i) (u j 0)) (s j) (u i 0)
  have hij : i ≠ j := by intro he; rw [he,hzj] at hzi; cases hzi
  obtain ⟨hH,hK,hE1,hE2,hE3,hE4,hV,hT,hM,hG⟩ :=
    private_leaf_swap_graph D hD H hv he htraits i j hi hj hdi hdj hij
  obtain ⟨hpos,hden,hdiff,hne⟩ :=
    private_leaf_swap_value D hD H hv he htraits i j hi hj hdi hdj hzi hzj hu1 hu2
  have hm : (0:ℝ) < 2*(H.edges.card:ℝ) := by
    have hn : 0 < H.edges.card := card_pos.mpr ⟨{s i,u i 0},hE1⟩
    positivity
  have hdF : hDenominator H = degreeTraitSum H *
      (2*(H.edges.card:ℝ)-degreeTraitSum H)/(2*(H.edges.card:ℝ)) := by
    rw [denominator_sum_identity]
    have hm0 : (H.edges.card:ℝ) ≠ 0 := by intro hz; rw [hz] at hm; linarith
    field_simp [hm0]
  have hA1 : hValue H-hValue K =
      (2*(1-(graphDegree H (s j):ℝ)*graphDegree H (u j 0)/(2*(H.edges.card:ℝ))) -
        2*(0-(graphDegree H (s j):ℝ)*graphDegree H (u j 0)/(2*(H.edges.card:ℝ)))) / hDenominator H := by
    rw [hdiff]
    congr 1
    ring
  exact ⟨hH,hK,hE1,hE2,hE3,hE4,hV,hT,hM,hG,denominator_sum_identity H,
    hdF,hden,hpos,hA1,hdiff,hne⟩


/-- T11: the private-leaf exchange is the same graph operation after
interchanging its two owners. Repaired Result 2 construction, p. 160. -/
theorem private_swap_reversed (H : State) (i j : ℕ) :
    addEdge (addEdge (removeEdge (removeEdge H (s i) (u i 0))
      (s j) (u j 0)) (s i) (u j 0)) (s j) (u i 0) =
    addEdge (addEdge (removeEdge (removeEdge H (s j) (u j 0))
      (s i) (u i 0)) (s j) (u i 0)) (s i) (u j 0) := by
  change {H with edges := insert {s j,u i 0} (insert {s i,u j 0}
    ((H.edges.erase {s i,u i 0}).erase {s j,u j 0}))} =
    {H with edges := insert {s i,u j 0} (insert {s j,u i 0}
    ((H.edges.erase {s j,u j 0}).erase {s i,u i 0}))}
  rw [erase_right_comm,insert_comm]

/-- T11, printed Result 2 and (A1), with a constructed legal starting pair:
opposite-trait observed vertices with spare degrees give two compatible pairs
with the same degree sequence, m, traits and denominator, and h1-h2=2/D≠0.
There is no nonrecruitment premise on i,j. pp. 155, 160. -/
theorem result2 (D : Data) (hD : Admissible D) (i j : ℕ)
    (hi : i ∈ D.sampled) (hj : j ∈ D.sampled)
    (hdi : recruitmentDegree D i < D.degree i)
    (hdj : recruitmentDegree D j < D.degree j) (hz : D.trait i ≠ D.trait j) :
    ∃ H K : State, Compatible D H ∧ Compatible D K ∧
      H = leafCompletion D true ∧
      {s i,u i 0} ∈ H.edges ∧ {s j,u j 0} ∈ H.edges ∧
      {s i,u j 0} ∉ H.edges ∧ {s j,u i 0} ∉ H.edges ∧
      K = addEdge (addEdge (removeEdge (removeEdge H (s i) (u i 0))
        (s j) (u j 0)) (s i) (u j 0)) (s j) (u i 0) ∧
      H.vertices = K.vertices ∧ H.edges.card = K.edges.card ∧ H.trait = K.trait ∧
      (∀ v, graphDegree H v = graphDegree K v) ∧
      0 < hDenominator H ∧ hDenominator H = hDenominator K ∧
      hValue H - hValue K = 2 / hDenominator H ∧
      hValue H ≠ hValue K ∧ ¬ PointIdentified (hValues D) := by
  let H := leafCompletion D true
  let K := addEdge (addEdge (removeEdge (removeEdge H (s i) (u i 0))
    (s j) (u j 0)) (s i) (u j 0)) (s j) (u i 0)
  have hij : i ≠ j := by rintro rfl; exact hz rfl
  have ht : ∀ k ∈ D.sampled, H.trait (s k) = D.trait k := fun k hk => rfl
  obtain ⟨hH,hK,hE1,hE2,hE3,hE4,hV,hT,hM,hG⟩ :=
    private_leaf_swap_graph D hD H rfl rfl ht i j hi hj hdi hdj hij
  have hval : 0 < hDenominator H ∧ hDenominator H = hDenominator K ∧
      hValue H-hValue K = 2/hDenominator H ∧ hValue H ≠ hValue K := by
    cases hti : D.trait i <;> cases htj : D.trait j
    · exact False.elim (hz (hti.trans htj.symm))
    · exact private_leaf_swap_value D hD H rfl rfl ht i j hi hj hdi hdj hti htj
        (by simpa [H,leafCompletion,u] using hti) (by simpa [H,leafCompletion,u] using htj)
    · have hr := private_leaf_swap_value D hD H rfl rfl ht j i hj hi hdj hdi htj hti
        (by simpa [H,leafCompletion,u] using htj) (by simpa [H,leafCompletion,u] using hti)
      simpa only [private_swap_reversed H j i] using hr
    · exact False.elim (hz (hti.trans htj.symm))
  obtain ⟨hpos,hden,hdiff,hne⟩ := hval
  have hm : 0 < H.edges.card := card_pos.mpr ⟨{s i,u i 0},hE1⟩
  have hdomH : HomophilyDefined H := ⟨hm,hpos.ne'⟩
  have hdomK : HomophilyDefined K := ⟨by rw [← hM]; exact hm,by rw [← hden]; exact hpos.ne'⟩
  have hnot : ¬ PointIdentified (hValues D) := by
    rintro ⟨r,he⟩
    have hmemH : hValue H ∈ hValues D := ⟨H,hH,by rw [homophily,if_pos hdomH]⟩
    have hmemK : hValue K ∈ hValues D := ⟨K,hK,by rw [homophily,if_pos hdomK]⟩
    rw [he,Set.mem_singleton_iff] at hmemH hmemK
    exact hne (hmemH.trans hmemK.symm)
  exact ⟨H,K,hH,hK,rfl,hE1,hE2,hE3,hE4,rfl,hV,hM,hT,hG,hpos,hden,hdiff,hne,hnot⟩


/-- T13 and T22: in an augmented simple compatible graph, a private
unsampled neighbour is incident only to its owner's edge. The model permits
shared neighbours generally; privacy is used here exactly as in the witness.
Appendix p. 160, corrected (A2); P012-E005. -/
theorem private_edge_incidence (D : Data) (H : State) (hH : Compatible D H)
    (i : ℕ) (hi : i ∈ D.sampled) (v : Vertex) (hv : v ∈ unsampled D H)
    (hprivate : ∀ k ∈ D.sampled, {s k,v} ∈ H.edges ↔ k = i)
    (e : Finset Vertex) (he : e ∈ H.edges) (hve : v ∈ e) : e = {s i,v} := by
  obtain ⟨k,hk,hke⟩ := hH.1.2 e he
  have hn : s k ≠ v := by
    intro he
    exact (mem_sdiff.mp hv).2 (he ▸ mem_image_of_mem s hk)
  have hp : ({s k,v}:Finset Vertex) ⊆ e := by
    simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨hke,hve⟩
  have hpair : ({s k,v}:Finset Vertex) = e := eq_of_subset_of_card_le hp
    (by rw [(hH.1.1 e he).1]; simp [hn])
  have hki := (hprivate k hk).1 (hpair.symm ▸ he)
  rw [hki] at hpair
  exact hpair.symm

/-- T22: flipping one same-trait private leaf removes exactly its one
homogeneous edge and adds one mixed edge; every other edge-type assignment
is unchanged. Identification witness in P012-E005, pp. 153--156. -/
theorem leaf_flip_edge_counts (D : Data) (hD : Admissible D)
    (i : ℕ) (hi : i ∈ D.sampled) (hsp : 0 < spare D i) :
    let H := leafCompletion D true
    let K := flipTrait H (u i 0)
    (∀ b : Bool, edgeCount K b+(if D.trait i = b then 1 else 0) = edgeCount H b) ∧
    mixedCount K = mixedCount H+1 := by
  dsimp only
  let H := leafCompletion D true
  let v := u i 0
  let K := flipTrait H v
  let e0 : Finset Vertex := {s i,v}
  have hH : Compatible D H := leafCompletion_compatible D hD true
  obtain ⟨hv,hprivate⟩ := private_leaf_member D hD true i 0 hi hsp
  have he0 : e0 ∈ H.edges := (hprivate i hi).2 rfl
  have hsame : ∀ e ∈ H.edges, e ≠ e0 → ∀ w ∈ e, K.trait w = H.trait w := by
    intro e he hn w hw
    have hwv : w ≠ v := by
      rintro rfl
      exact hn (private_edge_incidence D H hH i hi v hv hprivate e he hw)
    simp [K,flipTrait,Function.update_of_ne hwv]
  have hH0 : ∀ b : Bool, (∀ w ∈ e0, H.trait w = b) ↔ D.trait i = b := by
    intro b
    simp [e0,H,leafCompletion,s,v,u]
  have hK0 : ∀ b : Bool, ¬ (∀ w ∈ e0, K.trait w = b) := by
    intro b
    cases ht : D.trait i <;> cases b <;> simp [e0,K,H,flipTrait,leafCompletion,s,v,u,ht]
  have hHm : ¬ ((∃ w ∈ e0, H.trait w = true) ∧ (∃ w ∈ e0, H.trait w = false)) := by
    cases ht : D.trait i <;> simp [e0,H,leafCompletion,s,v,u,ht]
  have hKm : (∃ w ∈ e0, K.trait w = true) ∧ (∃ w ∈ e0, K.trait w = false) := by
    cases ht : D.trait i <;> simp [e0,K,H,flipTrait,leafCompletion,s,v,u,ht]
  constructor
  · intro b
    have hf : K.edges.filter (fun e => ∀ w ∈ e, K.trait w = b) =
        (H.edges.filter (fun e => ∀ w ∈ e, H.trait w = b)).erase e0 := by
      ext e
      by_cases hn : e = e0
      · subst e
        constructor
        · intro he
          exact False.elim ((hK0 b) (mem_filter.mp he).2)
        · intro he
          exact False.elim ((mem_erase.mp he).1 rfl)
      · constructor
        · intro he
          obtain ⟨he,ht⟩ := mem_filter.mp he
          exact mem_erase.mpr ⟨hn,mem_filter.mpr ⟨he,fun w hw => by rw [← hsame e he hn w hw]; exact ht w hw⟩⟩
        · intro he
          obtain ⟨_,hin⟩ := mem_erase.mp he
          obtain ⟨he,ht⟩ := mem_filter.mp hin
          exact mem_filter.mpr ⟨he,fun w hw => by rw [hsame e he hn w hw]; exact ht w hw⟩
    by_cases hz : D.trait i = b
    · have hin : e0 ∈ H.edges.filter (fun e => ∀ w ∈ e, H.trait w = b) :=
        mem_filter.mpr ⟨he0,(hH0 b).2 hz⟩
      change (K.edges.filter _).card+(if D.trait i = b then 1 else 0) = _
      rw [if_pos hz,hf]
      exact card_erase_add_one hin
    · have hn : e0 ∉ H.edges.filter (fun e => ∀ w ∈ e, H.trait w = b) :=
        fun he => hz ((hH0 b).1 (mem_filter.mp he).2)
      change (K.edges.filter _).card+(if D.trait i = b then 1 else 0) = _
      rw [if_neg hz,hf,erase_eq_of_notMem hn,add_zero]
      rfl
  · have hf : K.edges.filter (fun e => (∃ w ∈ e, K.trait w = true) ∧ (∃ w ∈ e, K.trait w = false)) =
        insert e0 (H.edges.filter (fun e => (∃ w ∈ e, H.trait w = true) ∧ (∃ w ∈ e, H.trait w = false))) := by
      ext e
      by_cases hn : e = e0
      · subst e
        constructor
        · intro he
          exact mem_insert_self _ _
        · intro he
          exact mem_filter.mpr ⟨he0,hKm⟩
      · constructor
        · intro he
          obtain ⟨he,⟨w,hw,hwt⟩,⟨q,hq,hqf⟩⟩ := mem_filter.mp he
          exact mem_insert_of_mem (mem_filter.mpr ⟨he,
            ⟨w,hw,by rw [← hsame e he hn w hw]; exact hwt⟩,
            ⟨q,hq,by rw [← hsame e he hn q hq]; exact hqf⟩⟩)
        · intro he
          obtain ⟨he,⟨w,hw,hwt⟩,⟨q,hq,hqf⟩⟩ := mem_filter.mp ((mem_insert.mp he).resolve_left hn)
          exact mem_filter.mpr ⟨he,
            ⟨w,hw,by rw [hsame e he hn w hw]; exact hwt⟩,
            ⟨q,hq,by rw [hsame e he hn q hq]; exact hqf⟩⟩
    have hn : e0 ∉ H.edges.filter (fun e => (∃ w ∈ e, H.trait w = true) ∧ (∃ w ∈ e, H.trait w = false)) :=
      fun he => hHm (mem_filter.mp he).2
    exact (congrArg Finset.card hf).trans (card_insert_of_notMem hn)

/-- T22 finite algebra: increasing the mixed-edge count strictly decreases
homophily whenever a homogeneous edge exists and both initial trait stub
counts are positive. Identification witness in P012-E005, pp. 153--156. -/
theorem phi_strict_anti_c (x y c C : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hh : 0 < x ∨ 0 < y) (hc : c < C) (hxc : 0 < 2*x+c) (hyc : 0 < 2*y+c) :
    phi x y C < phi x y c := by
  have hxC : 0 < 2*x+C := by linarith
  have hyC : 0 < 2*y+C := by linarith
  have h1 : c/(2*x+c) ≤ C/(2*x+C) := by
    apply (div_le_div_iff₀ hxc hxC).2
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hc.le)]
  have h2 : c/(2*y+c) ≤ C/(2*y+C) := by
    apply (div_le_div_iff₀ hyc hyC).2
    nlinarith [mul_nonneg hy (sub_nonneg.mpr hc.le)]
  rcases hh with hx | hy
  · have hs : c/(2*x+c) < C/(2*x+C) := by
      apply (div_lt_div_iff₀ hxc hxC).2
      nlinarith [mul_pos hx (sub_pos.mpr hc)]
    unfold phi
    linarith
  · have hs : c/(2*y+c) < C/(2*y+C) := by
      apply (div_lt_div_iff₀ hyc hyC).2
      nlinarith [mul_pos hy (sub_pos.mpr hc)]
    unfold phi
    linarith

/-- T22(ii): one private leaf's trait already separates h when any sampled
vertex has spare degree, under the full homophily domain. This fixes the two
witnesses for the identification headline (pp. 153--156). -/
theorem joint_leaf_flip_witness (D : Data) (hD : Admissible D)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (i : ℕ) (hi : i ∈ D.sampled) (hdi : recruitmentDegree D i < D.degree i) :
    Compatible D (leafCompletion D true) ∧
    Compatible D (flipTrait (leafCompletion D true) (u i 0)) ∧
    hValue (leafCompletion D true) ≠ hValue (flipTrait (leafCompletion D true) (u i 0)) := by
  let H := leafCompletion D true
  let K := flipTrait H (u i 0)
  have hH : Compatible D H := leafCompletion_compatible D hD true
  have hsp : 0 < spare D i := by unfold spare; omega
  have hv := (private_leaf_member D hD true i 0 hi hsp).1
  have hK : Compatible D K := corrected_trait_preserves D H K hH (TraitProposal.flip _ hv)
  have htH0 := sampled_trait_positive_transfer D H hH false h0
  have htH1 := sampled_trait_positive_transfer D H hH true h1
  have htK0 := sampled_trait_positive_transfer D K hK false h0
  have htK1 := sampled_trait_positive_transfer D K hK true h1
  have hfH := (graph_homophily_formula H hH.1.1 htH0 htH1).2.2.2
  have hfK := (graph_homophily_formula K hK.1.1 htK0 htK1).2.2.2
  obtain ⟨hcounts,hc⟩ := leaf_flip_edge_counts D hD i hi hsp
  have hxH : (0:ℝ) < 2*(edgeCount H true:ℝ)+mixedCount H := by
    exact_mod_cast ((binary_edge_counts H hH.1.1).1 ▸ htH1)
  have hyH : (0:ℝ) < 2*(edgeCount H false:ℝ)+mixedCount H := by
    exact_mod_cast ((binary_edge_counts H hH.1.1).2.1 ▸ htH0)
  have hxK : (0:ℝ) < 2*(edgeCount K true:ℝ)+mixedCount K := by
    exact_mod_cast ((binary_edge_counts K hK.1.1).1 ▸ htK1)
  have hyK : (0:ℝ) < 2*(edgeCount K false:ℝ)+mixedCount K := by
    exact_mod_cast ((binary_edge_counts K hK.1.1).2.1 ▸ htK0)
  have hstrict : hValue K < hValue H := by
    rw [hfK,hfH]
    have hcR : (mixedCount K:ℝ) = (mixedCount H:ℝ)+1 := by exact_mod_cast hc
    have hct : (mixedCount H:ℝ) < mixedCount K := by linarith
    cases hti : D.trait i
    · have hy : edgeCount K false+1 = edgeCount H false := by simpa [hti] using hcounts false
      have hx : edgeCount K true = edgeCount H true := by simpa [hti] using hcounts true
      have hyR : (edgeCount K false:ℝ)+1 = edgeCount H false := by exact_mod_cast hy
      have hp : (0:ℝ) < edgeCount H false := by linarith [show (0:ℝ) ≤ edgeCount K false from Nat.cast_nonneg _]
      have hm := phi_strict_anti_c (edgeCount H true) (edgeCount H false)
        (mixedCount H) (mixedCount K) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (Or.inr hp) hct hxH hyH
      rw [hx] at hxK ⊢
      have hmY : (0:ℝ) < 2*(edgeCount H false:ℝ)+mixedCount K := by linarith
      exact lt_of_le_of_lt (phi_mono_y _ _ _ _ (Nat.cast_nonneg _) (by linarith) hyK hmY) hm
    · have hx : edgeCount K true+1 = edgeCount H true := by simpa [hti] using hcounts true
      have hy : edgeCount K false = edgeCount H false := by simpa [hti] using hcounts false
      have hxR : (edgeCount K true:ℝ)+1 = edgeCount H true := by exact_mod_cast hx
      have hp : (0:ℝ) < edgeCount H true := by linarith [show (0:ℝ) ≤ edgeCount K true from Nat.cast_nonneg _]
      have hm := phi_strict_anti_c (edgeCount H true) (edgeCount H false)
        (mixedCount H) (mixedCount K) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (Or.inl hp) hct hxH hyH
      rw [hy] at hyK ⊢
      have hmX : (0:ℝ) < 2*(edgeCount H true:ℝ)+mixedCount K := by linarith
      exact lt_of_le_of_lt (phi_mono_x _ _ _ _ (Nat.cast_nonneg _) (by linarith) hxK hmX) hm
  exact ⟨hH,hK,ne_of_gt hstrict⟩


/-- T15 and T24: the actual graph correlation in equation (1) lies in
[-1,1] and is defined whenever both trait degree totals are positive.
Definition 1, p. 155; finite objective estimate, Web Appendix p. 2. -/
theorem homophily_global_range (H : State) (hS : Simple H)
    (h0 : 0 < traitDegree H false) (h1 : 0 < traitDegree H true) :
    HomophilyDefined H ∧ -1 ≤ hValue H ∧ hValue H ≤ 1 := by
  obtain ⟨hm,hd,hpos,hf⟩ := graph_homophily_formula H hS h0 h1
  have hx : (0:ℝ) < 2*(edgeCount H true:ℝ)+mixedCount H := by
    exact_mod_cast ((binary_edge_counts H hS).1 ▸ h1)
  have hy : (0:ℝ) < 2*(edgeCount H false:ℝ)+mixedCount H := by
    exact_mod_cast ((binary_edge_counts H hS).2.1 ▸ h0)
  have hc : (0:ℝ) ≤ mixedCount H := Nat.cast_nonneg _
  have hx0 : (0:ℝ) ≤ edgeCount H true := Nat.cast_nonneg _
  have hy0 : (0:ℝ) ≤ edgeCount H false := Nat.cast_nonneg _
  have hrx0 := div_nonneg hc hx.le
  have hry0 := div_nonneg hc hy.le
  have hrx1 : (mixedCount H:ℝ)/(2*(edgeCount H true:ℝ)+mixedCount H) ≤ 1 :=
    (div_le_one hx).2 (by linarith)
  have hry1 : (mixedCount H:ℝ)/(2*(edgeCount H false:ℝ)+mixedCount H) ≤ 1 :=
    (div_le_one hy).2 (by linarith)
  refine ⟨⟨hm,hpos.ne'⟩,?_,?_⟩ <;> rw [hf] <;> unfold phi <;> linarith

/-- T24 finite estimate: under the ordinary observed-stub domain, every
compatible graph has h in [-1,1] and the actual objective is positive and
at most 1/epsilon. Web Appendix p. 2, display (1), using equation (1), p. 155.
This bound does not assert chain convergence. -/
theorem compatible_objective_bounds (D : Data) (H : State) (hH : Compatible D H)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (ε : ℝ) (hε : 0 < ε) :
    HomophilyDefined H ∧ -1 ≤ hValue H ∧ hValue H ≤ 1 ∧
      0 < objective ε (hValue H) 0 ∧ objective ε (hValue H) 0 ≤ 1/ε := by
  have hr := homophily_global_range H hH.1.1
    (sampled_trait_positive_transfer D H hH false h0)
    (sampled_trait_positive_transfer D H hH true h1)
  have hb := objective_bounds ε (hValue H) 0 hε hr.2.1
  exact ⟨hr.1,hr.2.1,hr.2.2,hb.1,hb.2.1⟩

end
end AronowAudit.P012

