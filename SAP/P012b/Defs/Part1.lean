import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P012b

open Finset Filter
open scoped Topology
noncomputable section

abbrev Vertex := ℕ ⊕ (ℕ × ℕ)

def s (i : ℕ) : Vertex := Sum.inl i

def u (i k : ℕ) : Vertex := Sum.inr (i, k)

structure Data where
  sampled : Finset ℕ
  seeds : Finset ℕ
  parent : ℕ → ℕ
  time : ℕ → ℕ
  degree : ℕ → ℕ
  trait : ℕ → Bool

structure State where
  vertices : Finset Vertex
  edges : Finset (Finset Vertex)
  trait : Vertex → Bool

def nonseeds (D : Data) : Finset ℕ := D.sampled \ D.seeds

def sampledVertices (D : Data) : Finset Vertex := D.sampled.image s

def recruitmentEdges (D : Data) : Finset (Finset Vertex) :=
  (nonseeds D).image (fun j => {s (D.parent j), s j})

def graphDegree (H : State) (v : Vertex) : ℕ :=
  (H.edges.filter (fun e => v ∈ e)).card

def recruitmentDegree (D : Data) (i : ℕ) : ℕ :=
  ((recruitmentEdges D).filter (fun e => s i ∈ e)).card

def spare (D : Data) (i : ℕ) : ℕ := D.degree i - recruitmentDegree D i

def sampledTraitDegree (D : Data) (z : Bool) : ℕ :=
  ∑ i ∈ D.sampled.filter (fun i => D.trait i = z), D.degree i

abbrev Admissible (D : Data) : Prop :=
  D.seeds ⊆ D.sampled ∧
  (∀ i ∈ D.sampled, ∀ j ∈ D.sampled, D.time i = D.time j → i = j) ∧
  (∀ j ∈ nonseeds D, D.parent j ∈ D.sampled ∧ D.time (D.parent j) < D.time j) ∧
  (∀ i ∈ D.sampled, recruitmentDegree D i ≤ D.degree i)

abbrev Simple (H : State) : Prop :=
  ∀ e ∈ H.edges, e.card = 2 ∧ e ⊆ H.vertices

abbrev Augmented (D : Data) (H : State) : Prop :=
  Simple H ∧ ∀ e ∈ H.edges, ∃ i ∈ D.sampled, s i ∈ e

abbrev Compatible (D : Data) (H : State) : Prop :=
  Augmented D H ∧ sampledVertices D ⊆ H.vertices ∧
  recruitmentEdges D ⊆ H.edges ∧
  (∀ i ∈ D.sampled, H.trait (s i) = D.trait i) ∧
  (∀ v ∈ H.vertices, v ∉ sampledVertices D →
    ∃ i ∈ D.sampled, {s i, v} ∈ H.edges) ∧
  (∀ i ∈ D.sampled, graphDegree H (s i) = D.degree i)

def adjacency (H : State) (v w : Vertex) : ℝ :=
  if v ≠ w ∧ {v, w} ∈ H.edges then 1 else 0

def z (H : State) (v : Vertex) : ℝ := if H.trait v then 1 else 0

def hNumerator (H : State) : ℝ :=
  ∑ v ∈ H.vertices, ∑ w ∈ H.vertices,
    (adjacency H v w - (graphDegree H v : ℝ) * graphDegree H w /
      (2 * (H.edges.card : ℝ))) * z H v * z H w

def hDenominator (H : State) : ℝ :=
  ∑ v ∈ H.vertices, ∑ w ∈ H.vertices,
    ((if v = w then (graphDegree H v : ℝ) else 0) -
      (graphDegree H v : ℝ) * graphDegree H w / (2 * (H.edges.card : ℝ))) *
      z H v * z H w

def hValue (H : State) : ℝ := hNumerator H / hDenominator H

abbrev HomophilyDefined (H : State) : Prop := 0 < H.edges.card ∧ hDenominator H ≠ 0

noncomputable def homophily (H : State) : Option ℝ :=
  if HomophilyDefined H then some (hValue H) else none

@[simp] def notYetSampled (D : Data) (j : ℕ) (v : Vertex) : Bool :=
  match v with
  | Sum.inl k => decide (k ∉ D.sampled ∨ D.time j ≤ D.time k)
  | Sum.inr _ => true

def susceptible (D : Data) (H : State) (i j : ℕ) : Finset Vertex :=
  H.vertices.filter (fun v => {s i,v} ∈ H.edges ∧ notYetSampled D j v = true)

def sameSusceptible (D : Data) (H : State) (i j : ℕ) : Finset Vertex :=
  (susceptible D H i j).filter (fun v => H.trait v = H.trait (s i))

def pSum (D : Data) (H : State) : ℝ :=
  ∑ j ∈ nonseeds D,
    ((if H.trait (s j) = H.trait (s (D.parent j)) then (1 : ℝ) else 0) -
      (sameSusceptible D H (D.parent j) j).card /
      ((susceptible D H (D.parent j) j).card : ℝ))

def pValue (D : Data) (H : State) : ℝ := pSum D H / (nonseeds D).card

abbrev PreferentialDefined (D : Data) (H : State) : Prop :=
  0 < (nonseeds D).card ∧
  ∀ j ∈ nonseeds D, 0 < (susceptible D H (D.parent j) j).card

noncomputable def preferential (D : Data) (H : State) : Option ℝ :=
  if PreferentialDefined D H then some (pValue D H) else none

def traitDegree (H : State) (b : Bool) : ℕ :=
  ∑ v ∈ H.vertices.filter (fun v => H.trait v = b), graphDegree H v

def recruitmentState (D : Data) : State :=
  ⟨sampledVertices D, recruitmentEdges D,
    fun v => match v with | Sum.inl i => D.trait i | Sum.inr _ => false⟩

def hValues (D : Data) : Set ℝ := {r | ∃ H, Compatible D H ∧ homophily H = some r}

def pValues (D : Data) : Set ℝ := {r | ∃ H, Compatible D H ∧ preferential D H = some r}

def FullHomophilyRegion (D : Data) (L U : ℝ) : Prop :=
  (∀ H, Compatible D H → HomophilyDefined H) ∧
  IsLeast (hValues D) L ∧ IsGreatest (hValues D) U

def FullPreferentialRegion (D : Data) (L U : ℝ) : Prop :=
  (∀ H, Compatible D H → PreferentialDefined D H) ∧
  IsLeast (pValues D) L ∧ IsGreatest (pValues D) U

def PointIdentified (values : Set ℝ) : Prop := ∃ r, values = {r}

def leafVertices (D : Data) : Finset Vertex :=
  D.sampled.biUnion (fun i => (range (spare D i)).image (u i))

def leafEdges (D : Data) : Finset (Finset Vertex) :=
  D.sampled.biUnion (fun i => (range (spare D i)).image (fun k => {s i, u i k}))

def leafCompletion (D : Data) (same : Bool) : State :=
  ⟨sampledVertices D ∪ leafVertices D, recruitmentEdges D ∪ leafEdges D,
    fun v => match v with
      | Sum.inl i => D.trait i
      | Sum.inr (i, _) => if same then D.trait i else !(D.trait i)⟩

def induced (D : Data) (H : State) : State :=
  ⟨sampledVertices D, H.edges.filter (fun e => e ⊆ sampledVertices D), H.trait⟩

def InducedCompatible (D : Data) (H : State) : Prop :=
  Simple H ∧ H.vertices = sampledVertices D ∧ recruitmentEdges D ⊆ H.edges ∧
  ∀ i ∈ D.sampled, graphDegree H (s i) ≤ D.degree i

def flipTrait (H : State) (v : Vertex) : State :=
  {H with trait := Function.update H.trait v (!H.trait v)}

def unsampled (D : Data) (H : State) : Finset Vertex := H.vertices \ sampledVertices D

abbrev GraphCompatible (D : Data) (H : State) : Prop :=
  Augmented D H ∧ sampledVertices D ⊆ H.vertices ∧
  recruitmentEdges D ⊆ H.edges ∧
  (∀ v ∈ H.vertices, v ∉ sampledVertices D →
    ∃ i ∈ D.sampled, {s i,v} ∈ H.edges) ∧
  (∀ i ∈ D.sampled, graphDegree H (s i) = D.degree i)

def children (D : Data) (i : ℕ) : Finset ℕ :=
  (nonseeds D).filter (fun j => D.parent j = i)

def degreeTraitSum (H : State) : ℝ := ∑ v ∈ H.vertices, (graphDegree H v : ℝ)*z H v

end
end SAP.P012b
