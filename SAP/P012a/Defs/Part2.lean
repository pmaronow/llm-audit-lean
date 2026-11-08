import SAP.P012a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a

open Finset
open scoped Classical
noncomputable section

/-! Finite sampled data, augmented graphs, partial functionals and explicit witnesses.
Names `s i` denote sampled labels and `u i k` fresh labels; membership determines sampling.
Natural-number times represent the distinct recruitment order. -/

def removeEdge (H : State) (v w : Vertex) : State :=
  {H with edges := H.edges.erase {v, w}}

def addEdge (H : State) (v w : Vertex) : State :=
  {H with edges := insert {v, w} H.edges}

def addVertex (H : State) (v : Vertex) (t : Bool) : State :=
  {H with vertices := insert v H.vertices, trait := Function.update H.trait v t}

def flipTrait (H : State) (v : Vertex) : State :=
  {H with trait := Function.update H.trait v (!H.trait v)}

def unsampled (D : Data) (H : State) : Finset Vertex := H.vertices \ sampledVertices D

def replacementPool (D : Data) (H : State) (i : ℕ) : Finset Vertex :=
  (unsampled D H).filter (fun v => {s i, v} ∉ H.edges)

def cleanup (D : Data) (repaired : Bool) (H : State) : State :=
  {H with vertices := H.vertices.filter (fun v =>
    (repaired = true ∧ v ∈ sampledVertices D) ∨ graphDegree H v ≠ 0)}

inductive Replacement (D : Data) (current pendingState : State) (i : ℕ) : Vertex → State → Prop
  | existing (v : Vertex) (hv : v ∈ replacementPool D current i) :
      Replacement D current pendingState i v pendingState
  | fresh (v : Vertex) (hv : v ∉ pendingState.vertices) (t : Bool) :
      Replacement D current pendingState i v (addVertex pendingState v t)

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

inductive TraitProposal (D : Data) (repaired : Bool) (H : State) : State → Prop
  | flip (v : Vertex) (hv : v ∈ unsampled D H) : TraitProposal D repaired H (flipTrait H v)
  | empty (hr : repaired = true) (hu : unsampled D H = ∅) : TraitProposal D repaired H H

def Proposal (D : Data) (repaired : Bool) (H K : State) : Prop :=
  GraphProposal D repaired H K ∨ TraitProposal D repaired H K

abbrev GraphCompatible (D : Data) (H : State) : Prop :=
  Augmented D H ∧ sampledVertices D ⊆ H.vertices ∧
  recruitmentEdges D ⊆ H.edges ∧
  (∀ v ∈ H.vertices, v ∉ sampledVertices D →
    ∃ i ∈ D.sampled, {s i,v} ∈ H.edges) ∧
  (∀ i ∈ D.sampled, graphDegree H (s i) = D.degree i)

def proposalData : Data :=
  ⟨{1,2}, {1}, fun _ => 1, id, fun i => if i = 1 then 2 else 1,
    fun i => i == 2⟩

def proposalStart : State :=
  ⟨{s 1,s 2,u 3 0}, {{s 1,s 2},{s 1,u 3 0}}, fun v => decide (v = s 2)⟩

def proposalBad (t : Bool) : State :=
  cleanup proposalData false (addEdge
    (addEdge (addVertex (removeEdge proposalStart (s 1) (u 3 0)) (u 4 0) t)
      (s 1) (u 4 0)) (u 3 0) (u 4 0))

def proofStepData : Data :=
  ⟨{1,2,3}, {1}, fun j => if j = 3 then 2 else 1, id,
    fun i => if i = 2 then 2 else 3, fun i => i == 3⟩

def result1BadStart : State :=
  ⟨{s 1,s 2,s 3,u 4 0},
    {{s 1,s 2},{s 2,s 3},{s 1,s 3},{s 1,u 4 0},{s 3,u 4 0}},
    fun v => decide (v = s 3)⟩

def result1BadEnd : State :=
  cleanup proofStepData true
    (addEdge (removeEdge (removeEdge result1BadStart (s 1) (u 4 0))
      (s 3) (u 4 0)) (s 1) (s 3))

def result2BadStart : State :=
  ⟨{s 1,s 2,s 3,u 4 0,u 5 0},
    {{s 1,s 2},{s 2,s 3},{s 1,u 4 0},{s 3,u 5 0},{s 1,u 5 0},{s 3,u 4 0}},
    fun v => decide (v = s 3) || decide (v = u 5 0)⟩

def result2BadEnd : State :=
  addEdge (addEdge (removeEdge (removeEdge result2BadStart (s 1) (u 4 0))
    (s 3) (u 5 0)) (s 1) (u 5 0)) (s 3) (u 4 0)

def a2Data : Data :=
  ⟨{1,2,3}, {1}, fun _ => 1, fun i => i-1,
    fun i => if i = 1 then 3 else 1, fun _ => true⟩

def a2State (t : Bool) : State :=
  ⟨{s 1,s 2,s 3,u 4 0}, {{s 1,s 2},{s 1,s 3},{s 1,u 4 0}},
    fun v => match v with | Sum.inl _ => true | Sum.inr _ => t⟩

def domainA : Data :=
  ⟨{1,2},{1},fun _ => 1,fun i => i-1,fun _ => 1,fun _ => false⟩

def dyad (t1 t2 : Bool) : State :=
  ⟨{s 1,s 2},{{s 1,s 2}},fun v => if v = s 1 then t1 else t2⟩

def proposalDataB : Data :=
  ⟨{1,2,3},{1},fun j => if j = 3 then 2 else 1,id,
    fun i => if i = 2 then 3 else 1,fun i => i == 2⟩

def proposalStartB : State :=
  ⟨{s 1,s 2,s 3,u 4 0}, {{s 1,s 2},{s 2,s 3},{s 2,u 4 0}}, fun v => decide (v = s 2)⟩

def proposalBadB (t : Bool) : State :=
  cleanup proposalDataB false (addEdge
    (addEdge (addVertex (removeEdge proposalStartB (s 2) (u 4 0)) (u 5 0) t)
      (s 2) (u 5 0)) (u 4 0) (u 5 0))

def cleanupData : Data :=
  ⟨{1,2,3},{1,3},fun _ => 1,id,fun i => if i = 3 then 0 else 1,fun i => i == 2⟩

def cleanupStart : State :=
  ⟨{s 1,s 2,s 3},{{s 1,s 2}},fun v => decide (v = s 2)⟩

def emptyPoolData : Data := {domainA with trait := fun i => i == 2}

end
end SAP.P012a
