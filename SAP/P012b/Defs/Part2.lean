import SAP.P012b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P012b

open Finset Filter
open scoped Topology
noncomputable section

def removeEdge (H : State) (v w : Vertex) : State :=
  {H with edges := H.edges.erase {v, w}}

def addEdge (H : State) (v w : Vertex) : State :=
  {H with edges := insert {v, w} H.edges}

def addVertex (H : State) (v : Vertex) (t : Bool) : State :=
  {H with vertices := insert v H.vertices, trait := Function.update H.trait v t}

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

def domainA : Data :=
  ⟨{1,2},{1},fun _ => 1,fun i => i-1,fun _ => 1,fun _ => false⟩

def dyad (t1 t2 : Bool) : State :=
  ⟨{s 1,s 2},{{s 1,s 2}},fun v => if v = s 1 then t1 else t2⟩

def domainB : Data := {domainA with seeds := {1,2}, trait := fun i => i == 2}

def domainC : Data := ⟨{1},{1},fun _ => 1,id,fun _ => 0,fun _ => false⟩

def domainCState : State := ⟨{s 1},∅,fun _ => false⟩

def domainD : Data :=
  ⟨{1,2},{1},fun _ => 1,fun i => i-1,fun i => if i = 1 then 1 else 4,fun _ => true⟩

def domainDState (t3 t4 t5 : Bool) : State :=
  ⟨{s 1,s 2,u 3 0,u 4 0,u 5 0},
    {{s 1,s 2},{s 2,u 3 0},{s 2,u 4 0},{s 2,u 5 0}},
    fun v => if v = u 3 0 then t3 else if v = u 4 0 then t4
      else if v = u 5 0 then t5 else true⟩

def figureData : Data :=
  ⟨{1,2,3,4,5},{1},fun j => if j = 3 ∨ j = 5 then 2 else 1,id,
    fun i => if i = 1 then 5 else if i = 2 then 4 else if i = 5 then 2 else 3,
    fun i => !(i == 4)⟩

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

/- Algebraic supporting lemmas: these are separately audited, not substitutes
   for the graph theorems exact_h_region and exact_p_region. -/

def cooling (ε T₁ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then T₁ else 1/(ε*Real.log ((n:ℝ)+1))

end
end SAP.P012b
