import SAP.P012a.Defs
import AronowAudit.P012.P012_Identification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.Bridge

open SAP.P012a
open scoped Classical
noncomputable section

def data (D : Data) : AronowAudit.P012.Data :=
  ⟨D.sampled, D.seeds, D.parent, D.time, D.degree, D.trait⟩

def backData (D : AronowAudit.P012.Data) : Data :=
  ⟨D.sampled, D.seeds, D.parent, D.time, D.degree, D.trait⟩

def state (H : State) : AronowAudit.P012.State :=
  ⟨H.vertices, H.edges, H.trait⟩

def backState (H : AronowAudit.P012.State) : State :=
  ⟨H.vertices, H.edges, H.trait⟩

@[simp] theorem data_back (D : AronowAudit.P012.Data) : data (backData D) = D := rfl
@[simp] theorem back_data (D : Data) : backData (data D) = D := rfl
@[simp] theorem state_back (H : AronowAudit.P012.State) : state (backState H) = H := rfl
@[simp] theorem back_state (H : State) : backState (state H) = H := rfl

@[simp] theorem forall_state (P : AronowAudit.P012.State → Prop) :
    (∀ H, P H) ↔ ∀ H : State, P (state H) := by
  constructor
  · intro h H; exact h (state H)
  · intro h H; simpa only [state_back] using h (backState H)

@[simp] theorem exists_state (P : AronowAudit.P012.State → Prop) :
    (∃ H, P H) ↔ ∃ H : State, P (state H) := by
  constructor
  · rintro ⟨H, hH⟩
    exact ⟨backState H, by simpa only [state_back] using hH⟩
  · rintro ⟨H, hH⟩; exact ⟨state H, hH⟩

@[simp] theorem vertices_eq (H : State) : (state H).vertices = H.vertices := rfl
@[simp] theorem edges_eq (H : State) : (state H).edges = H.edges := rfl
@[simp] theorem trait_eq (H : State) : (state H).trait = H.trait := rfl
@[simp] theorem sampled_eq (D : Data) : (data D).sampled = D.sampled := rfl
@[simp] theorem seeds_eq (D : Data) : (data D).seeds = D.seeds := rfl
@[simp] theorem parent_eq (D : Data) : (data D).parent = D.parent := rfl
@[simp] theorem time_eq (D : Data) : (data D).time = D.time := rfl
@[simp] theorem degree_eq (D : Data) : (data D).degree = D.degree := rfl
@[simp] theorem data_trait_eq (D : Data) : (data D).trait = D.trait := rfl
@[simp] theorem s_eq : AronowAudit.P012.s = s := rfl
@[simp] theorem u_eq : AronowAudit.P012.u = u := rfl
@[simp] theorem state_inj (H K : State) : state H = state K ↔ H = K := by
  constructor
  · intro h; have := congrArg backState h; simpa only [back_state] using this
  · exact congrArg state

@[simp] theorem nonseeds_eq (D : Data) :
    AronowAudit.P012.nonseeds (data D) = SAP.P012a.nonseeds D := rfl

@[simp] theorem sampledVertices_eq (D : Data) :
    AronowAudit.P012.sampledVertices (data D) = SAP.P012a.sampledVertices D := rfl

@[simp] theorem recruitmentEdges_eq (D : Data) :
    AronowAudit.P012.recruitmentEdges (data D) = SAP.P012a.recruitmentEdges D := rfl

@[simp] theorem graphDegree_eq (H : State) (v : Vertex) :
    AronowAudit.P012.graphDegree (state H) v = SAP.P012a.graphDegree H v := rfl

@[simp] theorem recruitmentDegree_eq (D : Data) (i : ℕ) :
    AronowAudit.P012.recruitmentDegree (data D) i = SAP.P012a.recruitmentDegree D i := rfl

@[simp] theorem spare_eq (D : Data) (i : ℕ) :
    AronowAudit.P012.spare (data D) i = SAP.P012a.spare D i := rfl

@[simp] theorem totalSpare_eq (D : Data) :
    AronowAudit.P012.totalSpare (data D) = SAP.P012a.totalSpare D := rfl

@[simp] theorem a_eq (D : Data) :
    AronowAudit.P012.a (data D) = SAP.P012a.a D := rfl

@[simp] theorem b_eq (D : Data) :
    AronowAudit.P012.b (data D) = SAP.P012a.b D := rfl

@[simp] theorem cR_eq (D : Data) :
    AronowAudit.P012.cR (data D) = SAP.P012a.cR D := rfl

@[simp] theorem hLower_eq (D : Data) :
    AronowAudit.P012.hLower (data D) = SAP.P012a.hLower D := rfl

@[simp] theorem hUpper_eq (D : Data) :
    AronowAudit.P012.hUpper (data D) = SAP.P012a.hUpper D := rfl

@[simp] theorem pLower_eq (D : Data) :
    AronowAudit.P012.pLower (data D) = SAP.P012a.pLower D := rfl

@[simp] theorem pUpper_eq (D : Data) :
    AronowAudit.P012.pUpper (data D) = SAP.P012a.pUpper D := rfl

@[simp] theorem leafVertices_eq (D : Data) :
    AronowAudit.P012.leafVertices (data D) = SAP.P012a.leafVertices D := rfl

@[simp] theorem leafEdges_eq (D : Data) :
    AronowAudit.P012.leafEdges (data D) = SAP.P012a.leafEdges D := rfl

@[simp] theorem traitSpare_eq (D : Data) (t : Bool) :
    AronowAudit.P012.traitSpare (data D) t = SAP.P012a.traitSpare D t := rfl

@[simp] theorem sampledTraitDegree_eq (D : Data) (t : Bool) :
    AronowAudit.P012.sampledTraitDegree (data D) t = SAP.P012a.sampledTraitDegree D t := rfl

@[simp] theorem Admissible_eq (D : Data) :
    AronowAudit.P012.Admissible (data D) = SAP.P012a.Admissible D := rfl

@[simp] theorem Simple_eq (H : State) :
    AronowAudit.P012.Simple (state H) = SAP.P012a.Simple H := rfl

@[simp] theorem HomophilyDefined_eq (H : State) :
    AronowAudit.P012.HomophilyDefined (state H) = SAP.P012a.HomophilyDefined H := rfl

@[simp] theorem PreferentialDefined_eq (D : Data) (H : State) :
    AronowAudit.P012.PreferentialDefined (data D) (state H) = SAP.P012a.PreferentialDefined D H := rfl

@[simp] theorem Augmented_eq (D : Data) (H : State) :
    AronowAudit.P012.Augmented (data D) (state H) = SAP.P012a.Augmented D H := rfl

@[simp] theorem Compatible_eq (D : Data) (H : State) :
    AronowAudit.P012.Compatible (data D) (state H) = SAP.P012a.Compatible D H := rfl

@[simp] theorem GraphCompatible_eq (D : Data) (H : State) :
    AronowAudit.P012.GraphCompatible (data D) (state H) = SAP.P012a.GraphCompatible D H := rfl

@[simp] theorem adjacency_eq (H : State) (v w : Vertex) :
    AronowAudit.P012.adjacency (state H) v w = SAP.P012a.adjacency H v w := rfl

@[simp] theorem z_eq (H : State) (v : Vertex) :
    AronowAudit.P012.z (state H) v = SAP.P012a.z H v := rfl

@[simp] theorem hNumerator_eq (H : State) :
    AronowAudit.P012.hNumerator (state H) = SAP.P012a.hNumerator H := rfl

@[simp] theorem hDenominator_eq (H : State) :
    AronowAudit.P012.hDenominator (state H) = SAP.P012a.hDenominator H := rfl

@[simp] theorem hValue_eq (H : State) :
    AronowAudit.P012.hValue (state H) = SAP.P012a.hValue H := rfl

@[simp] theorem homophily_eq (H : State) :
    AronowAudit.P012.homophily (state H) = SAP.P012a.homophily H := rfl

@[simp] theorem mixedCount_eq (H : State) :
    AronowAudit.P012.mixedCount (state H) = SAP.P012a.mixedCount H := rfl

@[simp] theorem degreeTraitSum_eq (H : State) :
    AronowAudit.P012.degreeTraitSum (state H) = SAP.P012a.degreeTraitSum H := rfl

@[simp] theorem notYetSampled_eq (D : Data) (j : ℕ) (v : Vertex) :
    AronowAudit.P012.notYetSampled (data D) j v = SAP.P012a.notYetSampled D j v := rfl

@[simp] theorem susceptible_eq (D : Data) (H : State) (i j : ℕ) :
    AronowAudit.P012.susceptible (data D) (state H) i j = SAP.P012a.susceptible D H i j := rfl

@[simp] theorem sameSusceptible_eq (D : Data) (H : State) (i j : ℕ) :
    AronowAudit.P012.sameSusceptible (data D) (state H) i j = SAP.P012a.sameSusceptible D H i j := rfl

@[simp] theorem pSum_eq (D : Data) (H : State) :
    AronowAudit.P012.pSum (data D) (state H) = SAP.P012a.pSum D H := rfl

@[simp] theorem pValue_eq (D : Data) (H : State) :
    AronowAudit.P012.pValue (data D) (state H) = SAP.P012a.pValue D H := rfl

@[simp] theorem preferential_eq (D : Data) (H : State) :
    AronowAudit.P012.preferential (data D) (state H) = SAP.P012a.preferential D H := rfl

@[simp] theorem unsampled_eq (D : Data) (H : State) :
    AronowAudit.P012.unsampled (data D) (state H) = SAP.P012a.unsampled D H := rfl

@[simp] theorem traitDegree_eq (H : State) (t : Bool) :
    AronowAudit.P012.traitDegree (state H) t = SAP.P012a.traitDegree H t := rfl

@[simp] theorem edgeCount_eq (H : State) (t : Bool) :
    AronowAudit.P012.edgeCount (state H) t = SAP.P012a.edgeCount H t := rfl

@[simp] theorem phi_eq (x y c : ℝ) :
    AronowAudit.P012.phi x y c = SAP.P012a.phi x y c := rfl

@[simp] theorem laterChildren_eq (D : Data) (j : ℕ) :
    AronowAudit.P012.laterChildren (data D) j = SAP.P012a.laterChildren D j := rfl

@[simp] theorem childMatches_eq (D : Data) (j : ℕ) :
    AronowAudit.P012.childMatches (data D) j = SAP.P012a.childMatches D j := rfl

@[simp] theorem observedMatch_eq (D : Data) (j : ℕ) :
    AronowAudit.P012.observedMatch (data D) j = SAP.P012a.observedMatch D j := rfl

@[simp] theorem InducedCompatible_eq (D : Data) (H : State) :
    AronowAudit.P012.InducedCompatible (data D) (state H) = SAP.P012a.InducedCompatible D H := rfl

@[simp] theorem replacementPool_eq (D : Data) (H : State) (i : ℕ) :
    AronowAudit.P012.replacementPool (data D) (state H) i = SAP.P012a.replacementPool D H i := rfl

@[simp] theorem recruitmentState_eq (D : Data) :
    AronowAudit.P012.recruitmentState (data D) = state (SAP.P012a.recruitmentState D) := rfl

@[simp] theorem leafCompletion_eq (D : Data) (t : Bool) :
    AronowAudit.P012.leafCompletion (data D) t = state (SAP.P012a.leafCompletion D t) := rfl

@[simp] theorem induced_eq (D : Data) (H : State) :
    AronowAudit.P012.induced (data D) (state H) = state (SAP.P012a.induced D H) := rfl

@[simp] theorem removeEdge_eq (H : State) (v w : Vertex) :
    AronowAudit.P012.removeEdge (state H) v w = state (SAP.P012a.removeEdge H v w) := rfl

@[simp] theorem addEdge_eq (H : State) (v w : Vertex) :
    AronowAudit.P012.addEdge (state H) v w = state (SAP.P012a.addEdge H v w) := rfl

@[simp] theorem addVertex_eq (H : State) (v : Vertex) (t : Bool) :
    AronowAudit.P012.addVertex (state H) v t = state (SAP.P012a.addVertex H v t) := rfl

@[simp] theorem flipTrait_eq (H : State) (v : Vertex) :
    AronowAudit.P012.flipTrait (state H) v = state (SAP.P012a.flipTrait H v) := rfl

@[simp] theorem cleanup_eq (D : Data) (t : Bool) (H : State) :
    AronowAudit.P012.cleanup (data D) t (state H) = state (SAP.P012a.cleanup D t H) := rfl

end
end SAP.P012a.Bridge
