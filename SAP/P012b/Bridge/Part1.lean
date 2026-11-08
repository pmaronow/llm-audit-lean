import SAP.P012b.Defs
import AronowAudit.P012.P012_Identification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012b.Bridge

open Finset Filter
open scoped Topology
noncomputable section

def toData (D : Data) : AronowAudit.P012.Data :=
  ⟨D.sampled, D.seeds, D.parent, D.time, D.degree, D.trait⟩
def fromData (D : AronowAudit.P012.Data) : Data :=
  ⟨D.sampled, D.seeds, D.parent, D.time, D.degree, D.trait⟩
def toState (H : State) : AronowAudit.P012.State := ⟨H.vertices, H.edges, H.trait⟩
def fromState (H : AronowAudit.P012.State) : State := ⟨H.vertices, H.edges, H.trait⟩

@[simp] theorem from_to_data (D : Data) : fromData (toData D) = D := rfl
@[simp] theorem to_from_data (D : AronowAudit.P012.Data) : toData (fromData D) = D := rfl
@[simp] theorem from_to_state (H : State) : fromState (toState H) = H := rfl
@[simp] theorem to_from_state (H : AronowAudit.P012.State) : toState (fromState H) = H := rfl
@[simp] theorem toData_inj (D E : Data) : toData D = toData E ↔ D = E := by
  constructor
  · intro h; exact congrArg fromData h
  · rintro rfl; rfl
@[simp] theorem toState_inj (H K : State) : toState H = toState K ↔ H = K := by
  constructor
  · intro h; exact congrArg fromState h
  · rintro rfl; rfl

@[simp] theorem forall_data (P : AronowAudit.P012.Data → Prop) :
    (∀ D, P D) ↔ ∀ D : Data, P (toData D) := by
  constructor
  · intro h D; exact h _
  · intro h D; simpa only [to_from_data] using h (fromData D)
@[simp] theorem forall_state (P : AronowAudit.P012.State → Prop) :
    (∀ H, P H) ↔ ∀ H : State, P (toState H) := by
  constructor
  · intro h H; exact h _
  · intro h H; simpa only [to_from_state] using h (fromState H)
@[simp] theorem exists_state (P : AronowAudit.P012.State → Prop) :
    (∃ H, P H) ↔ ∃ H : State, P (toState H) := by
  constructor
  · rintro ⟨H,h⟩; exact ⟨fromState H, by simpa only [to_from_state] using h⟩
  · rintro ⟨H,h⟩; exact ⟨toState H,h⟩

@[simp] theorem data_sampled (D : Data) : (toData D).sampled = D.sampled := rfl
@[simp] theorem data_seeds (D : Data) : (toData D).seeds = D.seeds := rfl
@[simp] theorem data_parent (D : Data) : (toData D).parent = D.parent := rfl
@[simp] theorem data_time (D : Data) : (toData D).time = D.time := rfl
@[simp] theorem data_degree (D : Data) : (toData D).degree = D.degree := rfl
@[simp] theorem data_trait (D : Data) : (toData D).trait = D.trait := rfl
@[simp] theorem state_vertices (H : State) : (toState H).vertices = H.vertices := rfl
@[simp] theorem state_edges (H : State) : (toState H).edges = H.edges := rfl
@[simp] theorem state_trait (H : State) : (toState H).trait = H.trait := rfl

@[simp] theorem nonseeds_eq (D : Data) :
    AronowAudit.P012.nonseeds (toData D) = nonseeds D := rfl
@[simp] theorem sampledVertices_eq (D : Data) :
    AronowAudit.P012.sampledVertices (toData D) = sampledVertices D := rfl
@[simp] theorem recruitmentEdges_eq (D : Data) :
    AronowAudit.P012.recruitmentEdges (toData D) = recruitmentEdges D := rfl
@[simp] theorem graphDegree_eq (H : State) (v : Vertex) :
    AronowAudit.P012.graphDegree (toState H) v = graphDegree H v := rfl
@[simp] theorem recruitmentDegree_eq (D : Data) (i : ℕ) :
    AronowAudit.P012.recruitmentDegree (toData D) i = recruitmentDegree D i := rfl
@[simp] theorem spare_eq (D : Data) (i : ℕ) :
    AronowAudit.P012.spare (toData D) i = spare D i := rfl
@[simp] theorem sampledTraitDegree_eq (D : Data) (t : Bool) :
    AronowAudit.P012.sampledTraitDegree (toData D) t = sampledTraitDegree D t := rfl
@[simp] theorem Admissible_eq (D : Data) :
    AronowAudit.P012.Admissible (toData D) = Admissible D := rfl
@[simp] theorem Simple_eq (H : State) :
    AronowAudit.P012.Simple (toState H) = Simple H := rfl
@[simp] theorem Augmented_eq (D : Data) (H : State) :
    AronowAudit.P012.Augmented (toData D) (toState H) = Augmented D H := rfl
@[simp] theorem Compatible_eq (D : Data) (H : State) :
    AronowAudit.P012.Compatible (toData D) (toState H) = Compatible D H := rfl
@[simp] theorem GraphCompatible_eq (D : Data) (H : State) :
    AronowAudit.P012.GraphCompatible (toData D) (toState H) = GraphCompatible D H := rfl
@[simp] theorem InducedCompatible_eq (D : Data) (H : State) :
    AronowAudit.P012.InducedCompatible (toData D) (toState H) = InducedCompatible D H := rfl
@[simp] theorem hNumerator_eq (H : State) :
    AronowAudit.P012.hNumerator (toState H) = hNumerator H := rfl
@[simp] theorem hDenominator_eq (H : State) :
    AronowAudit.P012.hDenominator (toState H) = hDenominator H := rfl
@[simp] theorem hValue_eq (H : State) :
    AronowAudit.P012.hValue (toState H) = hValue H := rfl
@[simp] theorem HomophilyDefined_eq (H : State) :
    AronowAudit.P012.HomophilyDefined (toState H) = HomophilyDefined H := rfl
@[simp] theorem homophily_eq (H : State) :
    AronowAudit.P012.homophily (toState H) = homophily H := rfl
@[simp] theorem susceptible_eq (D : Data) (H : State) (i j : ℕ) :
    AronowAudit.P012.susceptible (toData D) (toState H) i j = susceptible D H i j := rfl
@[simp] theorem pSum_eq (D : Data) (H : State) :
    AronowAudit.P012.pSum (toData D) (toState H) = pSum D H := rfl
@[simp] theorem pValue_eq (D : Data) (H : State) :
    AronowAudit.P012.pValue (toData D) (toState H) = pValue D H := rfl
@[simp] theorem PreferentialDefined_eq (D : Data) (H : State) :
    AronowAudit.P012.PreferentialDefined (toData D) (toState H) = PreferentialDefined D H := rfl
@[simp] theorem preferential_eq (D : Data) (H : State) :
    AronowAudit.P012.preferential (toData D) (toState H) = preferential D H := rfl
@[simp] theorem traitDegree_eq (H : State) (t : Bool) :
    AronowAudit.P012.traitDegree (toState H) t = traitDegree H t := rfl
@[simp] theorem unsampled_eq (D : Data) (H : State) :
    AronowAudit.P012.unsampled (toData D) (toState H) = unsampled D H := rfl
@[simp] theorem replacementPool_eq (D : Data) (H : State) (i : ℕ) :
    AronowAudit.P012.replacementPool (toData D) (toState H) i = replacementPool D H i := rfl
@[simp] theorem children_eq (D : Data) (i : ℕ) :
    AronowAudit.P012.children (toData D) i = children D i := rfl
@[simp] theorem degreeTraitSum_eq (H : State) :
    AronowAudit.P012.degreeTraitSum (toState H) = degreeTraitSum H := rfl
@[simp] theorem PointIdentified_eq (S : Set ℝ) :
    AronowAudit.P012.PointIdentified S = PointIdentified S := rfl
@[simp] theorem cooling_eq (ε T₁ : ℝ) (n : ℕ) :
    AronowAudit.P012.cooling ε T₁ n = cooling ε T₁ n := rfl
@[simp] theorem leafCompletion_eq (D : Data) (t : Bool) :
    AronowAudit.P012.leafCompletion (toData D) t = toState (leafCompletion D t) := rfl
@[simp] theorem recruitmentState_eq (D : Data) :
    AronowAudit.P012.recruitmentState (toData D) = toState (recruitmentState D) := rfl
@[simp] theorem induced_eq (D : Data) (H : State) :
    AronowAudit.P012.induced (toData D) (toState H) = toState (induced D H) := rfl
@[simp] theorem flipTrait_eq (H : State) (v : Vertex) :
    AronowAudit.P012.flipTrait (toState H) v = toState (flipTrait H v) := rfl
@[simp] theorem removeEdge_eq (H : State) (v w : Vertex) :
    AronowAudit.P012.removeEdge (toState H) v w = toState (removeEdge H v w) := rfl
@[simp] theorem addEdge_eq (H : State) (v w : Vertex) :
    AronowAudit.P012.addEdge (toState H) v w = toState (addEdge H v w) := rfl
@[simp] theorem addVertex_eq (H : State) (v : Vertex) (t : Bool) :
    AronowAudit.P012.addVertex (toState H) v t = toState (addVertex H v t) := rfl
@[simp] theorem cleanup_eq (D : Data) (r : Bool) (H : State) :
    AronowAudit.P012.cleanup (toData D) r (toState H) = toState (cleanup D r H) := rfl

@[simp] theorem hValues_eq (D : Data) : AronowAudit.P012.hValues (toData D) = hValues D := by
  ext r
  simp only [AronowAudit.P012.hValues, hValues, Set.mem_ofPred_eq, exists_state,
    Compatible_eq, homophily_eq]
@[simp] theorem pValues_eq (D : Data) : AronowAudit.P012.pValues (toData D) = pValues D := by
  ext r
  simp only [AronowAudit.P012.pValues, pValues, Set.mem_ofPred_eq, exists_state,
    Compatible_eq, preferential_eq]
@[simp] theorem FullHomophilyRegion_eq (D : Data) (L U : ℝ) :
    AronowAudit.P012.FullHomophilyRegion (toData D) L U = FullHomophilyRegion D L U := by
  simp only [AronowAudit.P012.FullHomophilyRegion, FullHomophilyRegion, forall_state,
    Compatible_eq, HomophilyDefined_eq, hValues_eq]
@[simp] theorem FullPreferentialRegion_eq (D : Data) (L U : ℝ) :
    AronowAudit.P012.FullPreferentialRegion (toData D) L U = FullPreferentialRegion D L U := by
  simp only [AronowAudit.P012.FullPreferentialRegion, FullPreferentialRegion, forall_state,
    Compatible_eq, PreferentialDefined_eq, pValues_eq]
@[simp] theorem domainA_eq : AronowAudit.P012.domainA = toData domainA := rfl
@[simp] theorem domainB_eq : AronowAudit.P012.domainB = toData domainB := rfl
@[simp] theorem domainC_eq : AronowAudit.P012.domainC = toData domainC := rfl
@[simp] theorem domainD_eq : AronowAudit.P012.domainD = toData domainD := rfl
@[simp] theorem figureData_eq : AronowAudit.P012.figureData = toData figureData := rfl
@[simp] theorem dyad_eq (t₁ t₂ : Bool) :
    AronowAudit.P012.dyad t₁ t₂ = toState (dyad t₁ t₂) := rfl
@[simp] theorem domainCState_eq  :
    AronowAudit.P012.domainCState  = toState (domainCState ) := rfl
@[simp] theorem domainDState_eq (t₃ t₄ t₅ : Bool) :
    AronowAudit.P012.domainDState t₃ t₄ t₅ = toState (domainDState t₃ t₄ t₅) := rfl

@[simp] theorem printed_table_intervals_eq (Ds Dc Dh : Data) :
    AronowAudit.P012.printed_table_intervals (toData Ds) (toData Dc) (toData Dh) =
      printed_table_intervals Ds Dc Dh := by
  simp only [AronowAudit.P012.printed_table_intervals, printed_table_intervals,
    forall_data, List.mem_cons, List.not_mem_nil, Bool.false_eq_true, or_false, toData_inj,
    Admissible_eq, data_sampled, data_seeds, data_parent, data_degree, data_time,
    nonseeds_eq, FullHomophilyRegion_eq]

@[simp] theorem sampled_name_eq : AronowAudit.P012.s = s := rfl
@[simp] theorem unsampled_name_eq : AronowAudit.P012.u = u := rfl
@[simp] theorem cooling_function_eq (ε T₁ : ℝ) :
    AronowAudit.P012.cooling ε T₁ = cooling ε T₁ := rfl


end
end SAP.P012b.Bridge
