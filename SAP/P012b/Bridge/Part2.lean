import SAP.P012b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

namespace SAP.P012b.Bridge

noncomputable section

theorem replacement_to (D : Data) (H P : State) (i : ℕ) (v : Vertex) (Q : State)
    (h : Replacement D H P i v Q) :
    AronowAudit.P012.Replacement (toData D) (toState H) (toState P) i v (toState Q) := by
  cases h with
  | existing hv => exact .existing v hv
  | fresh hv t => exact .fresh v hv t

theorem replacement_from (D : Data) (H P : State) (i : ℕ) (v : Vertex)
    (Q : AronowAudit.P012.State)
    (h : AronowAudit.P012.Replacement (toData D) (toState H) (toState P) i v Q) :
    Replacement D H P i v (fromState Q) := by
  cases h with
  | existing hv => exact .existing v hv
  | fresh hv t => exact .fresh v hv t

theorem graphProposal_to (D : Data) (r : Bool) (H K : State)
    (h : GraphProposal D r H K) :
    AronowAudit.P012.GraphProposal (toData D) r (toState H) (toState K) := by
  cases h with
  | deleteUnobserved i j v P hi hj hn he hr hju hp =>
      cases r <;> exact .deleteUnobserved i j v (toState P) hi hj hn he hr hju
        (replacement_to D H _ i v P hp)
  | deleteObserved i j v w P Q hi hj hn he hr hp hq =>
      exact .deleteObserved i j v w (toState P) (toState Q) hi hj hn he hr
        (replacement_to D H _ i v P hp) (replacement_to D H _ j w Q hq)
  | addObserved i j v w hi hj hn he hv hw hiv hjw =>
      exact .addObserved i j v w hi hj hn he hv hw hiv hjw
  | unchanged i j hi hj hn hd ha =>
      exact .unchanged i j hi hj hn hd ha

theorem graphProposal_from (D : Data) (r : Bool) (H : State)
    (K : AronowAudit.P012.State)
    (h : AronowAudit.P012.GraphProposal (toData D) r (toState H) K) :
    GraphProposal D r H (fromState K) := by
  cases h with
  | deleteUnobserved i j v P hi hj hn he hr hju hp =>
      cases r <;> exact .deleteUnobserved i j v (fromState P) hi hj hn he hr hju
        (replacement_from D H _ i v P hp)
  | deleteObserved i j v w P Q hi hj hn he hr hp hq =>
      exact .deleteObserved i j v w (fromState P) (fromState Q) hi hj hn he hr
        (replacement_from D H _ i v P hp) (replacement_from D H _ j w Q hq)
  | addObserved i j v w hi hj hn he hv hw hiv hjw =>
      exact .addObserved i j v w hi hj hn he hv hw hiv hjw
  | unchanged i j hi hj hn hd ha =>
      exact .unchanged i j hi hj hn hd ha

theorem traitProposal_to (D : Data) (r : Bool) (H K : State)
    (h : TraitProposal D r H K) :
    AronowAudit.P012.TraitProposal (toData D) r (toState H) (toState K) := by
  cases h with
  | flip v hv => exact .flip v hv
  | empty hr hu => exact .empty hr hu

theorem traitProposal_from (D : Data) (r : Bool) (H : State)
    (K : AronowAudit.P012.State)
    (h : AronowAudit.P012.TraitProposal (toData D) r (toState H) K) :
    TraitProposal D r H (fromState K) := by
  cases h with
  | flip v hv => exact .flip v hv
  | empty hr hu => exact .empty hr hu

@[simp] theorem Proposal_eq (D : Data) (r : Bool) (H K : State) :
    AronowAudit.P012.Proposal (toData D) r (toState H) (toState K) ↔ Proposal D r H K := by
  constructor
  · rintro (h | h)
    · exact Or.inl (graphProposal_from D r H _ h)
    · exact Or.inr (traitProposal_from D r H _ h)
  · rintro (h | h)
    · exact Or.inl (graphProposal_to D r H K h)
    · exact Or.inr (traitProposal_to D r H K h)

macro "sap_transfer " h:term : tactic =>
  `(tactic| simpa only [
    forall_data, forall_state, exists_state, toData_inj,
    toState_inj, data_sampled, data_seeds, data_parent,
    data_time, data_degree, data_trait, state_vertices,
    state_edges, state_trait, nonseeds_eq, sampledVertices_eq,
    recruitmentEdges_eq, graphDegree_eq, recruitmentDegree_eq, spare_eq,
    sampledTraitDegree_eq, Admissible_eq, Simple_eq, Augmented_eq,
    Compatible_eq, GraphCompatible_eq, InducedCompatible_eq, hNumerator_eq,
    hDenominator_eq, hValue_eq, HomophilyDefined_eq, homophily_eq,
    susceptible_eq, pSum_eq, pValue_eq, PreferentialDefined_eq,
    preferential_eq, traitDegree_eq, unsampled_eq, replacementPool_eq,
    children_eq, degreeTraitSum_eq, PointIdentified_eq, cooling_eq,
    leafCompletion_eq, recruitmentState_eq, induced_eq, flipTrait_eq,
    removeEdge_eq, addEdge_eq, addVertex_eq, cleanup_eq,
    hValues_eq, pValues_eq, FullHomophilyRegion_eq, FullPreferentialRegion_eq,
    domainA_eq, domainB_eq, domainC_eq, domainD_eq,
    figureData_eq, dyad_eq, domainCState_eq, domainDState_eq,
    printed_table_intervals_eq, sampled_name_eq, unsampled_name_eq, cooling_function_eq,
    Proposal_eq] using $h)

end
end SAP.P012b.Bridge
