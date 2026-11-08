import SAP.P012a.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.Bridge

open SAP.P012a
noncomputable section

@[simp] theorem forall_data (P : AronowAudit.P012.Data → Prop) :
    (∀ D, P D) ↔ ∀ D : Data, P (data D) := by
  constructor
  · intro h D; exact h (data D)
  · intro h D; simpa only [data_back] using h (backData D)

theorem replacement_forward {D : SAP.P012a.Data} {C P Q : SAP.P012a.State}
    {i : ℕ} {v : Vertex} (h : SAP.P012a.Replacement D C P i v Q) :
    AronowAudit.P012.Replacement (data D) (state C) (state P) i v (state Q) := by
  cases h with
  | existing hv => exact .existing _ hv
  | fresh hv t => exact .fresh _ hv t

theorem graph_forward {D : SAP.P012a.Data} {repaired : Bool}
    {H K : SAP.P012a.State} (h : SAP.P012a.GraphProposal D repaired H K) :
    AronowAudit.P012.GraphProposal (data D) repaired (state H) (state K) := by
  cases h with
  | deleteUnobserved i j v P hi hj hne he hr hju hp =>
      cases repaired <;>
        exact .deleteUnobserved i j v (state P) hi hj hne he hr hju (replacement_forward hp)
  | deleteObserved i j v w P Q hi hj hne he hr hp hq =>
      exact .deleteObserved i j v w (state P) (state Q) hi hj hne he hr
        (replacement_forward hp) (replacement_forward hq)
  | addObserved i j v w hi hj hne he hv hw hiv hjw =>
      exact .addObserved i j v w hi hj hne he hv hw hiv hjw
  | unchanged i j hi hj hne hdel hadd =>
      exact .unchanged i j hi hj hne hdel hadd

theorem trait_forward {D : SAP.P012a.Data} {repaired : Bool}
    {H K : SAP.P012a.State} (h : SAP.P012a.TraitProposal D repaired H K) :
    AronowAudit.P012.TraitProposal (data D) repaired (state H) (state K) := by
  cases h with
  | flip v hv => exact .flip v hv
  | empty hr hu => exact .empty hr hu

theorem replacement_backward {D : AronowAudit.P012.Data} {C P Q : AronowAudit.P012.State}
    {i : ℕ} {v : Vertex} (h : AronowAudit.P012.Replacement D C P i v Q) :
    SAP.P012a.Replacement (backData D) (backState C) (backState P) i v (backState Q) := by
  cases h with
  | existing hv => exact .existing _ hv
  | fresh hv t => exact .fresh _ hv t

theorem graph_backward {D : AronowAudit.P012.Data} {repaired : Bool}
    {H K : AronowAudit.P012.State} (h : AronowAudit.P012.GraphProposal D repaired H K) :
    SAP.P012a.GraphProposal (backData D) repaired (backState H) (backState K) := by
  cases h with
  | deleteUnobserved i j v P hi hj hne he hr hju hp =>
      cases repaired <;>
        exact .deleteUnobserved i j v (backState P) hi hj hne he hr hju (replacement_backward hp)
  | deleteObserved i j v w P Q hi hj hne he hr hp hq =>
      exact .deleteObserved i j v w (backState P) (backState Q) hi hj hne he hr
        (replacement_backward hp) (replacement_backward hq)
  | addObserved i j v w hi hj hne he hv hw hiv hjw =>
      exact .addObserved i j v w hi hj hne he hv hw hiv hjw
  | unchanged i j hi hj hne hdel hadd =>
      exact .unchanged i j hi hj hne hdel hadd

theorem trait_backward {D : AronowAudit.P012.Data} {repaired : Bool}
    {H K : AronowAudit.P012.State} (h : AronowAudit.P012.TraitProposal D repaired H K) :
    SAP.P012a.TraitProposal (backData D) repaired (backState H) (backState K) := by
  cases h with
  | flip v hv => exact .flip v hv
  | empty hr hu => exact .empty hr hu

@[simp] theorem graph_eq (D : Data) (r : Bool) (H K : State) :
    AronowAudit.P012.GraphProposal (data D) r (state H) (state K) ↔ GraphProposal D r H K := by
  constructor
  · intro h; simpa only [back_data, back_state] using graph_backward h
  · exact graph_forward

@[simp] theorem trait_proposal_eq (D : Data) (r : Bool) (H K : State) :
    AronowAudit.P012.TraitProposal (data D) r (state H) (state K) ↔ TraitProposal D r H K := by
  constructor
  · intro h; simpa only [back_data, back_state] using trait_backward h
  · exact trait_forward

@[simp] theorem proposal_eq (D : Data) (r : Bool) (H K : State) :
    AronowAudit.P012.Proposal (data D) r (state H) (state K) ↔ Proposal D r H K := by
  simp only [AronowAudit.P012.Proposal, Proposal, graph_eq, trait_proposal_eq]

end
end SAP.P012a.Bridge
