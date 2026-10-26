import AronowAudit.P012.P012_Identification

noncomputable section
namespace AronowAudit.P012

/-- Refutation of the printed claim that every proposal preserves compatibility (T19). -/
theorem printed_proposal_preserves_refuted :
    ¬ (∀ (D : Data) (H K : State)
    (hD : Admissible D) (hH : Compatible D H) (hP : Proposal D false H K),
    Compatible D K) := by
  intro h
  have hw := proposal_counterexample
  exact (hw.2.2.2.1 false).2 (h proposalData proposalStart (proposalBad false)
    hw.1 hw.2.1 (hw.2.2.2.1 false).1)

end AronowAudit.P012

