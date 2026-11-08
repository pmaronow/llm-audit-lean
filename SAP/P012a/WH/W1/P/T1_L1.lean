import SAP.P012a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P012a

theorem SAP.P012a.WH.W1.T1_L1_proof : SAP.P012a.WH.W1.T1_L1 := by
  intro c₁ c₂ K
  constructor
  · intro h
    cases h with
    | deleteUnobserved v P hi hj hne he hr hju hp =>
        have hpool : replacementPool proposalData proposalStart 1 = ∅ :=
          SAP.P012a.Bridge.proposal_counterexample.2.2.1
        cases hp with
        | existing hc hv =>
            have hmem : v ∈ (∅ : Finset Vertex) := by
              simpa [hpool] using hv
            simp at hmem
        | fresh hc hv t =>
            have hv0 : v ∉ proposalStart.vertices := by
              simpa [removeEdge] using hv
            refine ⟨v, hv0, t, ?_⟩
            rfl
    | deleteObserved k hjk v w P Q hi hk hne he hr hp hq =>
        have hfalse : False := by
          simpa [s, u] using hjk
        exact hfalse.elim
    | addObserved v w hi hj hne he hv hw hiv hjw =>
        exact False.elim (he (by decide))
    | unchanged hi hj hne hdel hadd =>
        exact False.elim (hdel ⟨by decide, by decide⟩)
  · rintro ⟨v, hv, t, rfl⟩
    have hpool : replacementPool proposalData proposalStart 1 = ∅ :=
      SAP.P012a.Bridge.proposal_counterexample.2.2.1
    refine WholePrintedRun.deleteUnobserved (v := v)
      (P := addVertex (removeEdge proposalStart (s 1) (u 3 0)) v t)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_
    exact WholeCoinReplacement.fresh v (Or.inr hpool)
      (by simpa [removeEdge] using hv) t

