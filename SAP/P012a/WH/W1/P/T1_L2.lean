import SAP.P012a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open SAP.P012a SAP.P012a.WH.W1
open scoped Classical

theorem SAP.P012a.WH.W1.T1_L2_proof : SAP.P012a.WH.W1.T1_L2 := by
  intro c₁ c₂ K
  constructor
  · intro h
    cases h with
    | deleteUnobserved v P hi hj hne he hr hju hp =>
      cases hp with
      | existing hc hv =>
        have hpool : replacementPool proposalDataB proposalStartB 2 = ∅ := by decide
        rw [hpool] at hv
        simpa using hv
      | fresh hc hv t => exact ⟨v, hv, t, rfl⟩
    | deleteObserved k hjk v w P Q hi hk hne he hr hp hq =>
      cases hjk
    | addObserved v w hi hj hne he hv hw hiv hjw =>
      exact False.elim (he (by decide))
    | unchanged hi hj hne hd ha =>
      exact False.elim (hd ⟨by decide, by decide⟩)
  · rintro ⟨v, hv, t, rfl⟩
    have hpool : replacementPool proposalDataB proposalStartB 2 = ∅ := by decide
    have hp : WholeCoinReplacement proposalDataB proposalStartB
        (removeEdge proposalStartB (s 2) (u 4 0)) 2 c₁ v
        (addVertex (removeEdge proposalStartB (s 2) (u 4 0)) v t) :=
      WholeCoinReplacement.fresh
        (pending := removeEdge proposalStartB (s 2) (u 4 0)) (coin := c₁)
        v (Or.inr hpool) hv t
    exact WholePrintedRun.deleteUnobserved v
      (addVertex (removeEdge proposalStartB (s 2) (u 4 0)) v t)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hp

