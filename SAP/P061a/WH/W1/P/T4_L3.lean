import SAP.P061a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a.WH.W1.P.T4_L3

open SAP.P061a
open scoped BigOperators Topology Classical BoundedContinuousFunction ENNReal

lemma pairedPartner_eq_own (K : ℕ) (i : Fin (K*2)) (z : Fin K → BitPair) :
    pairedPartnerBit K i z = pairedOwnBit K (partnerIndexW1 K i) z := by
  simp [pairedPartnerBit, pairedOwnBit, partnerBit, ownBit, partnerIndexW1]

lemma own_replacement (K : ℕ) (i j : Fin (K*2)) (e : Fin 2)
    (z : Fin K → BitPair) :
    pairedOwnBit K i (pairedReplacement K j e z) =
      if i = j then (e.val : ℝ) else pairedOwnBit K i z := by
  by_cases hdiv : i.divNat = j.divNat
  · by_cases hmod : i.modNat = j.modNat
    · have hij : i = j := by
        apply finProdFinEquiv.symm.injective
        exact Prod.ext (by simpa using hdiv) (by simpa using hmod)
      subst i
      generalize hb : j.modNat = b
      fin_cases b <;>
        simp [pairedOwnBit, ownBit, pairedReplacement, replaceOwnBit, Function.update, hb]
    · have hji : i ≠ j := by
        intro heq
        subst j
        exact hmod rfl
      generalize hi : i.modNat = a
      generalize hj : j.modNat = b
      fin_cases a <;> fin_cases b <;>
        simp_all [pairedOwnBit, ownBit, pairedReplacement, replaceOwnBit, Function.update]
  · have hji : i ≠ j := by
      intro heq
      subst j
      exact hdiv rfl
    simp [pairedOwnBit, ownBit, pairedReplacement,
      Function.update, hdiv, hji]

lemma partner_replacement (K : ℕ) (i j : Fin (K*2)) (e : Fin 2)
    (z : Fin K → BitPair) :
    pairedPartnerBit K i (pairedReplacement K j e z) =
      if partnerIndexW1 K i = j then (e.val : ℝ) else pairedPartnerBit K i z := by
  rw [pairedPartner_eq_own K i (pairedReplacement K j e z)]
  rw [pairedPartner_eq_own K i z]
  exact own_replacement K (partnerIndexW1 K i) j e z

end SAP.P061a.WH.W1.P.T4_L3

theorem SAP.P061a.WH.W1.T4_L3_proof : SAP.P061a.WH.W1.T4_L3 := by
  intro m hm i j
  constructor
  · rintro ⟨hij, z, z', hagree, hresp⟩
    by_contra hne
    have hpar : pairedPartnerBit (m^8) i z = pairedPartnerBit (m^8) i z' := by
      calc
        pairedPartnerBit (m^8) i z = pairedOwnBit (m^8) (partnerIndexW1 (m^8) i) z :=
          SAP.P061a.WH.W1.P.T4_L3.pairedPartner_eq_own _ _ _
        _ = pairedOwnBit (m^8) (partnerIndexW1 (m^8) i) z' :=
          hagree _ (by intro heq; exact hne heq.symm)
        _ = pairedPartnerBit (m^8) i z' :=
          (SAP.P061a.WH.W1.P.T4_L3.pairedPartner_eq_own _ _ _).symm
    apply hresp
    unfold pairResponses
    rw [hpar]
  · intro hj
    have hij : i ≠ j := by
      rw [hj]
      intro heq
      have hdecode := congrArg finProdFinEquiv.symm heq
      simp only [partnerIndexW1, finProdFinEquiv.symm_apply_apply] at hdecode
      have hside := congrArg Prod.snd hdecode
      generalize hb : (finProdFinEquiv.symm i).2 = b at hside
      fin_cases b <;> simp at hside
    refine ⟨hij, pairedReplacement (m^8) j 0 (fun _ => (0,0)),
      pairedReplacement (m^8) j 1 (fun _ => (0,0)), ?_, ?_⟩
    · intro k hkj
      rw [SAP.P061a.WH.W1.P.T4_L3.own_replacement,
        SAP.P061a.WH.W1.P.T4_L3.own_replacement]
      simp [hkj]
    · unfold pairResponses
      rw [SAP.P061a.WH.W1.P.T4_L3.partner_replacement,
        SAP.P061a.WH.W1.P.T4_L3.partner_replacement, hj]
      simp only [Fin.val_zero, Fin.val_one, ↓reduceIte]
      have hparam : 0 < pairParameter m := by
        simp only [pairParameter, if_pos hm]
        positivity
      norm_num at *
      linarith
