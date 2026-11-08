import SAP.P061a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a.WH.W1.P.T4_L1

open SAP.P061a

private def unflatten {K : ℕ} (x : Fin (K * 2) → Fin 2) : Fin K → BitPair :=
  fun k => (x (finProdFinEquiv (k, 0)), x (finProdFinEquiv (k, 1)))

private theorem flatten_unflatten {K : ℕ} (x : Fin (K * 2) → Fin 2) :
    flattenBitsW1 K (unflatten x) = x := by
  funext i
  let q := finProdFinEquiv.symm i
  have hi : finProdFinEquiv q = i := finProdFinEquiv.apply_symm_apply i
  rcases q with ⟨k, b⟩
  subst i
  fin_cases b <;> simp [flattenBitsW1, unflatten]

private theorem unflatten_flatten {K : ℕ} (z : Fin K → BitPair) :
    unflatten (flattenBitsW1 K z) = z := by
  funext k
  apply Prod.ext <;> simp [unflatten, flattenBitsW1]

private theorem partner_facts (K : ℕ) (i : Fin (K * 2)) :
    partnerIndexW1 K i ≠ i ∧ partnerIndexW1 K (partnerIndexW1 K i) = i := by
  let q := finProdFinEquiv.symm i
  have hi : finProdFinEquiv q = i := finProdFinEquiv.apply_symm_apply i
  rcases q with ⟨k, b⟩
  subst i
  fin_cases b <;> simp [partnerIndexW1]

private theorem bit_facts (K : ℕ) (i : Fin (K * 2)) (z : Fin K → BitPair) :
    ((flattenBitsW1 K z i).val : ℝ) = pairedOwnBit K i z ∧
    pairedPartnerBit K i z = pairedOwnBit K (partnerIndexW1 K i) z := by
  let q := finProdFinEquiv.symm i
  have hi : finProdFinEquiv q = i := finProdFinEquiv.apply_symm_apply i
  rcases q with ⟨k, b⟩
  subst i
  fin_cases b <;> simp [flattenBitsW1, pairedOwnBit, pairedPartnerBit,
    partnerIndexW1, ownBit, partnerBit]

private theorem replacement_facts (K : ℕ) (i : Fin (K * 2)) (e : Fin 2)
    (z : Fin K → BitPair) :
    flattenBitsW1 K (pairedReplacement K i e z) =
      Function.update (flattenBitsW1 K z) i e := by
  funext j
  let q := finProdFinEquiv.symm i
  have hi : finProdFinEquiv q = i := finProdFinEquiv.apply_symm_apply i
  rcases q with ⟨k, b⟩
  subst i
  let q' := finProdFinEquiv.symm j
  have hj : finProdFinEquiv q' = j := finProdFinEquiv.apply_symm_apply j
  rcases q' with ⟨k', b'⟩
  subst j
  fin_cases b <;> fin_cases b' <;> by_cases hkk : k' = k <;>
    simp [flattenBitsW1, pairedReplacement, replaceOwnBit, hkk, Function.update]

end SAP.P061a.WH.W1.P.T4_L1

theorem SAP.P061a.WH.W1.T4_L1_proof : SAP.P061a.WH.W1.T4_L1 := by
  intro K
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro z z' h
      have hz := congrArg
        (SAP.P061a.WH.W1.P.T4_L1.unflatten (K := K)) h
      simpa only [SAP.P061a.WH.W1.P.T4_L1.unflatten_flatten] using hz
    · intro x
      exact ⟨SAP.P061a.WH.W1.P.T4_L1.unflatten x,
        SAP.P061a.WH.W1.P.T4_L1.flatten_unflatten x⟩
  · intro i
    exact SAP.P061a.WH.W1.P.T4_L1.partner_facts K i
  · intro i z
    exact SAP.P061a.WH.W1.P.T4_L1.bit_facts K i z
  · intro i e z
    exact SAP.P061a.WH.W1.P.T4_L1.replacement_facts K i e z
