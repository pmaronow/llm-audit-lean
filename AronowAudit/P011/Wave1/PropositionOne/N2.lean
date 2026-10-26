import AronowAudit.P011.Wave1.PropositionOneBlueprint
import AronowAudit.P011.P011_StarCompletion

/-! Reindexing and contraction of the block diagonal path oracle matrix. -/

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

theorem n2_proof : N2 := by
  classical
  intro K
  let e : Fin K × Fin 3 ≃ Fin (3 * K) := StarCompletion.blockEquiv 3 K
  have hlocal (b : Fin K) (r : Fin 3) :
      localIndex (by decide : 0 < 3) (e (b, r)) = r :=
    StarCompletion.block_local (by decide) (b, r)
  have hquot (b : Fin K) (r : Fin 3) : (e (b, r)).val / 3 = b.val :=
    StarCompletion.block_quot (by decide) (b, r)
  have hblock (b : Fin K) (r : Fin 3) :
      blockIndex (by decide : 0 < 3) (e (b, r)) = b := by
    apply Fin.ext
    exact hquot b r
  have hvec (y : Fin (3 * K) → ℝ) (b : Fin K) (r : Fin 3) :
      y (e (b, r)) = blockVec K y b r := by
    change y (e (b, r)) = y ⟨3 * b.val + r.val, _⟩
    congr 1
    apply Fin.ext
    change r.val + 3 * b.val = 3 * b.val + r.val
    omega
  have hreindex (f : Fin (3 * K) → ℝ) :
      (∑ i, f i) = ∑ b : Fin K, ∑ r : Fin 3, f (e (b, r)) := by
    rw [← e.sum_comp, Fintype.sum_prod_type]
  have heq (b c : Fin K) (r s : Fin 3) :
      e (b, r) = e (c, s) ↔ b = c ∧ r = s := by
    constructor
    · intro h
      have hp : (b, r) = (c, s) := e.injective h
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hadj (b c : Fin K) (r s : Fin 3) :
      (pathGraphK K).val (e (b, r)) (e (c, s)) =
        if b = c then pathGraph.val r s else false := by
    change (decide ((e (b, r)).val / 3 = (e (c, s)).val / 3) &&
      pathGraph.val (localIndex (by decide) (e (b, r)))
        (localIndex (by decide) (e (c, s)))) = _
    rw [hquot, hquot, hlocal, hlocal]
    by_cases hbc : b = c
    · subst c
      simp
    · have hv : b.val ≠ c.val := fun hv => hbc (Fin.ext hv)
      simp only [hv, hbc, decide_false, Bool.false_and, if_false]
  have horacle (b c : Fin K) (r s : Fin 3) :
      oracleMatrix (pathGraphK K) (e (b, r)) (e (c, s)) =
        if b = c then oracleMatrix pathGraph r s else 0 := by
    simp only [CliqueCompletion.oracle_apply, heq, hadj]
    by_cases hbc : b = c <;> simp [hbc]

  constructor
  · intro y
    refine ⟨?_, ?_, ?_⟩
    · rw [hreindex]
      simp only [hvec]
    · change (∑ i, ∑ j, oracleMatrix (pathGraphK K) i j * y i * y j) = _
      rw [hreindex]
      change (∑ b, ∑ r, ∑ j,
        oracleMatrix (pathGraphK K) (e (b, r)) j * y (e (b, r)) * y j) =
          ∑ b, ∑ r, ∑ s,
            oracleMatrix pathGraph r s * blockVec K y b r * blockVec K y b s
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro r _
      rw [hreindex]
      simp_rw [horacle, hvec]
      rw [Finset.sum_eq_single b]
      · simp only [ite_true]
      · intro c _ hcb
        simp only [if_neg (Ne.symm hcb), zero_mul, Finset.sum_const_zero]
      · intro hb
        exact (hb (Finset.mem_univ b)).elim
    · rw [hreindex]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro r _
      rw [hreindex]
      simp_rw [horacle, hvec]
      rw [Finset.sum_eq_single b]
      · simp only [ite_true]
      · intro c _ hcb
        simp only [if_neg (Ne.symm hcb), zero_mul, Finset.sum_const_zero]
      · intro hb
        exact (hb (Finset.mem_univ b)).elim
  · intro u b
    funext r
    rw [← hvec (pathSource K u) b r]
    change pathBlock 2 (sign (u (blockIndex (by decide) (e (b, r))) 0))
        (sign (u (blockIndex (by decide) (e (b, r))) 1))
        (localIndex (by decide) (e (b, r))) = _
    rw [hblock, hlocal]

end

end AronowAudit.P011.Wave1.PropositionOne
