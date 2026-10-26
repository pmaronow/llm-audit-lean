import AronowAudit.P011.P011_FiniteCompletion
import Mathlib.Logic.Equiv.Fin.Basic

namespace AronowAudit.P011.StarCompletion
open scoped BigOperators
noncomputable section
attribute [-simp] Finset.sum_boole
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

lemma saturated_relaxation {n : ℕ} (R : Graph n) (a : Edge n → ℝ) :
    RelaxedFeasible R (degree R) a ↔
      a=fun e => adjacency R e.val.1 e.val.2 := by
  classical
  constructor
  · intro ha
    have hlow (e : Edge n) : adjacency R e.val.1 e.val.2 ≤ a e := by
      cases he : R.val e.val.1 e.val.2
      · simpa [adjacency,he] using (ha.1 e).1
      · have hf := ha.2.1 e he
        simp [adjacency,he,hf]
    let f := fun (i : Fin n) (e : Edge n) =>
      if e.val.1=i ∨ e.val.2=i then a e-adjacency R e.val.1 e.val.2 else 0
    have hf (i : Fin n) (e : Edge n) : 0 ≤ f i e := by
      dsimp [f]
      split_ifs
      · exact sub_nonneg.mpr (hlow e)
      · rfl
    have hs (i : Fin n) : (∑ e, f i e) ≤ 0 := by
      have hrow := ha.2.2 i
      have hid : (∑ e, f i e) =
          (∑ e : Edge n, if e.val.1=i ∨ e.val.2=i then a e else 0)-
          (∑ e : Edge n, if e.val.1=i ∨ e.val.2=i then adjacency R e.val.1 e.val.2 else 0) := by
        simp only [f, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> ring
      rw [hid, ← LpCompletion.degree_incidence]
      exact sub_nonpos.mpr hrow
    funext e
    have hh := Finset.single_le_sum (fun e' (_ : e'∈(Finset.univ:Finset (Edge n))) => hf e.val.1 e')
      (Finset.mem_univ e)
    have he : f e.val.1 e = a e-adjacency R e.val.1 e.val.2 := by simp [f]
    rw [he] at hh
    linarith [hs e.val.1, hlow e]
  · rintro rfl
    have hcomp : Compatible R (degree R) (fromUpper (toUpper R)) := by
      rw [UpperCompletion.from_to]
      exact ⟨fun _ _ h => h,fun _ => le_rfl⟩
    exact LpCompletion.embedding_feasible R (degree R) (toUpper R) hcomp

def blockEquiv (q b : ℕ) : Fin b × Fin q ≃ Fin (q*b) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm b q))

lemma block_local {q b : ℕ} (hq : 0 < q) (v : Fin b × Fin q) :
    localIndex hq (blockEquiv q b v) = v.2 := by
  apply Fin.ext
  simp [localIndex, blockEquiv, finProdFinEquiv, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt v.2.isLt]

lemma block_quot {q b : ℕ} (hq : 0 < q) (v : Fin b × Fin q) :
    (blockEquiv q b v).val / q = v.1.val := by
  simp [blockEquiv, finProdFinEquiv, Nat.add_mul_div_left _ _ hq,
    Nat.div_eq_of_lt v.2.isLt]

lemma block_degree {q b : ℕ} (hq : 0 < q) (A : Graph q) (i : Fin (q*b)) :
    degree (blockGraph hq A b) i = degree A (localIndex hq i) := by
  classical
  unfold degree
  rw [← (blockEquiv q b).sum_comp]
  rw [Fintype.sum_prod_type]
  have hterm (v : Fin b) (j : Fin q) :
      (if (blockGraph hq A b).val i (blockEquiv q b (v,j)) then (1:ℕ) else 0) =
      if v=blockIndex hq i then (if A.val (localIndex hq i) j then 1 else 0) else 0 := by
    have he : i.val/q=v.val ↔ v=blockIndex hq i := by
      simp [Fin.ext_iff,blockIndex,eq_comm]
    simp only [blockGraph, block_local, block_quot hq, Bool.and_eq_true, decide_eq_true_eq, he]
    by_cases h : v=blockIndex hq i <;> simp [h]
  simp_rw [hterm]
  simp

lemma star_relaxation_singleton_completed (upper : Bool) (k : ℕ)
    (a : Edge (4*(k+1)) → ℝ) :
    RelaxedFeasible (starModel upper (k+1)).R (starModel upper (k+1)).d a ↔
      a=fun e => adjacency (starModel upper (k+1)).G e.val.1 e.val.2 := by
  have hd : (starModel upper (k+1)).d = degree (starModel upper (k+1)).R := by
    funext i
    exact (block_degree (by decide) starGraph i).symm
  rw [hd]
  exact saturated_relaxation _ _

end
end AronowAudit.P011.StarCompletion

namespace AronowAudit.P011
theorem star_relaxation_singleton (upper : Bool) (k : ℕ)
    (a : Edge (4*(k+1)) → ℝ) :
    RelaxedFeasible (starModel upper (k+1)).R (starModel upper (k+1)).d a ↔
      a=fun e => adjacency (starModel upper (k+1)).G e.val.1 e.val.2 := by
  exact StarCompletion.star_relaxation_singleton_completed upper k a
end AronowAudit.P011

