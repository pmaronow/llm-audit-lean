import SAP.P044.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044.WH.W1.P.T2_L7

open Finset
open scoped BigOperators

theorem permutation_sum_swap {α : Type} [Fintype α] [DecidableEq α]
    (a b : α) (g : α → ℚ) :
    (∑ e : Equiv.Perm α, g (e a)) = ∑ e : Equiv.Perm α, g (e b) := by
  classical
  let σ : Equiv.Perm α ≃ Equiv.Perm α := {
    toFun := fun e => (Equiv.swap a b).trans e
    invFun := fun e => (Equiv.swap a b).trans e
    left_inv := by
      intro e
      ext x
      simp [Equiv.trans_apply]
    right_inv := by
      intro e
      ext x
      simp [Equiv.trans_apply]
  }
  calc
    (∑ e : Equiv.Perm α, g (e a)) =
        ∑ e : Equiv.Perm α, g (((Equiv.swap a b).trans e) b) := by
      apply Finset.sum_congr rfl
      intro e _
      simp [Equiv.trans_apply, Equiv.swap_apply_right]
    _ = ∑ e : Equiv.Perm α, g (e b) := σ.sum_comp (fun e => g (e b))

theorem perm_sum_card_relation {α : Type} [Fintype α] [DecidableEq α]
    (a : α) (g : α → ℚ) :
    (Fintype.card α : ℚ) * (∑ e : Equiv.Perm α, g (e a)) =
      (Fintype.card (Equiv.Perm α) : ℚ) * (∑ x : α, g x) := by
  classical
  have hpoint (x : α) :
      (∑ e : Equiv.Perm α, g (e x)) = ∑ e : Equiv.Perm α, g (e a) :=
    permutation_sum_swap x a g
  calc
    (Fintype.card α : ℚ) * (∑ e : Equiv.Perm α, g (e a)) =
        ∑ x : α, ∑ e : Equiv.Perm α, g (e x) := by
      simp_rw [hpoint]
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ e : Equiv.Perm α, ∑ x : α, g (e x) := Finset.sum_comm
    _ = ∑ e : Equiv.Perm α, ∑ x : α, g x := by
      apply Finset.sum_congr rfl
      intro e _
      exact Equiv.sum_comp e g
    _ = (Fintype.card (Equiv.Perm α) : ℚ) * (∑ x : α, g x) := by
      simp [Finset.sum_const, nsmul_eq_mul]


end SAP.P044.WH.W1.P.T2_L7

theorem SAP.P044.WH.W1.T2_L7_proof : SAP.P044.WH.W1.T2_L7 := by
  intro α _ _ a g
  classical
  have hsum := SAP.P044.WH.W1.P.T2_L7.perm_sum_card_relation a g
  have hα : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨a⟩).ne'
  have hperm : (Fintype.card (Equiv.Perm α) : ℚ) ≠ 0 := by
    have hp : 0 < Fintype.card (Equiv.Perm α) :=
      Fintype.card_pos_iff.mpr ⟨Equiv.refl α⟩
    exact_mod_cast hp.ne'
  change (∑ e : Equiv.Perm α,
      w1Uniform e * g (e a)) = ∑ x : α, w1Uniform x * g x
  unfold w1Uniform
  calc
    (∑ e : Equiv.Perm α,
        (1 / (Fintype.card (Equiv.Perm α) : ℚ)) * g (e a)) =
        (1 / (Fintype.card (Equiv.Perm α) : ℚ)) *
          (∑ e : Equiv.Perm α, g (e a)) := by rw [Finset.mul_sum]
    _ = (1 / (Fintype.card α : ℚ)) * (∑ x : α, g x) := by
      field_simp [hα, hperm]
      nlinarith [hsum]
    _ = ∑ x : α, (1 / (Fintype.card α : ℚ)) * g x := by rw [Finset.mul_sum]

