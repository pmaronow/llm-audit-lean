import SAP.P042.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042.WH.W2.P.T6_L2

open SAP.P042
open Finset
open scoped BigOperators

def flipContact {N : ℕ} (Y : Fin N → Bool → ℝ) (k : Fin N) :
    Fin N → Bool → ℝ :=
  fun i t => if i = k ∧ t = true then 1 - Y i t else Y i t

lemma flipContact_binary {N : ℕ} (Y : Fin N → Bool → ℝ) (k : Fin N)
    (hY : BinaryScheduleW2 Y) : BinaryScheduleW2 (flipContact Y k) := by
  intro i t
  by_cases h : i = k ∧ t = true
  · rcases h with ⟨hik, ht⟩
    rw [hik, ht]
    rcases hY k true with h0 | h1
    · right
      simp [flipContact, h0]
    · left
      simp [flipContact, h1]
  · simpa [flipContact, h] using hY i t

lemma flipContact_neverTaker_sum {N : ℕ} (Y : Fin N → Bool → ℝ)
    (c : Fin N → Bool) (k : Fin N) (hk : c k = false) :
    (∑ i, if c i = false then
      flipContact Y k i true - flipContact Y k i false else 0) =
      (∑ i, if c i = false then Y i true - Y i false else 0) +
        ((1 - Y k true) - Y k true) := by
  have hterm (i : Fin N) :
      (if c i = false then
        flipContact Y k i true - flipContact Y k i false else 0) =
      (if c i = false then Y i true - Y i false else 0) +
        (if i = k then (1 - Y k true) - Y k true else 0) := by
    by_cases hik : i = k
    · subst i
      simp [flipContact, hk]
    · simp [flipContact, hik]
  calc
    (∑ i, if c i = false then
      flipContact Y k i true - flipContact Y k i false else 0) =
      ∑ i, ((if c i = false then Y i true - Y i false else 0) +
        (if i = k then (1 - Y k true) - Y k true else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
    _ = (∑ i, if c i = false then Y i true - Y i false else 0) +
        ((1 - Y k true) - Y k true) := by
          rw [Finset.sum_add_distrib]
          simp [Finset.sum_ite_eq']

end SAP.P042.WH.W2.P.T6_L2

theorem SAP.P042.WH.W2.T6_L2_proof : SAP.P042.WH.W2.T6_L2 := by
  intro N Y c k hY hk
  let Y' := SAP.P042.WH.W2.P.T6_L2.flipContact Y k
  have hY' : SAP.P042.BinaryScheduleW2 Y' := by
    exact SAP.P042.WH.W2.P.T6_L2.flipContact_binary Y k hY
  have hobs : ∀ S : Finset (Fin N),
      SAP.P042.contactedOutcome S Y' c = SAP.P042.contactedOutcome S Y c := by
    intro S
    funext i
    by_cases hik : i = k
    · subst i
      simp [SAP.P042.contactedOutcome, Y',
        SAP.P042.WH.W2.P.T6_L2.flipContact, hk]
    · simp [SAP.P042.contactedOutcome, Y',
        SAP.P042.WH.W2.P.T6_L2.flipContact, hik]
  have hcountNat : 0 < SAP.P042.neverTakerCountW2 c := by
    apply Finset.card_pos.mpr
    refine ⟨k, ?_⟩
    simp [hk]
  have hcount : 0 < (SAP.P042.neverTakerCountW2 c : ℝ) := by
    exact_mod_cast hcountNat
  have hdelta : ((1 - Y k true) - Y k true) ≠ 0 := by
    rcases hY k true with hy | hy
    · simp [hy]
    · simp [hy]
  have hnum :
      (∑ i, if c i = false then Y' i true - Y' i false else 0) ≠
        (∑ i, if c i = false then Y i true - Y i false else 0) := by
    rw [show (∑ i, if c i = false then Y' i true - Y' i false else 0) =
      (∑ i, if c i = false then Y i true - Y i false else 0) +
        ((1 - Y k true) - Y k true) by
          simpa [Y'] using
            SAP.P042.WH.W2.P.T6_L2.flipContact_neverTaker_sum Y c k hk]
    intro heq
    apply hdelta
    linarith
  refine ⟨Y', hY', hobs, ?_, ?_, hcountNat, ?_⟩
  · intro i t hit
    rcases hit with hik | ht
    · simp [Y', SAP.P042.WH.W2.P.T6_L2.flipContact, hik]
    · subst t
      simp [Y', SAP.P042.WH.W2.P.T6_L2.flipContact]
  · have hy' : Y' k true = 1 - Y k true := by
      simp [Y', SAP.P042.WH.W2.P.T6_L2.flipContact]
    have hy0 : Y' k false = Y k false := by
      simp [Y', SAP.P042.WH.W2.P.T6_L2.flipContact]
    rw [hy', hy0]
    rcases hY k true with hy | hy <;> linarith
  · change
      (∑ i, if c i = false then Y' i true - Y' i false else 0) /
          (SAP.P042.neverTakerCountW2 c : ℝ) ≠
        (∑ i, if c i = false then Y i true - Y i false else 0) /
          (SAP.P042.neverTakerCountW2 c : ℝ)
    intro heq
    exact hnum ((div_left_inj' (ne_of_gt hcount)).mp heq)
