import SAP.P042.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042.WH.W1.P.T6_L2

open SAP.P042
open Finset
open scoped BigOperators

lemma perturbed_never_taker_sum {N : ℕ} (Y : Fin N → Bool → ℝ)
    (c : Fin N → Bool) (k : Fin N) (δ : ℝ) (hk : c k = false) :
    (∑ i, if c i = false then
      perturbContact Y k δ i true - perturbContact Y k δ i false else 0) =
    (∑ i, if c i = false then Y i true - Y i false else 0) + δ := by
  calc
    (∑ i, if c i = false then
        perturbContact Y k δ i true - perturbContact Y k δ i false else 0) =
      ∑ i, ((if c i = false then Y i true - Y i false else 0) +
        (if i = k then δ else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hik : i = k
          · subst i
            simp [hk, perturbContact]
            ring
          · simp [hik, perturbContact]
    _ = (∑ i, if c i = false then Y i true - Y i false else 0) + δ := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq']

end SAP.P042.WH.W1.P.T6_L2

theorem SAP.P042.WH.W1.T6_L2_proof : SAP.P042.WH.W1.T6_L2 := by
  intro N Y c k δ hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S
    funext i
    by_cases hik : i = k
    · subst i
      simp [SAP.P042.contactedOutcome, SAP.P042.perturbContact, hk]
    · simp [SAP.P042.contactedOutcome, SAP.P042.perturbContact, hik]
  · simp [SAP.P042.perturbContact]
    ring
  · change
      (∑ i, if c i = false then
        SAP.P042.perturbContact Y k δ i true - SAP.P042.perturbContact Y k δ i false else 0) /
        (SAP.P042.neverTakerCount c : ℝ) =
      (∑ i, if c i = false then Y i true - Y i false else 0) /
        (SAP.P042.neverTakerCount c : ℝ) +
        δ / (SAP.P042.neverTakerCount c : ℝ)
    rw [SAP.P042.WH.W1.P.T6_L2.perturbed_never_taker_sum Y c k δ hk, add_div]
  · intro hBinary hδ i t
    by_cases hchange : i = k ∧ t = true
    · have hik : i = k := hchange.1
      have ht : t = true := hchange.2
      subst i
      subst t
      rcases hBinary k true with h0 | h1
      · simp [SAP.P042.perturbContact, hδ, h0]
      · norm_num [SAP.P042.perturbContact, hδ, h1]
    · simp only [SAP.P042.perturbContact, if_neg hchange]
      exact hBinary i t
