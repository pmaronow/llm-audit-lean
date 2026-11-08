import SAP.P008a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a.WH.W1.P.T10_L1

open scoped BigOperators Classical

theorem score_ne_zero_iff_residual_ne_zero {N : ℕ} (z : Assignment N)
    (m : Fin N → ℝ) (h₁ : 1 ≤ nTreated z) (h₀ : 1 ≤ nControl z) :
    ∀ i, wholeOLSScore z m i ≠ 0 ↔ olsResidual z m i ≠ 0 := by
  have hids := SAP.P008a.WH.W1.ols_identities z m h₁ h₀
  have hw : ∀ i, wholeOLSWeight z i = contrastWeight z i := hids.2.2.2.1
  have ht : nTreated z ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one h₁)
  have hc : nControl z ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one h₀)
  have hw_ne (i : Fin N) : wholeOLSWeight z i ≠ 0 := by
    rw [hw i]
    cases hz : z i with
    | false =>
        have hdiv : (1 : ℝ) / nControl z ≠ 0 := div_ne_zero one_ne_zero hc
        simpa [contrastWeight, bit, hz] using hdiv
    | true =>
        have hdiv : (1 : ℝ) / nTreated z ≠ 0 := div_ne_zero one_ne_zero ht
        simpa [contrastWeight, bit, hz] using hdiv
  intro i
  constructor
  · intro hs
    by_contra hr
    apply hs
    simp [wholeOLSScore, hw i, hr]
  · intro hr
    unfold wholeOLSScore
    exact mul_ne_zero (hw_ne i) hr

theorem score_eq_zero_iff_residual_eq_zero {N : ℕ} (z : Assignment N)
    (m : Fin N → ℝ) (h₁ : 1 ≤ nTreated z) (h₀ : 1 ≤ nControl z) :
    ∀ i, wholeOLSScore z m i = 0 ↔ olsResidual z m i = 0 := by
  have hne := score_ne_zero_iff_residual_ne_zero z m h₁ h₀
  intro i
  constructor
  · intro hs
    by_contra hr
    exact (hne i).2 hr hs
  · intro hr
    by_contra hs
    exact (hne i).1 hs hr

end SAP.P008a.WH.W1.P.T10_L1

theorem SAP.P008a.WH.W1.T10_L1_proof : SAP.P008a.WH.W1.T10_L1 := by
  classical
  intro N z m h₁ h₀
  let g : Fin N → ℝ := wholeOLSScore z m
  have hscore0 : (∑ i, g i ^ 2) = 0 ↔ ∀ i, g i = 0 := by
    simpa [g] using
      (Finset.sum_sq_eq_zero_iff Finset.univ (fun i : Fin N => wholeOLSScore z m i))
  have hres0 : (∑ i, g i ^ 2) = 0 ↔ ∀ i, olsResidual z m i = 0 := by
    rw [hscore0]
    constructor
    · intro h i
      exact (SAP.P008a.WH.W1.P.T10_L1.score_eq_zero_iff_residual_eq_zero
        z m h₁ h₀ i).mp (h i)
    · intro h i
      exact (SAP.P008a.WH.W1.P.T10_L1.score_eq_zero_iff_residual_eq_zero
        z m h₁ h₀ i).mpr (h i)
  have hnonneg : 0 ≤ ∑ i, g i ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact sq_nonneg (g i)
  refine ⟨?_, hres0⟩
  constructor
  · intro hp
    by_contra hnone
    have hall : ∀ i, olsResidual z m i = 0 := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    exact (ne_of_gt hp) (hres0.mpr hall)
  · rintro ⟨i, hi⟩
    have hsum_ne : (∑ i, g i ^ 2) ≠ 0 := by
      intro hz
      exact hi ((hres0.mp hz) i)
    exact lt_of_le_of_ne hnonneg (Ne.symm hsum_ne)
