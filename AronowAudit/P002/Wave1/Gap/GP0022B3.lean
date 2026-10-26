import AronowAudit.P002.P002_Audit
import AronowAudit.External.Causalean.Experimentation.FinitePopulationMoments

/-! P002-T7: finite-contrast variance identities and oracle variance formulas
(D.5)–(D.6). -/
namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

private lemma OV_expectation_bridge {n} (P : Population n) (h : ValidDesign P)
    (f : Finset (Fin n) → ℝ) :
    expectation P f =
      (Causalean.Experimentation.DesignBased.completeRandomization P.n1
        (show P.n1 ≤ Fintype.card (Fin n) by simpa using h.2.2.le)).E
        (fun S => f S.val) := by
  have hsum : (∑ S ∈ assignments P, f S) =
      ∑ S : {S : Finset (Fin n) // S.card = P.n1}, f S.val := by
    refine Finset.sum_bij
      (fun S hS => (⟨S, (Finset.mem_powersetCard.mp hS).2⟩ :
        {S : Finset (Fin n) // S.card = P.n1})) ?_ ?_ ?_ ?_
    · intro S hS; exact Finset.mem_univ _
    · intro S hS T hT he; exact congrArg Subtype.val he
    · intro S hS
      refine ⟨S.val, ?_, ?_⟩
      · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩
      · exact Subtype.ext rfl
    · intro S hS; rfl
  have hcard : (assignments P).card =
      Fintype.card {S : Finset (Fin n) // S.card = P.n1} := by
    simp only [assignments, Finset.card_powersetCard, Finset.card_univ,
      Causalean.Experimentation.DesignBased.completeRandomization_card]
  unfold expectation Causalean.Experimentation.DesignBased.FiniteDesign.E
    Causalean.Experimentation.DesignBased.completeRandomization
  rw [hsum, hcard, ← Finset.mul_sum]
  ring

private lemma OV_variance_bridge {n} (P : Population n) (h : ValidDesign P)
    (f : Finset (Fin n) → ℝ) :
    designVariance P f =
      (Causalean.Experimentation.DesignBased.completeRandomization P.n1
        (show P.n1 ≤ Fintype.card (Fin n) by simpa using h.2.2.le)).Var
        (fun S => f S.val) := by
  unfold designVariance Causalean.Experimentation.DesignBased.FiniteDesign.Var
  rw [OV_expectation_bridge P h f, OV_expectation_bridge P h]

private lemma OV_expectation_congr {n} (P : Population n)
    {f g : Finset (Fin n) → ℝ}
    (he : ∀ S ∈ assignments P, f S = g S) : expectation P f = expectation P g := by
  unfold expectation
  congr 1
  exact Finset.sum_congr rfl he

/-- Equality up to a deterministic shift on the actual support suffices. -/
private lemma OV_variance_shift {n} (P : Population n) (h : ValidDesign P)
    (f g : Finset (Fin n) → ℝ) (c : ℝ)
    (he : ∀ S ∈ assignments P, f S = g S - c) :
    designVariance P f = designVariance P g := by
  have hE : expectation P f = expectation P g - c := by
    calc
      _ = expectation P (fun S => g S - c) := OV_expectation_congr P he
      _ = _ := by rw [expectation_sub, expectation_const P h]
  unfold designVariance
  rw [hE]
  apply OV_expectation_congr
  intro S hS
  rw [he S hS]
  ring

private lemma OV_sample_variance {n} (P : Population n) (h : ValidDesign P)
    (y : Fin n → ℝ) :
    designVariance P (fun S => groupMean S y) =
      (1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar y := by
  rw [OV_variance_bridge P h]
  have he : (fun S : {S : Finset (Fin n) // S.card = P.n1} => groupMean S.val y) =
      Causalean.Experimentation.FinitePopulationMoments.sampleMean P.n1 y := by
    funext S
    simp only [groupMean, S.property,
      Causalean.Experimentation.FinitePopulationMoments.sampleMean]
    congr 1
    simp [← Finset.sum_filter]
  rw [he]
  simpa only [Causalean.Experimentation.FinitePopulationMoments.popVar,
    Causalean.Experimentation.FinitePopulationMoments.popMean,
    Fintype.card_fin, popVar, mean] using
    (Causalean.Experimentation.FinitePopulationMoments.Var_sampleMean P.n1
      (show P.n1 ≤ Fintype.card (Fin n) by simpa using h.2.2.le) h.2.1
      (show 2 ≤ Fintype.card (Fin n) by simpa using h.1) y)

/-- Two-potential-response contrast variance, derived from the proved SRS mean variance. -/
private lemma OV_contrast_variance {n} (P : Population n) (h : ValidDesign P)
    (a b : Fin n → ℝ) :
    designVariance P (fun S => groupMean S a - groupMean Sᶜ b) =
      popVar a / (P.n1 : ℝ) + popVar b / controlSize P -
        popVar (fun i => a i - b i) / (n : ℝ) := by
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by have := h.1; omega)
  have hm : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast h.2.1.ne'
  have hc : controlSize P ≠ 0 := by
    unfold controlSize
    exact sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast h.2.2))
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h.1
    linarith
  let y : Fin n → ℝ := fun i => a i + (P.n1 : ℝ) / controlSize P * b i
  have hpoint (S : Finset (Fin n)) (hS : S ∈ assignments P) :
      groupMean S a - groupMean Sᶜ b =
        groupMean S y - (∑ i, b i) / controlSize P := by
    have hs : S.card = P.n1 := (Finset.mem_powersetCard.mp hS).2
    have hcs : (Sᶜ.card : ℝ) = controlSize P := by
      rw [Finset.card_compl, Fintype.card_fin, hs, Nat.cast_sub h.2.2.le]
      rfl
    have htotal : (∑ i ∈ S, b i) + (∑ i ∈ Sᶜ, b i) = ∑ i, b i := by
      exact Finset.sum_add_sum_compl S b
    simp only [groupMean, hs, hcs, y, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← htotal]
    field_simp [hm, hc]
    <;> ring
  rw [OV_variance_shift P h _ _ ((∑ i, b i) / controlSize P) hpoint,
    OV_sample_variance P h]
  have hmean : mean y = mean a + (P.n1 : ℝ) / controlSize P * mean b := by
    unfold mean y
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hdiff : mean (fun i => a i - b i) = mean a - mean b := by
    simp only [mean, Finset.sum_sub_distrib, sub_div]
  have hi (i : Fin n) :
      (1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * ((y i - mean y)^2 / ((n : ℝ)-1)) =
        (a i - mean a)^2 / ((n : ℝ)-1) / (P.n1 : ℝ) +
        (b i - mean b)^2 / ((n : ℝ)-1) / controlSize P -
        ((a i - b i) - mean (fun j => a j - b j))^2 / ((n : ℝ)-1) / (n : ℝ) := by
    rw [hmean, hdiff]
    dsimp [y]
    unfold controlSize at *
    field_simp [hn, hm, hc, hn1]
    <;> ring
  simpa only [popVar, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_div, Finset.mul_sum] using
    (Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i))

private lemma OV_arm_nonempty {n} (P : Population n) (h : ValidDesign P)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) : S.Nonempty ∧ Sᶜ.Nonempty := by
  have hs : S.card = P.n1 := (Finset.mem_powersetCard.mp hS).2
  constructor
  · exact Finset.card_pos.mp (by rw [hs]; exact h.2.1)
  · apply Finset.card_pos.mp
    rw [Finset.card_compl, Fintype.card_fin, hs]
    exact Nat.sub_pos_of_lt h.2.2

private lemma OV_arm_intercept {n k} (P : CovPopulation n k)
    (A : Finset (Fin n)) (hA : A.Nonempty) (q : Fin n → ℝ)
    (c : Option (Fin k) → ℝ) :
    groupMean A (fun i => q i - slopeDot (P.x i) c) =
      groupMean A (fun i => q i - dotProduct (augmented P.x i) c) + c none := by
  calc
    _ = groupMean A (fun i => (q i - dotProduct (augmented P.x i) c) + c none) := by
      apply groupMean_congr
      intro i hi
      simp only [dotProduct, Fintype.sum_option, augmented, one_mul, slopeDot]
      ring
    _ = _ := groupMean_add_const _ _ _ hA

/-- The oracle is a residual contrast plus an intercept difference; no LATE
specialization or zero-mean residual premise is needed. -/
private lemma OV_oracle_decomposition {n k} (P : CovPopulation n k)
    (h : ValidDesign P.pop) (β : ℝ) (S : Finset (Fin n))
    (hS : S ∈ assignments P.pop) :
    oracleTau P β S =
      (groupMean S (residual P true β) - groupMean Sᶜ (residual P false β)) -
        (psi P false β none - psi P true β none) := by
  obtain ⟨hs, hc⟩ := OV_arm_nonempty P.pop h S hS
  have ht : groupMean S (fun i => observedW P.pop β S i - slopeDot (P.x i) (psi P true β)) =
      groupMean S (fun i => w P.pop true β i - slopeDot (P.x i) (psi P true β)) := by
    apply groupMean_congr
    intro i hi
    rw [observedW_treated _ _ _ _ hi]
  have hf : groupMean Sᶜ (fun i => observedW P.pop β S i - slopeDot (P.x i) (psi P false β)) =
      groupMean Sᶜ (fun i => w P.pop false β i - slopeDot (P.x i) (psi P false β)) := by
    apply groupMean_congr
    intro i hi
    rw [observedW_control _ _ _ _ hi]
  unfold oracleTau adjustedWith
  rw [ht, hf, OV_arm_intercept P S hs, OV_arm_intercept P Sᶜ hc]
  change (groupMean S (residual P true β) + psi P true β none) -
      (groupMean Sᶜ (residual P false β) + psi P false β none) = _
  ring

/-- The reassignment oracle is a contrast of pooled residuals; the pooled intercept cancels. -/
private lemma OV_star_decomposition {n k} (P : CovPopulation n k)
    (h : ValidDesign P.pop) (q : Fin n → ℝ) (S : Finset (Fin n))
    (hS : S ∈ assignments P.pop) :
    oracleStar P q S =
      groupMean S (fun i => q i - dotProduct (augmented P.x i) (ols P.x Finset.univ q)) -
      groupMean Sᶜ (fun i => q i - dotProduct (augmented P.x i) (ols P.x Finset.univ q)) := by
  obtain ⟨hs, hc⟩ := OV_arm_nonempty P.pop h S hS
  unfold oracleStar adjustedWith
  rw [OV_arm_intercept P S hs, OV_arm_intercept P Sᶜ hc]
  ring

/-- Exact oracle variance formulas (D.5)-(D.6), Supplement pp. 31-32. -/
theorem oracle_variances_proof {n k} (P : CovPopulation n k) (h : ValidDesign P.pop)
    (β : ℝ) (q : Fin n → ℝ) (hx : ∀ s, ∑ i, P.x i s = 0)
    (hg : (gram P.x Finset.univ).det ≠ 0) :
    designVariance P.pop (oracleTau P β) =
      popVar (residual P true β) / (P.pop.n1 : ℝ) +
      popVar (residual P false β) / controlSize P.pop -
      popVar (fun i => residual P true β i - residual P false β i) / (n : ℝ) ∧
    designVariance P.pop (oracleStar P q) =
      popVar (fun i => q i - dotProduct (augmented P.x i) (ols P.x Finset.univ q)) *
      (1/(P.pop.n1 : ℝ) + 1/controlSize P.pop) := by
  constructor
  · rw [OV_variance_shift P.pop h (oracleTau P β) _
      (psi P false β none - psi P true β none) (OV_oracle_decomposition P h β)]
    exact OV_contrast_variance P.pop h _ _
  · have he : ∀ S ∈ assignments P.pop,
        oracleStar P q S =
          (groupMean S (fun i => q i - dotProduct (augmented P.x i) (ols P.x Finset.univ q)) -
          groupMean Sᶜ (fun i => q i - dotProduct (augmented P.x i) (ols P.x Finset.univ q))) - 0 := by
      intro S hS
      simpa only [sub_zero] using OV_star_decomposition P h q S hS
    rw [OV_variance_shift P.pop h _ _ 0 he, OV_contrast_variance P.pop h]
    have hz : popVar (fun _ : Fin n => (0 : ℝ)) = 0 := by
      simp [popVar, mean]
    simp only [sub_self, hz, zero_div, sub_zero]
    ring

end
end AronowAudit.P002.Wave1
