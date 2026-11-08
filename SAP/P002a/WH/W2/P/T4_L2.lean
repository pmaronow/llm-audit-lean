import SAP.P002a.WH.W2.Leaves
import AronowAudit.P002.Wave1.PrintedTheorem2.N3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace SAP.P002a.WH.W2.P.T4_L2
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

private def optionFinOneEquivFinTwo : Option (Fin 1) ≃ Fin 2 where
  toFun := fun o => match o with | none => 0 | some _ => 1
  invFun := fun i => if i = 0 then none else some 0
  left_inv := by
    intro o
    cases o with
    | none => rfl
    | some i => fin_cases i; rfl
  right_inv := by intro i; fin_cases i <;> rfl

private lemma det_option_fin_one {A : Matrix (Option (Fin 1)) (Option (Fin 1)) ℝ} :
    A.det = A none none * A (some 0) (some 0) - A none (some 0) * A (some 0) none := by
  rw [← Matrix.det_reindex_self optionFinOneEquivFinTwo]
  rw [Matrix.det_fin_two]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  norm_num [optionFinOneEquivFinTwo]

private lemma gram_det_formula {n : ℕ} (x : Fin n → Fin 1 → ℝ)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    (gram x S).det = groupMean S (fun i => x i 0^2) -
      (groupMean S (fun i => x i 0))^2 := by
  rw [det_option_fin_one]
  have hc : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hS)
  simp [gram, groupMean, augmented, hc, pow_two]

private lemma six_late : late W2Six.pop = 7/3 := by
  norm_num [late, compliers, groupMean, W2Six, gridX, Fin.sum_univ_succ]

private lemma six_population_gram_det : (gram W2Six.x Finset.univ).det ≠ 0 := by
  rw [det_option_fin_one]
  norm_num [gram, groupMean, augmented, W2Six, gridX, Fin.sum_univ_succ]

private def treatedCoef : Option (Fin 1) → ℝ := fun o => if o = none then 0 else 2
private def controlCoef : Option (Fin 1) → ℝ := fun o => if o = none then 0 else 1

private lemma six_treated_psi : psi W2Six true (late W2Six.pop) = treatedCoef := by
  have hresponse : w W2Six.pop true (late W2Six.pop) =
      fun i => dotProduct (augmented W2Six.x i) treatedCoef := by
    funext i
    rw [six_late]
    simp [w, binary, W2Six, dotProduct, augmented, treatedCoef, Fintype.sum_option]
    ring
  have hscore : score W2Six.x Finset.univ (w W2Six.pop true (late W2Six.pop)) =
      gram W2Six.x Finset.univ *ᵥ treatedCoef := by
    rw [hresponse]
    simpa only [SAP.P002a.Bridge.score_eq, SAP.P002a.Bridge.gram_eq,
      SAP.P002a.Bridge.augmented_eq] using
      (AronowAudit.P002.score_of_dot W2Six.x Finset.univ treatedCoef)
  unfold psi
  rw [ols, if_pos six_population_gram_det, hscore, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr six_population_gram_det), Matrix.one_mulVec]

private lemma six_control_psi : psi W2Six false (late W2Six.pop) = controlCoef := by
  have hresponse : w W2Six.pop false (late W2Six.pop) =
      fun i => dotProduct (augmented W2Six.x i) controlCoef := by
    funext i
    rw [six_late]
    simp [w, binary, W2Six, dotProduct, augmented, controlCoef, Fintype.sum_option]
  have hscore : score W2Six.x Finset.univ (w W2Six.pop false (late W2Six.pop)) =
      gram W2Six.x Finset.univ *ᵥ controlCoef := by
    rw [hresponse]
    simpa only [SAP.P002a.Bridge.score_eq, SAP.P002a.Bridge.gram_eq,
      SAP.P002a.Bridge.augmented_eq] using
      (AronowAudit.P002.score_of_dot W2Six.x Finset.univ controlCoef)
  unfold psi
  rw [ols, if_pos six_population_gram_det, hscore, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr six_population_gram_det), Matrix.one_mulVec]

private lemma six_residual_zero :
    ∀ a i, SAP.P002a.residual W2Six a (late W2Six.pop) i = 0 := by
  intro a i
  cases a
  · rw [SAP.P002a.residual, six_control_psi, six_late]
    norm_num [w, binary, W2Six, controlCoef, dotProduct, augmented, Fintype.sum_option]
  · rw [SAP.P002a.residual, six_treated_psi, six_late]
    norm_num [w, binary, W2Six, treatedCoef, dotProduct, augmented, Fintype.sum_option]
    all_goals ring

private lemma six_x_sum : ∑ i : Fin 6, W2Six.x i 0 = 0 := by
  norm_num [W2Six, gridX, Fin.sum_univ_succ]

private lemma six_x_fourth : mean (fun i : Fin 6 => W2Six.x i 0 ^ 4) ≤ 4 := by
  norm_num [mean, W2Six, gridX, Fin.sum_univ_succ]

private lemma six_x_second_lower :
    1/4 ≤ mean (fun i : Fin 6 => W2Six.x i 0 ^ 2) := by
  norm_num [mean, W2Six, gridX, Fin.sum_univ_succ]

private lemma six_x_rayleigh (b : Fin 1 → ℝ) :
    (1/4 : ℝ) * normSq b ≤ mean (fun i : Fin 6 => (dotProduct (W2Six.x i) b)^2) := by
  norm_num [normSq, mean, dotProduct, W2Six, gridX, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (b 0)]

private lemma six_admissible : Xi W2Six 0 (1/4) 4 (1/2) (1/4) := by
  unfold Xi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [ValidDesign, W2Six]
  · intro i
    simp [MonotoneReceipt, W2Six]
  · have hc : compliers W2Six.pop = Finset.univ := by
      ext i
      simp [compliers, W2Six]
    rw [hc]
    exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by decide⟩⟩
  · norm_num [W2Six]
  · norm_num [W2Six]
  · simp [six_residual_zero, popCov, popVar, mean]
  · intro a
    simp [six_residual_zero, fourthNorm, popVar, mean]
  · intro s
    fin_cases s
    exact six_x_sum
  · intro s
    fin_cases s
    exact six_x_fourth
  · exact six_x_rayleigh

private lemma six_arm_grams : ∀ O ∈ assignments W2Six.pop,
    (gram W2Six.x O).det ≠ 0 ∧ (gram W2Six.x Oᶜ).det ≠ 0 := by
  intro O hO
  have hcard : O.card = 3 := (Finset.mem_powersetCard.mp hO).2
  have hSne : O.Nonempty := Finset.card_pos.mp (by rw [hcard]; norm_num)
  have hCcard : Oᶜ.card = 3 := by rw [Finset.card_compl, Fintype.card_fin, hcard]
  have hCne : Oᶜ.Nonempty := Finset.card_pos.mp (by rw [hCcard]; norm_num)
  have hdetS := gram_det_formula W2Six.x O hSne
  have hdetC := gram_det_formula W2Six.x Oᶜ hCne
  have hsum1 (f : Fin 6 → ℝ) :
      (∑ i ∈ Oᶜ, f i) = (∑ i, f i) - ∑ i ∈ O, f i := by
    have hh := Finset.sum_compl_add_sum O f
    linarith
  have hsumX : (∑ i ∈ Oᶜ, W2Six.x i 0) =
      (∑ i, W2Six.x i 0) - ∑ i ∈ O, W2Six.x i 0 := hsum1 _
  have hsumX2 : (∑ i ∈ Oᶜ, W2Six.x i 0^2) =
      (∑ i, W2Six.x i 0^2) - ∑ i ∈ O, W2Six.x i 0^2 := hsum1 _
  fin_cases O
  all_goals norm_num at hcard
  all_goals
    rw [hdetS, hdetC]
    unfold groupMean
    rw [hsumX, hsumX2]
    norm_num [Finset.card_compl, Fintype.card_fin, W2Six, gridX, Fin.sum_univ_succ]

private lemma six_observed_response (O : Finset (Fin 6)) (i : Fin 6) :
    observedW W2Six.pop (7/3) O i =
      if i ∈ O then 2 * W2Six.x i 0 else W2Six.x i 0 := by
  by_cases hi : i ∈ O
  · simp [observedW, observedY, observedD, W2Six, binary, hi]
  · simp [observedW, observedY, observedD, W2Six, binary, hi]

private lemma six_adjusted_stat_zero :
    ∀ O ∈ assignments W2Six.pop,
      adjustedAR W2Six (observedW W2Six.pop (7/3) O) O = 0 := by
  intro O hO
  let q : Fin 6 → ℝ := observedW W2Six.pop (7/3) O
  have hgrams := six_arm_grams O hO
  have hq1 : ∀ i ∈ O, q i = dotProduct (augmented W2Six.x i) treatedCoef := by
    intro i hi
    change observedW W2Six.pop (7/3) O i = _
    rw [six_observed_response, if_pos hi]
    simp [dotProduct, augmented, treatedCoef, Fintype.sum_option]
    ring
  have hq0 : ∀ i ∈ Oᶜ, q i = dotProduct (augmented W2Six.x i) controlCoef := by
    intro i hi
    change observedW W2Six.pop (7/3) O i = _
    have hnot : i ∉ O := Finset.mem_compl.mp hi
    rw [six_observed_response, if_neg hnot]
    simp [dotProduct, augmented, controlCoef, Fintype.sum_option]
  have recover (S : Finset (Fin 6)) (c : Option (Fin 1) → ℝ)
      (hg : (gram W2Six.x S).det ≠ 0)
      (hq : ∀ i ∈ S, q i = dotProduct (augmented W2Six.x i) c) :
      ols W2Six.x S q = c := by
    have hsc := AronowAudit.P002.score_congr W2Six.x S q
      (fun i => dotProduct (augmented W2Six.x i) c) hq
    have hsd := AronowAudit.P002.score_of_dot W2Six.x S c
    have hs : score W2Six.x S q = gram W2Six.x S *ᵥ c := by
      calc
        score W2Six.x S q = score W2Six.x S (fun i =>
            dotProduct (augmented W2Six.x i) c) := by
          simpa only [SAP.P002a.Bridge.score_eq, SAP.P002a.Bridge.augmented_eq] using hsc
        _ = gram W2Six.x S *ᵥ c := by
          simpa only [SAP.P002a.Bridge.score_eq, SAP.P002a.Bridge.gram_eq,
            SAP.P002a.Bridge.augmented_eq] using hsd
    unfold ols
    rw [if_pos hg, hs, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg), Matrix.one_mulVec]
  have hfit1 : fitted W2Six q O true = treatedCoef := by
    simpa [fitted] using recover O treatedCoef hgrams.1 hq1
  have hfit0 : fitted W2Six q O false = controlCoef := by
    simpa [fitted] using recover Oᶜ controlCoef hgrams.2 hq0
  have hrss1 : rss W2Six.x O q (fitted W2Six q O true) = 0 := by
    rw [hfit1]
    unfold rss
    apply Finset.sum_eq_zero
    intro i hi
    rw [hq1 i hi]
    simp [dotProduct, augmented, treatedCoef, Fintype.sum_option]
  have hrss0 : rss W2Six.x Oᶜ q (fitted W2Six q O false) = 0 := by
    rw [hfit0]
    unfold rss
    apply Finset.sum_eq_zero
    intro i hi
    rw [hq0 i hi]
    simp [dotProduct, augmented, controlCoef, Fintype.sum_option]
  have hmean1 : groupMean O (fun i => q i - slopeDot (W2Six.x i) treatedCoef) = 0 := by
    have hz : (∑ i ∈ O, (q i - slopeDot (W2Six.x i) treatedCoef)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hq1 i hi]
      simp [dotProduct, augmented, slopeDot, treatedCoef, Fintype.sum_option]
    change (∑ i ∈ O, (q i - slopeDot (W2Six.x i) treatedCoef)) / (O.card : ℝ) = 0
    rw [hz]
    simp
  have hmean0 : groupMean Oᶜ (fun i => q i - slopeDot (W2Six.x i) controlCoef) = 0 := by
    have hz : (∑ i ∈ Oᶜ, (q i - slopeDot (W2Six.x i) controlCoef)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hq0 i hi]
      simp [dotProduct, augmented, slopeDot, controlCoef, Fintype.sum_option]
    change (∑ i ∈ Oᶜ, (q i - slopeDot (W2Six.x i) controlCoef)) / (Oᶜ.card : ℝ) = 0
    rw [hz]
    simp
  have htau : adjustedTau W2Six q O = 0 := by
    simp [adjustedTau, adjustedWith, hfit1, hfit0, hmean1, hmean0]
  have hsigma : adjustedSigma2 W2Six q O = 0 := by
    simp [adjustedSigma2, hrss1, hrss0]
  change absStudent (adjustedTau W2Six q O) (adjustedSigma2 W2Six q O) = 0
  simp [htau, hsigma, absStudent]

end
end SAP.P002a.WH.W2.P.T4_L2

theorem SAP.P002a.WH.W2.T4_L2_proof : SAP.P002a.WH.W2.T4_L2 := by
  refine ⟨SAP.P002a.WH.W2.P.T4_L2.six_admissible,
    SAP.P002a.WH.W2.P.T4_L2.six_late, ?_, ?_, ?_⟩
  · refine ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩
    norm_num [SAP.P002a.W2Six, SAP.P002a.gridX]
  · norm_num [SAP.P002a.assignments, SAP.P002a.W2Six,
      Finset.card_powersetCard, Nat.choose]
  · intro O hO
    have hstat := SAP.P002a.WH.W2.P.T4_L2.six_adjusted_stat_zero O hO
    refine ⟨hstat, ?_⟩
    intro α hα
    rw [SAP.P002a.adjustedAccepted, hstat]
    exact bot_le
