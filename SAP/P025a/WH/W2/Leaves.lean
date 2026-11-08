import SAP.P025a.Defs.WholeW2
import SAP.P025a.Bridge
import AronowAudit.P025.P025_Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a.WH.W2
noncomputable section
open scoped BigOperators

/-- A finite product of normalized nonnegative masses is a probability law. Every rectangle
factorizes, and every coordinate has its supplied marginal law. Prove with `Fintype.prod_sum`;
write a rectangle indicator as the product of its coordinate indicators. For a coordinate event,
take the other events to be True. Empty index sets and singleton coordinate spaces are included.
This is only finite distributivity; no measure-theoretic independence theorem is needed. -/
def T5_L1 : Prop := by
  classical
  exact ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Ω : ι → Type) [∀ j, Fintype (Ω j)]
    (p : ∀ j, Ω j → ℝ), (∀ j x, 0 ≤ p j x) → (∀ j, (∑ x, p j x) = 1) →
    (∀ ω, 0 ≤ wholeProductProbability p ω) ∧
    (∑ ω, wholeProductProbability p ω) = 1 ∧
    wholeIndependentCoordinates p ∧
    (∀ j (A : Ω j → Prop),
      wholeEventProbability (wholeProductProbability p) (fun ω => A (ω j)) =
        wholeEventProbability (p j) A)

/-- For positive feasible quotas in two labeled infection strata, every tagged draw has the
specified counts and raw fraction. Weighting each selected unit by the reciprocal quota marginal
gives the population prevalence, with a positive denominator. Use `Finset.card_disjSum`,
`Finset.sum_disjSum`, and prove the infected/uninfected filter identities by extensionality and
case analysis on the population tag. These reduce the sums and counts to constants.
Positive quotas imply positive population sizes. Then field simplification gives s_b/(s_b/N_b)=N_b.
The quotas need not be strictly below the population sizes (a census stratum is allowed). -/
def T5_L2 : Prop :=
  ∀ (N₁ N₀ s₁ s₀ : ℕ), 0 < s₁ → 0 < s₀ → s₁ ≤ N₁ → s₀ ≤ N₀ →
    ∀ (t₁ : Finset (Fin N₁)) (t₀ : Finset (Fin N₀)), t₁.card = s₁ → t₀.card = s₀ →
    wholeBinaryDrawFacts
      (Sum.elim (fun _ => (s₁ : ℝ) / N₁) (fun _ => (s₀ : ℝ) / N₀))
      (wholeBinarySample t₁ t₀) ((N₁ : ℝ) / (N₁ + N₀)) s₁ s₀

private theorem lower_denominator_sum {J : ℕ} (mass : Fin J → ℝ) (γ : ℝ) (k : ℕ) :
    (∑ j, mass j * lowerWeights γ k j) = lowerDenominator mass γ k := by
  classical
  simp only [lowerWeights, mul_ite, mul_one, Finset.sum_ite, not_lt, lowerDenominator]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem upper_denominator_sum {J : ℕ} (mass : Fin J → ℝ) (γ : ℝ) (k : ℕ) :
    (∑ j, mass j * upperWeights γ k j) = wholeUpperDenominator mass γ k := by
  classical
  simp only [upperWeights, mul_ite, mul_one, Finset.sum_ite, not_lt, wholeUpperDenominator]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- All clauses of corrected Proposition 2 follow from existing donor theorems and finite algebra. -/
theorem T4_assembly : T4WholeStatement := by
  classical
  intro J hJ y mass hy hmass α β hα hab hb1
  let : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  have hβ : 0 < β := hα.trans_le hab
  have hγ : 0 < β / α := div_pos hβ hα
  have hlow (k : ℕ) (j : Fin J) : 0 < lowerWeights (β / α) k j := by
    dsimp [lowerWeights]
    split <;> positivity
  have hhigh (k : ℕ) (j : Fin J) : 0 < upperWeights (β / α) k j := by
    dsimp [upperWeights]
    split <;> positivity
  have hpartL (k : ℕ) : lowerValue y mass (β / α) k =
      lowerNumerator y mass (β / α) k / lowerDenominator mass (β / α) k := by
    simpa only [← Bridge.ratio_eq, Bridge.threshold_lower, lowerValue,
      lowerNumerator, lowerDenominator, one_mul] using
      AronowAudit.P025.threshold_partition y mass (β / α) 1 k
  have hpartH (k : ℕ) : upperValue y mass (β / α) k =
      wholeUpperNumerator y mass (β / α) k / wholeUpperDenominator mass (β / α) k := by
    simpa only [← Bridge.ratio_eq, Bridge.threshold_upper, upperValue,
      wholeUpperNumerator, wholeUpperDenominator, one_mul] using
      AronowAudit.P025.threshold_partition y mass 1 (β / α) k
  have hlast (j : Fin J) : y j ≤ y ⟨J - 1, by omega⟩ := by
    apply hy.monotone
    change j.val ≤ J - 1
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k _
    refine ⟨hpartL k, hpartH k, ?_, ?_⟩
    · rw [← lower_denominator_sum]
      exact AronowAudit.P025.denominator_pos mass _ hmass (hlow k)
    · rw [← upper_denominator_sum]
      exact AronowAudit.P025.denominator_pos mass _ hmass (hhigh k)
  · exact AronowAudit.P025.ratio_le y mass _ hmass (hlow (J - 1)) _ hlast
  · exact AronowAudit.P025.ratio_le y mass _ hmass (hhigh (J - 1)) _ hlast
  · intro k
    constructor
    · simpa only [← Bridge.ratio_eq, Bridge.threshold_lower, lowerValue,
        lower_denominator_sum] using
        AronowAudit.P025.threshold_increment hJ mass y hmass (β / α) 1 hγ zero_lt_one k
    · simpa only [← Bridge.ratio_eq, Bridge.threshold_upper, upperValue,
        upper_denominator_sum] using
        AronowAudit.P025.threshold_increment hJ mass y hmass 1 (β / α) zero_lt_one hγ k
  · obtain ⟨kL, kH, hL, hH, hwL, hwH, heL, heH, hl, hh, el, eh, _⟩ :=
      AronowAudit.P025.corrected_weighted_bounds hJ y mass hmass hy.monotone α β hα hab hb1
    have hWL (k : ℕ) : wholeLowerWeights_W2 (J := J) α β k =
        fun j => (1 / β) * lowerWeights (β / α) k j := by
      funext j
      dsimp [wholeLowerWeights_W2, lowerWeights]
      split
      · field_simp
      · simp
    have hWH (k : ℕ) : wholeUpperWeights_W2 (J := J) α β k =
        fun j => (1 / β) * upperWeights (β / α) k j := by
      funext j
      dsimp [wholeUpperWeights_W2, upperWeights]
      split
      · simp
      · field_simp
    refine ⟨kL, kH, hL, hH, ?_, ?_, ?_, ?_, ?_, hl, hh, ?_, ?_⟩
    · rw [hWL]
      exact hwL
    · rw [hWH]
      exact hwH
    · rw [hWL]
      exact heL
    · rw [hWH]
      exact heH
    · intro W hW
      exact ⟨hl.2 ⟨W, hW, rfl⟩, hh.2 ⟨W, hW, rfl⟩⟩
    · exact el.trans (hpartL kL.val)
    · exact eh.trans (hpartH kH.val)

private theorem quota_total (N s : ℕ) (hsN : s ≤ N) :
    (∑ t : WholeQuotaSpace N s, wholeQuotaProbability N s t) = 1 := by
  classical
  calc
    (∑ t : WholeQuotaSpace N s, wholeQuotaProbability N s t) =
        ∑ t ∈ quotaDraws N s, (1 : ℝ) / (quotaDraws N s).card :=
      Finset.sum_coe_sort (quotaDraws N s) (fun _ => (1 : ℝ) / (quotaDraws N s).card)
    _ = 1 := (AronowAudit.P025.quota_design_valid N s hsN).2.1

private theorem quota_event (N s : ℕ) (i : Fin N) :
    wholeEventProbability (wholeQuotaProbability N s) (fun t => i ∈ t.val) =
      quotaMarginal N s i := by
  classical
  calc
    wholeEventProbability (wholeQuotaProbability N s) (fun t => i ∈ t.val) =
        ∑ t : WholeQuotaSpace N s,
          if i ∈ t.val then (1 : ℝ) / (quotaDraws N s).card else 0 := by
      unfold wholeEventProbability wholeQuotaProbability
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : i ∈ t.val <;> simp [ht]
    _ = ∑ t ∈ quotaDraws N s,
        if i ∈ t then (1 : ℝ) / (quotaDraws N s).card else 0 :=
      Finset.sum_coe_sort (quotaDraws N s)
        (fun t => if i ∈ t then (1 : ℝ) / (quotaDraws N s).card else 0)
    _ = quotaMarginal N s i := by
      rw [← Finset.sum_filter]
      simp [quotaMarginal, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

private theorem binary_population_mean (N₁ N₀ : ℕ) :
    wholeBinaryPopulationMean N₁ N₀ = (N₁ : ℝ) / (N₁ + N₀) := by
  simp [wholeBinaryPopulationMean, Fintype.sum_sum_type, wholeBinaryOutcome]

private theorem application_certificate (h1 : T5_L1) (h2 : T5_L2)
    (N : Fin 4 → ℕ) (q : ℝ)
    (hquota : ∀ j, 0 < wholeApplicationQuotas j ∧ wholeApplicationQuotas j ≤ N j)
    (hbound : ∀ j, (wholeApplicationQuotas j : ℝ) / N j ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hmeanG : (N 0 : ℝ) / (N 0 + N 1) = q)
    (hmeanE : (N 2 : ℝ) / (N 2 + N 3) = q) :
    wholeApplicationCertificate N q := by
  classical
  have hnon (j : Fin 4) : Nonempty (WholeQuotaSpace (N j) (wholeApplicationQuotas j)) := by
    obtain ⟨t, ht⟩ := (AronowAudit.P025.quota_design_valid (N j) _ (hquota j).2).1
    exact ⟨⟨t, ht⟩⟩
  obtain ⟨hprob, htotal, hind, hcoord⟩ := h1 (Fin 4)
    (fun j => WholeQuotaSpace (N j) (wholeApplicationQuotas j))
    (fun j => wholeQuotaProbability (N j) (wholeApplicationQuotas j))
    (fun _ _ => by unfold wholeQuotaProbability; positivity)
    (fun j => quota_total (N j) _ (hquota j).2)
  have hmarg (j : Fin 4) (i : Fin (N j)) :
      wholeEventProbability (wholeApplicationProbability N) (fun ω => i ∈ (ω j).val) =
        (wholeApplicationQuotas j : ℝ) / N j := by
    change wholeEventProbability (wholeProductProbability _) _ = _
    rw [hcoord j (fun t => i ∈ t.val), quota_event]
    exact AronowAudit.P025.quota_marginal_eq (N j) _ (hquota j).1 (hquota j).2 i
  have hG (i : Fin (N 0) ⊕ Fin (N 1)) : wholeGalleryInclusion N i =
      Sum.elim (fun _ => (44 : ℝ) / N 0) (fun _ => (4 : ℝ) / N 1) i := by
    cases i with
    | inl i =>
      simpa [wholeGalleryInclusion, designInclusion, wholeGallerySample,
        wholeBinarySample, Finset.inl_mem_disjSum, wholeEventProbability,
        wholeApplicationQuotas, mul_ite, ← Finset.sum_filter] using hmarg 0 i
    | inr i =>
      simpa [wholeGalleryInclusion, designInclusion, wholeGallerySample,
        wholeBinarySample, Finset.inr_mem_disjSum, wholeEventProbability,
        wholeApplicationQuotas, mul_ite, ← Finset.sum_filter] using hmarg 1 i
  have hE (i : Fin (N 2) ⊕ Fin (N 3)) : wholeExchangeInclusion N i =
      Sum.elim (fun _ => (291 : ℝ) / N 2) (fun _ => (288 : ℝ) / N 3) i := by
    cases i with
    | inl i =>
      simpa [wholeExchangeInclusion, designInclusion, wholeExchangeSample,
        wholeBinarySample, Finset.inl_mem_disjSum, wholeEventProbability,
        wholeApplicationQuotas, mul_ite, ← Finset.sum_filter] using hmarg 2 i
    | inr i =>
      simpa [wholeExchangeInclusion, designInclusion, wholeExchangeSample,
        wholeBinarySample, Finset.inr_mem_disjSum, wholeEventProbability,
        wholeApplicationQuotas, mul_ite, ← Finset.sum_filter] using hmarg 3 i
  refine ⟨⟨fun j => Classical.choice (hnon j)⟩, hprob, htotal, hind, hmarg, hG, hE,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hG]
    cases i with
    | inl _ => simpa [wholeApplicationQuotas] using hbound 0
    | inr _ => simpa [wholeApplicationQuotas] using hbound 1
  · intro i
    rw [hE]
    cases i with
    | inl _ => simpa [wholeApplicationQuotas] using hbound 2
    | inr _ => simpa [wholeApplicationQuotas] using hbound 3
  · exact (binary_population_mean _ _).trans hmeanG
  · exact (binary_population_mean _ _).trans hmeanE
  · intro ω
    have hcard (j : Fin 4) : (ω j).val.card = wholeApplicationQuotas j :=
      (AronowAudit.P025.quota_design_valid (N j) _ (hquota j).2).2.2 _ (ω j).property
    have hGquota : 44 ≤ N 0 ∧ 4 ≤ N 1 := by
      exact ⟨(hquota 0).2, (hquota 1).2⟩
    have hEquota : 291 ≤ N 2 ∧ 288 ≤ N 3 := by
      exact ⟨(hquota 2).2, (hquota 3).2⟩
    have hfG := h2 (N 0) (N 1) 44 4 (by norm_num) (by norm_num)
      hGquota.1 hGquota.2 (ω 0).val (ω 1).val (hcard 0) (hcard 1)
    have hfE := h2 (N 2) (N 3) 291 288 (by norm_num) (by norm_num)
      hEquota.1 hEquota.2 (ω 2).val (ω 3).val (hcard 2) (hcard 3)
    norm_num only [Nat.cast_ofNat] at hfG hfE
    have heqG : wholeGalleryInclusion N =
        Sum.elim (fun _ => (44 : ℝ) / N 0) (fun _ => (4 : ℝ) / N 1) := funext hG
    have heqE : wholeExchangeInclusion N =
        Sum.elim (fun _ => (291 : ℝ) / N 2) (fun _ => (288 : ℝ) / N 3) := funext hE
    rw [← heqG, hmeanG] at hfG
    rw [← heqE, hmeanE] at hfE
    change wholeBinaryDrawFacts _ (wholeGallerySample N ω) _ _ _ at hfG
    change wholeBinaryDrawFacts _ (wholeExchangeSample N ω) _ _ _ at hfE
    refine ⟨hfG, hfE, ?_⟩
    rw [hfG.2.2.2.1, hfE.2.2.2.1]
    norm_num

/-- The whole counterexample combines its existing arithmetic certificates with two finite-design
leaves. Instantiating both quota designs and all arithmetic is proved here. -/
theorem T5_assembly (h1 : T5_L1) (h2 : T5_L2) : T5WholeStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨AronowAudit.P025.application_counterexample_numbers,
      AronowAudit.P025.application_rounded_counterexamples,
      AronowAudit.P025.application_counterexample_designs, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro N s hs
      have hsize : ∀ x ∈ applicationStrata, 0 < x.2 ∧ x.2 ≤ x.1 := by
        norm_num [applicationStrata]
      exact AronowAudit.P025.quota_design_valid N s (hsize (N, s) hs).2
    · norm_num
    all_goals norm_num [binaryInterval, binaryLower, binaryUpper]
  · apply application_certificate h1 h2 wholeApplicationSizesA (3 / 4)
    · intro j
      fin_cases j <;> norm_num [wholeApplicationQuotas, wholeApplicationSizesA]
    · intro j
      fin_cases j <;> norm_num [wholeApplicationQuotas, wholeApplicationSizesA]
    · norm_num [wholeApplicationSizesA]
    · norm_num [wholeApplicationSizesA]
  · apply application_certificate h1 h2 wholeApplicationSizesB (4 / 5)
    · intro j
      fin_cases j <;> norm_num [wholeApplicationQuotas, wholeApplicationSizesB]
    · intro j
      fin_cases j <;> norm_num [wholeApplicationQuotas, wholeApplicationSizesB]
    · norm_num [wholeApplicationSizesB]
    · norm_num [wholeApplicationSizesB]
  all_goals norm_num [binaryLower, binaryUpper]

end
end SAP.P025a.WH.W2
