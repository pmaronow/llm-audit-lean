import AronowAudit.P031.P031_Variance
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N7
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N9
import AronowAudit.P002.Wave1.Lib.FinitePopulationCLT
import AronowAudit.P053.P053_NormalQuantiles

/-!
P031-T6: explicit unbalanced populations, their actual finite-randomization
normal limit, and the common OLS/CE undercoverage limit. The finite-population
CLT is the proved P002 theorem; all probability manipulations below use the
P031 finite assignment law.
-/

namespace AronowAudit.P031.Wave1

open scoped BigOperators Matrix Topology
open Finset Filter

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000

lemma T6_size_sub_one_pos (n : ℕ) : (0 : ℝ) < ((4 * (n + 2) : ℕ) : ℝ) - 1 := by
  push_cast
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

def T6_design (n : ℕ) : AronowAudit.P002.Population (4 * (n + 2)) where
  y := fun _ _ => 0
  d := fun _ b => b
  n1 := n + 2

lemma T6_sign_mean (n : ℕ) :
    AronowAudit.P002.mean (footnoteSigns (n + 2)) = 0 := by
  simp [AronowAudit.P002.mean, (footnote_sign_moments (n + 2) (by omega)).1]

lemma T6_sign_variance (n : ℕ) :
    AronowAudit.P002.popVar (footnoteSigns (n + 2)) =
      (4 * (n + 2) : ℕ) / ((4 * (n + 2) : ℕ) - 1 : ℝ) := by
  simp [AronowAudit.P002.popVar, T6_sign_mean,
    (footnote_sign_moments (n + 2) (by omega)).2.1]

lemma T6_sign_maximum (n : ℕ) :
    AronowAudit.P002.maximum (fun i =>
      (footnoteSigns (n + 2) i - AronowAudit.P002.mean (footnoteSigns (n + 2))) ^ 2) = 1 := by
  simp only [T6_sign_mean, sub_zero]
  apply le_antisymm
  · apply AronowAudit.P002.maximum_le _ _ (by norm_num)
    intro i
    rw [(footnote_sign_moments (n + 2) (by omega)).2.1 i]
  · have hh := AronowAudit.P002.le_maximum (fun i => footnoteSigns (n + 2) i ^ 2)
        (⟨0, by omega⟩ : Fin (4 * (n + 2)))
    rw [(footnote_sign_moments (n + 2) (by omega)).2.1] at hh
    exact hh

lemma T6_maximum_ratio :
    Tendsto (fun n =>
      AronowAudit.P002.maximum (fun i => (footnoteSigns (n + 2) i -
        AronowAudit.P002.mean (footnoteSigns (n + 2))) ^ 2) /
      (((min (T6_design n).n1 (4 * (n + 2) - (T6_design n).n1) : ℕ) : ℝ) *
        AronowAudit.P002.popVar (footnoteSigns (n + 2)))) atTop (𝓝 0) := by
  have hk : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    hk.const_div_atTop 1
  have hl := hi.mul ((tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (hi.div_const 4))
  norm_num only [zero_div, sub_zero, zero_mul] at hl
  apply hl.congr
  intro n
  have hm : min (n + 2) (4 * (n + 2) - (n + 2)) = n + 2 := by omega
  simp only [T6_sign_maximum, T6_sign_variance, T6_design, hm]
  push_cast
  have hk0 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hN0 : 4 * ((n : ℝ) + 2) - 1 ≠ 0 := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using (T6_size_sub_one_pos n).ne'
  field_simp
  <;> ring

lemma T6_probability_bridge (n : ℕ) (E : Finset (Fin (4 * (n + 2))) → Prop) :
    AronowAudit.P002.probability (T6_design n) E =
      eventProbability (footnotePopulation 2 n) E := by
  classical
  let A : Finset (Finset (Fin (4 * (n + 2)))) := univ.powersetCard (n + 2)
  change ((A.filter E).card : ℝ) / A.card =
    (∑ s ∈ A, if E s then (1 : ℝ) else 0) / A.card
  simp only [Finset.sum_boole]

lemma T6_true_variance_pos (n : ℕ) : 0 < trueVariance (footnotePopulation 2 n) := by
  rw [footnote_true_variance_formula]
  exact div_pos (by norm_num) (T6_size_sub_one_pos n)

lemma T6_standardize (n : ℕ) (s : Finset (Fin (4 * (n + 2))))
    (hs : s ∈ (univ : Finset (Fin (4 * (n + 2)))).powersetCard (n + 2)) :
    (pointEstimate (footnotePopulation 2 n) s - populationEffect (footnotePopulation 2 n)) /
        Real.sqrt (trueVariance (footnotePopulation 2 n)) =
      (AronowAudit.P002.groupMean s (footnoteSigns (n + 2)) -
        AronowAudit.P002.mean (footnoteSigns (n + 2))) /
        Real.sqrt ((1 / ((T6_design n).n1 : ℝ) - 1 / ((4 * (n + 2) : ℕ) : ℝ)) *
          AronowAudit.P002.popVar (footnoteSigns (n + 2))) := by
  have hc := (mem_powersetCard.mp hs).2
  have hk : sᶜ.card = 3 * (n + 2) := by
    have hh := s.card_add_card_compl
    simp only [Fintype.card_fin] at hh
    omega
  have hm0 : (s.card : ℝ) ≠ 0 := by rw [hc]; positivity
  have hz := footnote_sign_moments (n + 2) (by omega)
  have hsplit := s.sum_add_sum_compl (footnoteSigns (n + 2))
  rw [hz.1] at hsplit
  have hcontrol : groupMean sᶜ (footnoteSigns (n + 2)) =
      -groupMean s (footnoteSigns (n + 2)) / 3 := by
    unfold groupMean
    rw [hc, hk]
    push_cast
    have hn0 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    linarith
  have ht : groupMean s (fun i => 2 * footnoteSigns (n + 2) i + 2) =
      2 * groupMean s (footnoteSigns (n + 2)) + 2 := by
    simp only [groupMean, sum_add_distrib, ← Finset.mul_sum, sum_const, nsmul_eq_mul]
    field_simp
  have hpoint : pointEstimate (footnotePopulation 2 n) s -
      populationEffect (footnotePopulation 2 n) =
      (7 / 3 : ℝ) * groupMean s (footnoteSigns (n + 2)) := by
    rw [(footnote_population_moments 2 n).2.2.2.1]
    change estimate s (observed s (fun i => 2 * footnoteSigns (n + 2) i + 2)
      (footnoteSigns (n + 2))) - 2 = _
    unfold estimate
    rw [(observed_group_means s (fun i => 2 * footnoteSigns (n + 2) i + 2)
      (footnoteSigns (n + 2))).1,
      (observed_group_means s (fun i => 2 * footnoteSigns (n + 2) i + 2)
        (footnoteSigns (n + 2))).2]
    rw [ht, hcontrol]
    ring
  let b : ℝ := (1 / ((T6_design n).n1 : ℝ) - 1 / ((4 * (n + 2) : ℕ) : ℝ)) *
    AronowAudit.P002.popVar (footnoteSigns (n + 2))
  have hv : trueVariance (footnotePopulation 2 n) = (7 / 3 : ℝ) ^ 2 * b := by
    rw [footnote_true_variance_formula]
    dsimp only [b, T6_design, footnotePopulation]
    rw [T6_sign_variance]
    push_cast
    have hn0 : (n : ℝ) + 2 ≠ 0 := by positivity
    have hN0 : 4 * ((n : ℝ) + 2) - 1 ≠ 0 := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using (T6_size_sub_one_pos n).ne'
    field_simp
    <;> ring
  have hroot : Real.sqrt (trueVariance (footnotePopulation 2 n)) =
      (7 / 3 : ℝ) * Real.sqrt b := by
    rw [hv, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (7 / 3 : ℝ) ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (7 / 3 : ℝ))]
  rw [hpoint, hroot, T6_sign_mean, sub_zero]
  change (7 / 3 : ℝ) * groupMean s (footnoteSigns (n + 2)) / ((7 / 3 : ℝ) * Real.sqrt b) =
    groupMean s (footnoteSigns (n + 2)) / Real.sqrt b
  exact mul_div_mul_left _ _ (by norm_num : (7 / 3 : ℝ) ≠ 0)

lemma T6_standardized_normal : StandardizedNormalLimit (footnotePopulation 2) := by
  refine ⟨Eventually.of_forall T6_true_variance_pos, ?_⟩
  intro x
  have hD : ∀ n, AronowAudit.P002.ValidDesign (T6_design n) := by
    intro n
    dsimp [AronowAudit.P002.ValidDesign, T6_design]
    omega
  have hv : ∀ n, 0 < AronowAudit.P002.popVar (footnoteSigns (n + 2)) := by
    intro n
    rw [T6_sign_variance]
    exact div_pos (by positivity) (T6_size_sub_one_pos n)
  have hclt := AronowAudit.P002.Wave1.finitePopulationCLT (fun n => 4 * (n + 2))
    (by intro a b h; dsimp only; omega) T6_design (fun n => footnoteSigns (n + 2)) hD hv T6_maximum_ratio x
  rw [← MeasureTheory.measureReal_def, ← ProbabilityTheory.cdf_eq_real] at hclt
  change Tendsto _ atTop (𝓝 (normalCDF x)) at hclt
  apply hclt.congr
  intro n
  rw [T6_probability_bridge]
  unfold eventProbability
  apply expectation_congr
  intro s hs
  have he := T6_standardize n s hs
  simp only [he]

lemma T6_event_nonneg (Q : Population) (E : Finset (Fin Q.N) → Prop) :
    0 ≤ eventProbability Q E := (FootnoteThreeProbability.n7_proof Q).1 E

lemma T6_event_mono (Q : Population) (E F : Finset (Fin Q.N) → Prop)
    (h : ∀ s ∈ (univ : Finset (Fin Q.N)).powersetCard Q.M, E s → F s) :
    eventProbability Q E ≤ eventProbability Q F :=
  (FootnoteThreeProbability.n7_proof Q).2.1 E F h

lemma T6_event_union (Q : Population) (E F : Finset (Fin Q.N) → Prop) :
    eventProbability Q (fun s => E s ∨ F s) ≤ eventProbability Q E + eventProbability Q F :=
  (FootnoteThreeProbability.n7_proof Q).2.2.1 E F

lemma T6_continuous_probability (P : ℕ → Population) (X : VarianceEstimator) (a : ℝ)
    (hX : ConvergesInProbability P X a) (f : ℝ → ℝ) (hf : ContinuousAt f a) :
    ConvergesInProbability P (fun Q s => f (X Q s)) (f a) := by
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp hf ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hX (δ / 2) (by positivity))
  · intro n
    exact T6_event_nonneg _ _
  · intro n
    apply T6_event_mono
    intro s _ hbad
    by_contra hnot
    have hsmall : |X (P n) s - a| ≤ δ / 2 := le_of_not_gt hnot
    have hh := hfδ (x := X (P n) s) (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at hh
    linarith

/-- A random cutoff approaching a constant has the same CDF limit. The
intermediate event may use either a strict or a non-strict inequality. -/
lemma T6_random_cdf (P : ℕ → Population) (W R : VarianceEstimator) (t : ℝ)
    (hW : ∀ x, Tendsto (fun n => eventProbability (P n) (fun s => W (P n) s ≤ x))
      atTop (𝓝 (normalCDF x)))
    (hR : ConvergesInProbability P R t)
    (E : (Q : Population) → Finset (Fin Q.N) → Prop)
    (hlo : ∀ Q s, W Q s < R Q s → E Q s)
    (hhi : ∀ Q s, E Q s → W Q s ≤ R Q s) :
    Tendsto (fun n => eventProbability (P n) (E (P n))) atTop (𝓝 (normalCDF t)) := by
  apply StatLean.HypothesisTesting.tendsto_of_squeeze_continuousAt
    (show ContinuousAt normalCDF t from
      StatLean.HypothesisTesting.lipschitzWith_cdf_gaussianReal.continuous.continuousAt)
  intro ε hε
  have hL := Metric.tendsto_nhds.mp (hW (t - ε / 2)) (ε / 2) (by positivity)
  have hU := Metric.tendsto_nhds.mp (hW (t + ε / 2)) (ε / 2) (by positivity)
  have hB := Metric.tendsto_nhds.mp (hR (ε / 4) (by positivity)) (ε / 2) (by positivity)
  filter_upwards [hL, hU, hB] with n hnL hnU hnB
  rw [Real.dist_eq, abs_lt] at hnL hnU
  rw [Real.dist_eq, sub_zero, abs_lt] at hnB
  have hleft : eventProbability (P n) (fun s => W (P n) s ≤ t - ε / 2) ≤
      eventProbability (P n) (E (P n)) +
        eventProbability (P n) (fun s => ε / 4 < |R (P n) s - t|) := by
    apply le_trans (T6_event_mono (P n) _
      (fun s => E (P n) s ∨ ε / 4 < |R (P n) s - t|) ?_) (T6_event_union _ _ _)
    intro s _ hs
    by_cases hb : ε / 4 < |R (P n) s - t|
    · exact Or.inr hb
    · left
      apply hlo
      have hh := (abs_le.mp (le_of_not_gt hb)).1
      linarith
  have hright : eventProbability (P n) (E (P n)) ≤
      eventProbability (P n) (fun s => W (P n) s ≤ t + ε / 2) +
        eventProbability (P n) (fun s => ε / 4 < |R (P n) s - t|) := by
    apply le_trans (T6_event_mono (P n) _
      (fun s => W (P n) s ≤ t + ε / 2 ∨ ε / 4 < |R (P n) s - t|) ?_)
      (T6_event_union _ _ _)
    intro s _ hs
    by_cases hb : ε / 4 < |R (P n) s - t|
    · exact Or.inr hb
    · left
      have hh := (abs_le.mp (le_of_not_gt hb)).2
      have hw := hhi (P n) s hs
      linarith
  have hmono : Monotone normalCDF := ProbabilityTheory.monotone_cdf _
  have hmL := hmono (show t - ε ≤ t - ε / 2 by linarith)
  have hmU := hmono (show t + ε / 2 ≤ t + ε by linarith)
  constructor <;> linarith

/-- Coverage follows from two random-cutoff CDFs on the finite design.
No independence or common probability space across rows is needed. -/
lemma T6_coverage_limit (P : ℕ → Population) (V : VarianceEstimator) (a v z : ℝ)
    (hNormal : StandardizedNormalLimit P)
    (hVar : Tendsto (fun n => ((P n).N : ℝ) * trueVariance (P n)) atTop (𝓝 v))
    (hv : 0 < v)
    (hV : ConvergesInProbability P (fun Q s => (Q.N : ℝ) * V Q s) a)
    (hz : 0 < z) :
    Tendsto (fun n => coverage (P n) V z) atTop
      (𝓝 (2 * normalCDF (z * Real.sqrt (a / v)) - 1)) := by
  let W : VarianceEstimator := fun Q s =>
    (pointEstimate Q s - populationEffect Q) / Real.sqrt (trueVariance Q)
  let R : VarianceEstimator := fun Q s => z * Real.sqrt (V Q s / trueVariance Q)
  let t : ℝ := z * Real.sqrt (a / v)
  have hRatio : ConvergesInProbability P (fun Q s => V Q s / trueVariance Q) (a / v) := by
    have hh := FootnoteThreeProbability.n9_proof FootnoteThreeProbability.n7_proof
      P (fun Q s => (Q.N : ℝ) * V Q s) (fun Q => (Q.N : ℝ) * trueVariance Q)
      a v hV hVar hv
    apply probability_limit_congr P (a / v) _ hh
    intro n s _
    have hN : ((P n).N : ℝ) ≠ 0 := by
      have hh : (4 : ℝ) ≤ (P n).N := by exact_mod_cast (population_sizes (P n)).2.2.2
      linarith
    exact (mul_div_mul_left _ _ hN).symm
  have hR : ConvergesInProbability P R t :=
    T6_continuous_probability P _ _ hRatio (fun x => z * Real.sqrt x)
      (Real.continuous_sqrt.continuousAt.const_mul z)
  have hNegR : ConvergesInProbability P (fun Q s => -R Q s) (-t) :=
    T6_continuous_probability P R t hR (fun x => -x) continuous_neg.continuousAt
  have hUpper := T6_random_cdf P W R t hNormal.2 hR (fun Q s => W Q s ≤ R Q s)
    (fun _ _ h => h.le) (fun _ _ h => h)
  have hLower := T6_random_cdf P W (fun Q s => -R Q s) (-t) hNormal.2 hNegR
    (fun Q s => W Q s < -R Q s) (fun _ _ h => h) (fun _ _ h => h.le)
  have hlim := hUpper.sub hLower
  rw [show normalCDF (-t) = 1 - normalCDF t from
    AronowAudit.P053.NormalCompletion.normal_cdf_neg t] at hlim
  have hmass : ∀ᶠ n in atTop,
      eventProbability (P n) (fun s => W (P n) s ≤ R (P n) s) -
        eventProbability (P n) (fun s => W (P n) s < -R (P n) s) = coverage (P n) V z := by
    filter_upwards [hNormal.1] with n hn
    unfold coverage eventProbability
    rw [← expectation_sub]
    apply expectation_congr
    intro s _
    change ((if W (P n) s ≤ R (P n) s then (1 : ℝ) else 0) -
      (if W (P n) s < -R (P n) s then 1 else 0)) =
      if |pointEstimate (P n) s - populationEffect (P n)| ≤ z * Real.sqrt (V (P n) s) then 1 else 0
    have hr : 0 ≤ R (P n) s := mul_nonneg hz.le (Real.sqrt_nonneg _)
    have hsqrt : 0 < Real.sqrt (trueVariance (P n)) := Real.sqrt_pos.mpr hn
    have hevent : (|pointEstimate (P n) s - populationEffect (P n)| ≤ z * Real.sqrt (V (P n) s)) ↔
        |W (P n) s| ≤ R (P n) s := by
      dsimp only [W, R]
      rw [abs_div, abs_of_pos hsqrt, Real.sqrt_div' _ hn.le]
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hsqrt]
    have hi : (|W (P n) s| ≤ R (P n) s) ↔ (W (P n) s ≤ R (P n) s ∧ ¬ W (P n) s < -R (P n) s) := by
      rw [abs_le]
      constructor
      · intro h
        exact ⟨h.2, not_lt.mpr h.1⟩
      · intro h
        exact ⟨le_of_not_gt h.2, h.1⟩
    simp only [hevent, hi]
    by_cases h2 : W (P n) s < -R (P n) s
    · have h1 : W (P n) s ≤ R (P n) s := by linarith
      simp [h1, h2]
    · by_cases h1 : W (P n) s ≤ R (P n) s <;> simp [h1, h2]
  have hh := hlim.congr' hmass
  have hq : normalCDF t - (1 - normalCDF t) =
      2 * normalCDF (z * Real.sqrt (a / v)) - 1 := by
    dsimp only [t]
    ring
  rw [hq] at hh
  exact hh

theorem ols_ce_may_be_too_small_or_large_proof :
    (∃ (P : ℕ → Population) (a v : ℝ), UnbalancedVarianceLimit P a v ∧ a < v ∧
      StandardizedNormalLimit P ∧ ∀ z : ℝ, 0 < z →
        ∃ q : ℝ, q < 2 * normalCDF z - 1 ∧
          Tendsto (fun r => coverage (P r) olsEstimator z) atTop (𝓝 q) ∧
          Tendsto (fun r => coverage (P r) ceEstimator z) atTop (𝓝 q)) ∧
    (∃ (P : ℕ → Population) (a v : ℝ), UnbalancedVarianceLimit P a v ∧ v < a) := by
  refine ⟨?_, ols_ce_variance_limit_witnesses.2⟩
  have hU : UnbalancedVarianceLimit (footnotePopulation 2) (28 / 3) (49 / 3) := by
    refine ⟨(footnote_population_growth 2).1, (footnote_population_growth 2).2,
      by norm_num, ?_, ?_, ?_⟩
    · convert (footnote_deterministic_limits 2).1 using 1 <;> norm_num
    · convert footnote_ols_probability_limit 2 using 1 <;> norm_num
    · convert footnote_ce_probability_limit 2 using 1 <;> norm_num
  refine ⟨footnotePopulation 2, 28 / 3, 49 / 3, hU, by norm_num, T6_standardized_normal, ?_⟩
  intro z hz
  refine ⟨2 * normalCDF (z * Real.sqrt ((28 / 3 : ℝ) / (49 / 3))) - 1, ?_,
    T6_coverage_limit _ _ _ _ _ T6_standardized_normal hU.2.2.2.1 hU.2.2.1 hU.2.2.2.2.1 hz,
    T6_coverage_limit _ _ _ _ _ T6_standardized_normal hU.2.2.2.1 hU.2.2.1 hU.2.2.2.2.2 hz⟩
  have hs : Real.sqrt ((28 / 3 : ℝ) / (49 / 3)) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    norm_num
  have ht : z * Real.sqrt ((28 / 3 : ℝ) / (49 / 3)) < z := by nlinarith
  have hh := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf ht
  change normalCDF (z * Real.sqrt ((28 / 3 : ℝ) / (49 / 3))) < normalCDF z at hh
  linarith

end
end AronowAudit.P031.Wave1
