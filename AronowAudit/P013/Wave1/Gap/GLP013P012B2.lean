import AronowAudit.P013.Wave1.CorrectedCoverage

set_option autoImplicit false

namespace AronowAudit.P013.Wave1

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Corrected coverage from the finite-design identities and dependency CLT. -/
theorem corrected_wald_coverage_proof (S : ExperimentSequence) (hnested : NestedPopulationSetup S) (hc3 : ComparisonBounded S)
    (hc5 : Condition5Genuine S) (hc6 : Condition6 S) (hL : LowerTailCondition S) :
    ∀ α : ℝ, 0 < α → α < 1 → 1-α ≤ liminf (seqCoverage S α) atTop := by
  exact corrected_wald_coverage_bridge S hnested hc3 hc5 hc6 hL

/-! Local ordered-pair scores for the original expression (11). -/

variable {Ω : Type} [Fintype Ω] {N K : ℕ} {P : Design Ω}

def shrinking_pairValue (F : Population P N K) (i j : Fin N) (d e a b : Fin K) : ℝ :=
  ((if a = d then 1 else 0) * (if b = e then 1 else 0)) *
    ((jointPi F i j d e - pi F i d * pi F j e) / jointPi F i j d e) *
      (F.outcome i d / pi F i d) * (F.outcome j e / pi F j e)

def shrinking_correctionValue (F : Population P N K) (i j : Fin N)
    (d e a b : Fin K) : ℝ :=
  if jointPi F i j d e = 0 then
    (if a = d then 1 else 0) * F.outcome i d ^ 2 / (2 * pi F i d) +
    (if b = e then 1 else 0) * F.outcome j e ^ 2 / (2 * pi F j e) else 0

def shrinking_scoreValue (F : Population P N K) (d e : Fin K)
    (i j : Fin N) (a b : Fin K) : ℝ :=
  if i = j then
    (if a = d then 1 else 0) * (F.outcome i d / pi F i d)^2 +
    (if a = e then 1 else 0) * (F.outcome i e / pi F i e)^2
  else
    shrinking_pairValue F i j d d a b + shrinking_pairValue F i j e e a b -
      2 * shrinking_pairValue F i j d e a b +
    shrinking_correctionValue F i j d d a b + shrinking_correctionValue F i j e e a b +
      2 * shrinking_correctionValue F i j d e a b

def shrinking_score (F : Population P N K) (d e : Fin K)
    (i j : Fin N) (z : Ω) : ℝ :=
  shrinking_scoreValue F d e i j (F.exposure z i) (F.exposure z j)

theorem shrinking_pairValue_eq (F : Population P N K) (i j : Fin N) (d e : Fin K)
    (z : Ω) : shrinking_pairValue F i j d e (F.exposure z i) (F.exposure z j) =
      pairTerm F i j d e z := rfl


theorem shrinking_positive_guard (F : Population P N K) (i j : Fin N) (d e : Fin K)
    (z : Ω) : (if 0 < jointPi F i j d e then pairTerm F i j d e z else 0) =
      pairTerm F i j d e z := by
  split_ifs with hp
  · rfl
  · have hz : jointPi F i j d e = 0 := le_antisymm (le_of_not_gt hp)
      (jointPi_nonneg F i j d e)
    simp [pairTerm, hz]

theorem shrinking_score_sum (F : Population P N K) (d e : Fin K) (hne : d ≠ e)
    (hd : Positivity F d) (he : Positivity F e) (z : Ω) :
    (∑ i, ∑ j, shrinking_score F d e i j z) =
      (varianceHT F d z + correctionA2 F d z + varianceHT F e z + correctionA2 F e z -
        2 * covarianceA F d e z) := by
  classical
  rw [sum_diag_off]
  have hdiag : ∀ i : Fin N,
      shrinking_score F d e i i z =
        indicator F.exposure i d z * (1 - pi F i d) * (F.outcome i d / pi F i d)^2 +
        indicator F.exposure i e z * (1 - pi F i e) * (F.outcome i e / pi F i e)^2 +
        2 * shrinking_correctionValue F i i d e (F.exposure z i) (F.exposure z i) := by
    intro i
    by_cases hid : F.exposure z i = d <;> by_cases hie : F.exposure z i = e <;>
      simp [shrinking_score, shrinking_scoreValue, shrinking_correctionValue, indicator,
        jointPi_cross_self F i d e hne, hid, hie, hne, Ne.symm hne] <;>
      field_simp [ne_of_gt (hd i).1, ne_of_gt (he i).1] <;> ring
  have hoff : ∀ i j : Fin N, j ∈ univ.erase i →
      shrinking_score F d e i j z =
        pairTerm F i j d d z + pairTerm F i j e e z - 2 * pairTerm F i j d e z +
        shrinking_correctionValue F i j d d (F.exposure z i) (F.exposure z j) +
        shrinking_correctionValue F i j e e (F.exposure z i) (F.exposure z j) +
        2 * shrinking_correctionValue F i j d e (F.exposure z i) (F.exposure z j) := by
    intro i j hj
    simp only [shrinking_score, shrinking_scoreValue,
      if_neg (Ne.symm (mem_erase.mp hj).1), shrinking_pairValue_eq]
  simp_rw [hdiag]
  have ho : (∑ i, ∑ j ∈ univ.erase i, shrinking_score F d e i j z) =
      ∑ i, ∑ j ∈ univ.erase i,
        (pairTerm F i j d d z + pairTerm F i j e e z - 2 * pairTerm F i j d e z +
        shrinking_correctionValue F i j d d (F.exposure z i) (F.exposure z j) +
        shrinking_correctionValue F i j e e (F.exposure z i) (F.exposure z j) +
        2 * shrinking_correctionValue F i j d e (F.exposure z i) (F.exposure z j)) := by
    apply sum_congr rfl
    intro i _
    exact sum_congr rfl (fun j hj => hoff i j hj)
  rw [ho]
  unfold varianceHT correctionA2 covarianceA
  simp_rw [shrinking_positive_guard]
  rw [sum_diag_off (fun i j => if jointPi F i j d e = 0 then
    indicator F.exposure i d z * F.outcome i d ^ 2 / (2 * pi F i d) +
    indicator F.exposure j e z * F.outcome j e ^ 2 / (2 * pi F j e) else 0)]
  simp only [shrinking_correctionValue, indicator, sum_add_distrib, sum_sub_distrib,
    ← mul_sum]
  ring

theorem shrinking_scaled_estimate (F : Population P N K) (hN : 0 < N) (d e : Fin K)
    (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e) :
    (fun z => (N : ℝ) * effectVariance F d e z) =
      (fun z => (∑ i, ∑ j, shrinking_score F d e i j z) / (N : ℝ)) := by
  funext z
  rw [shrinking_score_sum F d e hne hd he z]
  unfold effectVariance
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  field_simp
  <;> ring

/-- A common bound for inverse-marginal weighted outcomes. -/
theorem shrinking_weighted_bound (y p C : ℝ) (hC : 1 ≤ C)
    (hy : |y| ≤ C) (hp : |1 / p| ≤ C) : |y / p| ≤ C^2 := by
  calc
    |y / p| = |y| * |1 / p| := by simp [abs_div, div_eq_mul_inv]
    _ ≤ C * C := mul_le_mul hy hp (abs_nonneg _) (by linarith)
    _ = C^2 := by ring

theorem shrinking_half_bound (y p C : ℝ) (hp : 0 < p) (hC : 1 ≤ C)
    (hy : |y| ≤ C) (hi : |1 / p| ≤ C) : |y^2 / (2*p)| ≤ C^4 := by
  have hw := shrinking_weighted_bound y p C hC hy hi
  have hc : 0 ≤ C := by linarith
  have hform : y^2 / (2*p) = y * (y/p) / 2 := by field_simp <;> ring
  have hprod : |y * (y/p)| ≤ C^3 := by
    rw [abs_mul]
    calc
      _ ≤ C * C^2 := mul_le_mul hy hw (abs_nonneg _) hc
      _ = _ := by ring
  have hpow : C^3 ≤ C^4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (pow_nonneg hc 3)]
  rw [hform, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith [pow_nonneg hc 4]

theorem shrinking_correction_bound (F : Population P N K) (i j : Fin N) (d e a b : Fin K)
    (hd : Positivity F d) (he : Positivity F e) (C : ℝ) (hC : 1 ≤ C)
    (hy : |F.outcome i d| ≤ C) (hz : |F.outcome j e| ≤ C)
    (hi : |1 / pi F i d| ≤ C) (hj : |1 / pi F j e| ≤ C) :
    |shrinking_correctionValue F i j d e a b| ≤ 2*C^4 := by
  have hc : 0 ≤ C^4 := pow_nonneg (by linarith) _
  have h₁ : |(if a = d then 1 else 0) * F.outcome i d^2 / (2*pi F i d)| ≤ C^4 := by
    by_cases ha : a = d
    · simpa [ha] using shrinking_half_bound _ _ C (hd i).1 hC hy hi
    · simp [ha, hc]
  have h₂ : |(if b = e then 1 else 0) * F.outcome j e^2 / (2*pi F j e)| ≤ C^4 := by
    by_cases hb : b = e
    · simpa [hb] using shrinking_half_bound _ _ C (he j).1 hC hz hj
    · simp [hb, hc]
  by_cases hz' : jointPi F i j d e = 0
  · rw [shrinking_correctionValue, if_pos hz']
    exact (abs_add_le _ _).trans (by linarith only [h₁, h₂])
  · simp only [shrinking_correctionValue, if_neg hz', abs_zero]
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc

theorem shrinking_pair_moment (F : Population P N K) (i j : Fin N) (d e : Fin K)
    (C β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
    (hlow : 0 < jointPi F i j d e → β ≤ jointPi F i j d e)
    (hy : |F.outcome i d| ≤ C) (hz : |F.outcome j e| ≤ C)
    (hi : |1 / pi F i d| ≤ C) (hj : |1 / pi F j e| ≤ C) :
    expectation P (fun z => (pairTerm F i j d e z)^2) ≤ 4*C^8/β := by
  by_cases hp : 0 < jointPi F i j d e
  · have hh := pairTerm_second_moment_bound F i j d e (C^2) (sq_nonneg _) hp
      (shrinking_weighted_bound _ _ C hC hy hi)
      (shrinking_weighted_bound _ _ C hC hz hj)
    have hh' : expectation P (fun z => (pairTerm F i j d e z)^2) ≤
        4*C^8 / jointPi F i j d e := by convert hh using 1 <;> ring
    exact hh'.trans (div_le_div_of_nonneg_left (by positivity) hβ (hlow hp))
  · have hz : jointPi F i j d e = 0 := le_antisymm (le_of_not_gt hp)
      (jointPi_nonneg F i j d e)
    simp only [pairTerm, hz, div_zero, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0),
      expectation_const]
    positivity

theorem shrinking_six_square (a b c d e f : ℝ) :
    (a+b-2*c+d+e+2*f)^2 ≤ 6*(a^2+b^2+4*c^2+d^2+e^2+4*f^2) := by
  have hh := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 6)))
    (f := ![a,b,-2*c,d,e,2*f])
  norm_num [Fin.sum_univ_succ] at hh
  nlinarith only [hh]

/-- A loose common second-moment constant suffices for both existential rate statements. -/
theorem shrinking_score_moment (F : Population P N K) (d e : Fin K)
    (hd : Positivity F d) (he : Positivity F e)
    (C β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hb : ∀ i, |F.outcome i d| ≤ C ∧ |F.outcome i e| ≤ C ∧
      |1 / pi F i d| ≤ C ∧ |1 / pi F i e| ≤ C)
    (hlow : ∀ i j, i ≠ j →
      (0 < jointPi F i j d d → β ≤ jointPi F i j d d) ∧
      (0 < jointPi F i j e e → β ≤ jointPi F i j e e) ∧
      (0 < jointPi F i j d e → β ≤ jointPi F i j d e)) (i j : Fin N) :
    expectation P (fun z => (shrinking_score F d e i j z)^2) ≤ 288*C^8/β := by
  have hc : 0 ≤ C := by linarith
  have hpow : 0 ≤ C^8 := pow_nonneg hc _
  have hdiv : C^8 ≤ C^8/β := (le_div_iff₀ hβ).2 (by nlinarith)
  have hcorr (a b : Fin K) (ha : Positivity F a) (hb' : Positivity F b)
      (hya : |F.outcome i a| ≤ C) (hyb : |F.outcome j b| ≤ C)
      (hia : |1 / pi F i a| ≤ C) (hib : |1 / pi F j b| ≤ C) :
      expectation P (fun z =>
        (shrinking_correctionValue F i j a b (F.exposure z i) (F.exposure z j))^2) ≤
        4*C^8/β := by
    calc
      _ ≤ expectation P (fun _ => 4*C^8) := expectation_mono P (fun z => by
        have hh := shrinking_correction_bound F i j a b (F.exposure z i) (F.exposure z j)
          ha hb' C hC hya hyb hia hib
        have hs := pow_le_pow_left₀ (abs_nonneg _) hh 2
        nlinarith only [hs, sq_abs (shrinking_correctionValue F i j a b (F.exposure z i) (F.exposure z j))])
      _ = 4*C^8 := expectation_const _ _
      _ ≤ 4*C^8/β := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiv (by norm_num : (0:ℝ) ≤ 4)
  by_cases hij : i = j
  · subst j
    have hpoint (z : Ω) : |shrinking_score F d e i i z| ≤ 2*C^4 := by
      have hwd := shrinking_weighted_bound _ _ C hC (hb i).1 (hb i).2.2.1
      have hwe := shrinking_weighted_bound _ _ C hC (hb i).2.1 (hb i).2.2.2
      have hd2 : (F.outcome i d / pi F i d)^2 ≤ C^4 := by
        nlinarith [pow_le_pow_left₀ (abs_nonneg _) hwd 2, sq_abs (F.outcome i d / pi F i d)]
      have he2 : (F.outcome i e / pi F i e)^2 ≤ C^4 := by
        nlinarith [pow_le_pow_left₀ (abs_nonneg _) hwe 2, sq_abs (F.outcome i e / pi F i e)]
      rw [shrinking_score, shrinking_scoreValue, if_pos rfl]
      have h₁ : |(if F.exposure z i = d then 1 else 0) * (F.outcome i d / pi F i d)^2| ≤ C^4 := by
        by_cases ha : F.exposure z i = d
        · simpa [ha, abs_of_nonneg (sq_nonneg (F.outcome i d / pi F i d))] using hd2
        · simp [ha, pow_nonneg hc 4]
      have h₂ : |(if F.exposure z i = e then 1 else 0) * (F.outcome i e / pi F i e)^2| ≤ C^4 := by
        by_cases ha : F.exposure z i = e
        · simpa [ha, abs_of_nonneg (sq_nonneg (F.outcome i e / pi F i e))] using he2
        · simp [ha, pow_nonneg hc 4]
      exact (abs_add_le _ _).trans (by linarith only [h₁, h₂])
    calc
      _ ≤ expectation P (fun _ => 4*C^8) := expectation_mono P (fun z => by
        have hs := pow_le_pow_left₀ (abs_nonneg _) (hpoint z) 2
        nlinarith only [hs, sq_abs (shrinking_score F d e i i z)])
      _ = 4*C^8 := expectation_const _ _
      _ ≤ 288*C^8/β := by
        have h₁ : 4*C^8 ≤ 4*C^8/β := by
          simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiv (by norm_num : (0:ℝ) ≤ 4)
        exact h₁.trans (div_le_div_of_nonneg_right (by nlinarith) hβ.le)
  · have hpdd := shrinking_pair_moment F i j d d C β hC hβ (hlow i j hij).1
      (hb i).1 (hb j).1 (hb i).2.2.1 (hb j).2.2.1
    have hpee := shrinking_pair_moment F i j e e C β hC hβ (hlow i j hij).2.1
      (hb i).2.1 (hb j).2.1 (hb i).2.2.2 (hb j).2.2.2
    have hpde := shrinking_pair_moment F i j d e C β hC hβ (hlow i j hij).2.2
      (hb i).1 (hb j).2.1 (hb i).2.2.1 (hb j).2.2.2
    have hcdd := hcorr d d hd hd (hb i).1 (hb j).1 (hb i).2.2.1 (hb j).2.2.1
    have hcee := hcorr e e he he (hb i).2.1 (hb j).2.1 (hb i).2.2.2 (hb j).2.2.2
    have hcde := hcorr d e hd he (hb i).1 (hb j).2.1 (hb i).2.2.1 (hb j).2.2.2
    have hs := expectation_mono P (fun z => shrinking_six_square
      (pairTerm F i j d d z) (pairTerm F i j e e z) (pairTerm F i j d e z)
      (shrinking_correctionValue F i j d d (F.exposure z i) (F.exposure z j))
      (shrinking_correctionValue F i j e e (F.exposure z i) (F.exposure z j))
      (shrinking_correctionValue F i j d e (F.exposure z i) (F.exposure z j)))
    simp only [expectation_const_mul, expectation_add] at hs
    simp only [shrinking_score, shrinking_scoreValue, if_neg hij, shrinking_pairValue_eq]
    simp only [div_eq_mul_inv] at hpdd hpee hpde hcdd hcee hcde ⊢
    nlinarith only [hs, hpdd, hpee, hpde, hcdd, hcee, hcde]

/-- Off the closed graph all three joint coefficients and all corrections vanish. -/
theorem shrinking_score_zero (F : Population P N K) (d e : Fin K)
    (hd : Positivity F d) (he : Positivity F e) (h : Fin N → Fin N → Bool)
    (hs : ∀ i j, h i j = h j i) (hg : GenuineDependency P F.exposure h)
    (i j : Fin N) (hne : i ≠ j) (hij : h i j = false) (z : Ω) :
    shrinking_score F d e i j z = 0 := by
  have hp := genuine_implies_pair_independent F h hg i j hne hij (by rw [← hs]; exact hij)
  have hdd := hp d d
  have hee := hp e e
  have hde := hp d e
  have hdd0 := ne_of_gt (mul_pos (hd i).1 (hd j).1)
  have hee0 := ne_of_gt (mul_pos (he i).1 (he j).1)
  have hde0 := ne_of_gt (mul_pos (hd i).1 (he j).1)
  simp [shrinking_score, shrinking_scoreValue, hne, shrinking_pairValue,
    shrinking_correctionValue, hdd, hee, hde, hdd0, hee0, hde0]

/-- Full-vector independence transfers to any two endpoint scores. -/
theorem shrinking_covariance_zero (F : Population P N K) (d e : Fin K)
    (h : Fin N → Fin N → Bool) (hs : ∀ i j, h i j = h j i)
    (hg : GenuineDependency P F.exposure h) (i j k l : Fin N)
    (hsep : ∀ a ∈ ({i,j} : Finset (Fin N)), ∀ b ∈ ({k,l} : Finset (Fin N)),
      a ≠ b ∧ h a b = false) :
    covariance P (shrinking_score F d e i j) (shrinking_score F d e k l) = 0 := by
  classical
  let instMeasurableGLP013P012B2 : MeasurableSpace Ω := ⊤
  let A : Finset (Fin N) := {i,j}
  let B : Finset (Fin N) := {k,l}
  have hdisj : Disjoint A B := disjoint_left.mpr (by
    intro a ha hb
    exact (hsep a ha a hb).1 rfl)
  have hno : CorrectedNoEdge h A B :=
    (corrected_symmetric_equivalence h hs A B).2 (fun a ha b hb => (hsep a ha b hb).2)
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le d.val) d.isLt
  have hv := CorrectedCoverage.n2_proof hK P F.exposure A B (hg A B hdisj hno)
  let φ : (A → Fin K) → ℝ := fun v =>
    shrinking_scoreValue F d e i j (v ⟨i, by simp [A]⟩) (v ⟨j, by simp [A]⟩)
  let ψ : (B → Fin K) → ℝ := fun v =>
    shrinking_scoreValue F d e k l (v ⟨k, by simp [B]⟩) (v ⟨l, by simp [B]⟩)
  have hind := hv.comp (measurable_of_finite φ) (measurable_of_finite ψ)
  change ProbabilityTheory.IndepFun (shrinking_score F d e i j)
    (shrinking_score F d e k l) (designMeasure P) at hind
  have hh := hind.integral_fun_mul_eq_mul_integral
    (measurable_of_finite _).aestronglyMeasurable (measurable_of_finite _).aestronglyMeasurable
  simp only [integral_designMeasure] at hh
  exact sub_eq_zero.mpr hh

theorem shrinking_covariance_bound (X Y : Ω → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hx : expectation P (fun z => (X z)^2) ≤ A)
    (hy : expectation P (fun z => (Y z)^2) ≤ A) : |covariance P X Y| ≤ A := by
  have hv (Z : Ω → ℝ) (hz : expectation P (fun z => (Z z)^2) ≤ A) : variance P Z ≤ A := by
    unfold variance covariance
    simp only [← pow_two]
    nlinarith only [hz, sq_nonneg (expectation P Z)]
  calc
    _ ≤ Real.sqrt (variance P X * variance P Y) := covariance_abs_bound P X Y
    _ ≤ Real.sqrt (A^2) := Real.sqrt_le_sqrt (by
      simpa only [pow_two] using mul_le_mul (hv X hx) (hv Y hy) (variance_nonneg P Y) hA)
    _ = A := Real.sqrt_sq hA

theorem shrinking_cov_sum_left {I : Type*} [Fintype I]
    (X : I → Ω → ℝ) (Y : Ω → ℝ) :
    covariance P (fun z => ∑ i, X i z) Y = ∑ i, covariance P (X i) Y := by
  unfold covariance
  simp only [sum_mul, expectation_sum, sum_sub_distrib]

theorem shrinking_cov_sum_right {I : Type*} [Fintype I]
    (X : Ω → ℝ) (Y : I → Ω → ℝ) :
    covariance P X (fun z => ∑ i, Y i z) = ∑ i, covariance P X (Y i) := by
  rw [covariance_symm, shrinking_cov_sum_left]
  exact sum_congr rfl (fun i _ => covariance_symm P (Y i) X)

/-- The reflexive graph has row degree at most one plus the original row bound. -/
theorem shrinking_closed_row_nat (h : Fin N → Fin N → Bool) (m : ℕ) (hr : RowBound h m)
    (i : Fin N) : (∑ j, if i = j ∨ h i j = true then 1 else 0 : ℕ) ≤ m+1 := by
  classical
  calc
    _ ≤ ∑ j, ((if h i j = true then 1 else 0) + (if i = j then 1 else 0) : ℕ) := by
      apply sum_le_sum
      intro j _
      by_cases hij : h i j = true <;> by_cases heq : i = j <;> simp [hij, heq]
    _ = (∑ j, if h i j = true then 1 else 0 : ℕ) + 1 := by simp [sum_add_distrib]
    _ ≤ m+1 := Nat.add_le_add_right (hr i) 1

/-- A weighted count of two-step walks. -/
theorem shrinking_weighted_rows {I : Type*} [Fintype I]
    (a : I → I → ℝ) (w : I → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ i j, 0 ≤ a i j) (hw : ∀ i, 0 ≤ w i)
    (hr : ∀ i, ∑ j, a i j ≤ M) (hs : ∑ i, w i ≤ M) :
    (∑ i, ∑ j, a i j * w i) ≤ M^2 := by
  calc
    _ = ∑ i, w i * ∑ j, a i j := by
      apply sum_congr rfl
      intro i _
      rw [← sum_mul]
      ring
    _ ≤ ∑ i, w i * M := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hr i) (hw i))
    _ = (∑ i, w i) * M := (sum_mul _ _ _).symm
    _ ≤ M * M := mul_le_mul_of_nonneg_right hs hM
    _ = M^2 := by ring

/-- Ordered-pair covariance counting, including pairs with a shared endpoint. -/
theorem shrinking_graph_variance_bound {I : Type*} [Fintype I]
    (B : I → I → Ω → ℝ) (G : I → I → Prop) [DecidableRel G] (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hsym : ∀ i j, G i j ↔ G j i)
    (hrow : ∀ i, (∑ j, if G i j then 1 else 0 : ℝ) ≤ M)
    (hzero : ∀ i j, ¬ G i j → ∀ z, B i j z = 0)
    (hcov : ∀ i j k l, |covariance P (B i j) (B k l)| ≤ A)
    (hsep : ∀ i j k l, ¬ G i k → ¬ G i l → ¬ G j k → ¬ G j l →
      covariance P (B i j) (B k l) = 0) :
    variance P (fun z => ∑ i, ∑ j, B i j z) ≤
      4*A*(Fintype.card I : ℝ)*M^3 := by
  classical
  let a : I → I → ℝ := fun i j => if G i j then 1 else 0
  have ha : ∀ i j, 0 ≤ a i j := by intros; dsimp [a]; split_ifs <;> norm_num
  have has : ∀ i j, a i j = a j i := by
    intro i j
    simp only [a, hsym i j]
  have hr : ∀ i, ∑ j, a i j ≤ M := hrow
  have hcol : ∀ j, ∑ i, a i j ≤ M := by
    intro j
    calc
      _ = ∑ i, a j i := sum_congr rfl (fun i _ => has i j)
      _ ≤ M := hr j
  have hwalk (i : I) : (∑ k, ∑ l, a k l * a i k) ≤ M^2 :=
    shrinking_weighted_rows a (a i) M hM ha (ha i) hr (hr i)
  have hwalk' (i : I) : (∑ k, ∑ l, a k l * a i l) ≤ M^2 := by
    rw [sum_comm]
    exact shrinking_weighted_rows (fun k l => a l k) (a i) M hM
      (fun k l => ha l k) (ha i) hcol (hr i)
  have hcount (i j : I) :
      (∑ k, ∑ l, a k l * (a i k + a i l + a j k + a j l)) ≤ 4*M^2 := by
    simp only [mul_add, sum_add_distrib]
    linarith only [hwalk i, hwalk' i, hwalk j, hwalk' j]
  have hpoint (i j k l : I) : covariance P (B i j) (B k l) ≤
      A * (a k l * (a i k + a i l + a j k + a j l)) := by
    by_cases hkl : G k l
    · have hakl : a k l = 1 := by simp [a, hkl]
      rw [hakl, one_mul]
      by_cases hc : G i k ∨ G i l ∨ G j k ∨ G j l
      · have hsum : 1 ≤ a i k + a i l + a j k + a j l := by
          rcases hc with hh | hh | hh | hh
          · have : a i k = 1 := by simp [a, hh]
            linarith [ha i l, ha j k, ha j l]
          · have : a i l = 1 := by simp [a, hh]
            linarith [ha i k, ha j k, ha j l]
          · have : a j k = 1 := by simp [a, hh]
            linarith [ha i k, ha i l, ha j l]
          · have : a j l = 1 := by simp [a, hh]
            linarith [ha i k, ha i l, ha j k]
        exact ((le_abs_self _).trans (hcov i j k l)).trans
          (by nlinarith [mul_nonneg hA (sub_nonneg.mpr hsum)])
      · have hz := hsep i j k l (fun hh => hc (Or.inl hh))
          (fun hh => hc (Or.inr (Or.inl hh)))
          (fun hh => hc (Or.inr (Or.inr (Or.inl hh))))
          (fun hh => hc (Or.inr (Or.inr (Or.inr hh))))
        rw [hz]
        exact mul_nonneg hA (by positivity)
    · have hb : B k l = fun _ => 0 := funext (hzero k l hkl)
      rw [hb]
      simp [covariance, expectation_const, a, hkl]
  have hrows (i j : I) : (∑ k, ∑ l, covariance P (B i j) (B k l)) ≤
      a i j * (4*A*M^2) := by
    by_cases hij : G i j
    · have haij : a i j = 1 := by simp [a, hij]
      rw [haij, one_mul]
      calc
        _ ≤ ∑ k, ∑ l, A * (a k l * (a i k + a i l + a j k + a j l)) :=
          sum_le_sum (fun k _ => sum_le_sum (fun l _ => hpoint i j k l))
        _ = A * (∑ k, ∑ l, a k l * (a i k + a i l + a j k + a j l)) := by
          simp only [mul_sum]
        _ ≤ A * (4*M^2) := mul_le_mul_of_nonneg_left (hcount i j) hA
        _ = 4*A*M^2 := by ring
    · have hb : B i j = fun _ => 0 := funext (hzero i j hij)
      rw [hb]
      simp [covariance, expectation_const, a, hij]
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l, covariance P (B i j) (B k l) := by
      simp only [variance, shrinking_cov_sum_left, shrinking_cov_sum_right]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro l _
      exact covariance_symm P (B k l) (B i j)
    _ ≤ ∑ i, ∑ j, a i j * (4*A*M^2) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hrows i j))
    _ ≤ ∑ _i : I, M * (4*A*M^2) := by
      apply sum_le_sum
      intro i _
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (hr i) (by positivity)
    _ = 4*A*(Fintype.card I : ℝ)*M^3 := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      ring

/-- The common finite inequality costs only one inverse positive joint. -/
theorem shrinking_finite_variance_bound (F : Population P N K) (hN : 0 < N)
    (d e : Fin K) (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e)
    (h : Fin N → Fin N → Bool) (hs : ∀ i j, h i j = h j i)
    (hg : GenuineDependency P F.exposure h) (m : ℕ) (hr : RowBound h m)
    (C β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hb : ∀ i, |F.outcome i d| ≤ C ∧ |F.outcome i e| ≤ C ∧
      |1 / pi F i d| ≤ C ∧ |1 / pi F i e| ≤ C)
    (hlow : ∀ i j, i ≠ j →
      (0 < jointPi F i j d d → β ≤ jointPi F i j d d) ∧
      (0 < jointPi F i j e e → β ≤ jointPi F i j e e) ∧
      (0 < jointPi F i j d e → β ≤ jointPi F i j d e)) :
    variance P (fun z => (N : ℝ)*effectVariance F d e z) ≤
      1152*C^8*(m+1 : ℝ)^3 / ((N : ℝ)*β) := by
  classical
  let G : Fin N → Fin N → Prop := fun i j => i = j ∨ h i j = true
  have hsymm : ∀ i j, G i j ↔ G j i := by
    intro i j
    simp only [G, hs i j, eq_comm]
  have hrow : ∀ i, (∑ j, if G i j then 1 else 0 : ℝ) ≤ (m+1 : ℝ) := by
    intro i
    have hn := shrinking_closed_row_nat h m hr i
    exact_mod_cast hn
  have hzero : ∀ i j, ¬ G i j → ∀ z, shrinking_score F d e i j z = 0 := by
    intro i j hij z
    have hij' : i ≠ j := fun heq => hij (Or.inl heq)
    have hfalse : h i j = false := by
      cases hx : h i j
      · rfl
      · exact False.elim (hij (Or.inr hx))
    exact shrinking_score_zero F d e hd he h hs hg i j hij' hfalse z
  have hsep : ∀ i j k l, ¬ G i k → ¬ G i l → ¬ G j k → ¬ G j l →
      covariance P (shrinking_score F d e i j) (shrinking_score F d e k l) = 0 := by
    intro i j k l hik hil hjk hjl
    apply shrinking_covariance_zero F d e h hs hg i j k l
    intro a ha b hb'
    have hh : ¬ G a b := by
      simp only [mem_insert, mem_singleton] at ha hb'
      rcases ha with rfl | rfl <;> rcases hb' with rfl | rfl <;> assumption
    constructor
    · exact fun heq => hh (Or.inl heq)
    · cases hx : h a b
      · rfl
      · exact False.elim (hh (Or.inr hx))
  have hmoment := shrinking_score_moment F d e hd he C β hC hβ hβ1 hb hlow
  have hbound := shrinking_graph_variance_bound (shrinking_score F d e) G
    (m+1 : ℝ) (288*C^8/β) (by positivity) (by positivity) hsymm hrow hzero
    (fun i j k l => shrinking_covariance_bound _ _ _ (by positivity)
      (hmoment i j) (hmoment k l)) hsep
  rw [shrinking_scaled_estimate F hN d e hne hd he, variance_div]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  calc
    _ ≤ (4*(288*C^8/β)*(N : ℝ)*(m+1 : ℝ)^3) / (N : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [Fintype.card_fin] using hbound
    _ = 1152*C^8*(m+1 : ℝ)^3 / ((N : ℝ)*β) := by
      field_simp
      <;> ring

/-- Bounded degree itself supplies a positive distinct-unit joint on a tail. -/
theorem shrinking_eventual_domain (S : ExperimentSequence) (hc5 : Condition5Genuine S) :
    ∀ᶠ n in atTop, PositiveJointDomain S n := by
  classical
  obtain ⟨m,h,hh⟩ := hc5
  filter_upwards [eventually_ge_atTop (m+1)] with n hn
  by_contra hnone
  have hall (j : Fin (n+1)) : (0 : Fin (n+1)) = j ∨ h n 0 j = true := by
    by_contra hj
    have hne : (0 : Fin (n+1)) ≠ j := fun heq => hj (Or.inl heq)
    have hfalse : h n 0 j = false := by
      cases hx : h n 0 j
      · rfl
      · exact False.elim (hj (Or.inr hx))
    have hp := genuine_implies_pair_independent (seqPopulation S n) (h n) (hh n).2.1
      0 j hne hfalse (by rw [← (hh n).1]; exact hfalse)
    have hpos : 0 < jointPi (seqPopulation S n) 0 j (S.treated n) (S.treated n) := by
      rw [hp]
      exact mul_pos (S.positiveTreated n 0).1 (S.positiveTreated n j).1
    exact hnone ⟨0,j,hne,Or.inl hpos⟩
  have hr := shrinking_closed_row_nat (h n) m (hh n).2.2 0
  simp only [if_pos (hall _), sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hr
  omega

/-- An attained minimum is a legitimate lower bound, and is at most one. -/
theorem shrinking_minimum_bounds (S : ExperimentSequence) (n : ℕ) (b : ℝ)
    (hb : IsMinimumPositiveJoint S n b) :
    0 < b ∧ b ≤ 1 ∧ ∀ i j, i ≠ j →
      (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.treated n) →
        b ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.treated n)) ∧
      (0 < jointPi (seqPopulation S n) i j (S.control n) (S.control n) →
        b ≤ jointPi (seqPopulation S n) i j (S.control n) (S.control n)) ∧
      (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.control n) →
        b ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.control n)) := by
  refine ⟨hb.1, ?_, hb.2.2⟩
  obtain ⟨i,j,_,hij⟩ := hb.2.1
  rcases hij with hij | hij | hij
  all_goals rw [hij]; exact (jointPi_bounds _ _ _ _ _).2

/-- Squeeze the nonnegative variances by a rate with a diverging denominator. -/
theorem shrinking_rate_lower_tail (S : ExperimentSequence) (a : ℕ → ℝ) (C : ℝ)
    (hr : ∀ᶠ n in atTop, variance (seqLaw S n)
      (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ C/a n)
    (ha : Tendsto a atTop atTop) : LowerTailCondition S := by
  apply vanishing_variance_implies_lower_tail
  have ht : Tendsto (fun n => C/a n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp ha) :
        Tendsto (fun n => C*(a n)⁻¹) atTop (𝓝 (C*0)))
  exact squeeze_zero' (Eventually.of_forall (fun n => variance_nonneg _ _)) hr ht

/-- The attained shrinking minimum gives the variance rate and then (L). -/
theorem shrinking_joints_variance_rate_proof (S : ExperimentSequence) (hnested : NestedPopulationSetup S) (hc3 : ComparisonBounded S)
    (hc5 : Condition5Genuine S) (b : ℕ → ℝ)
    (hmin : ∀ n, PositiveJointDomain S n → IsMinimumPositiveJoint S n (b n)) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      variance (seqLaw S n) (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ C/((n+1 : ℝ)*b n)) ∧
    (Tendsto (fun n : ℕ => (n+1 : ℝ)*b n) atTop atTop → LowerTailCondition S) := by
  obtain ⟨c1,c2,hc1,hc2,hb⟩ := hc3
  obtain ⟨m,h,hh⟩ := hc5
  let A : ℝ := max 1 (max c1 c2)
  have hA : 1 ≤ A := le_max_left _ _
  have hc1A : c1 ≤ A := (le_max_left c1 c2).trans (le_max_right _ _)
  have hc2A : c2 ≤ A := (le_max_right c1 c2).trans (le_max_right _ _)
  have hbA : ∀ n i, |(seqPopulation S n).outcome i (S.treated n)| ≤ A ∧
      |(seqPopulation S n).outcome i (S.control n)| ≤ A ∧
      |1 / pi (seqPopulation S n) i (S.treated n)| ≤ A ∧
      |1 / pi (seqPopulation S n) i (S.control n)| ≤ A := by
    intro n i
    exact ⟨(hb n i).1.trans hc1A, (hb n i).2.1.trans hc1A,
      (hb n i).2.2.1.trans hc2A, (hb n i).2.2.2.trans hc2A⟩
  let C : ℝ := 1152*A^8*(m+1 : ℝ)^3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdom := shrinking_eventual_domain S ⟨m,h,hh⟩
  have hr : ∀ᶠ n in atTop, variance (seqLaw S n)
      (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ C/((n+1 : ℝ)*b n) := by
    filter_upwards [hdom] with n hn
    have hmin' := shrinking_minimum_bounds S n (b n) (hmin n hn)
    have hfinite := shrinking_finite_variance_bound (seqPopulation S n) (Nat.succ_pos n)
      (S.treated n) (S.control n) (S.distinct n) (S.positiveTreated n) (S.positiveControl n)
      (h n) (hh n).1 (hh n).2.1 m (hh n).2.2 A (b n) hA hmin'.1 hmin'.2.1
      (hbA n) hmin'.2.2
    simpa only [C, Nat.cast_add, Nat.cast_one] using hfinite
  exact ⟨⟨C,hC,hr⟩, fun ht => shrinking_rate_lower_tail S
    (fun n => (n+1 : ℝ)*b n) C hr ht⟩

/-- A fixed positive joint bound is the constant-denominator specialization. -/
theorem uniform_joints_variance_rate_proof (S : ExperimentSequence) (hnested : NestedPopulationSetup S) (hc3 : ComparisonBounded S)
    (hc5 : Condition5Genuine S) (b : ℝ) (hb : 0 < b) (hj : JointLowerBound S b) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      variance (seqLaw S n) (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ C/(n+1 : ℝ)) ∧
      LowerTailCondition S := by
  obtain ⟨c1,c2,hc1,hc2,hbounds⟩ := hc3
  obtain ⟨m,h,hh⟩ := hc5
  let A : ℝ := max 1 (max c1 c2)
  have hA : 1 ≤ A := le_max_left _ _
  have hc1A : c1 ≤ A := (le_max_left c1 c2).trans (le_max_right _ _)
  have hc2A : c2 ≤ A := (le_max_right c1 c2).trans (le_max_right _ _)
  have hbA : ∀ n i, |(seqPopulation S n).outcome i (S.treated n)| ≤ A ∧
      |(seqPopulation S n).outcome i (S.control n)| ≤ A ∧
      |1 / pi (seqPopulation S n) i (S.treated n)| ≤ A ∧
      |1 / pi (seqPopulation S n) i (S.control n)| ≤ A := by
    intro n i
    exact ⟨(hbounds n i).1.trans hc1A, (hbounds n i).2.1.trans hc1A,
      (hbounds n i).2.2.1.trans hc2A, (hbounds n i).2.2.2.trans hc2A⟩
  let β : ℝ := min b 1
  have hβ : 0 < β := lt_min hb zero_lt_one
  have hβ1 : β ≤ 1 := min_le_right _ _
  have hpos (p : ℝ) (hp : p = 0 ∨ b ≤ p) : 0 < p → β ≤ p := by
    intro hp0
    rcases hp with hp | hp
    · exact False.elim ((ne_of_gt hp0) hp)
    · exact (min_le_left _ _).trans hp
  have hlow : ∀ n i j, i ≠ j →
      (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.treated n) →
        β ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.treated n)) ∧
      (0 < jointPi (seqPopulation S n) i j (S.control n) (S.control n) →
        β ≤ jointPi (seqPopulation S n) i j (S.control n) (S.control n)) ∧
      (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.control n) →
        β ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.control n)) := by
    intro n i j hij
    exact ⟨hpos _ (hj n i j hij).1, hpos _ (hj n i j hij).2.1,
      hpos _ (hj n i j hij).2.2⟩
  let C : ℝ := (1152*A^8*(m+1 : ℝ)^3)/β
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hr : ∀ n, variance (seqLaw S n)
      (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ C/(n+1 : ℝ) := by
    intro n
    have hfinite := shrinking_finite_variance_bound (seqPopulation S n) (Nat.succ_pos n)
      (S.treated n) (S.control n) (S.distinct n) (S.positiveTreated n) (S.positiveControl n)
      (h n) (hh n).1 (hh n).2.1 m (hh n).2.2 A β hA hβ hβ1 (hbA n) (hlow n)
    have hfinite' : variance (seqLaw S n)
        (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤
        1152*A^8*(m+1 : ℝ)^3/((n+1 : ℝ)*β) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hfinite
    calc
      _ ≤ 1152*A^8*(m+1 : ℝ)^3/((n+1 : ℝ)*β) := hfinite'
      _ = C/(n+1 : ℝ) := by
        dsimp [C]
        rw [div_div, mul_comm β]
  refine ⟨⟨C,hC,Eventually.of_forall hr⟩, ?_⟩
  apply shrinking_rate_lower_tail S (fun n => (n+1 : ℝ)) C (Eventually.of_forall hr)
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

end

end AronowAudit.P013.Wave1
