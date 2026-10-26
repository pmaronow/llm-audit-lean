import AronowAudit.P033.P033_Audit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Finset.Powerset

namespace AronowAudit.P033.Wave1

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section

/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng (the adapted tail lemmas below).

The finite Pascal recursion and tail monotonicity below are adapted from
Daniel Lyng, module `Econlib.Probability.Distributions.Binomial.Tail.Basic`,
commit d7bd9477476cade1c6695c8891746048ceddc52f (Apache-2.0, 2026).
Only the elementary finite-sum lemmas are copied; no Econlib dependency is used.
See NOTICE at the repository root.
-/
def P033T8_tail (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.filter (fun i => k ≤ i) (Finset.range (n + 1)),
    (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

/-- The tail probability at threshold 0 equals 1, i.e., `Pr(Bin(n, p) ≥ 0) = 1`. -/
@[simp] lemma P033T8_tail_zero (n : ℕ) (p : ℝ) :
    P033T8_tail n p 0 = 1 := by
  simp only [P033T8_tail, Nat.zero_le, Finset.filter_true_of_mem (fun _ _ => trivial)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using (add_pow p (1 - p) n).symm

/-- The tail probability is 0 when the threshold `k` exceeds `n`. -/
lemma P033T8_tail_large (n : ℕ) (p : ℝ) (k : ℕ) (hk : n < k) :
    P033T8_tail n p k = 0 := by
  simp only [P033T8_tail]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  omega
private lemma P033T8_tail_term_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n i : ℕ) :
    0 ≤ (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _)) (pow_nonneg (by linarith) _)
lemma P033T8_tail_anti_k {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) {k₁ k₂ : ℕ}
    (hk : k₁ ≤ k₂) :
    P033T8_tail n p k₂ ≤ P033T8_tail n p k₁ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i; simp [Finset.mem_filter, Finset.mem_range]; omega
  · intro i _ _; exact P033T8_tail_term_nonneg hp hp1 n i

/-- Pascal recursion for the upper binomial tail:
`Pr(Bin(n+1, p) ≥ k+1) = (1-p) · Pr(Bin(n, p) ≥ k+1) + p · Pr(Bin(n, p) ≥ k)`. -/
lemma P033T8_tail_succ_succ (n : ℕ) (p : ℝ) (k : ℕ) :
    P033T8_tail (n + 1) p (k + 1) =
      (1 - p) * P033T8_tail n p (k + 1) + p * P033T8_tail n p k := by
  have to_ite : ∀ m q j, P033T8_tail m q j =
      ∑ i ∈ Finset.range (m + 1),
        (if j ≤ i then (m.choose i : ℝ) * q ^ i * (1 - q) ^ (m - i) else 0) := by
    intro m q j; simp only [P033T8_tail, Finset.sum_filter]
  rw [to_ite (n + 1) p (k + 1), to_ite n p (k + 1), to_ite n p k]
  -- Apply Pascal's identity via sum_choose_succ_mul, then factor out p and (1-p) from each half.
  have hsplit := Finset.sum_choose_succ_mul (R := ℝ)
    (f := fun i j => if k + 1 ≤ i then p ^ i * (1 - p) ^ j else 0) n
  have hLHS_eq : ∑ i ∈ Finset.range (n + 1 + 1),
      (if k + 1 ≤ i then ((n + 1).choose i : ℝ) * p ^ i * (1 - p) ^ (n + 1 - i) else 0) =
      ∑ i ∈ Finset.range (n + 2),
        ((n + 1).choose i : ℝ) * (if k + 1 ≤ i then p ^ i * (1 - p) ^ (n + 1 - i) else 0) := by
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> ring
  rw [hLHS_eq]; clear hLHS_eq
  have hrewrite : ∑ i ∈ Finset.range (n + 2),
      ((n + 1).choose i : ℝ) * (if k + 1 ≤ i then p ^ i * (1 - p) ^ (n + 1 - i) else 0) =
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (if k + 1 ≤ i then p ^ i * (1 - p) ^ (n + 1 - i) else 0) +
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (if k + 1 ≤ i + 1 then p ^ (i + 1) * (1 - p) ^ (n - i) else 0) := by
    simpa using hsplit
  rw [hrewrite]; clear hrewrite
  have hA : ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (if k + 1 ≤ i then p ^ i * (1 - p) ^ (n + 1 - i) else 0) =
      (1 - p) * ∑ i ∈ Finset.range (n + 1),
        (if k + 1 ≤ i then (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) else 0) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
    have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    split_ifs with h
    · have : n + 1 - i = (n - i) + 1 := by omega
      rw [this, pow_succ]; ring
    · ring
  have hB : ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (if k + 1 ≤ i + 1 then p ^ (i + 1) * (1 - p) ^ (n - i) else 0) =
      p * ∑ i ∈ Finset.range (n + 1),
        (if k ≤ i then (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) else 0) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    by_cases h : k ≤ i
    · rw [if_pos (show k + 1 ≤ i + 1 from by omega), if_pos h, pow_succ']; ring
    · rw [if_neg (show ¬(k + 1 ≤ i + 1) from by omega), if_neg h]; ring
  rw [hA, hB]

/-- The tail probability is monotone in the success probability: If `p₁ ≤ p₂` then
`Pr(Bin(n, p₁) ≥ k) ≤ Pr(Bin(n, p₂) ≥ k)`. -/
theorem P033T8_tail_mono_p {p₁ p₂ : ℝ} (hp₁ : 0 ≤ p₁) (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1)
    (n k : ℕ) :
    P033T8_tail n p₁ k ≤ P033T8_tail n p₂ k := by
  suffices h : ∀ k, P033T8_tail n p₁ k ≤ P033T8_tail n p₂ k from h k
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => simp
    | succ k => simp [P033T8_tail_large 0 _ (k + 1) (by omega)]
  | succ n ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [P033T8_tail_succ_succ, P033T8_tail_succ_succ]
      have hIH_k1 := ih (k + 1)
      have hIH_k := ih k
      have hmono_k := P033T8_tail_anti_k hp₁ (le_trans hp₁₂ hp₂) n (Nat.le_succ k)
      nlinarith

lemma P033T8_tail_eq (n k : ℕ) (p : ℝ) : P033T8_tail n p k = binomialTail n k p := by
  unfold P033T8_tail binomialTail
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

lemma P033T8_tail_monotone (n k : ℕ) : MonotoneOn (binomialTail n k) (Icc 0 1) := by
  intro p hp q hq hpq
  simpa only [P033T8_tail_eq] using P033T8_tail_mono_p hp.1 hpq hq.2 n k

lemma P033T8_above_shift (f : ℝ → ℝ) (h : ℝ) :
    caliperAbove f h = ∫ u in (0:ℝ)..h, f (caliperCutoff+u) := by
  simp only [intervalIntegral.integral_comp_add_left, add_zero, caliperAbove]

lemma P033T8_below_shift (f : ℝ → ℝ) (h : ℝ) :
    caliperBelow f h = ∫ u in (0:ℝ)..h, f (caliperCutoff-u) := by
  simp only [intervalIntegral.integral_comp_sub_left, sub_zero, caliperBelow]

lemma P033T8_shift_integrable (f : ℝ → ℝ) (hfi : Integrable f volume) (h : ℝ) :
    IntervalIntegrable (fun u => f (caliperCutoff+u)) volume 0 h ∧
    IntervalIntegrable (fun u => f (caliperCutoff-u)) volume 0 h := by
  constructor
  · simpa using (hfi.intervalIntegrable (a := caliperCutoff) (b := caliperCutoff+h)).comp_add_left caliperCutoff
  · simpa using (hfi.intervalIntegrable (a := caliperCutoff-h) (b := caliperCutoff)).comp_sub_left caliperCutoff |>.symm

lemma P033T8_side_nonneg (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ caliperAbove f h ∧ 0 ≤ caliperBelow f h := by
  constructor
  · exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => hf0 x)
  · exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => hf0 x)

lemma P033T8_prob_mem (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x) {h : ℝ} (hh : 0 ≤ h)
    (hs : 0 < caliperAbove f h+caliperBelow f h) : caliperProbability f h ∈ Icc (0:ℝ) 1 := by
  obtain ⟨ha,hb⟩ := P033T8_side_nonneg f hf0 hh
  exact ⟨div_nonneg ha hs.le, (div_le_one hs).mpr (by linarith)⟩

lemma P033T8_symmetric (f : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hsym : ∀ u : ℝ, 0 < u → u < h → f (caliperCutoff+u) = f (caliperCutoff-u)) :
    caliperAbove f h = caliperBelow f h := by
  rw [P033T8_above_shift, P033T8_below_shift]
  exact intervalIntegral.integral_congr_Ioo_of_le hh (fun u hu => hsym u hu.1 hu.2)

lemma P033T8_side_order (f : ℝ → ℝ) (hfi : Integrable f volume) {h : ℝ} (hh : 0 ≤ h) :
    (AntitoneOn f (Icc (caliperCutoff-h) (caliperCutoff+h)) → caliperAbove f h ≤ caliperBelow f h) ∧
    (MonotoneOn f (Icc (caliperCutoff-h) (caliperCutoff+h)) → caliperBelow f h ≤ caliperAbove f h) := by
  obtain ⟨hiA,hiB⟩ := P033T8_shift_integrable f hfi h
  rw [P033T8_above_shift, P033T8_below_shift]
  constructor
  · intro hm
    apply intervalIntegral.integral_mono_on hh hiA hiB
    intro u hu
    exact hm ⟨by linarith [hu.2], by linarith [hu.1]⟩
      ⟨by linarith [hu.1], by linarith [hu.2]⟩ (by linarith [hu.1])
  · intro hm
    apply intervalIntegral.integral_mono_on hh hiB hiA
    intro u hu
    exact hm ⟨by linarith [hu.2], by linarith [hu.1]⟩
      ⟨by linarith [hu.1], by linarith [hu.2]⟩ (by linarith [hu.1])

lemma P033T8_ratio_identity (A B : ℝ) (hs : 0 < A+B) :
    |A/(A+B)-1/2| = |A-B|/(2*(A+B)) := by
  have he : A/(A+B)-1/2 = (A-B)/(2*(A+B)) := by field_simp; ring
  rw [he, abs_div, abs_of_pos (by positivity : 0 < 2*(A+B))]

lemma P033T8_lipschitz (f : ℝ → ℝ) (hfi : Integrable f volume) {h : ℝ} (hh : 0 < h)
    (hs : 0 < caliperAbove f h+caliperBelow f h) (a L : ℝ) (ha : 0 < a)
    (hlower : ∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h), a ≤ f x)
    (hlip : ∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h),
      ∀ y ∈ Icc (caliperCutoff-h) (caliperCutoff+h), |f x-f y| ≤ L*|x-y|) :
    |caliperAbove f h-caliperBelow f h| ≤ L*h^2 ∧
    2*h*a ≤ caliperAbove f h+caliperBelow f h ∧
    |caliperProbability f h-1/2| = |caliperAbove f h-caliperBelow f h|/
      (2*(caliperAbove f h+caliperBelow f h)) ∧
    |caliperProbability f h-1/2| ≤ L*h/(4*a) := by
  obtain ⟨hiA,hiB⟩ := P033T8_shift_integrable f hfi h
  have hm (u : ℝ) (hu : u ∈ Icc 0 h) :
      caliperCutoff+u ∈ Icc (caliperCutoff-h) (caliperCutoff+h) ∧
      caliperCutoff-u ∈ Icc (caliperCutoff-h) (caliperCutoff+h) := by
    constructor <;> constructor <;> linarith [hu.1,hu.2]
  have hdiff : |caliperAbove f h-caliperBelow f h| ≤ L*h^2 := by
    rw [P033T8_above_shift, P033T8_below_shift, ← intervalIntegral.integral_sub hiA hiB]
    calc
      |∫ u in (0:ℝ)..h, (f (caliperCutoff+u)-f (caliperCutoff-u))| ≤
          ∫ u in (0:ℝ)..h, |f (caliperCutoff+u)-f (caliperCutoff-u)| :=
        intervalIntegral.abs_integral_le_integral_abs hh.le
      _ ≤ ∫ u in (0:ℝ)..h, (2*L*u) := by
        apply intervalIntegral.integral_mono_on hh.le (hiA.sub hiB).abs
          ((continuous_const.mul continuous_id).intervalIntegrable _ _)
        intro u hu
        have hl := hlip _ (hm u hu).1 _ (hm u hu).2
        have he : |caliperCutoff+u-(caliperCutoff-u)| = 2*u := by
          rw [abs_of_nonneg (by linarith [hu.1])]; ring
        rw [he] at hl
        change |f (caliperCutoff+u)-f (caliperCutoff-u)| ≤ 2*L*u
        nlinarith
      _ = L*h^2 := by rw [intervalIntegral.integral_const_mul, integral_id]; ring
  have hlA : h*a ≤ caliperAbove f h := by
    rw [P033T8_above_shift]
    calc
      h*a = ∫ _ in (0:ℝ)..h, a := by simp [intervalIntegral.integral_const, mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hh.le intervalIntegrable_const hiA
        (fun u hu => hlower _ (hm u hu).1)
  have hlB : h*a ≤ caliperBelow f h := by
    rw [P033T8_below_shift]
    calc
      h*a = ∫ _ in (0:ℝ)..h, a := by simp [intervalIntegral.integral_const, mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hh.le intervalIntegrable_const hiB
        (fun u hu => hlower _ (hm u hu).2)
  have hlo : 2*h*a ≤ caliperAbove f h+caliperBelow f h := by linarith
  have hid := P033T8_ratio_identity (caliperAbove f h) (caliperBelow f h) hs
  refine ⟨hdiff,hlo,hid,?_⟩
  rw [caliperProbability, hid]
  apply (div_le_iff₀ (by positivity : 0 < 2*(caliperAbove f h+caliperBelow f h))).mpr
  have hLa : 0 ≤ L := by
    have he := hlip (caliperCutoff+h) ⟨by linarith,le_rfl⟩
      (caliperCutoff-h) ⟨le_rfl,by linarith⟩
    rw [abs_of_pos (by linarith : 0 < caliperCutoff+h-(caliperCutoff-h))] at he
    nlinarith [abs_nonneg (f (caliperCutoff+h)-f (caliperCutoff-h))]
  have hx : L*h/(4*a)*(2*(2*h*a)) = L*h^2 := by field_simp; ring
  calc
    |caliperAbove f h-caliperBelow f h| ≤ L*h^2 := hdiff
    _ = L*h/(4*a)*(2*(2*h*a)) := hx.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)


lemma P033T8_scaled_mass_limits (f : ℝ → ℝ) (hfi : Integrable f volume)
    (hc : ContinuousAt f caliperCutoff) :
    Tendsto (fun h => caliperAbove f h/h) (𝓝[>] (0:ℝ)) (𝓝 (f caliperCutoff)) ∧
    Tendsto (fun h => caliperBelow f h/h) (𝓝[>] (0:ℝ)) (𝓝 (f caliperCutoff)) := by
  have hA : HasDerivAt (caliperAbove f) (f caliperCutoff) 0 := by
    convert (intervalIntegral.integral_hasDerivAt_right
      (hfi.intervalIntegrable (a := caliperCutoff) (b := caliperCutoff))
      hfi.aestronglyMeasurable.stronglyMeasurableAtFilter hc).comp_of_eq 0
      ((hasDerivAt_id 0).const_add caliperCutoff) (by simp) using 1 <;> try { simp } <;> rfl
  have hB : HasDerivAt (caliperBelow f) (f caliperCutoff) 0 := by
    convert (intervalIntegral.integral_hasDerivAt_left
      (hfi.intervalIntegrable (a := caliperCutoff) (b := caliperCutoff))
      hfi.aestronglyMeasurable.stronglyMeasurableAtFilter hc).comp_of_eq 0
      ((hasDerivAt_const 0 caliperCutoff).sub (hasDerivAt_id 0)) (by simp) using 1 <;> try { simp } <;> rfl
  constructor
  · simpa [caliperAbove, smul_eq_mul, div_eq_mul_inv, mul_comm] using hA.tendsto_slope_zero_right
  · simpa [caliperBelow, smul_eq_mul, div_eq_mul_inv, mul_comm] using hB.tendsto_slope_zero_right

lemma P033T8_probability_limit (f : ℝ → ℝ) (hfi : Integrable f volume)
    (hc : ContinuousAt f caliperCutoff) (hf : 0 < f caliperCutoff) :
    Tendsto (caliperProbability f) (𝓝[>] (0:ℝ)) (𝓝 (1/2)) := by
  obtain ⟨hA,hB⟩ := P033T8_scaled_mass_limits f hfi hc
  have hl := hA.div (hA.add hB) (by positivity : f caliperCutoff+f caliperCutoff ≠ 0)
  have hval : f caliperCutoff/(f caliperCutoff+f caliperCutoff) = 1/2 := by field_simp; ring
  rw [hval] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change 0 < h at hh
  dsimp [caliperProbability]
  rw [← add_div]
  exact div_div_div_cancel_right₀ hh.ne' _ _

lemma P033T8_integral_remainder (r : ℝ → ℝ)
    (hri : ∀ h : ℝ, IntervalIntegrable r volume 0 h)
    (hr : Asymptotics.IsLittleO (𝓝 (0:ℝ)) r (fun u => u)) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ)) (fun h => ∫ u in (0:ℝ)..h, r u) (fun h => h^2) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hrδ⟩ := Metric.eventually_nhds_iff.mp (hr.bound hε)
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
    with h hh hsmall
  change 0 < h at hh
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
  calc
    |∫ u in (0:ℝ)..h, r u| ≤ ∫ u in (0:ℝ)..h, |r u| :=
      intervalIntegral.abs_integral_le_integral_abs hh.le
    _ ≤ ∫ u in (0:ℝ)..h, ε*u := by
      apply intervalIntegral.integral_mono_on hh.le (hri h).abs
        ((continuous_const.mul continuous_id).intervalIntegrable _ _)
      intro u hu
      have he := hrδ (show dist u 0 < δ by simpa [Real.dist_eq, abs_of_nonneg hu.1] using hu.2.trans_lt hsmall)
      simpa [Real.norm_eq_abs, abs_of_nonneg hu.1] using he
    _ = ε*(h^2/2) := by rw [intervalIntegral.integral_const_mul, integral_id]; ring
    _ ≤ ε*h^2 := by nlinarith [sq_nonneg h]

lemma P033T8_second_order (f : ℝ → ℝ) (hfi : Integrable f volume) (f' : ℝ)
    (hd : HasDerivAt f f' caliperCutoff) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun h => caliperAbove f h-f caliperCutoff*h-f'/2*h^2) (fun h => h^2) ∧
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun h => caliperBelow f h-f caliperCutoff*h+f'/2*h^2) (fun h => h^2) := by
  have hr := hasDerivAt_iff_isLittleO_nhds_zero.mp hd
  simp only [smul_eq_mul] at hr
  have hrB : Asymptotics.IsLittleO (𝓝 (0:ℝ))
      (fun u => f (caliperCutoff-u)-f caliperCutoff+u*f') (fun u => u) := by
    simpa [Function.comp_def, sub_eq_add_neg] using (hr.comp_tendsto (show Tendsto (fun u : ℝ => -u) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) by simpa using (tendsto_id.neg : Tendsto (fun u : ℝ => -u) (𝓝 (0:ℝ)) (𝓝 (-0:ℝ))))).of_neg_right
  have hi (h : ℝ) := P033T8_shift_integrable f hfi h
  have hiL (h : ℝ) : IntervalIntegrable (fun u : ℝ => u*f') volume 0 h :=
    (continuous_id.mul continuous_const).intervalIntegrable _ _
  constructor
  · have he := P033T8_integral_remainder _ (fun h => ((hi h).1.sub intervalIntegrable_const).sub (hiL h)) hr
    convert he using 1
    ext h
    rw [intervalIntegral.integral_sub ((hi h).1.sub intervalIntegrable_const) (hiL h),
      intervalIntegral.integral_sub (hi h).1 intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const, integral_id,
      ← P033T8_above_shift]
    simp only [sub_zero, smul_eq_mul]
    ring
  · have he := P033T8_integral_remainder _ (fun h => ((hi h).2.sub intervalIntegrable_const).add (hiL h)) hrB
    convert he using 1
    ext h
    rw [intervalIntegral.integral_add ((hi h).2.sub intervalIntegrable_const) (hiL h),
      intervalIntegral.integral_sub (hi h).2 intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const, integral_id,
      ← P033T8_below_shift]
    simp only [sub_zero, smul_eq_mul]
    ring

lemma P033T8_probability_expansion (f : ℝ → ℝ) (hfi : Integrable f volume) (f' : ℝ)
    (hd : HasDerivAt f f' caliperCutoff) (hf : 0 < f caliperCutoff) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun h => caliperProbability f h-1/2-h*f'/(4*f caliperCutoff)) (fun h => h) := by
  obtain ⟨hA,hB⟩ := P033T8_scaled_mass_limits f hfi hd.continuousAt
  obtain ⟨hrA,hrB⟩ := P033T8_second_order f hfi f' hd
  have hs : Tendsto (fun h => (caliperAbove f h+caliperBelow f h)/h)
      (𝓝[>] (0:ℝ)) (𝓝 (2*f caliperCutoff)) := by
    simpa [add_div, two_mul] using hA.add hB
  have hD : Tendsto (fun h => (caliperAbove f h-caliperBelow f h)/h^2)
      (𝓝[>] (0:ℝ)) (𝓝 f') := by
    have hl := (hrA.tendsto_div_nhds_zero.sub hrB.tendsto_div_nhds_zero).add_const f'
    simp only [sub_self, zero_add] at hl
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    change 0 < h at hh
    field_simp
    <;> ring
  have hl := (hD.div (hs.const_mul 2) (by positivity : 2*(2*f caliperCutoff) ≠ 0)).sub_const (f'/(4*f caliperCutoff))
  have hv : f'/(2*(2*f caliperCutoff))-f'/(4*f caliperCutoff) = 0 := by ring
  rw [hv] at hl
  have hne : ∀ᶠ h in 𝓝[>] (0:ℝ), h = 0 →
      caliperProbability f h-1/2-h*f'/(4*f caliperCutoff) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact fun hz => (ne_of_gt hh hz).elim
  apply (Asymptotics.isLittleO_iff_tendsto' hne).mpr
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin,
    hs.eventually (eventually_gt_nhds (by positivity : 0 < 2*f caliperCutoff))] with h hh hm
  change 0 < h at hh
  have hS : caliperAbove f h+caliperBelow f h ≠ 0 := by
    intro hz
    simp [hz] at hm
  dsimp [caliperProbability]
  field_simp [hh.ne', hS, hf.ne']
  <;> ring


/-- The indices whose observations belong to a measurable category. -/
def P033T8_indices {M : ℕ} (s : Set ℝ) (X : Fin M → ℝ) : Finset (Fin M) :=
  by classical exact Finset.univ.filter (fun i => X i ∈ s)

/-- A specified membership pattern, before taking its cardinality. -/
def P033T8_cell {M : ℕ} (s : Set ℝ) (W : Finset (Fin M)) : Set (Fin M → ℝ) :=
  {X | P033T8_indices s X = W}

lemma P033T8_cell_pi {M : ℕ} (s : Set ℝ) (W : Finset (Fin M)) :
    P033T8_cell s W = Set.univ.pi (fun i => if i ∈ W then s else sᶜ) := by
  classical
  ext X
  simp only [P033T8_cell, mem_setOf_eq, Finset.ext_iff, P033T8_indices,
    Finset.mem_filter, Finset.mem_univ, true_and, mem_univ_pi]
  constructor
  · intro hx i
    by_cases hi : i ∈ W <;> simp_all
  · intro hx i
    have hi := hx i
    by_cases hw : i ∈ W <;> simp_all

lemma P033T8_cell_measurable {M : ℕ} {s : Set ℝ} (hs : MeasurableSet s)
    (W : Finset (Fin M)) : MeasurableSet (P033T8_cell s W) := by
  classical
  rw [P033T8_cell_pi]
  apply MeasurableSet.univ_pi
  intro i
  split_ifs <;> simp_all

lemma P033T8_cell_disjoint {M : ℕ} (s : Set ℝ) {W V : Finset (Fin M)} (hne : W ≠ V) :
    Disjoint (P033T8_cell s W) (P033T8_cell s V) := by
  apply Set.disjoint_left.mpr
  intro X hW hV
  exact hne (hW.symm.trans hV)

lemma P033T8_prod_two {M : ℕ} (I W : Finset (Fin M)) (hW : W ⊆ I) (a b : ℝ) :
    (∏ i ∈ I, if i ∈ W then a else b) = a^W.card*b^(I.card-W.card) := by
  classical
  have h1 : I.filter (fun i => i ∈ W) = W := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hi => ⟨hW hi, hi⟩⟩
  have h2 : I.filter (fun i => i ∉ W) = I \ W := by ext i; simp
  rw [Finset.prod_ite, h1, h2, Finset.prod_const, Finset.prod_const,
    Finset.card_sdiff_of_subset hW]

lemma P033T8_cell_mass {M : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s : Set ℝ) (W : Finset (Fin M)) :
    (Measure.pi (fun _ : Fin M => ν)).real (P033T8_cell s W) =
      ν.real s^W.card*ν.real sᶜ^(M-W.card) := by
  classical
  rw [P033T8_cell_pi, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [apply_ite]
  simpa only [Finset.card_univ, Fintype.card_fin, Measure.real] using
    P033T8_prod_two Finset.univ W (Finset.subset_univ W) (ν.real s) (ν.real sᶜ)

lemma P033T8_count_union {M : ℕ} (s : Set ℝ) (n : ℕ) :
    {X : Fin M → ℝ | (P033T8_indices s X).card = n} =
      ⋃ W ∈ Finset.univ.powersetCard n, P033T8_cell s W := by
  classical
  ext X
  simp only [mem_setOf_eq, mem_iUnion, Finset.mem_powersetCard, Finset.subset_univ,
    true_and, P033T8_cell]
  exact ⟨fun hx => ⟨P033T8_indices s X, hx, rfl⟩, fun ⟨W,hW,hX⟩ => hX ▸ hW⟩

lemma P033T8_count_measurable {M : ℕ} {s : Set ℝ} (hs : MeasurableSet s) (n : ℕ) :
    MeasurableSet {X : Fin M → ℝ | (P033T8_indices s X).card = n} := by
  rw [P033T8_count_union]
  exact MeasurableSet.biUnion (Finset.countable_toSet _) (fun W _ => P033T8_cell_measurable hs W)

lemma P033T8_count_mass {M : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s : Set ℝ) (hs : MeasurableSet s) (n : ℕ) :
    (Measure.pi (fun _ : Fin M => ν)).real {X | (P033T8_indices s X).card = n} =
      (M.choose n:ℝ)*ν.real s^n*ν.real sᶜ^(M-n) := by
  classical
  rw [P033T8_count_union, measureReal_biUnion_finset]
  · calc
      (∑ W ∈ Finset.univ.powersetCard n, (Measure.pi (fun _ : Fin M => ν)).real (P033T8_cell s W)) =
          ∑ _W ∈ Finset.univ.powersetCard n, ν.real s^n*ν.real sᶜ^(M-n) := by
        apply Finset.sum_congr rfl
        intro W hW
        rw [P033T8_cell_mass, (Finset.mem_powersetCard.mp hW).2]
      _ = _ := by simp [Finset.card_powersetCard]; ring
  · intro W _ V _ hne
    exact P033T8_cell_disjoint s hne
  · exact fun W _ => P033T8_cell_measurable hs W

lemma P033T8_joint_pi {M : ℕ} (s t : Set ℝ) (hts : t ⊆ s)
    (W J : Finset (Fin M)) (hJW : J ⊆ W) :
    P033T8_cell s W ∩ P033T8_cell t J =
      Set.univ.pi (fun i => if i ∈ W then (if i ∈ J then t else s \ t) else sᶜ) := by
  classical
  rw [P033T8_cell_pi, P033T8_cell_pi]
  ext X
  simp only [mem_inter_iff, mem_univ_pi]
  constructor
  · intro hx i
    have hs := hx.1 i
    have ht := hx.2 i
    by_cases hiW : i ∈ W <;> by_cases hiJ : i ∈ J <;> simp_all [Finset.subset_iff]
  · intro hx
    constructor <;> intro i
    · have hi := hx i
      by_cases hiW : i ∈ W <;> by_cases hiJ : i ∈ J <;> simp_all [Finset.subset_iff]
      exact hts hi
    · have hi := hx i
      by_cases hiW : i ∈ W <;> by_cases hiJ : i ∈ J <;> simp_all [Finset.subset_iff]
      exact fun ht => hi (hts ht)

lemma P033T8_joint_cell_mass {M : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s t : Set ℝ) (hts : t ⊆ s) (W J : Finset (Fin M)) (hJW : J ⊆ W) :
    (Measure.pi (fun _ : Fin M => ν)).real (P033T8_cell s W ∩ P033T8_cell t J) =
      ν.real t^J.card*ν.real (s \ t)^(W.card-J.card)*ν.real sᶜ^(M-W.card) := by
  classical
  rw [P033T8_joint_pi s t hts W J hJW, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [apply_ite]
  rw [Finset.prod_ite]
  have hW : Finset.univ.filter (fun i : Fin M => i ∈ W) = W := by ext i; simp
  have hWc : (Finset.univ.filter (fun i : Fin M => i ∉ W)).card = M-W.card := by
    have he : Finset.univ.filter (fun i : Fin M => i ∉ W) = Finset.univ \ W := by ext i; simp
    rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ W), Finset.card_univ, Fintype.card_fin]
  rw [hW, P033T8_prod_two W J hJW, Finset.prod_const, hWc]
  rfl

lemma P033T8_indices_subset {M : ℕ} {s t : Set ℝ} (hts : t ⊆ s) (X : Fin M → ℝ) :
    P033T8_indices t X ⊆ P033T8_indices s X := by
  classical
  intro i hi
  simp only [P033T8_indices, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hts hi

lemma P033T8_joint_union {M : ℕ} (s t : Set ℝ) (hts : t ⊆ s) (W : Finset (Fin M)) (j : ℕ) :
    P033T8_cell s W ∩ {X | (P033T8_indices t X).card = j} =
      ⋃ J ∈ W.powersetCard j, P033T8_cell s W ∩ P033T8_cell t J := by
  classical
  ext X
  simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion, Finset.mem_powersetCard,
    P033T8_cell]
  constructor
  · intro hx
    refine ⟨P033T8_indices t X, ⟨?_,hx.2⟩,hx.1,rfl⟩
    rw [← hx.1]
    exact P033T8_indices_subset hts X
  · rintro ⟨J,⟨_,hJ⟩,hW,hX⟩
    exact ⟨hW, hX ▸ hJ⟩

lemma P033T8_joint_fixed_mass {M : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s)
    (W : Finset (Fin M)) (j : ℕ) :
    (Measure.pi (fun _ : Fin M => ν)).real (P033T8_cell s W ∩ {X | (P033T8_indices t X).card = j}) =
      (W.card.choose j:ℝ)*ν.real t^j*ν.real (s \ t)^(W.card-j)*ν.real sᶜ^(M-W.card) := by
  classical
  rw [P033T8_joint_union s t hts, measureReal_biUnion_finset]
  · calc
      (∑ J ∈ W.powersetCard j, (Measure.pi (fun _ : Fin M => ν)).real (P033T8_cell s W ∩ P033T8_cell t J)) =
          ∑ _J ∈ W.powersetCard j, ν.real t^j*ν.real (s \ t)^(W.card-j)*ν.real sᶜ^(M-W.card) := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [P033T8_joint_cell_mass ν s t hts W J (Finset.mem_powersetCard.mp hJ).1,
          (Finset.mem_powersetCard.mp hJ).2]
      _ = _ := by simp [Finset.card_powersetCard]; ring
  · intro J _ K _ hne
    exact (P033T8_cell_disjoint t hne).mono inter_subset_right inter_subset_right
  · exact fun J _ => (P033T8_cell_measurable hs W).inter (P033T8_cell_measurable ht J)

lemma P033T8_joint_mass {M : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s)
    (n j : ℕ) :
    (Measure.pi (fun _ : Fin M => ν)).real
      ({X | (P033T8_indices s X).card = n} ∩ {X | (P033T8_indices t X).card = j}) =
      (M.choose n:ℝ)*(n.choose j:ℝ)*ν.real t^j*ν.real (s \ t)^(n-j)*ν.real sᶜ^(M-n) := by
  classical
  rw [P033T8_count_union]
  simp only [iUnion_inter]
  rw [measureReal_biUnion_finset]
  · calc
      (∑ W ∈ Finset.univ.powersetCard n, (Measure.pi (fun _ : Fin M => ν)).real
          (P033T8_cell s W ∩ {X | (P033T8_indices t X).card = j})) =
          ∑ _W ∈ Finset.univ.powersetCard n,
            (n.choose j:ℝ)*ν.real t^j*ν.real (s \ t)^(n-j)*ν.real sᶜ^(M-n) := by
        apply Finset.sum_congr rfl
        intro W hW
        rw [P033T8_joint_fixed_mass ν s t hs ht hts, (Finset.mem_powersetCard.mp hW).2]
      _ = _ := by simp [Finset.card_powersetCard]; ring
  · intro W _ V _ hne
    exact (P033T8_cell_disjoint s hne).mono inter_subset_left inter_subset_left
  · exact fun W _ => (P033T8_cell_measurable hs W).inter (P033T8_count_measurable ht j)


lemma P033T8_conditional_point {M : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s)
    (hpos : 0 < ν.real s) (n : ℕ)
    (hN : 0 < (Measure.pi (fun _ : Fin M => ν)).real {X | (P033T8_indices s X).card = n})
    (j : ℕ) (hj : j ≤ n) :
    (Measure.pi (fun _ : Fin M => ν)).real
        ({X | (P033T8_indices s X).card = n} ∩ {X | (P033T8_indices t X).card = j}) /
      (Measure.pi (fun _ : Fin M => ν)).real {X | (P033T8_indices s X).card = n} =
    (n.choose j:ℝ)*(ν.real t/ν.real s)^j*(1-ν.real t/ν.real s)^(n-j) := by
  rw [P033T8_count_mass ν s hs n] at hN
  rw [P033T8_joint_mass ν s t hs ht hts n j, P033T8_count_mass ν s hs n,
    div_eq_iff hN.ne']
  have hcomp : 1-ν.real t/ν.real s = ν.real (s \ t)/ν.real s := by
    rw [measureReal_sdiff hts ht]
    field_simp
    <;> ring
  rw [hcomp]
  have hpow : (ν.real s)^j*(ν.real s)^(n-j) = (ν.real s)^n := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  have hp : (n.choose j:ℝ)*(ν.real t/ν.real s)^j*(ν.real (s \ t)/ν.real s)^(n-j) =
      ((n.choose j:ℝ)*ν.real t^j*ν.real (s \ t)^(n-j))/(ν.real s)^n := by
    rw [div_pow, div_pow]
    calc
      (n.choose j:ℝ)*(ν.real t^j/ν.real s^j)*(ν.real (s \ t)^(n-j)/ν.real s^(n-j)) =
          ((n.choose j:ℝ)*ν.real t^j)/ν.real s^j*(ν.real (s \ t)^(n-j)/ν.real s^(n-j)) := by
        rw [mul_div_assoc]
      _ = _ := by rw [div_mul_div_comm, hpow]
  rw [hp]
  field_simp [hpos.ne']
  <;> ring

lemma P033T8_tail_union {M : ℕ} (s t : Set ℝ) (hts : t ⊆ s) (n k : ℕ) :
    {X : Fin M → ℝ | (P033T8_indices s X).card = n} ∩ {X | k ≤ (P033T8_indices t X).card} =
      ⋃ j ∈ Finset.Icc k n,
        {X | (P033T8_indices s X).card = n} ∩ {X | (P033T8_indices t X).card = j} := by
  ext X
  simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion, Finset.mem_Icc]
  constructor
  · intro hx
    refine ⟨(P033T8_indices t X).card, ⟨hx.2,?_⟩,hx.1,rfl⟩
    rw [← hx.1]
    exact Finset.card_le_card (P033T8_indices_subset hts X)
  · rintro ⟨j,⟨hkj,_⟩,hN,hK⟩
    exact ⟨hN,hK ▸ hkj⟩

lemma P033T8_conditional_tail {M : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s)
    (hpos : 0 < ν.real s) (n : ℕ)
    (hN : 0 < (Measure.pi (fun _ : Fin M => ν)).real {X | (P033T8_indices s X).card = n})
    (k : ℕ) :
    (Measure.pi (fun _ : Fin M => ν)).real
        ({X | (P033T8_indices s X).card = n} ∩ {X | k ≤ (P033T8_indices t X).card}) /
      (Measure.pi (fun _ : Fin M => ν)).real {X | (P033T8_indices s X).card = n} =
    binomialTail n k (ν.real t/ν.real s) := by
  rw [P033T8_tail_union s t hts n k, measureReal_biUnion_finset]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    exact P033T8_conditional_point ν s t hs ht hts hpos n hN j (Finset.mem_Icc.mp hj).2
  · intro j _ l _ hne
    apply Set.disjoint_left.mpr
    intro X hx hy
    exact hne (hx.2.symm.trans hy.2)
  · exact fun j _ => (P033T8_count_measurable hs n).inter (P033T8_count_measurable ht j)

lemma P033T8_density_probability (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f volume) (hfn : (∫ x, f x) = 1) :
    IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0), hfn, ENNReal.ofReal_one]

lemma P033T8_density_real (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f volume) (s : Set ℝ) (hs : MeasurableSet s) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).real s = ∫ x in s, f x := by
  rw [Measure.real, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn (ae_of_all _ hf0),
    ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg hf0)]

lemma P033T8_density_interval (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f volume) (a b : ℝ) (hab : a ≤ b) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).real (Icc a b) = ∫ x in a..b, f x := by
  rw [P033T8_density_real f hf0 hfi _ measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

lemma P033T8_indices_count {M : ℕ} (h : ℝ) (X : Fin M → ℝ) :
    (P033T8_indices (Icc (caliperCutoff-h) (caliperCutoff+h)) X).card = caliperCount h X := by
  unfold caliperCount
  congr 1
  ext i
  simp [P033T8_indices]

lemma P033T8_indices_successes {M : ℕ} (h : ℝ) (X : Fin M → ℝ) :
    (P033T8_indices (Icc caliperCutoff (caliperCutoff+h)) X).card = caliperSuccesses h X := by
  unfold caliperSuccesses
  congr 1
  ext i
  simp [P033T8_indices]

lemma P033T8_caliper_counts (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f volume) (hfn : (∫ x, f x) = 1) (h : ℝ) (hh : 0 < h)
    (hs : 0 < caliperAbove f h+caliperBelow f h) (M n : ℕ)
    (hN : (caliperDataLaw M f).real {X | caliperCount h X = n} > 0) :
    (∀ j : ℕ, j ≤ n →
      (caliperDataLaw M f).real ({X | caliperCount h X = n} ∩ {X | caliperSuccesses h X = j}) /
        (caliperDataLaw M f).real {X | caliperCount h X = n} =
      (n.choose j:ℝ)*caliperProbability f h^j*(1-caliperProbability f h)^(n-j)) ∧
    (∀ k : ℕ, k ≤ n →
      (caliperDataLaw M f).real ({X | caliperCount h X = n} ∩ {X | k ≤ caliperSuccesses h X}) /
        (caliperDataLaw M f).real {X | caliperCount h X = n} =
      binomialTail n k (caliperProbability f h)) := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  letI P033T8_instDensityProbability : IsProbabilityMeasure ν := P033T8_density_probability f hf0 hfi hfn
  let s := Icc (caliperCutoff-h) (caliperCutoff+h)
  let t := Icc caliperCutoff (caliperCutoff+h)
  have hts : t ⊆ s := by intro x hx; exact ⟨by linarith [hx.1],hx.2⟩
  have hS : ν.real s = caliperAbove f h+caliperBelow f h := by
    rw [P033T8_density_interval f hf0 hfi _ _ (by linarith)]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hfi.intervalIntegrable (a := caliperCutoff-h) (b := caliperCutoff))
      (hfi.intervalIntegrable (a := caliperCutoff) (b := caliperCutoff+h))]
    exact add_comm _ _
  have hA : ν.real t = caliperAbove f h :=
    P033T8_density_interval f hf0 hfi _ _ (by linarith)
  have hpos : 0 < ν.real s := hS ▸ hs
  have hp : ν.real t/ν.real s = caliperProbability f h := by rw [hA,hS]; rfl
  have hN' : 0 < (Measure.pi (fun _ : Fin M => ν)).real {X | (P033T8_indices s X).card = n} := by
    simpa only [s, P033T8_indices_count, caliperDataLaw, ν] using hN
  constructor
  · intro j hj
    have he := P033T8_conditional_point ν s t measurableSet_Icc measurableSet_Icc hts hpos n hN' j hj
    simpa only [hp, s, t, P033T8_indices_count, P033T8_indices_successes, caliperDataLaw, ν] using he
  · intro k _
    have he := P033T8_conditional_tail ν s t measurableSet_Icc measurableSet_Icc hts hpos n hN' k
    simpa only [hp, s, t, P033T8_indices_count, P033T8_indices_successes, caliperDataLaw, ν] using he


theorem caliper_correction_proof (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfs : ∀ x, x < 0 → f x = 0) (hfi : Integrable f volume)
    (hfn : (∫ x, f x) = 1) :
    (∀ h : ℝ, 0 < h → h < caliperCutoff → 0 < caliperAbove f h+caliperBelow f h →
      (∀ M n : ℕ, (caliperDataLaw M f).real {X | caliperCount h X = n} > 0 →
        (∀ j : ℕ, j ≤ n →
          (caliperDataLaw M f).real ({X | caliperCount h X = n} ∩ {X | caliperSuccesses h X = j}) /
            (caliperDataLaw M f).real {X | caliperCount h X = n} =
          (n.choose j:ℝ)*caliperProbability f h^j*(1-caliperProbability f h)^(n-j)) ∧
        (∀ k : ℕ, k ≤ n →
          (caliperDataLaw M f).real ({X | caliperCount h X = n} ∩ {X | k ≤ caliperSuccesses h X}) /
            (caliperDataLaw M f).real {X | caliperCount h X = n} =
          binomialTail n k (caliperProbability f h))) ∧
      (caliperProbability f h = 1/2 ↔ caliperAbove f h = caliperBelow f h) ∧
      ((∀ u : ℝ, 0 < u → u < h → f (caliperCutoff+u) = f (caliperCutoff-u)) →
        caliperAbove f h = caliperBelow f h) ∧
      (AntitoneOn f (Icc (caliperCutoff-h) (caliperCutoff+h)) →
        caliperAbove f h ≤ caliperBelow f h ∧ caliperProbability f h ≤ 1/2 ∧
        ∀ n k : ℕ, k ≤ n → binomialTail n k (caliperProbability f h) ≤ binomialTail n k (1/2)) ∧
      (MonotoneOn f (Icc (caliperCutoff-h) (caliperCutoff+h)) →
        caliperBelow f h ≤ caliperAbove f h ∧ 1/2 ≤ caliperProbability f h ∧
        ∀ n k : ℕ, k ≤ n → binomialTail n k (1/2) ≤ binomialTail n k (caliperProbability f h)) ∧
      (∀ a L : ℝ, 0 < a →
        (∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h), a ≤ f x) →
        (∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h),
          ∀ y ∈ Icc (caliperCutoff-h) (caliperCutoff+h), |f x-f y| ≤ L*|x-y|) →
        |caliperAbove f h-caliperBelow f h| ≤ L*h^2 ∧
        2*h*a ≤ caliperAbove f h+caliperBelow f h ∧
        |caliperProbability f h-1/2| = |caliperAbove f h-caliperBelow f h|/
          (2*(caliperAbove f h+caliperBelow f h)) ∧
        |caliperProbability f h-1/2| ≤ L*h/(4*a))) ∧
    (∀ n k : ℕ, k ≤ n → MonotoneOn (binomialTail n k) (Icc 0 1)) ∧
    (ContinuousAt f caliperCutoff → 0 < f caliperCutoff →
      Tendsto (caliperProbability f) (𝓝[>] (0:ℝ)) (𝓝 (1/2))) ∧
    (∀ f' : ℝ, HasDerivAt f f' caliperCutoff → 0 < f caliperCutoff →
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun h => caliperProbability f h-1/2-h*f'/(4*f caliperCutoff)) (fun h => h)) ∧
    (binomialTail 12 9 (1/2) = 299/4096 ∧ binomialTail 15 11 (1/2) = 1941/32768 ∧
      binomialTail 19 14 (1/2) = 2083/65536) := by
  refine ⟨?_, (fun n k _ => P033T8_tail_monotone n k), P033T8_probability_limit f hfi,
    P033T8_probability_expansion f hfi, ?_⟩
  · intro h hh _ hs
    refine ⟨P033T8_caliper_counts f hf0 hfi hfn h hh hs,
      equal_caliper_mass_iff _ _ hs, P033T8_symmetric f hh.le, ?_, ?_,
      P033T8_lipschitz f hfi hh hs⟩
    · intro hm
      have hab := (P033T8_side_order f hfi hh.le).1 hm
      have hp : caliperProbability f h ≤ 1/2 := by
        apply (div_le_iff₀ hs).mpr
        linarith
      refine ⟨hab,hp,?_⟩
      intro n k _
      exact P033T8_tail_monotone n k (P033T8_prob_mem f hf0 hh.le hs)
        (by constructor <;> norm_num) hp
    · intro hm
      have hba := (P033T8_side_order f hfi hh.le).2 hm
      have hp : 1/2 ≤ caliperProbability f h := by
        apply (le_div_iff₀ hs).mpr
        linarith
      refine ⟨hba,hp,?_⟩
      intro n k _
      exact P033T8_tail_monotone n k (by constructor <;> norm_num)
        (P033T8_prob_mem f hf0 hh.le hs) hp
  · exact ⟨caliper_exact_tails.1, caliper_exact_tails.2.2.1,
      caliper_exact_tails.2.2.2.2.1⟩

end
end AronowAudit.P033.Wave1
