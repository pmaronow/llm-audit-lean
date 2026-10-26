import AronowAudit.P001.P001_Foundations

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGLP0014B2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Conditional moment and variance convergence. The proof uses a
continuous compact cutoff. Its quadratic coercivity proves the converse
directly, without choosing an almost-sure weak-convergence subsequence. -/

private lemma t62b2_prob_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) : prob μ A ≤ 1 := by
  exact (measureReal_mono (Set.subset_univ A) (measure_ne_top μ _)).trans_eq (by simp)

private lemma t62b2_prob_union {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω) :
    prob μ (A ∪ B) ≤ prob μ A + prob μ B :=
  measureReal_union_le A B

private lemma t62b2_cp_iff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ) (z : ℝ) :
    CP μ Z z ↔ ∀ ε > 0, ∀ b > 0,
      ∀ᶠ n in atTop, prob μ {ω | ε ≤ |Z n ω - z|} < b := by
  simp only [CP, Real.dist_eq]
  constructor
  · intro h ε hε b hb
    exact (tendsto_order.1 (h ε hε)).2 b hb
  · intro h ε hε
    exact tendsto_order.2 ⟨fun a ha => Eventually.of_forall
      (fun _ => ha.trans_le ENNReal.toReal_nonneg), fun b hb => h ε hε b hb⟩

private lemma t62b2_cp_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z W : ℕ → Ω → ℝ} {z w : ℝ}
    (hZ : CP μ Z z) (hW : CP μ W w) :
    CP μ (fun n ω => Z n ω - W n ω) (z - w) := by
  rw [t62b2_cp_iff] at hZ hW ⊢
  intro ε hε b hb
  filter_upwards [hZ (ε/2) (by positivity) (b/2) (by positivity),
    hW (ε/2) (by positivity) (b/2) (by positivity)] with n hn hm
  have hs : {ω | ε ≤ |Z n ω - W n ω - (z-w)|} ⊆
      {ω | ε/2 ≤ |Z n ω-z|} ∪ {ω | ε/2 ≤ |W n ω-w|} := by
    intro ω hω
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at h
    have ht' : |Z n ω-W n ω-(z-w)| ≤ |Z n ω-z|+|W n ω-w| := by
      convert abs_sub (Z n ω-z) (W n ω-w) using 1 <;> congr 1 <;> ring
    change ε ≤ |Z n ω-W n ω-(z-w)| at hω
    linarith
  have hp := (measureReal_mono hs (measure_ne_top μ _)).trans
    (t62b2_prob_union μ _ _)
  change prob μ _ ≤ _ at hp
  linarith

private lemma t62b2_cp_add {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z W : ℕ → Ω → ℝ} {z w : ℝ}
    (hZ : CP μ Z z) (hW : CP μ W w) :
    CP μ (fun n ω => Z n ω + W n ω) (z + w) := by
  have hn := probability_convergence_continuous_at μ W w (fun x : ℝ => -x)
    hW (by fun_prop)
  simpa only [sub_neg_eq_add] using t62b2_cp_sub μ hZ hn

private lemma t62b2_cp_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : ℕ → Ω → ℝ} {z : ℝ}
    (hZ : CP μ Z z) : CP μ (fun n ω => (Z n ω)^2) (z^2) :=
  probability_convergence_continuous_at μ Z z (fun x : ℝ => x^2) hZ (by fun_prop)

private def t62b2_cut (K : ℕ) (x : ℝ) : ℝ :=
  min 1 (max 0 ((K : ℝ)+1-|x|))

private lemma t62b2_cut_cont (K : ℕ) : Continuous (t62b2_cut K) := by
  unfold t62b2_cut
  fun_prop

private lemma t62b2_cut_bounds (K : ℕ) (x : ℝ) :
    0 ≤ t62b2_cut K x ∧ t62b2_cut K x ≤ 1 := by
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

private lemma t62b2_cut_one {K : ℕ} {x : ℝ} (h : |x| ≤ (K : ℝ)) :
    t62b2_cut K x = 1 := by
  unfold t62b2_cut
  exact min_eq_left ((by linarith : (1 : ℝ) ≤ (K : ℝ)+1-|x|).trans (le_max_right _ _))

private lemma t62b2_cut_zero {K : ℕ} {x : ℝ} (h : (K : ℝ)+1 ≤ |x|) :
    t62b2_cut K x = 0 := by
  simp [t62b2_cut, max_eq_left (by linarith : (K : ℝ)+1-|x| ≤ 0)]

private lemma t62b2_cut_abs (K : ℕ) (x : ℝ) :
    |t62b2_cut K x * x| ≤ (K : ℝ)+1 := by
  by_cases h : |x| ≤ (K : ℝ)+1
  · rw [abs_mul, abs_of_nonneg (t62b2_cut_bounds K x).1]
    exact (mul_le_of_le_one_left (abs_nonneg x) (t62b2_cut_bounds K x).2).trans h
  · rw [t62b2_cut_zero (le_of_not_ge h), zero_mul, abs_zero]
    positivity

private lemma t62b2_cut_sq (K : ℕ) (x : ℝ) :
    |t62b2_cut K x * x^2| ≤ ((K : ℝ)+1)^2 := by
  rw [abs_of_nonneg (mul_nonneg (t62b2_cut_bounds K x).1 (sq_nonneg x))]
  by_cases h : |x| ≤ (K : ℝ)+1
  · exact (mul_le_of_le_one_left (sq_nonneg x) (t62b2_cut_bounds K x).2).trans
      (by nlinarith [sq_abs x, abs_nonneg x, Nat.cast_nonneg (α := ℝ) K])
  · rw [t62b2_cut_zero (le_of_not_ge h), zero_mul]
    positivity

private lemma t62b2_cut_tendsto (x : ℝ) :
    Tendsto (fun K : ℕ => t62b2_cut K x) atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [((tendsto_natCast_atTop_atTop : Tendsto (fun K : ℕ => (K : ℝ))
    atTop atTop).eventually (eventually_ge_atTop |x|))] with K hK
  exact (t62b2_cut_one hK).symm

private lemma t62b2_bounded_integrable (P : Measure ℝ) [IsProbabilityMeasure P]
    {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    Integrable g P := by
  exact Integrable.of_bound hg.aestronglyMeasurable B (ae_of_all _ (by simpa using hB))

private def t62b2_tail (P : Measure ℝ) (K : ℕ) : ℝ :=
  ∫ x, if (K : ℝ) < |x| then x^2 else 0 ∂P

private lemma t62b2_tail_integrable (P : Measure ℝ) (h2 : MemLp id 2 P) (K : ℕ) :
    Integrable (fun x : ℝ => if (K : ℝ) < |x| then x^2 else 0) P := by
  have ht := h2.integrable_sq.indicator (s := {x : ℝ | (K : ℝ) < |x|})
    (measurableSet_lt measurable_const (by fun_prop : Measurable (fun x : ℝ => |x|)))
  apply ht.congr
  apply ae_of_all
  intro x
  by_cases hx : (K : ℝ) < |x| <;> simp [Set.indicator, hx]


private lemma t62b2_cut_integrable (P : Measure ℝ) [IsProbabilityMeasure P] (K : ℕ) :
    Integrable (t62b2_cut K) P ∧
    Integrable (fun x => t62b2_cut K x*x) P ∧
    Integrable (fun x => t62b2_cut K x*x^2) P := by
  refine ⟨t62b2_bounded_integrable P (t62b2_cut_cont K) (B := 1) (fun x => ?_),
    t62b2_bounded_integrable P ((t62b2_cut_cont K).mul continuous_id)
      (t62b2_cut_abs K),
    t62b2_bounded_integrable P ((t62b2_cut_cont K).mul (continuous_id.pow 2))
      (t62b2_cut_sq K)⟩
  rw [abs_of_nonneg (t62b2_cut_bounds K x).1]
  exact (t62b2_cut_bounds K x).2

private lemma t62b2_first_error (P : Measure ℝ) [IsProbabilityMeasure P]
    (h2 : MemLp id 2 P) {K : ℕ} (hK : 1 ≤ K) :
    |(∫ x, x ∂P) - ∫ x, t62b2_cut K x*x ∂P| ≤ t62b2_tail P K := by
  rw [← integral_sub (f := fun x : ℝ => x) (h2.integrable (by norm_num)) (t62b2_cut_integrable P K).2.1]
  rw [← Real.norm_eq_abs]
  unfold t62b2_tail
  apply norm_integral_le_of_norm_le (t62b2_tail_integrable P h2 K)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs]
  by_cases hx : |x| ≤ (K : ℝ)
  · simp [t62b2_cut_one hx, not_lt_of_ge hx]
  · have hxK : (K : ℝ) < |x| := lt_of_not_ge hx
    have hx1 : 1 ≤ |x| := (by exact_mod_cast hK : (1 : ℝ) ≤ K).trans hxK.le
    rw [if_pos hxK]
    have hw := t62b2_cut_bounds K x
    calc
      |x-t62b2_cut K x*x| = (1-t62b2_cut K x)*|x| := by
        have he : x-t62b2_cut K x*x = (1-t62b2_cut K x)*x := by ring
        rw [he, abs_mul, abs_of_nonneg (by linarith)]
      _ ≤ |x| := by nlinarith [abs_nonneg x]
      _ ≤ x^2 := by nlinarith [sq_abs x]

private lemma t62b2_second_error (P : Measure ℝ) [IsProbabilityMeasure P]
    (h2 : MemLp id 2 P) (K : ℕ) :
    |(∫ x, x^2 ∂P) - ∫ x, t62b2_cut K x*x^2 ∂P| ≤ t62b2_tail P K := by
  rw [← integral_sub (f := fun x : ℝ => x^2) h2.integrable_sq (t62b2_cut_integrable P K).2.2]
  rw [← Real.norm_eq_abs]
  unfold t62b2_tail
  apply norm_integral_le_of_norm_le (t62b2_tail_integrable P h2 K)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs]
  by_cases hx : |x| ≤ (K : ℝ)
  · simp [t62b2_cut_one hx, not_lt_of_ge hx]
  · have hxK : (K : ℝ) < |x| := lt_of_not_ge hx
    rw [if_pos hxK]
    have hw := t62b2_cut_bounds K x
    rw [abs_of_nonneg (by nlinarith [sq_nonneg x] : 0 ≤ x^2-t62b2_cut K x*x^2)]
    nlinarith [sq_nonneg x]

private lemma t62b2_tail_le_remainder (P : Measure ℝ) [IsProbabilityMeasure P]
    (h2 : MemLp id 2 P) (K L : ℕ) (hKL : K+1 ≤ L) :
    t62b2_tail P L ≤ (∫ x, x^2 ∂P) - ∫ x, t62b2_cut K x*x^2 ∂P := by
  rw [← integral_sub (f := fun x : ℝ => x^2) h2.integrable_sq (t62b2_cut_integrable P K).2.2]
  apply integral_mono (t62b2_tail_integrable P h2 L)
    (h2.integrable_sq.sub (t62b2_cut_integrable P K).2.2)
  intro x
  by_cases hx : (L : ℝ) < |x|
  · have hcut : t62b2_cut K x = 0 :=
      t62b2_cut_zero ((by exact_mod_cast hKL : (K : ℝ)+1 ≤ L).trans hx.le)
    simp [hx, hcut]
  · simp only [if_neg hx]
    change 0 ≤ x^2-t62b2_cut K x*x^2
    nlinarith [(t62b2_cut_bounds K x).2, sq_nonneg x]

private lemma t62b2_cut_mass_limit (P : Measure ℝ) [IsProbabilityMeasure P] :
    Tendsto (fun K => ∫ x, t62b2_cut K x ∂P) atTop (nhds 1) := by
  have ht := tendsto_integral_of_dominated_convergence (μ := P) (fun _ : ℝ => (1 : ℝ))
    (fun K => (t62b2_cut_cont K).aestronglyMeasurable) (integrable_const 1)
    (fun K => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (t62b2_cut_bounds K x).1]
      exact (t62b2_cut_bounds K x).2))
    (ae_of_all _ t62b2_cut_tendsto)
  simpa using ht

private lemma t62b2_cut_first_limit (P : Measure ℝ) [IsProbabilityMeasure P]
    (h2 : MemLp id 2 P) :
    Tendsto (fun K => ∫ x, t62b2_cut K x*x ∂P) atTop (nhds (∫ x, x ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun x : ℝ => |x|)
    (fun K => ((t62b2_cut_cont K).mul continuous_id).aestronglyMeasurable)
    (h2.integrable (by norm_num)).abs
  · intro K
    apply ae_of_all
    intro x
    change |t62b2_cut K x*x| ≤ |x|
    rw [abs_mul, abs_of_nonneg (t62b2_cut_bounds K x).1]
    exact mul_le_of_le_one_left (abs_nonneg x) (t62b2_cut_bounds K x).2
  · exact ae_of_all _ (fun x => by simpa using (t62b2_cut_tendsto x).mul_const x)

private lemma t62b2_cut_second_limit (P : Measure ℝ) [IsProbabilityMeasure P]
    (h2 : MemLp id 2 P) :
    Tendsto (fun K => ∫ x, t62b2_cut K x*x^2 ∂P) atTop (nhds (∫ x, x^2 ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun x : ℝ => x^2)
    (fun K => ((t62b2_cut_cont K).mul (continuous_id.pow 2)).aestronglyMeasurable)
    h2.integrable_sq
  · intro K
    apply ae_of_all
    intro x
    change |t62b2_cut K x*x^2| ≤ x^2
    rw [abs_of_nonneg (mul_nonneg (t62b2_cut_bounds K x).1 (sq_nonneg x))]
    exact mul_le_of_le_one_left (sq_nonneg x) (t62b2_cut_bounds K x).2
  · exact ae_of_all _ (fun x => by simpa using (t62b2_cut_tendsto x).mul_const (x^2))

private lemma t62b2_variance_cut (P : Measure ℝ) [IsProbabilityMeasure P]
    (h2 : MemLp id 2 P) (K : ℕ) :
    (∫ x, t62b2_cut K x*x^2 ∂P) -
      2*(∫ x, x ∂P)*(∫ x, t62b2_cut K x*x ∂P) +
      (∫ x, x ∂P)^2*(∫ x, t62b2_cut K x ∂P) ≤ var P id := by
  let a : ℝ := ∫ x, x ∂P
  have hi := t62b2_cut_integrable P K
  have he : (fun x => t62b2_cut K x*(x-a)^2) =
      (fun x => t62b2_cut K x*x^2 - (2*a)*(t62b2_cut K x*x) +
        a^2*t62b2_cut K x) := by ext x; ring
  have hwi : Integrable (fun x => t62b2_cut K x*(x-a)^2) P := by
    rw [he]
    exact (hi.2.2.sub (hi.2.1.const_mul _)).add (hi.1.const_mul _)
  have hcenter : MemLp (fun x : ℝ => x-a) 2 P := by
    exact h2.sub (memLp_const a)
  have hv := integral_mono hwi hcenter.integrable_sq (fun x =>
    mul_le_of_le_one_left (sq_nonneg (x-a)) (t62b2_cut_bounds K x).2)
  rw [he, integral_add (f := fun x => t62b2_cut K x*x^2 - (2*a)*(t62b2_cut K x*x))
    (hi.2.2.sub (hi.2.1.const_mul _)) (hi.1.const_mul _),
    integral_sub (f := fun x => t62b2_cut K x*x^2)
      (g := fun x => (2*a)*(t62b2_cut K x*x)) hi.2.2 (hi.2.1.const_mul _),
    integral_const_mul, integral_const_mul] at hv
  simpa only [var, variance_eq_integral measurable_id.aemeasurable, a, id_eq] using hv

private lemma t62b2_mean_coercive (P : Measure ℝ) [IsProbabilityMeasure P]
    (h2 : MemLp id 2 P) (K : ℕ) (hp : 1/2 ≤ ∫ x, t62b2_cut K x ∂P) :
    (∫ x, x ∂P)^2 / 4 ≤ var P id - (∫ x, t62b2_cut K x*x^2 ∂P) +
      4*(∫ x, t62b2_cut K x*x ∂P)^2 := by
  have h := t62b2_variance_cut P h2 K
  have hp' := mul_le_mul_of_nonneg_left hp (sq_nonneg (∫ x, x ∂P))
  nlinarith [sq_nonneg ((∫ x, x ∂P)/2 - 2*(∫ x, t62b2_cut K x*x ∂P))]

private lemma t62b2_cp_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : ℕ → Ω → ℝ} {z : ℝ}
    (hZ : CP μ Z z) (c : ℝ) : CP μ (fun n ω => c*Z n ω) (c*z) :=
  probability_convergence_continuous_at μ Z z (fun x : ℝ => c*x) hZ (by fun_prop)

/-- The exact iterated tail condition suffices for approximation by bounded tests.
No measurability beyond that in the stated convergence hypotheses is needed:
all event comparisons use outer-measure monotonicity and subadditivity. -/
private lemma t62b2_approx_cp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ) (W : ℕ → ℕ → Ω → ℝ) (T : ℕ → ℕ → Ω → ℝ)
    (a : ℝ) (b : ℕ → ℝ)
    (hW : ∀ K, CP μ (W K) (b K))
    (hb : Tendsto b atTop (nhds a))
    (happrox : ∀ K, 1 ≤ K → ∀ n ω, |Z n ω-W K n ω| ≤ T n K ω)
    (hT : ∀ ε : ℝ, 0 < ε → Tendsto (fun K : ℕ => Filter.limsup
      (fun n => prob μ {ω | ε < T n K ω}) atTop) atTop (nhds 0)) : CP μ Z a := by
  rw [t62b2_cp_iff]
  intro ε hε d hd
  have hba := Metric.tendsto_nhds.1 hb (ε/3) (by positivity)
  have hta := (tendsto_order.1 (hT (ε/3) (by positivity))).2 (d/2) (by positivity)
  obtain ⟨K, hK, hbK, htK⟩ := ((eventually_ge_atTop 1).and (hba.and hta)).exists
  have ht : ∀ᶠ n in atTop, prob μ {ω | ε/3 < T n K ω} < d/2 :=
    eventually_lt_of_limsup_lt htK ⟨(1 : ℝ),
      (Eventually.of_forall (fun n : ℕ => t62b2_prob_le_one μ {ω | ε/3 < T n K ω}) :
        ∀ᶠ n : ℕ in atTop, prob μ {ω | ε/3 < T n K ω} ≤ 1)⟩
  have hw := (t62b2_cp_iff μ (W K) (b K)).1 (hW K)
    (ε/3) (by positivity) (d/2) (by positivity)
  filter_upwards [ht, hw] with n htn hwn
  have hs : {ω | ε ≤ |Z n ω-a|} ⊆
      {ω | ε/3 < T n K ω} ∪ {ω | ε/3 ≤ |W K n ω-b K|} := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_le] at hn
    have h1 := happrox K hK n ω
    have h2 : |Z n ω-a| ≤ |Z n ω-W K n ω| + |W K n ω-b K| + |b K-a| := by
      calc
        _ ≤ |Z n ω-W K n ω| + |W K n ω-a| := abs_sub_le _ _ _
        _ ≤ _ := by linarith [abs_sub_le (W K n ω) (b K) a]
    rw [Real.dist_eq] at hbK
    change ε ≤ |Z n ω-a| at hω
    linarith
  have hp := (measureReal_mono hs (measure_ne_top μ _)).trans (t62b2_prob_union μ _ _)
  change prob μ _ ≤ _ at hp
  linarith

private lemma t62b2_gaussian_second (φ : ℝ) :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 ⟨φ^2, sq_nonneg _⟩) = φ^2 := by
  have hv := variance_eq_sub
    (memLp_id_gaussianReal (μ := 0) (v := ⟨φ^2, sq_nonneg _⟩) 2)
  simpa [Pi.pow_apply, id_eq, NNReal.toReal] using hv.symm

private lemma t62b2_truncation_suffices {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : ℕ → Ω → Measure ℝ) (hν : ∀ n ω, IsProbabilityMeasure (ν n ω))
    (h2 : ∀ n ω, MemLp id 2 (ν n ω)) (φ : ℝ)
    (hweak : ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      CP μ (fun n ω => mean (ν n ω) f) (mean (gaussianReal 0 ⟨φ^2,sq_nonneg _⟩) f))
    (hT : ∀ ε : ℝ, 0 < ε → Tendsto (fun K : ℕ => Filter.limsup
      (fun n => prob μ {ω | ε < t62b2_tail (ν n ω) K}) atTop) atTop (nhds 0)) :
    CP μ (fun n ω => ∫ x, x ∂ν n ω) 0 ∧
    CP μ (fun n ω => ∫ x, x^2 ∂ν n ω) (φ^2) := by
  let γ := gaussianReal 0 ⟨φ^2, sq_nonneg _⟩
  have hg : MemLp id 2 γ := memLp_id_gaussianReal 2
  constructor
  · apply t62b2_approx_cp μ _
      (fun K n ω => ∫ x, t62b2_cut K x*x ∂ν n ω)
      (fun n K ω => t62b2_tail (ν n ω) K) 0
      (fun K => ∫ x, t62b2_cut K x*x ∂γ)
    · intro K
      exact hweak _ ((t62b2_cut_cont K).mul continuous_id)
        ⟨(K : ℝ)+1, t62b2_cut_abs K⟩
    · simpa [γ] using t62b2_cut_first_limit γ hg
    · intro K hK n ω
      letI instProbabilityT62B2 : IsProbabilityMeasure (ν n ω) := hν n ω
      exact t62b2_first_error _ (h2 n ω) hK
    · exact hT
  · apply t62b2_approx_cp μ _
      (fun K n ω => ∫ x, t62b2_cut K x*x^2 ∂ν n ω)
      (fun n K ω => t62b2_tail (ν n ω) K) (φ^2)
      (fun K => ∫ x, t62b2_cut K x*x^2 ∂γ)
    · intro K
      exact hweak _ ((t62b2_cut_cont K).mul (continuous_id.pow 2))
        ⟨((K : ℝ)+1)^2, t62b2_cut_sq K⟩
    · simpa only [γ, t62b2_gaussian_second] using t62b2_cut_second_limit γ hg
    · intro K _ n ω
      letI instProbabilityT62B2 : IsProbabilityMeasure (ν n ω) := hν n ω
      exact t62b2_second_error _ (h2 n ω) K
    · exact hT

private lemma t62b2_variance_forces_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : ℕ → Ω → Measure ℝ) (hν : ∀ n ω, IsProbabilityMeasure (ν n ω))
    (h2 : ∀ n ω, MemLp id 2 (ν n ω)) (φ : ℝ)
    (hweak : ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      CP μ (fun n ω => mean (ν n ω) f) (mean (gaussianReal 0 ⟨φ^2,sq_nonneg _⟩) f))
    (hv : CP μ (fun n ω => var (ν n ω) id) (φ^2)) :
    CP μ (fun n ω => ∫ x, x ∂ν n ω) 0 := by
  let γ := gaussianReal 0 ⟨φ^2, sq_nonneg _⟩
  have hg : MemLp id 2 γ := memLp_id_gaussianReal 2
  let p := fun K => ∫ x, t62b2_cut K x ∂γ
  let b := fun K => ∫ x, t62b2_cut K x*x ∂γ
  let q := fun K => ∫ x, t62b2_cut K x*x^2 ∂γ
  have hp : Tendsto p atTop (nhds 1) := t62b2_cut_mass_limit γ
  have hb : Tendsto b atTop (nhds 0) := by simpa [γ, b] using t62b2_cut_first_limit γ hg
  have hq : Tendsto q atTop (nhds (φ^2)) := by
    simpa only [q, γ, t62b2_gaussian_second] using t62b2_cut_second_limit γ hg
  have hr : Tendsto (fun K => φ^2-q K+4*(b K)^2) atTop (nhds 0) := by
    have hc : Tendsto (fun _ : ℕ => φ^2) atTop (nhds (φ^2)) := tendsto_const_nhds
    have h4 : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4) := tendsto_const_nhds
    simpa using (hc.sub hq).add (h4.mul (hb.pow 2))
  rw [t62b2_cp_iff]
  intro ε hε d hd
  obtain ⟨K, hpK, hrK⟩ := (((tendsto_order.1 hp).1 (3/4) (by norm_num)).and
    ((tendsto_order.1 hr).2 (ε^2/8) (by positivity))).exists
  have hpCP := hweak (t62b2_cut K) (t62b2_cut_cont K)
    ⟨1, fun x => by rw [abs_of_nonneg (t62b2_cut_bounds K x).1]; exact (t62b2_cut_bounds K x).2⟩
  have hbCP := hweak (fun x => t62b2_cut K x*x) ((t62b2_cut_cont K).mul continuous_id)
    ⟨(K : ℝ)+1, t62b2_cut_abs K⟩
  have hqCP := hweak (fun x => t62b2_cut K x*x^2)
    ((t62b2_cut_cont K).mul (continuous_id.pow 2)) ⟨((K : ℝ)+1)^2, t62b2_cut_sq K⟩
  have hrCP := t62b2_cp_add μ (t62b2_cp_sub μ hv hqCP)
    (t62b2_cp_const_mul μ (t62b2_cp_sq μ hbCP) 4)
  have hep := (t62b2_cp_iff μ _ _).1 hpCP (1/4) (by norm_num) (d/2) (by positivity)
  have her := (t62b2_cp_iff μ _ _).1 hrCP (ε^2/8) (by positivity) (d/2) (by positivity)
  filter_upwards [hep, her] with n hpn hrn
  have hs : {ω | ε ≤ |(∫ x, x ∂ν n ω)-0|} ⊆
      {ω | 1/4 ≤ |(∫ x, t62b2_cut K x ∂ν n ω)-p K|} ∪
      {ω | ε^2/8 ≤ |(var (ν n ω) id-(∫ x, t62b2_cut K x*x^2 ∂ν n ω)+
        4*(∫ x, t62b2_cut K x*x ∂ν n ω)^2)-(φ^2-q K+4*(b K)^2)|} := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hn
    have hpp : 1/2 ≤ ∫ x, t62b2_cut K x ∂ν n ω := by
      have := (abs_lt.1 hn.1).1
      change 3/4 < p K at hpK
      linarith
    letI instProbabilityT62B2 : IsProbabilityMeasure (ν n ω) := hν n ω
    have hc := t62b2_mean_coercive _ (h2 n ω) K hpp
    have hrr := (abs_lt.1 hn.2).2
    simp only [Set.mem_setOf_eq, sub_zero] at hω
    have ha : ε^2 ≤ (∫ x, x ∂ν n ω)^2 := by
      nlinarith [sq_abs (∫ x, x ∂ν n ω), abs_nonneg (∫ x, x ∂ν n ω)]
    nlinarith
  have he := (measureReal_mono hs (measure_ne_top μ _)).trans (t62b2_prob_union μ _ _)
  change prob μ _ ≤ _ at he
  change prob μ {ω | ε ≤ |(∫ x, x ∂ν n ω)-0|} < d
  change prob μ _ < d/2 at hpn hrn
  dsimp only [p, b, q, γ, mean] at hpn hrn he
  linarith

private lemma t62b2_second_cp_implies_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : ℕ → Ω → Measure ℝ) (hν : ∀ n ω, IsProbabilityMeasure (ν n ω))
    (h2 : ∀ n ω, MemLp id 2 (ν n ω)) (φ : ℝ)
    (hweak : ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      CP μ (fun n ω => mean (ν n ω) f) (mean (gaussianReal 0 ⟨φ^2,sq_nonneg _⟩) f))
    (hq : CP μ (fun n ω => ∫ x, x^2 ∂ν n ω) (φ^2)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun L : ℕ => Filter.limsup
      (fun n => prob μ {ω | ε < t62b2_tail (ν n ω) L}) atTop) atTop (nhds 0) := by
  let γ := gaussianReal 0 ⟨φ^2, sq_nonneg _⟩
  have hg : MemLp id 2 γ := memLp_id_gaussianReal 2
  have hlim : Tendsto (fun K => φ^2-(∫ x, t62b2_cut K x*x^2 ∂γ)) atTop (nhds 0) := by
    have ht := t62b2_cut_second_limit γ hg
    rw [show (∫ x, x^2 ∂γ) = φ^2 from t62b2_gaussian_second φ] at ht
    have hc : Tendsto (fun _ : ℕ => φ^2) atTop (nhds (φ^2)) := tendsto_const_nhds
    simpa using hc.sub ht
  intro ε hε
  obtain ⟨K, hK⟩ := ((tendsto_order.1 hlim).2 (ε/2) (by positivity)).exists
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (K+1)] with L hL
  symm
  apply Tendsto.limsup_eq
  have hqK := hweak (fun x => t62b2_cut K x*x^2)
    ((t62b2_cut_cont K).mul (continuous_id.pow 2)) ⟨((K : ℝ)+1)^2, t62b2_cut_sq K⟩
  have hr := t62b2_cp_sub μ hq hqK
  have hc := hr (ε/2) (by positivity)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ hc
  intro n
  apply measureReal_mono _ (measure_ne_top μ _)
  intro ω hω
  change ε < t62b2_tail (ν n ω) L at hω
  letI instProbabilityT62B2 : IsProbabilityMeasure (ν n ω) := hν n ω
  have ht := t62b2_tail_le_remainder _ (h2 n ω) K L hL
  change ε/2 ≤ |(∫ x, x^2 ∂ν n ω)-(∫ x, t62b2_cut K x*x^2 ∂ν n ω)-
    (φ^2-(∫ x, t62b2_cut K x*x^2 ∂γ))|
  exact (by linarith : ε/2 ≤ (∫ x, x^2 ∂ν n ω)-(∫ x, t62b2_cut K x*x^2 ∂ν n ω)-
    (φ^2-(∫ x, t62b2_cut K x*x^2 ∂γ))).trans (le_abs_self _)

theorem bootstrap_moments_correction_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (ν : ℕ → Ω → Measure ℝ) (hν : ∀ n ω, IsProbabilityMeasure (ν n ω))
   (hKernel : ∀ n (A : Set ℝ),MeasurableSet A → Measurable (fun ω => ν n ω A))
   (h2 : ∀ n ω, MemLp id 2 (ν n ω)) (φ : ℝ) (hφ : 0 < φ)
   (hweak : ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
     CP μ (fun n ω => mean (ν n ω) f) (mean (gaussianReal 0 ⟨φ^2,sq_nonneg _⟩) f)) :
   ( (∀ ε : ℝ, 0 < ε → Tendsto (fun K : ℕ => Filter.limsup
       (fun (n : ℕ) => prob μ {ω | ε  <  ∫ x, if (K : ℝ) <  |x| then x^2 else 0 ∂(ν n ω)}) atTop)
       atTop (nhds 0)) ↔ CP μ (fun n ω => var (ν n ω) id) (φ^2)) ∧
   (CP μ (fun n ω => var (ν n ω) id) (φ^2) →
     CP μ (fun n ω => Real.sqrt (var (ν n ω) id)) φ) := by
  have hvEq (n : ℕ) (ω : Ω) : var (ν n ω) id =
      (∫ x, x^2 ∂ν n ω)-(∫ x, x ∂ν n ω)^2 := by
    letI instProbabilityT62B2 : IsProbabilityMeasure (ν n ω) := hν n ω
    exact variance_eq_sub (h2 n ω)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hT
    obtain ⟨ha, hq⟩ := t62b2_truncation_suffices μ ν hν h2 φ hweak hT
    have hv := t62b2_cp_sub μ hq (t62b2_cp_sq μ ha)
    simpa only [hvEq, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] using hv
  · intro hv
    have ha := t62b2_variance_forces_mean μ ν hν h2 φ hweak hv
    have hq := t62b2_cp_add μ hv (t62b2_cp_sq μ ha)
    have he (n : ℕ) (ω : Ω) : var (ν n ω) id+(∫ x, x ∂ν n ω)^2 = ∫ x, x^2 ∂ν n ω := by
      rw [hvEq]; ring
    simp only [he, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hq
    exact t62b2_second_cp_implies_tails μ ν hν h2 φ hweak hq
  · intro hv
    have hs := probability_convergence_continuous_at μ (fun n ω => var (ν n ω) id)
      (φ^2) Real.sqrt hv Real.continuous_sqrt.continuousAt
    simpa only [Real.sqrt_sq hφ.le] using hs

end
end AronowAudit.P001.Wave1
