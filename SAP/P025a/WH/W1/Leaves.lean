import SAP.P025a.Defs.WholeW1
import SAP.P025a.Bridge
import AronowAudit.P025.P025_Interval
import AronowAudit.P025.P025_PrintedRefutations
import AronowAudit.P025.Wave1.Gap.FidP025

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a.WH.W1
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- The exact four-coordinate residual and its sign. Expand the finite sums;
the box gives sum w ≥ 4. Clear the positive denominator, use ring, and use
nonnegativity of the four slacks. Expected proof: 20-40 lines. -/
def T10_L1 : Prop :=
  ∀ w : Fin 4 → ℝ, normBox 2 w →
    0 < ∑ i, w i ∧
    ratio fourOutcomes (fun _ => 1) w - 7/6 = wholeTailSlack w / (6*∑ i, w i) ∧
    0 ≤ wholeTailSlack w / (6*∑ i, w i)

/-- Equality is unique over the entire real box. Clear the strictly positive
sum of weights in the ratio equation. The four nonnegative slacks have
positive coefficients 7,1,5,11, so each vanishes. Finish by extensionality
and finite cases; evaluate the converse. Expected proof: 40-70 lines. -/
def T10_L2 : Prop :=
  ∀ w : Fin 4 → ℝ, normBox 2 w →
    (ratio fourOutcomes (fun _ => 1) w = 7/6 ↔ w = ![2,2,1,1])

/-- Both numerical sample residual certificates. The box implies u+v>0;
field_simp and ring prove the equalities and positivity proves the signs.
Expected proof: 15-30 lines. -/
def T1_L1 : Prop := wholeSampleTwoResiduals

/-- The sample-mean residual and the exact first-coordinate change.
Parenthesize each difference inside the finite sum, and distribute that
sum for the first identity. Use threshold_increment
at zero and threshold_den_update to obtain n+gamma-1 for the second
denominator. Sortedness gives the residual sign. Expected proof: 40-80 lines. -/
def T1_L2V2 : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ), Monotone y →
    ∀ γ : ℝ, 1 ≤ γ →
      populationMean y - y ⟨0,hn⟩ = (∑ i, (y i - y ⟨0,hn⟩)) / n ∧
      0 ≤ (∑ i, (y i - y ⟨0,hn⟩)) / n ∧
      lowerValue y (fun _ => 1) γ 1 - populationMean y =
        (γ-1)*(y ⟨0,hn⟩ - populationMean y) / ((n : ℝ) + (γ-1))

/-- Both numerical class-total residual certificates. The box implies
u/2+v>0 and u+2v>0. Clear these denominators, use ring, and prove the
slack signs from the box. Expected proof: 20-40 lines. -/
def T2_L1 : Prop := wholeClassTwoResiduals

/-- Affine segments in the original positive box are feasible and have a
positive sum of weights; their ratios are continuous on [0,1]. Prove the
coordinate bounds by convexity, positivity by a finite nonempty sum, and
continuity by ContinuousOn.div with finite sums of affine functions.
No differentiability, distinctness, or strict bound gap is required.
Expected proof: 40-80 lines. -/
def T3_L1 : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (y : Fin n → ℝ) (α β : ℝ),
    0 < α → α ≤ β → ∀ wL wH : Fin n → ℝ,
    weightBox α β wL → weightBox α β wH →
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      weightBox α β (wholeSegment wL wH t) ∧
      0 < ∑ i, wholeSegment wL wH t i) ∧
    ContinuousOn (fun t => ratio y (fun _ => 1) (wholeSegment wL wH t)) (Set.Icc 0 1)

/-- Count the two parts of an upper threshold, including k=0 and k=n.
Split the finite sum with sum_ite; count Fin intervals (or use a Fin n
prefix embedding) and cast Nat subtraction using k≤n. This is a polynomial
identity, also valid for n=0. Expected proof: 30-80 lines. -/
def T11_L1 : Prop :=
  ∀ (n : ℕ) (γ : ℝ) (k : ℕ), k ≤ n →
    (∑ i : Fin n, upperWeights γ k i) = (k : ℝ) + γ * ((n-k : ℕ) : ℝ)

/-- Regroup the actual unit population by its represented outcome classes.
Surjectivity gives positive fiber sizes. Use Finset.sum_fiberwise, or
grouped_numerator with constant weights, for the cardinality and outcome
sums. This identifies the class mean with the unit population mean.
Expected proof: 60-120 lines. -/
def T11_L2 : Prop :=
  ∀ {N J : ℕ}, 0 < N → 0 < J →
    ∀ (z : Fin N → ℝ) (y : Fin J → ℝ) (cls : Fin N → Fin J),
    Function.Surjective cls → (∀ i, z i = y (cls i)) →
    (∀ j, 0 < wholeClassSize cls j) ∧
    (∑ j, wholeClassSize cls j) = N ∧
    (∑ j, (wholeClassSize cls j : ℝ)*y j) /
      (∑ j, (wholeClassSize cls j : ℝ)) = populationMean z

/-- Equal probabilities make the class box and its entire image singletons.
For positive integer sizes m and c>0, cancel c*m in the true class weights,
and use class_mean_ratio for the objective. The box forces every weight
to 1/c. Exhibit that vector to prove equality of sets, then use the
singleton infimum/supremum lemmas. Expected proof: 70-140 lines. -/
def T11_L3 : Prop :=
  ∀ {J : ℕ}, 0 < J → ∀ (y : Fin J → ℝ) (m : Fin J → ℕ),
    (∀ j, 0 < m j) → ∀ c : ℝ, 0 < c →
    let mass := fun j => c * (m j : ℝ)
    let μ := (∑ j, (m j : ℝ)*y j) / (∑ j, (m j : ℝ))
    (∀ j, (m j : ℝ)/mass j = 1/c) ∧
    ratio y mass (fun j => (m j : ℝ)/mass j) = μ ∧
    (∀ w : Fin J → ℝ, weightBox c c w ↔ w = fun _ => 1/c) ∧
    attainable y mass c c = {μ} ∧
    IsLeast (attainable y mass c c) μ ∧ IsGreatest (attainable y mass c c) μ ∧
    lowerEndpoint y mass c c = μ ∧ upperEndpoint y mass c c = μ


private theorem restrictedT1 : T1Statement := by
  refine ⟨AronowAudit.P025.sample_sign_counterexample,
    AronowAudit.P025.sample_counterexample_range, ?_, ?_⟩
  · exact ⟨AronowAudit.P025.twoDesign.nonnegative, AronowAudit.P025.twoDesign.total,
      AronowAudit.P025.two_design_realizes_example⟩
  · intro n hn y hy γ _
    refine ⟨AronowAudit.P025.printed_lower_rule_always_zero hn y (fun _ => 1)
      hy (fun _ => zero_lt_one) γ, ?_, ?_⟩
    · simp [lowerValue, ratio, lowerWeights, populationMean]
    · exact AronowAudit.P025.printed_lower_vector_not_optimal hn y (fun _ => 1)
        hy (fun _ => zero_lt_one) γ


private theorem restrictedT2 : T2Statement := by
  exact AronowAudit.P025.class_sign_counterexample


private theorem restrictedT3 : T3Statement := by
  intro n hn y hy α β hα hab hb1
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hβ : 0 < β := hα.trans_le hab
  have hγ : 1 ≤ β/α := (le_div_iff₀ hα).2 (by linarith)
  have hγp : 0 < β/α := div_pos hβ hα
  have hlow (k : ℕ) (i : Fin n) : 0 < lowerWeights (β/α) k i := by
    dsimp [lowerWeights]; split <;> positivity
  have hhigh (k : ℕ) (i : Fin n) : 0 < upperWeights (β/α) k i := by
    dsimp [upperWeights]; split <;> positivity
  have hlast (i : Fin n) : y i ≤ y ⟨n-1, by omega⟩ :=
    hy (by have := i.isLt; change i.val ≤ n-1; omega)
  refine ⟨?_, ?_, ?_⟩
  · exact AronowAudit.P025.ratio_le y (fun _ => 1) _ (fun _ => zero_lt_one)
      (hhigh (n-1)) _ hlast
  · exact AronowAudit.P025.ratio_le y (fun _ => 1) _ (fun _ => zero_lt_one)
      (hlow (n-1)) _ hlast
  obtain ⟨kL,kH,hL,hH,hwL,hwH,heL,heH,hl,hh,el,eh,hr⟩ :=
    AronowAudit.P025.corrected_weighted_bounds hn y (fun _ => 1)
      (fun _ => zero_lt_one) hy α β hα hab hb1
  refine ⟨kL,kH,⟨hL,hH,hwL,hwH,heL,heH,hl,hh,el,eh,hr⟩,?_,?_,?_⟩
  · intro z hz
    have hLB : normBox (β/α) (lowerWeights (n:=n) (β/α) kL.val) := by
      intro i; dsimp [lowerWeights]; split <;> exact ⟨by linarith, by linarith⟩
    have hHB : normBox (β/α) (upperWeights (n:=n) (β/α) kH.val) := by
      intro i; dsimp [upperWeights]; split <;> exact ⟨by linarith, by linarith⟩
    obtain ⟨t,ht,hbox,hval⟩ := AronowAudit.P025.Wave1.ratio_segment_attains_certificate
      y (fun _ => 1) (fun _ => zero_lt_one) (β/α) _ _ hLB hHB z hz
    refine ⟨t,ht,?_,?_⟩
    · apply (AronowAudit.P025.normalize_box α β hα hab _).2
      simpa only [← mul_assoc, one_div, mul_inv_cancel₀ hβ.ne', one_mul] using hbox
    · exact (AronowAudit.P025.ratio_scale_weights y (fun _ => 1) _ (1/β)
        (one_div_ne_zero hβ.ne')).trans hval
  · intro k
    constructor
    · simpa only [← Bridge.ratio_eq, Bridge.threshold_lower, Bridge.threshold_upper,
        lowerValue, upperValue, one_mul, mul_one] using
        AronowAudit.P025.threshold_increment hn (fun _ => 1) y (fun _ => zero_lt_one)
          (β/α) 1 hγp zero_lt_one k
    · simpa only [← Bridge.ratio_eq, Bridge.threshold_lower, Bridge.threshold_upper,
        lowerValue, upperValue, one_mul, mul_one] using
        AronowAudit.P025.threshold_increment hn (fun _ => 1) y (fun _ => zero_lt_one)
          1 (β/α) zero_lt_one hγp k
  · dsimp only
    have hs := AronowAudit.P025.threshold_separator hn (fun _ => 1) y
      (fun _ => zero_lt_one) hy (β/α) 1 hγp zero_lt_one kL hL
    refine ⟨hs.1,hs.2,?_⟩
    intro u hu
    have hdu := AronowAudit.P025.denominator_pos (fun _ => 1) u
      (fun _ => zero_lt_one) (fun i => lt_of_lt_of_le zero_lt_one (hu i).1)
    have hdl := AronowAudit.P025.denominator_pos (fun _ => 1)
      (lowerWeights (β/α) kL.val) (fun _ => zero_lt_one) (hlow kL.val)
    refine ⟨?_,?_,sub_nonneg.mpr (AronowAudit.P025.lower_threshold_optimal hn
      (fun _ => 1) y (fun _ => zero_lt_one) hy (β/α) hγ kL hL u hu)⟩
    · simpa only [← Bridge.ratio_eq, lowerValue, one_mul] using AronowAudit.P025.ratio_difference_residual y
        (fun _ => 1) u (lowerWeights (β/α) kL.val) hdu.ne' hdl.ne'
    · intro i
      by_cases hi : i.val < kL.val
      · apply mul_nonneg_of_nonpos_of_nonpos
        · simpa only [lowerWeights, ite_eq_left hi] using sub_nonpos.mpr (hu i).2
        · exact (sub_neg.mpr (hs.1 i hi)).le
      · apply mul_nonneg
        · simpa only [lowerWeights, ite_eq_right hi] using sub_nonneg.mpr (hu i).1
        · exact sub_nonneg.mpr (hs.2 i (by omega))


private theorem restrictedT10 : T10Statement := by
  obtain ⟨hi,ht,hsize,hm⟩ := AronowAudit.P025.tail_design_realizes_example
  refine ⟨AronowAudit.P025.tail_index_counterexample,
    ⟨AronowAudit.P025.fourClassDesign.nonnegative, AronowAudit.P025.fourClassDesign.total,
      hi,ht,hsize,hm⟩,?_,?_,?_⟩
  · norm_num [lowerValue,ratio,lowerWeights,fourOutcomes,Fin.sum_univ_succ]
  · norm_num [lowerValue,ratio,lowerWeights,fourOutcomes,Fin.sum_univ_succ]
  · intro j
    change ((Finset.univ.filter (fun i => AronowAudit.P025.sixTailClass i = j)).card : ℝ) /
      AronowAudit.P025.classTotal AronowAudit.P025.fourClassDesign
        AronowAudit.P025.sixTailClass j = lowerWeights 2 2 j
    rw [hsize j,ht j]
    fin_cases j <;> norm_num [lowerWeights]


private theorem restrictedT11 : T11Statement := by
  refine ⟨?_,@AronowAudit.P025.pair_difference_identities,@AronowAudit.P025.pair_boundary_repair⟩
  intro n hn y hy γ hγ
  obtain ⟨hinc,hsets⟩ := AronowAudit.P025.Wave1.gamma_stationarity_certificate hn y
    (fun _ => 1) (fun _ => zero_lt_one) γ hγ
  refine ⟨?_,?_,hsets,?_,?_⟩
  · simpa only [← Bridge.upperValue_eq, ← Bridge.upperWeights_eq, one_mul, mul_one] using hinc
  · intro h k
    subst γ
    exact AronowAudit.P025.equal_probability_thresholds y k
  · intro k hk
    exact AronowAudit.P025.upper_cut_persistence hn y (fun _ => 1)
      (fun _ => zero_lt_one) hy γ hγ k hk
  · intro hstrict k
    have h := Set.ext_iff.mp (hsets hstrict) k
    simpa only [← Bridge.upperValue_eq, Set.mem_ofPred_eq, sub_nonpos] using h

private theorem original_lower_eq {n : ℕ} (α β : ℝ) (hβ : β ≠ 0) (k : ℕ) :
    wholeLowerWeights (n:=n) α β k =
      (fun i => (1/β)*lowerWeights (β/α) k i) := by
  funext i
  by_cases hi : i.val < k
  · simp only [wholeLowerWeights, lowerWeights, ite_eq_left hi]
    field_simp
  · simp [wholeLowerWeights, lowerWeights, hi]

private theorem original_upper_eq {n : ℕ} (α β : ℝ) (hβ : β ≠ 0) (k : ℕ) :
    wholeUpperWeights (n:=n) α β k =
      (fun i => (1/β)*upperWeights (β/α) k i) := by
  funext i
  by_cases hi : i.val < k
  · simp [wholeUpperWeights, upperWeights, hi]
  · simp only [wholeUpperWeights, upperWeights, ite_eq_right hi]
    field_simp

private theorem zero_diagnosis {n : ℕ} (hn : 0 < n) (y a : Fin n → ℝ)
    (hy : Monotone y) (ha : ∀ i, 0 < a i) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) : wholeZeroDiagnosis hn y a α β := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have : NeZero n := ⟨hn.ne'⟩
  have hβ : 0 < β := hα.trans_le hab
  have hi : 1/β ≤ 1/α := one_div_le_one_div_of_le hα hab
  have hw (k : ℕ) : weightBox α β (wholeLowerWeights (n:=n) α β k) := by
    intro i
    dsimp [wholeLowerWeights]
    split <;> exact ⟨by first | exact hi | rfl, by first | exact hi | rfl⟩
  have hv (k : ℕ) : ratio y a (wholeLowerWeights α β k) =
      lowerValue y a (β/α) k := by
    rw [original_lower_eq α β hβ.ne']
    exact AronowAudit.P025.ratio_scale_weights y a _ (1/β) (one_div_ne_zero hβ.ne')
  have hm : lowerValue y a (β/α) 0 = (∑ i, a i*y i)/(∑ i, a i) := by
    simp [lowerValue, ratio, lowerWeights]
  dsimp [wholeZeroDiagnosis]
  refine ⟨AronowAudit.P025.printed_lower_rule_always_zero hn y a hy ha (β/α),
    by funext i; simp [wholeLowerWeights], hw 0, hm, (hv 0).trans hm, ?_, ?_⟩
  · have h : y ⟨0,hn⟩ ≤ ratio y a (fun _ => 1) :=
      AronowAudit.P025.le_ratio y a (fun _ => 1) ha
        (fun _ => zero_lt_one) (y ⟨0,hn⟩) (fun i => hy (Fin.zero_le i))
    simpa [ratio] using h
  · intro hγ hvar
    have hdec := (AronowAudit.P025.printed_lower_vector_not_optimal
      hn y a hy ha (β/α) hγ hvar).1
    have hd : ratio y a (wholeLowerWeights α β 1) < (∑ i, a i*y i)/(∑ i, a i) := by
      rw [hv 1, ← hm]
      exact hdec
    refine ⟨hw 1, hd, ?_⟩
    intro hmin
    exact (not_le_of_gt hd) (hmin.2 ⟨_, hw 1, rfl⟩)

/-- Whole six-unit counterexample, conditional only on its two algebra leaves. -/
theorem T10_assembly (h1 : T10_L1) (h2 : T10_L2) : T10WholeStatement := by
  have hb := restrictedT10
  rcases hb.1 with ⟨hmono,hcut,hval,hprinted,hzero,hundef,hne,hbound⟩
  have hbox : normBox 2 (lowerWeights (n:=4) 2 2) := by
    intro i; fin_cases i <;> norm_num [lowerWeights]
  have hmin : IsLeast (attainable fourOutcomes (fun _ => 1) (1/2) 1) (7/6) := by
    constructor
    · exact ⟨lowerWeights 2 2, by simpa [weightBox, normBox] using hbox, hval⟩
    · rintro v ⟨w,hw,rfl⟩
      exact hbound w (by simpa [weightBox, normBox] using hw)
  refine ⟨hb, ?_, ?_⟩
  · intro w hw
    exact ⟨(h1 w hw).1,(h1 w hw).2.1,(h1 w hw).2.2,h2 w hw⟩
  · refine ⟨?_,?_,hbox,hmin,hmin.csInf_eq⟩
    · intro i
      rw [hb.2.1.2.2.1 i]
      fin_cases i <;> norm_num
    · intro i
      fin_cases i <;> norm_num [sixTailOutcomes, sixTailClass, fourOutcomes]

/-- Whole sample counterexample and the general original-scale diagnosis. -/
theorem T1_assembly (h1 : T1_L1) (h2 : T1_L2V2) : T1WholeStatement := by
  refine ⟨restrictedT1,h1,?_,?_,h2,?_⟩
  · intro b c
    cases b <;> cases c <;> norm_num [twoProbability, twoSample, Fin.sum_univ_two]
  · refine ⟨?_,?_,?_,?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [ratio, binaryTwo, Fin.sum_univ_two]
    · intro i; fin_cases i <;> norm_num
    · norm_num [ratio, binaryTwo, Fin.sum_univ_two]
  · intro n hn y hy α β hα hab _
    refine ⟨zero_diagnosis hn y (fun _ => 1) hy (fun _ => zero_lt_one) α β hα hab,?_⟩
    have hβ : 0 < β := hα.trans_le hab
    have hv : ratio y (fun _ => 1) (wholeLowerWeights α β 1) =
        lowerValue y (fun _ => 1) (β/α) 1 := by
      rw [original_lower_eq α β hβ.ne']
      exact AronowAudit.P025.ratio_scale_weights y (fun _ => 1) _ (1/β)
        (one_div_ne_zero hβ.ne')
    rw [hv]
    exact (h2 hn y hy (β/α) ((le_div_iff₀ hα).2 (by linarith))).2.2

private theorem two_replication : wholeTwoReplication := by
  have hi := AronowAudit.P025.joint_replications_iid AronowAudit.P025.twoDesign
  refine ⟨?_,?_,hi.1,hi.2,?_,?_,?_,?_,?_⟩
  · change IsProbabilityMeasure (AronowAudit.P025.jointLaw AronowAudit.P025.twoDesign)
    infer_instance
  · intro ω
    simp [wholeTwoPMF]
  · exact hi.1.comp (fun _ => twoSample) (fun _ => measurable_of_countable _)
  · intro h; simp
  · intro h ω ri; simp [wholeTwoPooledSample]
  · intro h hh
    have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    simp [Fintype.sum_prod_type, binaryTwo, Fin.sum_univ_two, Nat.cast_mul]
    field_simp
  · intro h hh ω
    refine ⟨(⟨0,hh⟩,1), ?_⟩
    simp only [wholeTwoPooledSample, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only [twoSample]
    split <;> simp

private theorem two_classes : wholeTwoClasses := by
  have hi := AronowAudit.P025.two_design_realizes_example
  have htotal (j : Fin 2) : designClassTotal twoSample twoProbability id j = twoPi j := by
    simpa [designClassTotal, Finset.sum_filter] using
      (show designInclusion twoSample twoProbability j = twoPi j from hi.1 j)
  have hfiber (j : Fin 2) : Finset.univ.filter (fun i : Fin 2 => binaryTwo i = binaryTwo j) = {j} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    fin_cases i <;> fin_cases j <;> norm_num [binaryTwo]
  refine ⟨hfiber,htotal,?_,?_⟩
  · intro j; rw [hfiber j, htotal j]
    fin_cases j <;> norm_num [twoPi]
  · norm_num [ratio, populationMean, binaryTwo, twoPi, Fin.sum_univ_two]

/-- Whole class-total counterexample, with its actual iid sampling realization. -/
theorem T2_assembly (h1 : T2_L1) : T2WholeStatement := by
  have hbounds := restrictedT2.2.2.2.2.2.2.2.2.2
  have hmin : IsLeast (attainable binaryTwo twoPi (1/2) 1) (1/2) := by
    constructor
    · refine ⟨![2,1],?_,?_⟩
      · intro i; fin_cases i <;> norm_num [weightBox]
      · norm_num [ratio, binaryTwo, twoPi, Fin.sum_univ_two]
    · rintro v ⟨w,hw,rfl⟩
      have hu := hw 0
      have hv := hw 1
      have he := hbounds (w 0) (w 1) (by norm_num at hu ⊢; exact hu.1)
        (by norm_num at hu ⊢; exact hu.2) (by norm_num at hv ⊢; exact hv.1)
        (by norm_num at hv ⊢; exact hv.2)
      simpa [ratio,binaryTwo,twoPi,Fin.sum_univ_two,div_eq_mul_inv,mul_comm] using he.1
  have hmax : IsGreatest (attainable binaryTwo twoPi (1/2) 1) (4/5) := by
    constructor
    · refine ⟨![1,2],?_,?_⟩
      · intro i; fin_cases i <;> norm_num [weightBox]
      · norm_num [ratio, binaryTwo, twoPi, Fin.sum_univ_two]
    · rintro v ⟨w,hw,rfl⟩
      have hu := hw 0
      have hv := hw 1
      have he := hbounds (w 0) (w 1) (by norm_num at hu ⊢; exact hu.1)
        (by norm_num at hu ⊢; exact hu.2) (by norm_num at hv ⊢; exact hv.1)
        (by norm_num at hv ⊢; exact hv.2)
      simpa [ratio,binaryTwo,twoPi,Fin.sum_univ_two,div_eq_mul_inv,mul_comm] using he.2
  refine ⟨restrictedT2,two_replication,two_classes,h1,?_,hmin,hmax,?_⟩
  · constructor
    · norm_num [upperValue,ratio,upperWeights,binaryTwo,twoPi,Fin.sum_univ_two]
    · intro j hj
      fin_cases j
      · norm_num [upperValue,ratio,upperWeights,binaryTwo,twoPi,Fin.sum_univ_two] at hj
      · rfl
  · intro J hJ y mass hy hm α β hα hab _
    have hd := zero_diagnosis hJ y mass hy.monotone hm α β hα hab
    refine ⟨hd,?_⟩
    intro hγ hJ2
    have hv : ∃ i : Fin J, y ⟨0,hJ⟩ < y i := ⟨⟨1,by omega⟩,hy (by show (0:ℕ) < 1; omega)⟩
    simpa only [hd.2.2.2.2.1] using (hd.2.2.2.2.2.2 hγ hv).2.2

/-- Whole corrected sample bounds, including segment continuity and the
original-scale form of the termwise residual certificate. -/
theorem T3_assembly (h1 : T3_L1) : T3WholeStatement := by
  refine ⟨restrictedT3,?_⟩
  intro n hn y hy α β hα hab _ kL kH hc
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hβ : 0 < β := hα.trans_le hab
  have hγ : 1 ≤ β/α := (le_div_iff₀ hα).2 (by linarith)
  have hγp : 0 < β/α := div_pos hβ hα
  constructor
  · exact h1 hn y α β hα hab _ _ hc.2.2.1 hc.2.2.2.1
  · intro w hw
    have hu : normBox (β/α) (fun i => β*w i) :=
      (AronowAudit.P025.normalize_box α β hα hab w).1 hw
    have hs := AronowAudit.P025.threshold_separator hn (fun _ => 1) y
      (fun _ => zero_lt_one) hy (β/α) 1 hγp zero_lt_one kL hc.1
    have hdu := AronowAudit.P025.denominator_pos (fun _ => 1) (fun i => β*w i)
      (fun _ => zero_lt_one) (fun i => lt_of_lt_of_le zero_lt_one (hu i).1)
    have hdl := AronowAudit.P025.denominator_pos (fun _ : Fin n => 1)
      (lowerWeights (n:=n) (β/α) kL.val) (fun _ => zero_lt_one) (by
        intro i; dsimp [lowerWeights]; split <;> positivity)
    have hscale : ratio y (fun _ => 1) (fun i => β*w i) = ratio y (fun _ => 1) w :=
      AronowAudit.P025.ratio_scale_weights y (fun _ => 1) w β hβ.ne'
    dsimp only
    refine ⟨hu,?_,?_,?_⟩
    · have he := AronowAudit.P025.ratio_difference_residual y (fun _ => 1)
        (fun i => β*w i) (lowerWeights (β/α) kL.val) hdu.ne' hdl.ne'
      simpa only [← Bridge.ratio_eq, one_mul, hscale, lowerValue] using he
    · intro i
      by_cases hi : i.val < kL.val
      · apply mul_nonneg_of_nonpos_of_nonpos
        · simpa [lowerWeights,hi] using sub_nonpos.mpr (hu i).2
        · exact (sub_neg.mpr (hs.1 i hi)).le
      · apply mul_nonneg
        · simpa [lowerWeights,hi] using sub_nonneg.mpr (hu i).1
        · exact sub_nonneg.mpr (hs.2 i (by omega))
    · rw [← hscale]
      exact sub_nonneg.mpr (AronowAudit.P025.lower_threshold_optimal hn (fun _ => 1)
        y (fun _ => zero_lt_one) hy (β/α) hγ kL hc.1 _ hu)

private theorem sample_proof_repair (hcount : T11_L1) : wholeSampleProofRepair := by
  intro n hn y hy α β hα hab hb1
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have : NeZero n := ⟨hn.ne'⟩
  have hβ : 0 < β := hα.trans_le hab
  have hγ : 1 ≤ β/α := (le_div_iff₀ hα).2 (by linarith)
  have hγp : 0 < β/α := div_pos hβ hα
  have hs := restrictedT11.1 hn y hy (β/α) hγ
  have hden (k : ℕ) : 0 < ∑ i : Fin n, upperWeights (β/α) k i := by
    simpa only [one_mul] using AronowAudit.P025.denominator_pos (fun _ => 1)
      (upperWeights (β/α) k) (fun _ => zero_lt_one) (by
        intro i; dsimp [upperWeights]; split <;> positivity)
  have hcut : ∃ kH : Fin n, upperCut y (fun _ => 1) (β/α) kH :=
    AronowAudit.P025.threshold_cut_exists hn (fun _ => 1) y (fun _ => zero_lt_one)
      hy 1 (β/α) zero_lt_one hγp
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k hk
    refine ⟨?_,?_,hcount n (β/α) k hk,?_,?_⟩
    · intro i
      have hi := one_div_le_one_div_of_le hα hab
      dsimp [wholeUpperWeights]
      split <;> exact ⟨by first | exact hi | rfl, by first | exact hi | rfl⟩
    · rw [original_upper_eq α β hβ.ne']
      exact AronowAudit.P025.ratio_scale_weights y (fun _ => 1) _ (1/β)
        (one_div_ne_zero hβ.ne')
    · rw [← hcount n (β/α) k hk]
      exact hden k
    · simp only [upperValue,ratio,one_mul]
      rw [hcount n (β/α) k hk]
      congr 1
      simp only [upperWeights, ite_mul, one_mul, Finset.sum_ite, not_lt,
        ← Finset.mul_sum]
  · intro k
    rw [← hcount n (β/α) (k.val+1) (by omega)]
    exact hs.1 k
  · intro heq
    have hba : β = α := (div_eq_one_iff_eq hα.ne').1 heq
    have he := AronowAudit.P025.equal_probability_box_and_endpoints hn y α β hα hab hb1 heq
    have hvalues (k : ℕ) : upperValue y (fun _ => 1) (β/α) k = populationMean y :=
      (hs.2.1 heq k).1
    obtain ⟨kH,hH⟩ := hcut
    refine ⟨hba.symm,he.1,?_,he.2.1,he.2.2,?_,?_,?_⟩
    · intro k
      exact ⟨by funext i; simp [wholeUpperWeights,hba],hvalues k⟩
    · have hlast (i : Fin n) : y i ≤ y ⟨n-1,by omega⟩ := hy (by
        change i.val ≤ n-1; omega)
      have hl : ratio y (fun _ => 1) (fun _ => 1) ≤ y ⟨n-1,by omega⟩ :=
        AronowAudit.P025.ratio_le y (fun _ => 1)
          (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ hlast
      simpa [ratio,populationMean] using hl
    · refine ⟨kH,?_,hH,hvalues kH.val⟩
      have hset : {k : Fin n | upperValue y (fun _ => 1) (β/α) k.val ≤ y k} =
          {k : Fin n | populationMean y ≤ y k} := by
        ext k
        change (upperValue y (fun _ => 1) (β/α) k.val ≤ y k) ↔ populationMean y ≤ y k
        rw [hvalues k.val]
      change IsLeast {k : Fin n | upperValue y (fun _ => 1) (β/α) k.val ≤ y k} kH at hH
      rw [hset] at hH
      exact hH
    · constructor
      · change upperValue y (fun _ => 1) (β/α) 0 ≥ upperValue y (fun _ => 1) (β/α) 1
        rw [hvalues 0,hvalues 1]
      · intro j _; exact Fin.zero_le j
  · intro hstrict
    obtain ⟨kH,hH⟩ := hcut
    have hstat : IsLeast {k : Fin n | upperValue y (fun _ => 1) (β/α) k.val ≥
        upperValue y (fun _ => 1) (β/α) (k.val+1)} kH := by
      rw [hs.2.2.1 hstrict]
      exact hH
    have hmax (j : ℕ) : upperValue y (fun _ => 1) (β/α) j ≤
        upperValue y (fun _ => 1) (β/α) kH.val := by
      apply AronowAudit.P025.upper_threshold_optimal hn (fun _ => 1) y
        (fun _ => zero_lt_one) hy (β/α) hγ kH hH
      intro i; dsimp [upperWeights]; split <;> exact ⟨by linarith,by linarith⟩
    refine ⟨kH,hH,hstat,fun j _ => hmax j,?_,?_⟩
    · exact ⟨kH.val,by omega,rfl⟩
    · rintro v ⟨j,_,rfl⟩; exact hmax j
  · intro k hk
    refine ⟨hs.2.2.2.1 k hk,?_⟩
    intro hk1
    apply hy
    change k.val ≤ k.val+1
    omega

private theorem population_boundary (hgroup : T11_L2) (hsingle : T11_L3) :
    wholePopulationBoundary := by
  intro N J hN hJ z y cls _ hsurj hz c hc _ π hπ
  obtain ⟨hmpos,hsize,hmean⟩ := hgroup hN hJ z y cls hsurj hz
  have heq (i : Fin N) : π i = c := le_antisymm (hπ i).2 (hπ i).1
  have hmass (j : Fin J) : wholeClassMass cls π j = c * wholeClassSize cls j := by
    simp [wholeClassMass,heq,wholeClassSize,Finset.sum_const,nsmul_eq_mul,mul_comm]
  have hmassfun : wholeClassMass cls π = fun j => c * (wholeClassSize cls j : ℝ) :=
    funext hmass
  have h := hsingle hJ y (wholeClassSize cls) hmpos c hc
  dsimp only at h
  rw [← hmassfun,hmean] at h
  rcases h with ⟨htrue,hr,hbox,hset,hl,hh,el,eh⟩
  dsimp only
  refine ⟨heq,?_,hsize,hmean,?_,hbox,hset,hl,hh,el,eh⟩
  · intro j
    refine ⟨hmpos j,hmass j,?_,?_⟩
    · rw [hmass j]
      exact mul_pos hc (by exact_mod_cast hmpos j)
    · rw [hmass j]
      exact htrue j
  · simpa only [← hmass] using hr

/-- Whole repaired proof: counting and two small class-population leaves
complete the existing normalized and pair-improvement certificates. -/
theorem T11_assembly (h1 : T11_L1) (h2 : T11_L2) (h3 : T11_L3) : T11WholeStatement := by
  refine ⟨restrictedT11,sample_proof_repair h1,population_boundary h2 h3,?_⟩
  intro c₂ p q a b hc hp hq ha _ x hx z hz
  have hxp : 0 < x*p := mul_pos (ha.trans_le hx.1) hp
  have hzq : 0 < z*q := mul_pos (ha.trans_le hz.1) hq
  linarith

end
end SAP.P025a.WH.W1
