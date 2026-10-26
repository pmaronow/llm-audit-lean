import AronowAudit.P029.Wave1.Gap.GP029B3b

/-!
P029-T16: the corrected Winsorization limit.

Finite covariate support permits a direct uniform-score argument: a
positive-mass profile attains the smallest true score, and its empirical
frequency eventually exceeds the fraction below the type-7 cutoff.
The general proved ICSW limit then applies to the Winsorized scores.
-/

namespace AronowAudit.P029.Wave1

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Finite measurable profiles partition every integrable moment. -/
lemma wcl_profile_integral {Ω X : Type*} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} {T : Ω → X} (hT : Measurable T)
    {v : Ω → ℝ} (hv : Integrable v μ) (w : X → ℝ) :
    (∫ ω, w (T ω) * v ω ∂μ) =
      ∑ x : X, w x * (∫ ω in {ω | T ω = x}, v ω ∂μ) := by
  have hcell (x : X) : MeasurableSet {ω | T ω = x} :=
    hT (measurableSet_singleton x)
  calc
    _ = ∫ ω, ∑ x : X, ({ω | T ω = x}.indicator (fun ω => w x * v ω)) ω ∂μ := by
      congr 1
      funext ω
      simp [Set.indicator]
    _ = ∑ x : X, ∫ ω, ({ω | T ω = x}.indicator (fun ω => w x * v ω)) ω ∂μ :=
      integral_finsetSum _ (fun x _ => (hv.const_mul (w x)).indicator (hcell x))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [integral_indicator (hcell x), integral_const_mul]

lemma wcl_profile_mean {Ω X : Type*} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → X}
    (hT : Measurable T) (w : X → ℝ) :
    (∫ ω, w (T ω) ∂μ) = ∑ x : X, mP μ {ω | T ω = x} * w x := by
  simpa [setIntegral_const, mP, measureReal_def, mul_comm] using
    wcl_profile_integral hT (integrable_const (1 : ℝ)) w

lemma wcl_null_cell {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {A : Set Ω}
    (hA : mP μ A = 0) : μ A = 0 :=
  ((ENNReal.toReal_eq_zero_iff _).mp hA).resolve_right (measure_ne_top μ A)

lemma wcl_mass_mul_mean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (v : Ω → ℝ) (A : Set Ω) :
    mP μ A * mCE μ v A = ∫ ω in A, v ω ∂μ := by
  by_cases hA : mP μ A = 0
  · have hz : μ.restrict A = 0 := Measure.restrict_eq_zero.mpr (wcl_null_cell hA)
    simp [mCE, hA, hz]
  · unfold mCE
    field_simp [hA]

/-- A finite-valued observation almost surely belongs to a positive-mass cell. -/
lemma wcl_ae_positive_cell {Ω X : Type*} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (T : Ω → X) :
    ∀ᵐ ω ∂μ, 0 < mP μ {η | T η = T ω} := by
  have hall (x : X) : ∀ᵐ ω ∂μ, T ω = x → 0 < mP μ {η | T η = x} := by
    by_cases hx : 0 < mP μ {η | T η = x}
    · exact Filter.Eventually.of_forall (fun _ _ => hx)
    · have hz : μ {η | T η = x} = 0 :=
        wcl_null_cell (le_antisymm (le_of_not_gt hx) ENNReal.toReal_nonneg)
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with ω hω
      exact fun h => False.elim (hω h)
  filter_upwards [ae_all_iff.mpr hall] with ω hω
  exact hω (T ω) rfl

/-- A positive-mass profile attaining the smallest score on the population support. -/
lemma wcl_minimal_profile {Ω X : Type*} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → X}
    (hT : Measurable T) (c : X → ℝ) :
    ∃ x : X, 0 < mP μ {ω | T ω = x} ∧
      ∀ y, 0 < mP μ {ω | T ω = y} → c x ≤ c y := by
  let S := Finset.univ.filter (fun x => 0 < mP μ {ω | T ω = x})
  have hmass : (∑ x : X, mP μ {ω | T ω = x}) = 1 := by
    simpa using (wcl_profile_mean (μ := μ) hT (fun _ => (1 : ℝ))).symm
  have hS : S.Nonempty := by
    by_contra hn
    have hz (x : X) : mP μ {ω | T ω = x} = 0 := by
      apply le_antisymm _ ENNReal.toReal_nonneg
      apply le_of_not_gt
      intro hx
      exact hn ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    simp only [hz, Finset.sum_const_zero] at hmass
    norm_num at hmass
  obtain ⟨x, hx, hmin⟩ := S.exists_min_image c hS
  refine ⟨x, (Finset.mem_filter.mp hx).2, ?_⟩
  intro y hy
  exact hmin y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)

/-- Interpolation keeps the quantile below every common upper bound. This
also covers the initial sample of size one and level one. -/
lemma wcl_quantile_upper {n : ℕ} (s : Fin (n+1) → ℝ) (level cutoff b : ℝ)
    (hq : Type7Quantile s level cutoff) (hs : ∀ i, s i ≤ b) : cutoff ≤ b := by
  obtain ⟨π, _, j, hj, hj1, hc⟩ := hq
  have hγ0 : 0 ≤ (n : ℝ) * level - j.val := by linarith
  have hγ1 : (n : ℝ) * level - j.val ≤ 1 := by linarith
  have h0 := mul_nonneg (sub_nonneg.mpr hγ1) (sub_nonneg.mpr (hs (π j)))
  have h1 := mul_nonneg hγ0 (sub_nonneg.mpr (hs (π (nextOrderIndex j))))
  nlinarith

/-- If a minimum-score profile is more frequent than the quantile's changed
fraction, replacing scores by the cutoff cannot increase their uniform error. -/
lemma wcl_clipped_error_bound {n : ℕ} (p s : Fin (n+1) → ℝ)
    (A : Fin (n+1) → Prop) (level cutoff a r : ℝ)
    (hlevel : level ∈ Ioo (0 : ℝ) 1) (hq : Type7Quantile s level cutoff)
    (hp : ∀ i, a ≤ p i) (hA : ∀ i, A i → p i = a)
    (herr : ∀ i, |s i - p i| ≤ r)
    (hfreq : level + 1/(n+1) <
      ((Finset.univ.filter A).card : ℝ)/(n+1)) :
    ∀ i, |max (s i) cutoff - p i| ≤ r := by
  classical
  have hs : ∀ i, a-r ≤ s i := by
    intro i
    have := (abs_le.mp (herr i)).1
    linarith [hp i]
  have hcount := (quantile_count_and_lower_bound s level cutoff (a-r) hlevel hq hs).2.1
  have hcut : cutoff ≤ a+r := by
    by_contra hc
    have hsub : Finset.univ.filter A ⊆ Finset.univ.filter (fun i => s i < cutoff) := by
      intro i hi
      have hiA := (Finset.mem_filter.mp hi).2
      have hierr := (abs_le.mp (herr i)).2
      rw [hA i hiA] at hierr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by linarith⟩
    have hcard : ((Finset.univ.filter A).card : ℝ) ≤ (belowCount s cutoff : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hN : (0 : ℝ) < n+1 := by positivity
    have hle := div_le_div_of_nonneg_right hcard hN.le
    linarith
  intro i
  apply abs_le.mpr
  constructor
  · have := (abs_le.mp (herr i)).1
    linarith [le_max_left (s i) cutoff]
  · have hi := (abs_le.mp (herr i)).2
    have : max (s i) cutoff ≤ p i+r := max_le (by linarith) (by linarith [hp i])
    linarith

lemma wcl_uniform_error_measurable {Ω X : Type*} [MeasurableSpace Ω]
    (U : ℕ → Ω → PotentialUnit X) (c : X → ℝ) (s : ℕ → ℕ → Ω → ℝ)
    (hc : ∀ i, Measurable (fun ω => c (U i ω).x))
    (hs : ∀ n i, Measurable (s n i)) (n : ℕ) :
    Measurable (uniformScoreError U c s n) := by
  exact Finset.measurable_range_sup'' (fun i _ => ((hs n i).sub (hc i)).abs)

lemma wcl_uniform_error_nonneg {Ω X : Type*} (U : ℕ → Ω → PotentialUnit X)
    (c : X → ℝ) (s : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ uniformScoreError U c s n ω := by
  exact (abs_nonneg (s n 0 ω - c (U 0 ω).x)).trans
    (Finset.le_sup' (fun i : ℕ => |s n i ω - c (U i ω).x|)
      (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

lemma wcl_identical_profile_mass {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} {U : ℕ → Ω → PotentialUnit X} {Z : ℕ → Ω → Bool}
    {c m : X → ℝ} {s : ℕ → ℕ → Ω → ℝ} (h : ICSWConditions μ U Z c m s)
    (i : ℕ) (x : X) :
    mP μ {ω | (U i ω).x = x} = mP μ {ω | (U 0 ω).x = x} := by
  have hid := (h.identical i).comp (measurable_fst.comp measurable_fst)
  have hm := hid.measure_mem_eq (measurableSet_singleton x)
  exact congrArg ENNReal.toReal hm

/-- The iid strong law for the frequency of one profile, including null profiles. -/
lemma wcl_profile_frequency {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : ℕ → Ω → PotentialUnit X}
    {Z : ℕ → Ω → Bool} {c m : X → ℝ} {s : ℕ → ℕ → Ω → ℝ}
    (h : ICSWConditions μ U Z c m s) (x : X) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      ((Finset.univ.filter (fun i : Fin (n+1) => (U i ω).x = x)).card : ℝ)/(n+1))
      atTop (𝓝 (mP μ {ω | (U 0 ω).x = x})) := by
  let F : (X × Bool × Bool × ℝ × ℝ) × Bool → ℝ :=
    fun t => if t.1.1 = x then 1 else 0
  have hF : Measurable F := Measurable.ite
    ((measurable_fst.comp measurable_fst) (measurableSet_singleton x))
    measurable_const measurable_const
  have hcell : MeasurableSet {ω | (U 0 ω).x = x} :=
    (h.iv 0).1 (measurableSet_singleton x)
  have hi : Integrable (fun ω => F (jointVariables (U 0) (Z 0) ω)) μ :=
    (integrable_const (1 : ℝ)).indicator hcell
  have hmean : (∫ ω, F (jointVariables (U 0) (Z 0) ω) ∂μ) =
      mP μ {ω | (U 0 ω).x = x} := by
    simpa [F, jointVariables, Set.indicator_apply, mP, measureReal_def] using
      (integral_indicator_one (μ := μ) hcell)
  have hlln := GP029B3b_iid_average h F hF hi
  rw [hmean] at hlln
  simpa [F, jointVariables] using hlln

lemma wcl_quantile_level_bound (α : ℝ) (hα : 0 < α) :
    Tendsto (fun n : ℕ => (((n+1 : ℕ) : ℝ)^(-α)) + 1/(n+1)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  simpa [one_div] using
    ((tendsto_rpow_neg_atTop hα).comp hcast).add (tendsto_inv_atTop_zero.comp hcast)

/-- With finite covariate support, the clipped scores retain the original
uniform consistency. A repeated minimum-score profile controls the cutoff,
so no bounded-outcome or independence assumption on fitted scores is needed. -/
lemma wcl_clipped_uniform_consistency {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : ℕ → Ω → PotentialUnit X}
    {Z : ℕ → Ω → Bool} {c m : X → ℝ} {s : ℕ → ℕ → Ω → ℝ}
    (cutoff : ℕ → Ω → ℝ) (h : ICSWConditions μ U Z c m s)
    (α : ℝ) (hα : 0 < α) (hcmeas : ∀ n, Measurable (cutoff n))
    (hquantile : ∀ n, ∀ᵐ ω ∂μ, Type7Quantile
      (fun i : Fin (n+1) => s n i ω) (((n+1 : ℕ) : ℝ)^(-α)) (cutoff n ω)) :
    TendstoInMeasure μ
      (uniformScoreError U c (fun n i ω => max (s n i ω) (cutoff n ω)))
      atTop (fun _ => 0) := by
  obtain ⟨x, hx, hmin⟩ := wcl_minimal_profile (μ := μ) (h.iv 0).1 c
  have hsupp : ∀ᵐ ω ∂μ, ∀ i, 0 < mP μ {η | (U 0 η).x = (U i ω).x} := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [wcl_ae_positive_cell (μ := μ) (fun ω => (U i ω).x)] with ω hω
    rwa [wcl_identical_profile_mass h i] at hω
  have hfreq := wcl_profile_frequency h x
  have hqa := ae_all_iff.mpr hquantile
  have hcm : ∀ i, Measurable (fun ω => c (U i ω).x) :=
    fun i => (h.score i).1.comp (h.iv i).1
  have hsm : ∀ n i, Measurable (fun ω => max (s n i ω) (cutoff n ω)) :=
    fun n i => (h.estimated_measurable n i).max (hcmeas n)
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n =>
    (wcl_uniform_error_measurable U c _ hcm hsm n).aestronglyMeasurable)).2
  intro ns hns
  obtain ⟨ks, hks, heae⟩ :=
    (h.uniform_consistency.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ks, hks, ?_⟩
  filter_upwards [hsupp, hfreq, hqa, heae] with ω hω hf hq he
  let a : ℕ → ℕ := fun k => ns (ks k)
  have hat : Tendsto a atTop atTop := hns.tendsto_atTop.comp hks.tendsto_atTop
  have htail : ∀ᶠ n : ℕ in atTop,
      (((n+1 : ℕ) : ℝ)^(-α)) + 1/(n+1) <
        ((Finset.univ.filter (fun i : Fin (n+1) => (U i ω).x = x)).card : ℝ)/(n+1) := by
    filter_upwards [(wcl_quantile_level_bound α hα).eventually
      (gt_mem_nhds (show 0 < mP μ {η | (U 0 η).x = x}/2 by linarith)),
      hf.eventually (lt_mem_nhds (show mP μ {η | (U 0 η).x = x}/2 <
        mP μ {η | (U 0 η).x = x} by linarith))] with n hn hf'
    exact hn.trans hf'
  have hbound : ∀ᶠ k in atTop,
      uniformScoreError U c (fun n i ω => max (s n i ω) (cutoff n ω)) (a k) ω ≤
        uniformScoreError U c s (a k) ω := by
    filter_upwards [hat.eventually htail, hat.eventually (eventually_ge_atTop (1 : ℕ))]
      with k hk hn
    have hN0 : (0 : ℝ) < ((a k+1 : ℕ) : ℝ) := by positivity
    have hN1 : (1 : ℝ) < ((a k+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < a k+1)
    have hlevel : (((a k+1 : ℕ) : ℝ)^(-α)) ∈ Ioo (0 : ℝ) 1 :=
      ⟨Real.rpow_pos_of_pos hN0 _,
        Real.rpow_lt_one_of_one_lt_of_neg hN1 (neg_lt_zero.mpr hα)⟩
    have herr (i : Fin (a k+1)) : |s (a k) i ω - c (U i ω).x| ≤
        uniformScoreError U c s (a k) ω :=
      Finset.le_sup' (fun j : ℕ => |s (a k) j ω - c (U j ω).x|)
        (Finset.mem_range.mpr i.isLt)
    have hpoint := wcl_clipped_error_bound
      (fun i : Fin (a k+1) => c (U i ω).x) (fun i => s (a k) i ω)
      (fun i => (U i ω).x = x) _ (cutoff (a k) ω) (c x)
      (uniformScoreError U c s (a k) ω) hlevel (hq (a k))
      (fun i => hmin _ (hω i)) (fun i hi => by rw [hi]) herr hk
    apply Finset.sup'_le
    intro i hi
    exact hpoint ⟨i, Finset.mem_range.mp hi⟩
  exact squeeze_zero'
    (Filter.Eventually.of_forall (fun k => wcl_uniform_error_nonneg U c _ (a k) ω))
    hbound he

/-- The same regularity conditions hold after Winsorizing the estimated scores. -/
lemma wcl_clipped_conditions {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : ℕ → Ω → PotentialUnit X}
    {Z : ℕ → Ω → Bool} {c m : X → ℝ} {s : ℕ → ℕ → Ω → ℝ}
    (cutoff : ℕ → Ω → ℝ) (h : ICSWConditions μ U Z c m s)
    (α : ℝ) (hα : 0 < α) (hcmeas : ∀ n, Measurable (cutoff n))
    (hquantile : ∀ n, ∀ᵐ ω ∂μ, Type7Quantile
      (fun i : Fin (n+1) => s n i ω) (((n+1 : ℕ) : ℝ)^(-α)) (cutoff n ω)) :
    ICSWConditions μ U Z c m (fun n i ω => max (s n i ω) (cutoff n ω)) := by
  refine {
    iv := h.iv
    independent := h.independent
    identical := h.identical
    score := h.score
    overlap := h.overlap
    estimated_measurable := fun n i => (h.estimated_measurable n i).max (hcmeas n)
    estimated_range := ?_
    uniform_consistency := wcl_clipped_uniform_consistency cutoff h α hα hcmeas hquantile }
  intro n
  filter_upwards [h.estimated_range n, hquantile n] with ω hr hq
  have hcut := wcl_quantile_upper (fun i : Fin (n+1) => s n i ω)
    _ (cutoff n ω) 1 hq (fun i => (hr i).2)
  intro i
  exact ⟨lt_of_lt_of_le (hr i).1 (le_max_left _ _), max_le (hr i).2 hcut⟩

/-- Integrating a profile function over one of its cells gives mass times value. -/
lemma wcl_cell_integral {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} {T : Ω → X} (hT : Measurable T) (w : X → ℝ) (x : X) :
    (∫ ω in {ω | T ω = x}, w (T ω) ∂μ) = mP μ {ω | T ω = x} * w x := by
  calc
    _ = ∫ _ in {ω | T ω = x}, w x ∂μ :=
      setIntegral_congr_fun (hT (measurableSet_singleton x)) (fun ω hω => by rw [hω])
    _ = _ := by simp [mP, measureReal_def]

/-- Restricting an event indicator to a profile intersects the two events. -/
lemma wcl_event_cell_integral {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} {T : Ω → X} (hT : Measurable T)
    {C : Set Ω} (hC : MeasurableSet C) (v : Ω → ℝ) (x : X) :
    (∫ ω in {ω | T ω = x}, (if ω ∈ C then v ω else 0) ∂μ) =
      ∫ ω in {ω | ω ∈ C ∧ T ω = x}, v ω ∂μ := by
  have hA : MeasurableSet {ω | T ω = x} := hT (measurableSet_singleton x)
  have hset : {ω | ω ∈ C ∧ T ω = x} = C ∩ {ω | T ω = x} := rfl
  rw [hset, ← integral_indicator hA, ← integral_indicator (hC.inter hA)]
  congr 1
  funext ω
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs <;> simp_all

/-- The two conditional-expectation versions give exact identities on every
measurable profile cell, including the zero-mass cells. -/
lemma wcl_profile_versions {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Ω → PotentialUnit X}
    {Z : Ω → Bool} (hiv : IVAssumptions μ U Z) {c m : X → ℝ}
    (hv : ScoreVersions μ U c m) (x : X) :
    mP μ {ω | (U ω).x = x} * c x = mP μ {ω | (U ω).complier ∧ (U ω).x = x} ∧
    mP μ {ω | (U ω).x = x} * c x * m x =
      ∫ ω in {ω | (U ω).complier ∧ (U ω).x = x}, (U ω).tau ∂μ := by
  have hG : covariateSigma U ≤ ‹MeasurableSpace Ω› := hiv.1.comap_le
  have hAG : MeasurableSet[covariateSigma U] {ω | (U ω).x = x} :=
    ⟨{x}, measurableSet_singleton x, rfl⟩
  have hC := GP029B3b_appendix_complier_measurable hiv
  have hscore : (∫ ω in {ω | (U ω).x = x}, c (U ω).x ∂μ) =
      ∫ ω in {ω | (U ω).x = x}, if (U ω).complier then (1 : ℝ) else 0 ∂μ := by
    calc
      _ = ∫ ω in {ω | (U ω).x = x}, condExp (covariateSigma U) μ
          (fun ω => if (U ω).complier then (1 : ℝ) else 0) ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hv.2.2.1)
      _ = _ := setIntegral_condExp hG (GP029B3b_appendix_indicator_integrable hiv) hAG
  have heffect : (∫ ω in {ω | (U ω).x = x}, c (U ω).x * m (U ω).x ∂μ) =
      ∫ ω in {ω | (U ω).x = x}, if (U ω).complier then (U ω).tau else 0 ∂μ := by
    calc
      _ = ∫ ω in {ω | (U ω).x = x}, condExp (covariateSigma U) μ
          (fun ω => if (U ω).complier then (U ω).tau else 0) ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hv.2.2.2)
      _ = _ := setIntegral_condExp hG (GP029B3b_appendix_effect_integrable hiv) hAG
  constructor
  · have hcell := wcl_event_cell_integral (μ := μ) hiv.1 hC (fun _ => (1 : ℝ)) x
    simp only [Set.mem_setOf_eq] at hcell
    rw [wcl_cell_integral hiv.1 c x, hcell] at hscore
    simpa only [setIntegral_const, smul_eq_mul, mul_one, mP, measureReal_def] using hscore
  · have hcell := wcl_event_cell_integral (μ := μ) hiv.1 hC (fun ω => (U ω).tau) x
    simp only [Set.mem_setOf_eq] at hcell
    rw [wcl_cell_integral hiv.1 (fun x => c x * m x) x, hcell] at heffect
    simpa only [mul_assoc] using heffect

/-- Finite-profile identification of the general ICSW probability limit. -/
lemma wcl_finite_limit {Ω X : Type*} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Ω → PotentialUnit X}
    {Z : Ω → Bool} (hiv : IVAssumptions μ U Z) {c m : X → ℝ}
    (hv : ScoreVersions μ U c m) (ε : ℝ) (he : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε < c (U ω).x ∧ c (U ω).x ≤ 1) :
    (∫ ω, m (U ω).x ∂μ) =
      ∑ x, mP μ {ω | (U ω).x = x} * complierAt μ U x := by
  have hcx (x : X) (hx : 0 < mP μ {ω | (U ω).x = x}) : 0 < c x := by
    have hμ : μ {ω | (U ω).x = x} ≠ 0 := by
      intro hz
      simp [mP, hz] at hx
    obtain ⟨ω, hω, hbound⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hμ (ae_restrict_of_ae hpos)
    change (U ω).x = x at hω
    rw [hω] at hbound
    exact lt_trans he hbound.1
  have hm (x : X) (hx : 0 < mP μ {ω | (U ω).x = x}) : m x = complierAt μ U x := by
    obtain ⟨hq, hqm⟩ := wcl_profile_versions hiv hv x
    have hqpos : 0 < mP μ {ω | (U ω).complier ∧ (U ω).x = x} := by
      rw [← hq]
      exact mul_pos hx (hcx x hx)
    unfold complierAt mCE
    apply (eq_div_iff (ne_of_gt hqpos)).mpr
    calc
      m x * mP μ {ω | (U ω).complier ∧ (U ω).x = x} =
          mP μ {ω | (U ω).x = x} * c x * m x := by rw [← hq]; ring
      _ = _ := hqm
  rw [wcl_profile_mean hiv.1 m]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : mP μ {ω | (U ω).x = x} = 0
  · simp [hx]
  · rw [hm x (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hx))]

/-- The displayed profilewise latent-ignorability premise identifies the
finite limit with the population average effect. -/
lemma wcl_A1_identification {Ω X : Type*} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Ω → PotentialUnit X}
    {Z : Ω → Bool} (hiv : IVAssumptions μ U Z)
    (hlat : ∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) :
    (∑ x, mP μ {ω | (U ω).x = x} * complierAt μ U x) =
      ∫ ω, (U ω).tau ∂μ := by
  have hpartition : (∫ ω, (U ω).tau ∂μ) =
      ∑ x, ∫ ω in {ω | (U ω).x = x}, (U ω).tau ∂μ := by
    simpa using wcl_profile_integral hiv.1 (GP029B3b_appendix_tau_integrable hiv)
      (fun _ => (1 : ℝ))
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro x _
  rw [← wcl_mass_mul_mean (fun ω => (U ω).tau) {ω | (U ω).x = x}]
  by_cases hx : mP μ {ω | (U ω).x = x} = 0
  · simp [hx]
  · have ht := hlat x (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hx))
    change mCE μ (fun ω => (U ω).tau) {ω | (U ω).x = x} = complierAt μ U x at ht
    rw [ht]

/-- P029-T16: the corrected Winsorization limit. -/
theorem winsorization_corrected_limit_proof {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ)
    (cutoff : ℕ → Ω → ℝ) (h : ICSWConditions μ U Z c m s) (α : ℝ) (hα : 0 < α)
    (hA3 : ∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < mP μ {ω | (U 0 ω).x = x} →
      ε < scoreAt μ (U 0) x ∧ scoreAt μ (U 0) x ≤ 1)
    (hcmeas : ∀ n, Measurable (cutoff n))
    (hquantile : ∀ n, ∀ᵐ ω ∂μ,
      Type7Quantile (fun i : Fin (n+1) => s n i.val ω)
        (((n+1 : ℕ) : ℝ)^(-α)) (cutoff n ω)) :
    TendstoInMeasure μ (fun n ω => winsorizedSequence U Z s cutoff n ω -
      icswSequence U Z s n ω) atTop (fun _ => 0) ∧
    TendstoInMeasure μ (icswSequence U Z s) atTop
      (fun _ => ∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) ∧
    TendstoInMeasure μ (winsorizedSequence U Z s cutoff) atTop
      (fun _ => ∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) ∧
    ((∀ x, 0 < mP μ {ω | (U 0 ω).x = x} → latentAt μ (U 0) x) →
      (∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) = ∫ ω, (U 0 ω).tau ∂μ) := by
  -- The overlap field of `h` already supplies the bound needed below.
  clear hA3
  have hclip := wcl_clipped_conditions cutoff h α hα hcmeas hquantile
  have hi := GP029B3b_icsw_limit h
  have hw := GP029B3b_icsw_limit hclip
  change TendstoInMeasure μ (winsorizedSequence U Z s cutoff) atTop
    (fun _ => ∫ ω, m (U 0 ω).x ∂μ) at hw
  obtain ⟨ε, he, hpos⟩ := h.overlap
  have hfinite := wcl_finite_limit (h.iv 0) (h.score 0) ε he (hpos 0)
  have hdiff := AronowAudit.P015.ConvergenceCompletion.sub_limit μ hw hi
  refine ⟨by simpa only [sub_self] using hdiff, ?_, ?_, ?_⟩
  · simpa only [hfinite] using hi
  · simpa only [hfinite] using hw
  · exact wcl_A1_identification (h.iv 0)

end

end AronowAudit.P029.Wave1
