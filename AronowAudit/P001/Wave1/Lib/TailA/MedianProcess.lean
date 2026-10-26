import AronowAudit.P001.Wave1.Lib.TailA.BernoulliRows

/-! Monotone local empirical processes and random thresholds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
universe u
local instance instDecidableMedianProcess (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

/-- Addition of scalar convergence-in-probability statements. -/
theorem medianProcess_cp_add {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {U V : ℕ → Ω → ℝ} {a b : ℝ}
    (hU : CP μ U a) (hV : CP μ V b) : CP μ (fun n ω => U n ω + V n ω) (a+b) := by
  intro ε hε
  have hbound (n : ℕ) :
      prob μ {ω | ε ≤ dist (U n ω + V n ω) (a+b)} ≤
        prob μ {ω | ε/2 ≤ dist (U n ω) a} + prob μ {ω | ε/2 ≤ dist (V n ω) b} := by
    apply le_trans (measureReal_mono (s₂ := {ω | ε/2 ≤ dist (U n ω) a} ∪
      {ω | ε/2 ≤ dist (V n ω) b}) ?_ (measure_ne_top μ _))
    · exact measureReal_union_le _ _
    · intro ω hω
      by_contra hn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hn
      have ht := dist_add_add_le (U n ω) (V n ω) a b
      exact (not_lt_of_ge hω) (ht.trans_lt (by linarith [hn.1, hn.2]))
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound
    (by simpa using (hU (ε/2) (by positivity)).add (hV (ε/2) (by positivity)))

/-- A deterministic convergent sequence is also convergent in probability. -/
theorem medianProcess_cp_deterministic {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℕ → ℝ) (b : ℝ)
    (ha : Tendsto a atTop (𝓝 b)) : CP μ (fun n _ => a n) b := by
  intro ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [ha.eventually (Metric.ball_mem_nhds b hε)] with n hn
  have he : {ω : Ω | ε ≤ dist (a n) b} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact hn
  simp [he, prob]

/-- A measurable scalar weak limit gives asymptotic tightness, in the form needed
for inserting a random threshold into a local empirical process. -/
theorem medianProcess_tight_of_cd {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (G : Measure ℝ) [IsProbabilityMeasure G]
    [NullSingletonClass G] (h : CD μ Z G) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧
      ∀ᶠ n in atTop, prob μ {ω | B < |Z n ω|} ≤ η := by
  intro η hη
  have hc := bernoulliRows_cdf_continuous G
  have heCDF : (fun R : ℝ => G.real (Set.Iic R)) = ProbabilityTheory.cdf G := by
    funext R
    exact (cdf_eq_real G R).symm
  have hhi : Tendsto (fun R : ℝ => G.real (Set.Iic R)) atTop (𝓝 1) := by
    rw [heCDF]
    exact tendsto_cdf_atTop G
  have hlo : Tendsto (fun R : ℝ => G.real (Set.Iic (-R))) atTop (𝓝 0) := by
    change Tendsto ((fun R : ℝ => G.real (Set.Iic R)) ∘ Neg.neg) atTop (𝓝 0)
    rw [heCDF]
    exact (tendsto_cdf_atBot G).comp tendsto_neg_atTop_atBot
  obtain ⟨B, hB, hBl, hBh⟩ : ∃ B : ℝ, 0 < B ∧
      G.real (Set.Iic (-B)) < η/4 ∧ 1-η/4 < G.real (Set.Iic B) := by
    obtain ⟨B, hB⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      ((hlo.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < η/4))).and
        (hhi.eventually (eventually_gt_nhds (by linarith : 1-η/4 < (1 : ℝ)))))).exists
    exact ⟨B, hB.1, hB.2.1, hB.2.2⟩
  refine ⟨B, hB, ?_⟩
  have hleft := (h (-B) hc.continuousAt).eventually (eventually_lt_nhds
    (show prob G (Set.Iic (-B)) < η/2 by change G.real _ < _; linarith))
  have hright := (h B hc.continuousAt).eventually (eventually_gt_nhds
    (show 1-η/2 < prob G (Set.Iic B) by change _ < G.real _; linarith))
  filter_upwards [hleft, hright] with n hl hr
  have he : prob μ {ω | B < Z n ω} = 1 - cdf μ (Z n) B := by
    have hh := measureReal_compl (μ := μ) (measurableSet_le (hZ n) (measurable_const (a := B)))
    simpa only [cdf, prob, Measure.real, Set.compl_setOf, not_le, measure_univ, ENNReal.toReal_one] using hh
  calc
    prob μ {ω | B < |Z n ω|} ≤ prob μ ({ω | Z n ω ≤ -B} ∪ {ω | B < Z n ω}) :=
      measureReal_mono (fun ω hω => by
        change B < |Z n ω| at hω
        by_cases hz : B < Z n ω
        · exact Or.inr hz
        · left
          have hZB : Z n ω ≤ B := not_lt.mp hz
          by_contra hh
          change ¬Z n ω ≤ -B at hh
          have hbnd : |Z n ω| ≤ B := abs_le.mpr ⟨by linarith, hZB⟩
          exact (not_lt_of_ge hbnd) hω) (measure_ne_top μ _)
    _ ≤ prob μ {ω | Z n ω ≤ -B} + prob μ {ω | B < Z n ω} := measureReal_union_le _ _
    _ ≤ η := by rw [he]; change cdf μ (Z n) (-B) + (1-cdf μ (Z n) B) ≤ η; linarith

/-- Finite meshes and monotonicity upgrade pointwise local limits to random-threshold
linearization. The threshold only needs tightness; it need not converge. -/
theorem medianProcess_random_threshold {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ → ℝ)
    (d : ℝ) (hd : 0 ≤ d) (hmono : ∀ n ω, Monotone (U n ω))
    (hpoint : ∀ t : ℝ, CP μ (fun n ω => U n ω t) (d*t))
    (T : ℕ → Ω → ℝ)
    (htight : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧
      ∀ᶠ n in atTop, prob μ {ω | B < |T n ω|} ≤ η) :
    CP μ (fun n ω => U n ω (T n ω) - d*T n ω) 0 := by
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le ENNReal.toReal_nonneg
  · intro η hη
    obtain ⟨B, hB, htail⟩ := htight (η/2) (by positivity)
    let δ : ℝ := ε / (8*(d+1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hsmall : 2*d*δ < ε/2 := by
      dsimp [δ]
      have hden : 0 < 8*(d+1) := by positivity
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hden).mpr
      nlinarith
    obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover
      (fun t : ℝ => Set.Ioo (t-δ) (t+δ)) (fun _ => isOpen_Ioo)
      (show Set.Icc (-B) B ⊆ ⋃ t : ℝ, Set.Ioo (t-δ) (t+δ) from by
        intro x _
        exact Set.mem_iUnion.mpr ⟨x, by constructor <;> linarith⟩)
    let E := fun n t => {ω | ε/4 ≤ dist (U n ω (t-δ)) (d*(t-δ))} ∪
      {ω | ε/4 ≤ dist (U n ω (t+δ)) (d*(t+δ))}
    have hE (t : ℝ) : Tendsto (fun n => prob μ (E n t)) atTop (𝓝 0) := by
      exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
        (fun _ => measureReal_union_le _ _)
        (by simpa [prob, Measure.real] using ((hpoint (t-δ) (ε/4) (by positivity)).add
          (hpoint (t+δ) (ε/4) (by positivity))))
    have hsum : Tendsto (fun n => ∑ t ∈ s, prob μ (E n t)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum s (fun t _ => hE t)
    filter_upwards [htail, hsum.eventually (eventually_lt_nhds (show (0 : ℝ) < η/2 by positivity))]
      with n htn hsn
    have hsub : {ω | ε ≤ dist (U n ω (T n ω) - d*T n ω) 0} ⊆
        {ω | B < |T n ω|} ∪ ⋃ t ∈ s, E n t := by
      intro ω hω
      by_cases hb : B < |T n ω|
      · exact Or.inl hb
      · right
        have ht : T n ω ∈ Set.Icc (-B) B := abs_le.mp (not_lt.mp hb)
        obtain ⟨t, hts, hcover⟩ := Set.mem_iUnion₂.mp (hs ht)
        by_contra hn
        have hnot : ω ∉ E n t := by
          intro he
          exact hn (Set.mem_iUnion₂.mpr ⟨t, hts, he⟩)
        have hl : |U n ω (t-δ) - d*(t-δ)| < ε/4 := by
          apply lt_of_not_ge
          intro he
          exact hnot (Or.inl he)
        have hr : |U n ω (t+δ) - d*(t+δ)| < ε/4 := by
          apply lt_of_not_ge
          intro he
          exact hnot (Or.inr he)
        have hmlo := hmono n ω hcover.1.le
        have hmhi := hmono n ω hcover.2.le
        change ε ≤ dist (U n ω (T n ω) - d*T n ω) 0 at hω
        rw [Real.dist_eq, sub_zero] at hω
        have hbad : |U n ω (T n ω) - d*T n ω| < ε := by
          rw [abs_lt] at hl hr ⊢
          constructor <;> nlinarith [mul_nonneg hd (sub_nonneg.mpr hcover.1.le),
            mul_nonneg hd (sub_nonneg.mpr hcover.2.le)]
        exact (not_lt_of_ge hω) hbad
    calc
      prob μ {ω | ε ≤ dist (U n ω (T n ω) - d*T n ω) 0} ≤
          prob μ ({ω | B < |T n ω|} ∪ ⋃ t ∈ s, E n t) :=
        measureReal_mono hsub (measure_ne_top μ _)
      _ ≤ prob μ {ω | B < |T n ω|} + prob μ (⋃ t ∈ s, E n t) := measureReal_union_le _ _
      _ ≤ prob μ {ω | B < |T n ω|} + ∑ t ∈ s, prob μ (E n t) :=
        add_le_add le_rfl (measureReal_biUnion_finset_le s _)
      _ < η := by linarith

/-- A difference of two nested threshold indicators has a bounded second moment
that tends to zero with the probability of the intervening interval. -/
theorem medianProcess_indicator_difference {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y) (a b : ℝ) :
    let D := fun ω => (if Y ω ≤ a then (1 : ℝ) else 0) - (if Y ω ≤ b then 1 else 0)
    MemLp D 2 μ ∧ mean μ D = cdf μ Y a - cdf μ Y b ∧
      var μ D ≤ |cdf μ Y a - cdf μ Y b| := by
  let I := fun t ω => if Y ω ≤ t then (1 : ℝ) else 0
  let D := fun ω => I a ω - I b ω
  have hI (t : ℝ) : Measurable (I t) := Measurable.ite
    (measurableSet_le hY measurable_const) measurable_const measurable_const
  have hIL (t : ℝ) : MemLp (I t) 2 μ := MemLp.of_bound (hI t).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by dsimp [I]; split_ifs <;> norm_num)
  have hIM (t : ℝ) : mean μ (I t) = cdf μ Y t := by
    have hh := integral_indicator_one (μ := μ) (measurableSet_le hY (measurable_const (a := t)))
    simpa only [mean, cdf, prob, Measure.real, Set.indicator, Pi.one_apply, Set.mem_setOf_eq] using hh
  have hL : MemLp D 2 μ := (hIL a).sub (hIL b)
  have hmean : mean μ D = cdf μ Y a - cdf μ Y b := by
    rw [mean, integral_sub ((hIL a).integrable one_le_two) ((hIL b).integrable one_le_two)]
    exact congrArg₂ (· - ·) (hIM a) (hIM b)
  have hsq : (∫ ω, (D ω)^2 ∂μ) = |mean μ D| := by
    change (∫ ω, (D ω)^2 ∂μ) = |∫ ω, D ω ∂μ|
    rcases le_total b a with hba | hab
    · have hpos : ∀ ω, 0 ≤ D ω := by
        intro ω
        dsimp [D, I]
        split_ifs <;> norm_num <;> linarith
      have he : (fun ω => (D ω)^2) = D := by
        funext ω
        dsimp [D, I]
        split_ifs <;> norm_num <;> linarith
      rw [he, abs_of_nonneg (integral_nonneg hpos)]
    · have hneg : ∀ ω, D ω ≤ 0 := by
        intro ω
        dsimp [D, I]
        split_ifs <;> norm_num <;> linarith
      have he : (fun ω => (D ω)^2) = fun ω => -D ω := by
        funext ω
        dsimp [D, I]
        split_ifs <;> norm_num <;> linarith
      rw [he, integral_neg, abs_of_nonpos (integral_nonpos hneg)]
  refine ⟨hL, hmean, ?_⟩
  rw [var, variance_eq_sub hL]
  change (∫ ω, (D ω)^2 ∂μ) - (mean μ D)^2 ≤ _
  rw [hsq, hmean]
  exact sub_le_self _ (sq_nonneg _)

/-- The finite-vector CDF is exactly the sample mean of threshold indicators. -/
theorem medianProcess_finiteCDF_mean {Ω : Type u} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ) :
    Literature.FiniteCDF (firstSample X n ω) t =
      sampleMean (fun i ω => if X i ω ≤ t then (1 : ℝ) else 0) n ω := by
  simp only [Literature.FiniteCDF, firstSample, sampleMean]
  rw [Fin.sum_univ_eq_sum_range (fun i => if X i ω ≤ t then (1 : ℝ) else 0) n]

/-- Shrinking deterministic local increments have vanishing variance on the root-size scale. -/
theorem medianProcess_increment_cp {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (m : ℝ) (a : ℕ → ℝ) (c : ℝ)
    (hcdf : Tendsto (fun n => cdf μ (X 0) (a n)) atTop (𝓝 (cdf μ (X 0) m)))
    (hmean : Tendsto (fun n : ℕ => Real.sqrt n * (cdf μ (X 0) (a n) - cdf μ (X 0) m))
      atTop (𝓝 c)) :
    CP μ (fun n ω => Real.sqrt n *
      (Literature.FiniteCDF (firstSample X n ω) (a n) -
        Literature.FiniteCDF (firstSample X n ω) m)) c := by
  let g := fun n y => (if y ≤ a n then (1 : ℝ) else 0) - (if y ≤ m then 1 else 0)
  let Y := fun n i ω => g n (X i ω)
  have hg (n : ℕ) : Measurable (g n) :=
    (Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const).sub
      (Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const)
  have hi (n : ℕ) : IID μ (Y n) := ⟨fun i => (hg n).comp (hiid.1 i),
    hiid.2.1.comp (fun _ => g n) (fun _ => hg n), fun i => (hiid.2.2 i).comp (hg n)⟩
  have hmom (n : ℕ) := medianProcess_indicator_difference μ (X 0) (hiid.1 0) (a n) m
  have hL (n : ℕ) : MemLp (Y n 0) 2 μ := (hmom n).1
  have heq (n : ℕ) : (fun ω => Real.sqrt n *
      (Literature.FiniteCDF (firstSample X n ω) (a n) -
        Literature.FiniteCDF (firstSample X n ω) m)) =
      fun ω => Real.sqrt n * sampleMean (Y n) n ω := by
    funext ω
    rw [medianProcess_finiteCDF_mean, medianProcess_finiteCDF_mean]
    simp only [sampleMean, Y, g, Finset.sum_sub_distrib, sub_div]
  have hvlim : Tendsto (fun n => var μ (Y n 0)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero (fun _ => variance_nonneg _ _) (fun n => (hmom n).2.2)
    simpa only [sub_self, abs_zero] using (hcdf.sub_const (cdf μ (X 0) m)).abs
  apply probability_convergence_from_mean_variance μ _
    (fun n => by rw [heq n]; exact (sample_mean_memLp μ (Y n) (hi n) (hL n) n).const_mul _)
    (fun n => Real.sqrt n * (cdf μ (X 0) (a n) - cdf μ (X 0) m))
    (fun n => var μ (Y n 0)) c ?_ ?_ hmean hvlim
  · intro n hn
    rw [heq n, mean, integral_const_mul]
    change Real.sqrt n * mean μ (sampleMean (Y n) n) = _
    rw [(iid_sample_mean_finite_moments μ (Y n) (hi n) (hL n) n hn).1, (hmom n).2.1]
  · intro n hn
    rw [heq n, var, variance_const_mul, Real.sq_sqrt (Nat.cast_nonneg n)]
    change (n : ℝ) * var μ (sampleMean (Y n) n) = _
    rw [(iid_sample_mean_finite_moments μ (Y n) (hi n) (hL n) n hn).2]
    field_simp

/-- Changes on events of vanishing probability preserve convergence in probability. -/
theorem medianProcess_cp_on_good {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {U V : ℕ → Ω → ℝ} {c : ℝ}
    (hU : CP μ U c) (A : ℕ → Set Ω)
    (hA : Tendsto (fun n => prob μ (A n)) atTop (𝓝 0))
    (heq : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, ω ∉ A n → V n ω = U n ω) : CP μ V c := by
  intro ε hε
  have hbound : ∀ᶠ n in atTop, prob μ {ω | ε ≤ dist (V n ω) c} ≤
      prob μ (A n) + prob μ {ω | ε ≤ dist (U n ω) c} := by
    filter_upwards [heq] with n hn
    have hsub : {ω | ε ≤ dist (V n ω) c} ≤ᵐ[μ]
        A n ∪ {ω | ε ≤ dist (U n ω) c} := by
      filter_upwards [hn] with ω hω he
      by_cases ha : ω ∈ A n
      · exact Or.inl ha
      · right
        change ε ≤ dist (U n ω) c
        change ε ≤ dist (V n ω) c at he
        rw [hω ha] at he
        exact he
    exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)).trans
      (measureReal_union_le _ _)
  exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound
    (by simpa using hA.add (hU ε hε))

/-- Eventual almost-everywhere equality suffices; finite sample prefixes are irrelevant. -/
theorem medianProcess_cp_congr {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {U V : ℕ → Ω → ℝ} {c : ℝ}
    (hU : CP μ U c) (heq : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, V n ω = U n ω) : CP μ V c :=
  medianProcess_cp_on_good μ hU (fun _ => ∅) (by simp [prob])
    (heq.mono fun _ hn => hn.mono fun _ h _ => h)

/-- Tight scalar sequences vanish after division by the diverging square-root size. -/
theorem medianProcess_unscale_cp {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → ℝ)
    (htight : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧
      ∀ᶠ n in atTop, prob μ {ω | B < |T n ω|} ≤ η) :
    CP μ (fun n ω => T n ω / Real.sqrt n) 0 := by
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le ENNReal.toReal_nonneg
  · intro η hη
    obtain ⟨B, hB, hb⟩ := htight (η/2) (by positivity)
    have hs : ∀ᶠ n : ℕ in atTop, B/ε < Real.sqrt n :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop _)
    filter_upwards [hb, hs] with n hn hsn
    have hpos : 0 < Real.sqrt (n : ℝ) := (div_pos hB hε).trans hsn
    have hsub : {ω | ε ≤ dist (T n ω / Real.sqrt n) 0} ⊆ {ω | B < |T n ω|} := by
      intro ω hω
      change ε ≤ dist (T n ω / Real.sqrt n) 0 at hω
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos] at hω
      change B < |T n ω|
      have hh := (le_div_iff₀ hpos).mp hω
      have hB' := (div_lt_iff₀ hε).mp hsn
      nlinarith
    exact lt_of_le_of_lt ((measureReal_mono hsub (measure_ne_top μ _)).trans hn) (by linarith)

/-- Tightness is stable under adding a fixed scalar. -/
theorem medianProcess_tight_shift {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → ℝ)
    (htight : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧
      ∀ᶠ n in atTop, prob μ {ω | B < |T n ω|} ≤ η) (z : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧
      ∀ᶠ n in atTop, prob μ {ω | B < |T n ω + z|} ≤ η := by
  intro η hη
  obtain ⟨B, hB, hb⟩ := htight η hη
  refine ⟨B+|z|, by positivity, hb.mono fun n hn => ?_⟩
  apply le_trans (measureReal_mono ?_ (measure_ne_top μ _)) hn
  intro ω hω
  change B+|z| < |T n ω + z| at hω
  change B < |T n ω|
  linarith [abs_add_le (T n ω) z]

/-- Every sequence converging in probability to a scalar is tight. -/
theorem medianProcess_tight_of_cp {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : ℕ → Ω → ℝ} {c : ℝ} (h : CP μ T c) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧
      ∀ᶠ n in atTop, prob μ {ω | B < |T n ω|} ≤ η := by
  intro η hη
  refine ⟨|c|+1, by positivity, ?_⟩
  filter_upwards [(h 1 (by norm_num)).eventually (eventually_lt_nhds hη)] with n hn
  apply le_trans (measureReal_mono ?_ (measure_ne_top μ _)) hn.le
  intro ω hω
  change |c|+1 < |T n ω| at hω
  change 1 ≤ dist (T n ω) c
  rw [Real.dist_eq]
  have hh := abs_sub_le (T n ω) c 0
  simp only [sub_zero] at hh
  linarith

end AronowAudit.P001.TailA
