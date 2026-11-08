import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDiscreteLimits
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellLocalization
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellWindowCounts

/-! Finite multinomial avoidance and its shared-site two-replica limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellSurvival (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Exact avoidance probability, with the central label excluded from the
category of other original labels but included in the resampling population. -/
theorem marked_no_retained_exact (n : ℕ) (E : Set MatchUnit) (z : Fin n → MatchUnit) :
    mean (UniformResampling (n+1)) (fun a => if markedNoRetained E z a then 1 else 0) =
      (1-(markedWindowCount E z : ℝ)/(n+1 : ℕ))^(n+1) := by
  let e : Fin n ↪ Fin (n+1) := ⟨Fin.succ, Fin.succ_injective n⟩
  let D := (Finset.univ.filter (fun i => z i ∈ E)).map e
  have heq (a : Fin (n+1) → Fin (n+1)) :
      markedNoRetained E z a ↔ ∀ t, a t ∉ D := by
    constructor
    · intro h t ht
      obtain ⟨i, hi, hit⟩ := Finset.mem_map.mp ht
      exact h i (Finset.mem_filter.mp hi).2 t hit.symm
    · intro h i hi t ht
      exact h t (Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hi⟩, ht.symm⟩)
  simp only [heq]
  simpa only [D, Finset.card_map, markedWindowCount] using
    reuse_uniform_avoid (Nat.succ_pos n) D

theorem marked_no_retained_pair_exact (n : ℕ) (E F : Set MatchUnit)
    (z : Fin n → MatchUnit) :
    mean (UniformResampling (n+1)) (fun a =>
      mean (UniformResampling (n+1)) (fun b =>
        if markedNoRetained E z a ∧ markedNoRetained F z b then 1 else 0)) =
      (1-(markedWindowCount E z : ℝ)/(n+1 : ℕ))^(n+1) *
        (1-(markedWindowCount F z : ℝ)/(n+1 : ℕ))^(n+1) := by
  have heq (a b : Fin (n+1) → Fin (n+1)) :
      (if markedNoRetained E z a ∧ markedNoRetained F z b then (1 : ℝ) else 0) =
      (if markedNoRetained E z a then 1 else 0) *
        (if markedNoRetained F z b then 1 else 0) := by
    by_cases ha : markedNoRetained E z a <;>
      by_cases hb : markedNoRetained F z b <;> simp [ha, hb]
  simp only [heq, mean, integral_const_mul, integral_mul_const]
  exact congrArg₂ (fun x y : ℝ => x*y)
    (marked_no_retained_exact n E z) (marked_no_retained_exact n F z)

def markedAvoidancePower (N c : ℕ) : ℝ := (max 0 (1-(c : ℝ)/(N : ℝ)))^N

theorem marked_avoidance_power_bounds (N c : ℕ) :
    0 ≤ markedAvoidancePower N c ∧ markedAvoidancePower N c ≤ 1 := by
  have hbase : max 0 (1-(c : ℝ)/(N : ℝ)) ≤ 1 := by
    apply max_le (by norm_num)
    have hd : 0 ≤ (c : ℝ)/(N : ℝ) := by positivity
    linarith
  exact ⟨pow_nonneg (le_max_left _ _) _, pow_le_one₀ (le_max_left _ _) hbase⟩

theorem marked_avoidance_power_of_le {N c : ℕ} (hN : 0 < N) (hc : c ≤ N) :
    markedAvoidancePower N c = (1-(c : ℝ)/(N : ℝ))^N := by
  have hbase : 0 ≤ 1-(c : ℝ)/(N : ℝ) :=
    sub_nonneg.mpr ((div_le_one (Nat.cast_pos.mpr hN)).mpr (by exact_mod_cast hc))
  simp only [markedAvoidancePower, max_eq_right hbase]

theorem marked_avoidance_power_limit (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (c : ℕ) :
    Tendsto (fun n => markedAvoidancePower (m n) c) atTop (𝓝 (Real.exp (-(c : ℝ)))) := by
  have hr : Tendsto (fun n => (m n : ℝ)*((c : ℝ)/(m n : ℝ))) atTop (𝓝 (c : ℝ)) := by
    apply (tendsto_const_nhds (x := (c : ℝ))).congr'
    filter_upwards [hm.eventually (eventually_ge_atTop 1)] with n hn
    have hn0 : (m n : ℝ) ≠ 0 := by positivity
    field_simp
  have ht := rare_counts_residual_power m hm (fun n => (c : ℝ)/(m n : ℝ))
    (c : ℝ) hr 0
  simp only [Nat.sub_zero] at ht
  apply ht.congr'
  filter_upwards [hm.eventually (eventually_ge_atTop (max c 1))] with n hn
  have hn0 : (0 : ℝ) < m n := by exact_mod_cast (show 0 < m n by omega)
  have hc : (c : ℝ) ≤ m n := by exact_mod_cast (show c ≤ m n by omega)
  have hbase : 0 ≤ 1-(c : ℝ)/(m n : ℝ) :=
    sub_nonneg.mpr ((div_le_one hn0).mpr hc)
  simp only [markedAvoidancePower, max_eq_right hbase]

/-- A bounded, row-dependent test of nested category counts. -/
theorem marked_nested_count_test_limit
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (X : (n : ℕ) → Ω n → Fin 2 → ℕ) (hX : ∀ n, Measurable (X n))
    (rates : Fin 2 → ℝ≥0)
    (hweak : AronowAudit.Literature.RowWeak P X
      (Measure.pi (fun i => poissonMeasure (rates i))))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => ∫ x,
      markedAvoidancePower (m n) (X n x 0) *
        markedAvoidancePower (m n) (X n x 0+X n x 1) ∂P n) atTop
      (𝓝 (Real.exp ((rates 0 : ℝ)*(Real.exp (-2)-1) +
        (rates 1 : ℝ)*(Real.exp (-1)-1)))) := by
  let f : (Fin 2 → ℕ) → ℝ := fun v => (Real.exp (-2))^(v 0)*(Real.exp (-1))^(v 1)
  have hlim (v : Fin 2 → ℕ) : Tendsto (fun n =>
      markedAvoidancePower (m n) (v 0)*markedAvoidancePower (m n) (v 0+v 1))
      atTop (𝓝 (f v)) := by
    convert (marked_avoidance_power_limit m hm (v 0)).mul
      (marked_avoidance_power_limit m hm (v 0+v 1)) using 1
    dsimp [f]
    simp only [← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_add]
    congr 1
    ring
  have hbound (n : ℕ) (v : Fin 2 → ℕ) :
      |markedAvoidancePower (m n) (v 0)*markedAvoidancePower (m n) (v 0+v 1)| ≤ 1 := by
    obtain ⟨h0, h1⟩ := marked_avoidance_power_bounds (m n) (v 0)
    obtain ⟨h2, h3⟩ := marked_avoidance_power_bounds (m n) (v 0+v 1)
    rw [abs_of_nonneg (mul_nonneg h0 h2)]
    exact mul_le_one₀ h1 h2 h3
  have ht := marked_discrete_varying_test_limit P hP X hX _ hweak
    (fun n v => markedAvoidancePower (m n) (v 0)*markedAvoidancePower (m n) (v 0+v 1))
    f (by norm_num : (0 : ℝ) ≤ 1) hbound hlim
  have hi : (∫ v, f v ∂Measure.pi (fun i => poissonMeasure (rates i))) =
      Real.exp ((rates 0 : ℝ)*(Real.exp (-2)-1)+(rates 1 : ℝ)*(Real.exp (-1)-1)) := by
    let z : Fin 2 → ℝ := ![Real.exp (-2), Real.exp (-1)]
    have hh := marked_poisson_product_power_integral 2 rates z
    simpa only [Fin.prod_univ_two, Fin.sum_univ_two, z, Matrix.cons_val_zero,
      Matrix.cons_val_one, f] using hh
  simpa only [hi] using ht

theorem marked_window_count_le (n : ℕ) (E : Set MatchUnit) (z : Fin n → MatchUnit) :
    markedWindowCount E z ≤ n := by
  simpa only [markedWindowCount, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun i => z i ∈ E)

theorem marked_window_count_union (n : ℕ) (E F : Set MatchUnit) (hEF : Disjoint E F)
    (z : Fin n → MatchUnit) :
    markedWindowCount (E ∪ F) z = markedWindowCount E z+markedWindowCount F z := by
  have hd : Disjoint (Finset.univ.filter (fun i => z i ∈ E))
      (Finset.univ.filter (fun i => z i ∈ F)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Set.disjoint_left.mp hEF (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  calc
    _ = (Finset.univ.filter (fun i => z i ∈ E) ∪
        Finset.univ.filter (fun i => z i ∈ F)).card := by
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Set.mem_union]
    _ = _ := Finset.card_union_of_disjoint hd

/-- Shared original sites produce the `exp(-2)` term on the overlap.  This is
a limit of the actual two multinomial resamples, not an assumed process law. -/
theorem marked_disjoint_category_pair_survival
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (E : ℕ → Fin 2 → Set MatchUnit) (hE : ∀ n i, MeasurableSet (E n i))
    (hdis : ∀ n, Disjoint (E n 0) (E n 1)) (rates : Fin 2 → ℝ≥0)
    (hrates : ∀ i, Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n i))
      atTop (𝓝 (rates i : ℝ))) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      mean (UniformResampling (m n+1)) (fun a =>
        mean (UniformResampling (m n+1)) (fun b =>
          if markedNoRetained (E n 0) z a ∧
            markedNoRetained (E n 0 ∪ E n 1) z b then 1 else 0)))) atTop
      (𝓝 (Real.exp ((rates 0 : ℝ)*(Real.exp (-2)-1) +
        (rates 1 : ℝ)*(Real.exp (-1)-1)))) := by
  let X : (n : ℕ) → (Fin (m n) → MatchUnit) → Fin 2 → ℕ :=
    fun n z i => markedWindowCount (E n i) z
  have hX (n : ℕ) : Measurable (X n) :=
    measurable_pi_lambda (fun i => marked_window_count_measurable _ _ (hE n i))
  have hdis' : ∀ n i j, i ≠ j → Disjoint (E n i) (E n j) := by
    intro n i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hdis n
    · exact (hdis n).symm
    · exact False.elim (hij rfl)
  have hw := rare_partition_counts 2 m hm (fun _ => matchingUnitLaw)
    (fun _ => inferInstance) E hE hdis' rates hrates
  have hres : Tendsto (fun n => m n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (m n)) hm
  have ht := marked_nested_count_test_limit (fun n => MatchProduct (m n))
    (fun _ => inferInstance) X hX rates hw _ hres
  apply ht.congr'
  exact Eventually.of_forall (fun n => by
    apply integral_congr_ae
    apply ae_of_all
    intro z
    dsimp only
    rw [marked_no_retained_pair_exact]
    dsimp only [X]
    rw [← marked_window_count_union _ _ _ (hdis n) z]
    rw [marked_avoidance_power_of_le (Nat.succ_pos _) ((marked_window_count_le _ _ _).trans (Nat.le_succ _)),
      marked_avoidance_power_of_le (Nat.succ_pos _) ((marked_window_count_le _ _ _).trans (Nat.le_succ _))])

/-- The actual finite experiment has the ordered one-side two-replica survival
limit used by the cell-intersection calculation. -/
theorem marked_right_pair_survival_ordered (p a b : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun n => mean (MatchProduct n) (fun z =>
      mean (UniformResampling (n+1)) (fun u =>
        mean (UniformResampling (n+1)) (fun v =>
          if markedNoRetained (markedTypeInterval true p (p+a/(n : ℝ))) z u ∧
            markedNoRetained (markedTypeInterval true p (p+b/(n : ℝ))) z v
          then 1 else 0)))) atTop
      (𝓝 (Real.exp (-(2*p)*(matchS*(a+b)-matchS^2*a)))) := by
  let E : ℕ → Fin 2 → Set MatchUnit := fun n =>
    ![markedTypeInterval true p (p+a/(n : ℝ)),
      markedTypeInterval true (p+a/(n : ℝ)) (p+b/(n : ℝ))]
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hba0 : 0 ≤ b-a := sub_nonneg.mpr hab
  let rates : Fin 2 → ℝ≥0 := ![⟨(2*p)*a, by positivity⟩, ⟨(2*p)*(b-a), by positivity⟩]
  have hE : ∀ n i, MeasurableSet (E n i) := by
    intro n i
    fin_cases i <;> exact marked_type_interval_measurable _ _ _
  have hdis (n : ℕ) : Disjoint (E n 0) (E n 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.1.2) hy.1.1
  have hrate (i : Fin 2) : Tendsto (fun n : ℕ => (n : ℝ)*matchingUnitLaw.real (E n i))
      atTop (𝓝 (rates i : ℝ)) := by
    fin_cases i
    · change Tendsto (fun n : ℕ => (n : ℝ)*matchingUnitLaw.real
        (markedTypeInterval true p (p+a/(n : ℝ)))) atTop (𝓝 ((2*p)*a))
      simpa only [zero_div, add_zero, sub_zero, markedTypeDensity, ite_true, mul_comm]
        using marked_type_interval_rate true p hp (fun n => n) tendsto_id 0 a ha
    · change Tendsto (fun n : ℕ => (n : ℝ)*matchingUnitLaw.real
        (markedTypeInterval true (p+a/(n : ℝ)) (p+b/(n : ℝ))))
        atTop (𝓝 ((2*p)*(b-a)))
      simpa only [markedTypeDensity, ite_true, mul_comm] using
        marked_type_interval_rate true p hp (fun n => n) tendsto_id a b hab
  have hunion (n : ℕ) : E n 0 ∪ E n 1 = markedTypeInterval true p (p+b/(n : ℝ)) := by
    ext x
    have hmid : p ≤ p+a/(n : ℝ) := le_add_of_nonneg_right (div_nonneg ha (Nat.cast_nonneg _))
    have hhi : p+a/(n : ℝ) ≤ p+b/(n : ℝ) :=
      add_le_add (le_refl p) (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _))
    change (x ∈ markedTypeInterval true p (p+a/(n : ℝ)) ∨
      x ∈ markedTypeInterval true (p+a/(n : ℝ)) (p+b/(n : ℝ))) ↔
        x ∈ markedTypeInterval true p (p+b/(n : ℝ))
    constructor
    · rintro (hx | hx)
      · exact ⟨⟨hx.1.1, hx.1.2.trans hhi⟩, hx.2⟩
      · exact ⟨⟨hmid.trans_lt hx.1.1, hx.1.2⟩, hx.2⟩
    · intro hx
      by_cases h : x.1 ≤ p+a/(n : ℝ)
      · exact Or.inl ⟨⟨hx.1.1, h⟩, hx.2⟩
      · exact Or.inr ⟨⟨lt_of_not_ge h, hx.1.2⟩, hx.2⟩
  have ht := marked_disjoint_category_pair_survival (fun n => n) tendsto_id E hE hdis rates hrate
  have hexp : (rates 0 : ℝ)*(Real.exp (-2)-1)+(rates 1 : ℝ)*(Real.exp (-1)-1) =
      -(2*p)*(matchS*(a+b)-matchS^2*a) := by
    change (2*p)*a*(Real.exp (-2)-1)+(2*p)*(b-a)*(Real.exp (-1)-1) = _
    rw [show (-2 : ℝ) = -1+(-1) by norm_num, Real.exp_add]
    unfold matchS
    ring
  simp_rw [hunion] at ht
  rw [hexp] at ht
  exact ht

theorem marked_no_retained_pair_symm (n : ℕ) (E F : Set MatchUnit)
    (z : Fin n → MatchUnit) :
    mean (UniformResampling (n+1)) (fun a =>
      mean (UniformResampling (n+1)) (fun b =>
        if markedNoRetained E z a ∧ markedNoRetained F z b then 1 else 0)) =
    mean (UniformResampling (n+1)) (fun a =>
      mean (UniformResampling (n+1)) (fun b =>
        if markedNoRetained F z a ∧ markedNoRetained E z b then 1 else 0)) := by
  rw [marked_no_retained_pair_exact, marked_no_retained_pair_exact, mul_comm]

/-- The exact shared-site survival function, now obtained from the actual
finite pinned experiment for every pair of nonnegative one-side radii. -/
theorem marked_right_pair_survival (p a b : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun n => mean (MatchProduct n) (fun z =>
      mean (UniformResampling (n+1)) (fun u =>
        mean (UniformResampling (n+1)) (fun v =>
          if markedNoRetained (markedTypeInterval true p (p+a/(n : ℝ))) z u ∧
            markedNoRetained (markedTypeInterval true p (p+b/(n : ℝ))) z v
          then 1 else 0)))) atTop
      (𝓝 (Real.exp (-(2*p)*(matchS*(a+b)-matchS^2*min a b)))) := by
  rcases le_total a b with hab | hba
  · simpa only [min_eq_left hab] using marked_right_pair_survival_ordered p a b hp ha hab
  · have ht := marked_right_pair_survival_ordered p b a hp hb hba
    have heq (n : ℕ) :
        mean (MatchProduct n) (fun z => mean (UniformResampling (n+1)) (fun u =>
          mean (UniformResampling (n+1)) (fun v =>
            if markedNoRetained (markedTypeInterval true p (p+a/(n : ℝ))) z u ∧
              markedNoRetained (markedTypeInterval true p (p+b/(n : ℝ))) z v
            then 1 else 0))) =
        mean (MatchProduct n) (fun z => mean (UniformResampling (n+1)) (fun u =>
          mean (UniformResampling (n+1)) (fun v =>
            if markedNoRetained (markedTypeInterval true p (p+b/(n : ℝ))) z u ∧
              markedNoRetained (markedTypeInterval true p (p+a/(n : ℝ))) z v
            then 1 else 0))) := by
      exact integral_congr_ae (ae_of_all _ (fun z => marked_no_retained_pair_symm n _ _ z))
    simpa only [heq, min_eq_right hba, add_comm a b] using ht

end AronowAudit.P001.TailA
