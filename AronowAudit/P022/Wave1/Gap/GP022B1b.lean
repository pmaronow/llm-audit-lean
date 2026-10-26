import AronowAudit.P022.P022_Variance
import AronowAudit.P022.Wave1.SharpBounds.N1
import AronowAudit.P022.Wave1.SharpBounds.N2
import AronowAudit.P022.Wave1.SharpBounds.N3
import AronowAudit.P022.Wave1.SharpBounds.N4
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.CombinatorialCLT

/-!
P022-T16: the exact Proposition 2 rate, using finite CDF/quantile transport.
The proof uses finite rank cells and permutation block moments.
-/

namespace AronowAudit.P022.Wave1

open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option autoImplicit false

noncomputable section

private def GP022B1b_Good (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (Set.range f).Finite

private lemma GP022B1b_good_integrable {f : ℝ → ℝ} (hf : GP022B1b_Good f) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  obtain ⟨C, hC⟩ := (hf.2.image (fun x : ℝ => ‖x‖)).bddAbove
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) :=
    isFiniteMeasure_restrict.mpr (by simp only [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
  apply intervalIntegrable_iff.mpr
  apply Integrable.of_bound hf.1.aestronglyMeasurable.restrict C
  exact Filter.Eventually.of_forall (fun u => hC ⟨f u, ⟨u, rfl⟩, rfl⟩)

private lemma GP022B1b_quantile_good {s : ℕ} (a : Fin s → ℝ) :
    GP022B1b_Good (empiricalQuantile a) := by
  classical
  refine ⟨(measurable_of_countable (orderStatistic a)).comp
    ((measurable_const.mul measurable_id).nat_ceil), ?_⟩
  let l := sortedOutcomes a
  have hl : l.length = s := by simp [l, sortedOutcomes]
  apply ((Set.finite_range (fun i : Fin (s + 1) => l.getD i.val 0))).subset
  rintro _ ⟨u, rfl⟩
  let j := Nat.ceil ((s : ℝ) * u) - 1
  by_cases hj : j < s
  · exact ⟨⟨j, by omega⟩, rfl⟩
  · refine ⟨⟨s, by omega⟩, ?_⟩
    change l.getD s 0 = l.getD j 0
    rw [List.getD_eq_default l 0 (by omega), List.getD_eq_default l 0 (by omega)]

private lemma GP022B1b_good_binary {f g : ℝ → ℝ}
    (hf : GP022B1b_Good f) (hg : GP022B1b_Good g)
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    GP022B1b_Good (fun u => F (f u, g u)) := by
  refine ⟨hF.measurable.comp (hf.1.prodMk hg.1),
    ((hf.2.prod hg.2).image F).subset ?_⟩
  rintro _ ⟨u, rfl⟩
  exact ⟨(f u, g u), ⟨⟨u, rfl⟩, ⟨u, rfl⟩⟩, rfl⟩

private lemma GP022B1b_quantile_integral {s : ℕ} (hs : 0 < s)
    (a : Fin s → ℝ) (f : ℝ → ℝ) :
    (∫ u in (0 : ℝ)..1, f (empiricalQuantile a u)) = finiteMean (fun i => f (a i)) := by
  letI : NeZero s := ⟨ne_of_gt hs⟩
  have h := SharpBounds.quadrature SharpBounds.n3_proof SharpBounds.n4_proof
    a a .H (fun p => f p.1)
  simp only at h
  rw [h]
  exact SharpBounds.n1_proof _ _ (SharpBounds.n2_proof a).1 f

private def GP022B1b_refine {s : ℕ} (a : Fin s → ℝ) {t : ℕ} (ht : 0 < t)
    (r : Fin (s * t)) : ℝ :=
  sortedValues a ⟨r.val / t, (Nat.div_lt_iff_lt_mul ht).2 r.isLt⟩

private lemma GP022B1b_refine_mono {s t : ℕ} (a : Fin s → ℝ) (ht : 0 < t) :
    Monotone (GP022B1b_refine a ht) := by
  intro i j hij
  apply (SharpBounds.n2_proof a).2.2
  exact Nat.div_le_div_right hij

private lemma GP022B1b_refine_cell {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (a : Fin s → ℝ) (r : Fin (s * t)) (u : ℝ)
    (hl : (r : ℝ) / (s * t) < u) (hu : u < ((r : ℝ) + 1) / (s * t)) :
    empiricalQuantile a u = GP022B1b_refine a ht r := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hstR : (0 : ℝ) < s * t := mul_pos hsR htR
  have hlo : ((r.val / t : ℕ) : ℝ) * t ≤ r := by
    exact_mod_cast Nat.div_mul_le_self r.val t
  have hhi : (r : ℝ) + 1 ≤ (((r.val / t : ℕ) : ℝ) + 1) * t := by
    exact_mod_cast (show r.val + 1 ≤ (r.val / t + 1) * t by
      have := Nat.lt_mul_div_succ r.val ht
      rw [Nat.mul_comm t] at this
      omega)
  apply (SharpBounds.n3_proof a
    ⟨r.val / t, (Nat.div_lt_iff_lt_mul ht).2 r.isLt⟩ u ?_ ?_).1
  · apply (div_lt_iff₀ hsR).2
    have h := (div_lt_iff₀ hstR).mp hl
    change ((r.val / t : ℕ) : ℝ) < u * s
    nlinarith
  · apply (lt_div_iff₀ hsR).2
    have h := (lt_div_iff₀ hstR).mp hu
    change u * s < ((r.val / t : ℕ) : ℝ) + 1
    nlinarith

private lemma GP022B1b_common_quadrature {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (f : ℝ → ℝ → ℝ) :
    (∫ u in (0 : ℝ)..1, f (empiricalQuantile a u) (empiricalQuantile b u)) =
      finiteMean (fun r : Fin (m * k) => f (GP022B1b_refine a hk r)
        (GP022B1b_refine b hm (Fin.cast (Nat.mul_comm m k) r))) := by
  letI : NeZero (m * k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm hk)⟩
  apply SharpBounds.n4_proof
  intro r u hl hu
  simp only [Nat.cast_mul] at hl hu
  rw [GP022B1b_refine_cell hm hk a r u hl hu]
  rw [GP022B1b_refine_cell hk hm b (Fin.cast (Nat.mul_comm m k) r) u]
  · simpa only [Fin.coe_cast, mul_comm] using hl
  · simpa only [Fin.coe_cast, mul_comm] using hu


private lemma GP022B1b_indicator_integrable (v a b : ℝ) :
    IntervalIntegrable (fun x => if v ≤ x then (1 : ℝ) else 0) volume a b := by
  have hm : Monotone (fun x : ℝ => if v ≤ x then (1 : ℝ) else 0) := by
    intro x y hxy
    by_cases hx : v ≤ x
    · simp [hx, hx.trans hxy]
    · simp only [if_neg hx]
      split_ifs <;> norm_num
  exact hm.intervalIntegrable

private lemma GP022B1b_indicator_integral (C v : ℝ) (hv : |v| ≤ C) :
    (∫ x in (-C)..C, if v ≤ x then (1 : ℝ) else 0) = C - v := by
  have hv' := abs_le.mp hv
  have h1 : (∫ x in (-C)..v, if v ≤ x then (1 : ℝ) else 0) = 0 := by
    rw [intervalIntegral.integral_congr_uIoo (g := fun _ => (0 : ℝ))]
    · simp
    · rw [Set.uIoo_of_le hv'.1]
      intro x hx
      simp only [if_neg (not_le.mpr hx.2)]
  have h2 : (∫ x in v..C, if v ≤ x then (1 : ℝ) else 0) = C - v := by
    rw [intervalIntegral.integral_congr_uIoo (g := fun _ => (1 : ℝ))]
    · simp
    · rw [Set.uIoo_of_le hv'.2]
      intro x hx
      simp only [if_pos hx.1.le]
  have h := intervalIntegral.integral_add_adjacent_intervals
    (GP022B1b_indicator_integrable v (-C) v) (GP022B1b_indicator_integrable v v C)
  rw [h1, h2, zero_add] at h
  exact h.symm

private lemma GP022B1b_indicator_distance_integral (C v w : ℝ)
    (hv : |v| ≤ C) (hw : |w| ≤ C) :
    (∫ x in (-C)..C, |(if v ≤ x then (1 : ℝ) else 0) -
      (if w ≤ x then (1 : ℝ) else 0)|) = |v - w| := by
  have haux (v w : ℝ) (hv : |v| ≤ C) (hw : |w| ≤ C) (hvw : v ≤ w) :
      (∫ x in (-C)..C, |(if v ≤ x then (1 : ℝ) else 0) -
        (if w ≤ x then (1 : ℝ) else 0)|) = w - v := by
    have hp (x : ℝ) : (if w ≤ x then (1 : ℝ) else 0) ≤
        (if v ≤ x then (1 : ℝ) else 0) := by
      by_cases hx : w ≤ x
      · simp [hx, hvw.trans hx]
      · simp only [if_neg hx]
        split_ifs <;> norm_num
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (hp _))]
    rw [intervalIntegral.integral_sub
      (GP022B1b_indicator_integrable _ _ _) (GP022B1b_indicator_integrable _ _ _),
      GP022B1b_indicator_integral C v hv, GP022B1b_indicator_integral C w hw]
    ring
  rcases le_total v w with h | h
  · rw [haux v w hv hw h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · simp_rw [abs_sub_comm (if v ≤ _ then (1 : ℝ) else 0)]
    rw [haux w v hw hv h, abs_of_nonneg (sub_nonneg.mpr h)]

private lemma GP022B1b_integral_mean {s : ℕ} (f : Fin s → ℝ → ℝ) (a b : ℝ)
    (hf : ∀ i, IntervalIntegrable (f i) volume a b) :
    (∫ x in a..b, finiteMean (fun i => f i x)) =
      finiteMean (fun i => ∫ x in a..b, f i x) := by
  simp only [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum]
  intro i _
  exact hf i

private lemma GP022B1b_abs_mean_sub {s : ℕ} (f g : Fin s → ℝ)
    (h : ∀ i, g i ≤ f i) :
    |finiteMean f - finiteMean g| = finiteMean (fun i => |f i - g i|) := by
  have hm : finiteMean g ≤ finiteMean f := Finset.expect_le_expect (fun i _ => h i)
  rw [abs_of_nonneg (sub_nonneg.mpr hm)]
  simp only [abs_of_nonneg (sub_nonneg.mpr (h _)), finiteMean,
    Finset.expect_sub_distrib]

private lemma GP022B1b_sorted_cdf_abs {s : ℕ} (a b : Fin s → ℝ)
    (ha : Monotone a) (hb : Monotone b) (x : ℝ) :
    |empiricalCDF a x - empiricalCDF b x| =
      finiteMean (fun i => |(if a i ≤ x then (1 : ℝ) else 0) -
        (if b i ≤ x then (1 : ℝ) else 0)|) := by
  classical
  by_cases h : ∃ i, a i ≤ x ∧ ¬b i ≤ x
  · obtain ⟨i, hai, hbi⟩ := h
    apply GP022B1b_abs_mean_sub
    intro j
    by_cases hj : b j ≤ x
    · have hj' : a j ≤ x := by
        rcases le_total j i with hji | hij
        · exact (ha hji).trans hai
        · exact False.elim (hbi ((hb hij).trans hj))
      simp [hj, hj']
    · simp only [if_neg hj]
      split_ifs <;> norm_num
  · rw [abs_sub_comm]
    have h' : ∀ i, (if a i ≤ x then (1 : ℝ) else 0) ≤
        (if b i ≤ x then (1 : ℝ) else 0) := by
      intro i
      by_cases hi : a i ≤ x
      · have hb' : b i ≤ x := by
          by_contra hn
          exact h ⟨i, hi, hn⟩
        simp [hi, hb']
      · simp only [if_neg hi]
        split_ifs <;> norm_num
    change |finiteMean (fun i => if b i ≤ x then (1 : ℝ) else 0) -
      finiteMean (fun i => if a i ≤ x then (1 : ℝ) else 0)| = _
    rw [GP022B1b_abs_mean_sub _ _ h']
    congr 1
    funext i
    exact abs_sub_comm _ _

private lemma GP022B1b_sorted_transport {s : ℕ} (a b : Fin s → ℝ)
    (ha : Monotone a) (hb : Monotone b) (C : ℝ)
    (haC : ∀ i, |a i| ≤ C) (hbC : ∀ i, |b i| ≤ C) :
    (∫ x in (-C)..C, |empiricalCDF a x - empiricalCDF b x|) =
      finiteMean (fun i => |a i - b i|) := by
  simp_rw [GP022B1b_sorted_cdf_abs a b ha hb]
  rw [GP022B1b_integral_mean]
  · simp_rw [GP022B1b_indicator_distance_integral C _ _ (haC _) (hbC _)]
  · intro i
    exact ((GP022B1b_indicator_integrable _ _ _).sub
      (GP022B1b_indicator_integrable _ _ _)).abs

private lemma GP022B1b_sorted_bound {s : ℕ} (a : Fin s → ℝ) (C : ℝ)
    (ha : ∀ i, |a i| ≤ C) (i : Fin s) : |sortedValues a i| ≤ C := by
  have hmem : sortedValues a i ∈ List.ofFn (sortedValues a) := List.mem_ofFn.mpr ⟨i, rfl⟩
  have hp := (SharpBounds.n2_proof a).1
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp (hp.mem_iff.mp hmem)
  rw [← hj]
  exact ha j

/-- Finite one-dimensional transport, proved by refining both rank grids. -/
lemma GP022B1b_quantile_transport {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (C : ℝ)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ i, |b i| ≤ C) :
    (∫ u in (0 : ℝ)..1, |empiricalQuantile a u - empiricalQuantile b u|) =
      (∫ x in (-C)..C, |empiricalCDF a x - empiricalCDF b x|) := by
  let A : Fin (m * k) → ℝ := GP022B1b_refine a hk
  let B : Fin (m * k) → ℝ := fun r =>
    GP022B1b_refine b hm (Fin.cast (Nat.mul_comm m k) r)
  have hAm : Monotone A := GP022B1b_refine_mono a hk
  have hBm : Monotone B := by
    intro i j hij
    apply GP022B1b_refine_mono b hm
    exact hij
  have hAc : ∀ x, empiricalCDF A x = empiricalCDF a x := by
    intro x
    have h := GP022B1b_common_quadrature hm hk a b
      (fun v _ => if v ≤ x then (1 : ℝ) else 0)
    rw [GP022B1b_quantile_integral hm a (fun v => if v ≤ x then (1 : ℝ) else 0)] at h
    exact h.symm
  have hBc : ∀ x, empiricalCDF B x = empiricalCDF b x := by
    intro x
    have h := GP022B1b_common_quadrature hm hk a b
      (fun _ v => if v ≤ x then (1 : ℝ) else 0)
    rw [GP022B1b_quantile_integral hk b (fun v => if v ≤ x then (1 : ℝ) else 0)] at h
    exact h.symm
  rw [GP022B1b_common_quadrature hm hk a b (fun v w => |v - w|)]
  change finiteMean (fun i => |A i - B i|) = _
  rw [← GP022B1b_sorted_transport A B hAm hBm C]
  · simp_rw [hAc, hBc]
  · intro i
    exact GP022B1b_sorted_bound a C ha _
  · intro i
    exact GP022B1b_sorted_bound b C hb _

/-! Bounded moment and sharp-covariance transport. -/

private lemma GP022B1b_mean_bound {s : ℕ} (hs : 0 < s) (a : Fin s → ℝ)
    (C : ℝ) (ha : ∀ i, |a i| ≤ C) : |finiteMean a| ≤ C := by
  letI : NeZero s := ⟨ne_of_gt hs⟩
  exact (Finset.abs_expect_le _ a).trans (by
    have h : (𝔼 i, |a i|) ≤ 𝔼 _ : Fin s, C :=
      Finset.expect_le_expect (fun i _ => ha i)
    simpa using h)

private lemma GP022B1b_quantile_bound {s : ℕ} (a : Fin s → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ i, |a i| ≤ C) (u : ℝ) :
    |empiricalQuantile a u| ≤ C := by
  let j := Nat.ceil ((s : ℝ) * u) - 1
  by_cases hj : j < s
  · exact GP022B1b_sorted_bound a C ha ⟨j, hj⟩
  · unfold empiricalQuantile orderStatistic
    rw [List.getD_eq_default]
    · simpa using hC
    · simpa only [sortedOutcomes, List.length_mergeSort, List.length_ofFn] using
        Nat.le_of_not_gt hj

private lemma GP022B1b_moment_transport {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (C L : ℝ) (f : ℝ → ℝ)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ i, |b i| ≤ C)
    (hf : ∀ v w : ℝ, |v| ≤ C → |w| ≤ C → |f v - f w| ≤ L * |v - w|) :
    |finiteMean (fun i => f (a i)) - finiteMean (fun i => f (b i))| ≤
      L * (∫ x in (-C)..C, |empiricalCDF a x - empiricalCDF b x|) := by
  let A : Fin (m * k) → ℝ := GP022B1b_refine a hk
  let B : Fin (m * k) → ℝ := fun r =>
    GP022B1b_refine b hm (Fin.cast (Nat.mul_comm m k) r)
  have hAf : finiteMean (fun i => f (a i)) = finiteMean (fun i => f (A i)) := by
    rw [← GP022B1b_quantile_integral hm a f]
    exact GP022B1b_common_quadrature hm hk a b (fun v _ => f v)
  have hBf : finiteMean (fun i => f (b i)) = finiteMean (fun i => f (B i)) := by
    rw [← GP022B1b_quantile_integral hk b f]
    exact GP022B1b_common_quadrature hm hk a b (fun _ w => f w)
  have hD : (∫ x in (-C)..C, |empiricalCDF a x - empiricalCDF b x|) =
      finiteMean (fun i => |A i - B i|) := by
    rw [← GP022B1b_quantile_transport hm hk a b C ha hb]
    exact GP022B1b_common_quadrature hm hk a b (fun v w => |v - w|)
  rw [hAf, hBf, hD]
  change |(𝔼 i, f (A i)) - 𝔼 i, f (B i)| ≤ L * 𝔼 i, |A i - B i|
  rw [← Finset.expect_sub_distrib, Finset.mul_expect]
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le_expect
  intro i _
  exact hf _ _ (GP022B1b_sorted_bound a C ha _) (GP022B1b_sorted_bound b C hb _)

private lemma GP022B1b_mean_transport {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (C : ℝ)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ i, |b i| ≤ C) :
    |finiteMean a - finiteMean b| ≤
      (∫ x in (-C)..C, |empiricalCDF a x - empiricalCDF b x|) := by
  simpa only [one_mul] using GP022B1b_moment_transport hm hk a b C 1 (fun x => x)
    ha hb (fun _ _ _ _ => by simp)

private lemma GP022B1b_square_lipschitz (v w C : ℝ) (hv : |v| ≤ C) (hw : |w| ≤ C) :
    |v ^ 2 - w ^ 2| ≤ 2 * C * |v - w| := by
  have hsum : |v + w| ≤ 2 * C := (abs_add_le _ _).trans (by linarith)
  calc
    |v ^ 2 - w ^ 2| = |v - w| * |v + w| := by rw [← abs_mul]; congr 1; ring
    _ ≤ |v - w| * (2 * C) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = _ := by ring

private lemma GP022B1b_variance_transport {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ i, |b i| ≤ C) :
    |finiteVariance a - finiteVariance b| ≤
      4 * C * (∫ x in (-C)..C, |empiricalCDF a x - empiricalCDF b x|) := by
  have h2 := GP022B1b_moment_transport hm hk a b C (2 * C) (fun x => x ^ 2)
    ha hb (fun v w hv hw => GP022B1b_square_lipschitz v w C hv hw)
  have h1 := GP022B1b_mean_transport hm hk a b C ha hb
  have hμ := GP022B1b_square_lipschitz (finiteMean a) (finiteMean b) C
    (GP022B1b_mean_bound hm a C ha) (GP022B1b_mean_bound hk b C hb)
  have hμ' := hμ.trans (mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * C))
  rw [finite_variance_second_moment hm, finite_variance_second_moment hk]
  calc
    _ = |(finiteMean (fun i => a i ^ 2) - finiteMean (fun i => b i ^ 2)) -
      (finiteMean a ^ 2 - finiteMean b ^ 2)| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

private lemma GP022B1b_variance_bounds {s : ℕ} (hs : 0 < s) (a : Fin s → ℝ)
    (C : ℝ) (ha : ∀ i, |a i| ≤ C) : 0 ≤ finiteVariance a ∧ finiteVariance a ≤ C ^ 2 := by
  letI : NeZero s := ⟨ne_of_gt hs⟩
  refine ⟨Finset.expect_nonneg (fun _ _ => sq_nonneg _), ?_⟩
  have h2 : finiteMean (fun i => a i ^ 2) ≤ C ^ 2 := by
    have h : finiteMean (fun i => a i ^ 2) ≤ finiteMean (fun _ : Fin s => C ^ 2) := by
      apply Finset.expect_le_expect
      intro i _
      nlinarith [ha i, abs_nonneg (a i), sq_abs (a i)]
    simpa [finiteMean] using h
  rw [finite_variance_second_moment hs]
  nlinarith [sq_nonneg (finiteMean a)]

private lemma GP022B1b_good_precomp {f : ℝ → ℝ} (hf : GP022B1b_Good f)
    (g : ℝ → ℝ) (hg : Measurable g) : GP022B1b_Good (fun u => f (g u)) := by
  refine ⟨hf.1.comp hg, hf.2.subset ?_⟩
  rintro _ ⟨u, rfl⟩
  exact ⟨g u, rfl⟩

private lemma GP022B1b_covariance_transport {m k N : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hN : 0 < N)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (y z : Fin N → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ i, |b i| ≤ C)
    (hy : ∀ i, |y i| ≤ C) (hz : ∀ i, |z i| ≤ C) (B : BoundSide) :
    |sharpCovariance a b B - sharpCovariance y z B| ≤
      2 * C * ((∫ x in (-C)..C, |empiricalCDF a x - empiricalCDF y x|) +
        ∫ x in (-C)..C, |empiricalCDF b x - empiricalCDF z x|) := by
  let r : ℝ → ℝ := fun u => if B = .H then u else 1 - u
  have hr : Measurable r := by dsimp [r]; split_ifs <;> fun_prop
  let A := empiricalQuantile a
  let Y := empiricalQuantile y
  let F := fun u => empiricalQuantile b (r u)
  let Z := fun u => empiricalQuantile z (r u)
  have hA : GP022B1b_Good A := GP022B1b_quantile_good a
  have hY : GP022B1b_Good Y := GP022B1b_quantile_good y
  have hF : GP022B1b_Good F := GP022B1b_good_precomp (GP022B1b_quantile_good b) r hr
  have hZ : GP022B1b_Good Z := GP022B1b_good_precomp (GP022B1b_quantile_good z) r hr
  have hAY := GP022B1b_good_binary hA hY (fun p => |p.1 - p.2|) (by fun_prop)
  have hFZ := GP022B1b_good_binary hF hZ (fun p => |p.1 - p.2|) (by fun_prop)
  have hAF := GP022B1b_good_binary hA hF (fun p => p.1 * p.2) (by fun_prop)
  have hYZ := GP022B1b_good_binary hY hZ (fun p => p.1 * p.2) (by fun_prop)
  have hdiff := GP022B1b_good_binary hAF hYZ (fun p => |p.1 - p.2|) (by fun_prop)
  have hsum := GP022B1b_good_binary hAY hFZ (fun p => C * (p.1 + p.2)) (by fun_prop)
  have hpoint (u : ℝ) : |A u * F u - Y u * Z u| ≤ C * (|A u - Y u| + |F u - Z u|) := by
    have hFbound : |F u| ≤ C := GP022B1b_quantile_bound b C hC hb _
    have hYbound : |Y u| ≤ C := GP022B1b_quantile_bound y C hC hy _
    calc
      _ = |(A u - Y u) * F u + Y u * (F u - Z u)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ = |A u - Y u| * |F u| + |Y u| * |F u - Z u| := by rw [abs_mul, abs_mul]
      _ ≤ |A u - Y u| * C + C * |F u - Z u| :=
        add_le_add (mul_le_mul_of_nonneg_left hFbound (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hYbound (abs_nonneg _))
      _ = _ := by ring
  have hi : |(∫ u in (0 : ℝ)..1, A u * F u) - ∫ u in (0 : ℝ)..1, Y u * Z u| ≤
      C * ((∫ u in (0 : ℝ)..1, |A u - Y u|) + ∫ u in (0 : ℝ)..1, |F u - Z u|) := by
    rw [← intervalIntegral.integral_sub (GP022B1b_good_integrable hAF 0 1)
      (GP022B1b_good_integrable hYZ 0 1)]
    apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0 : ℝ) ≤ 1)).trans
    have h := intervalIntegral.integral_mono (by norm_num : (0 : ℝ) ≤ 1)
      (GP022B1b_good_integrable hdiff 0 1) (GP022B1b_good_integrable hsum 0 1) hpoint
    simpa only [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (GP022B1b_good_integrable hAY 0 1) (GP022B1b_good_integrable hFZ 0 1)] using h
  have hleft := GP022B1b_quantile_transport hm hN a y C ha hy
  have hright : (∫ u in (0 : ℝ)..1, |F u - Z u|) =
      (∫ x in (-C)..C, |empiricalCDF b x - empiricalCDF z x|) := by
    dsimp [F, Z, r]
    split_ifs
    · exact GP022B1b_quantile_transport hk hN b z C hb hz
    · rw [intervalIntegral.integral_comp_sub_left (fun u =>
        |empiricalQuantile b u - empiricalQuantile z u|) 1]
      norm_num only [sub_self, sub_zero]
      exact GP022B1b_quantile_transport hk hN b z C hb hz
  rw [hleft, hright] at hi
  have hma := GP022B1b_mean_transport hm hN a y C ha hy
  have hmb := GP022B1b_mean_transport hk hN b z C hb hz
  have hprod : |finiteMean a * finiteMean b - finiteMean y * finiteMean z| ≤
      C * ((∫ x in (-C)..C, |empiricalCDF a x - empiricalCDF y x|) +
        ∫ x in (-C)..C, |empiricalCDF b x - empiricalCDF z x|) := by
    calc
      _ = |(finiteMean a - finiteMean y) * finiteMean b +
          finiteMean y * (finiteMean b - finiteMean z)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ _ := add_le_add
        (mul_le_mul hma (GP022B1b_mean_bound hk b C hb) (abs_nonneg _)
          (intervalIntegral.integral_nonneg_of_forall (by linarith : -C ≤ C)
            (fun _ => abs_nonneg _)))
        (mul_le_mul (GP022B1b_mean_bound hN y C hy) hmb (abs_nonneg _) hC)
      _ = _ := by ring
  unfold sharpCovariance
  change |((_ : ℝ) - finiteMean a * finiteMean b) -
      ((_ : ℝ) - finiteMean y * finiteMean z)| ≤ _
  calc
    _ = |((∫ u in (0 : ℝ)..1, A u * F u) - ∫ u in (0 : ℝ)..1, Y u * Z u) -
      (finiteMean a * finiteMean b - finiteMean y * finiteMean z)| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

/-! Finite-population correction and the deterministic estimator bound. -/

private lemma GP022B1b_marginal_correction {N s : ℕ} (hN : 4 ≤ N) (hs : 2 ≤ s)
    (hsN : s ≤ N) (a : Fin s → ℝ) (C c : ℝ) (ha : ∀ i, |a i| ≤ C)
    (hc : 0 < c) (hm : c * N ≤ s) :
    |marginalVarianceEstimate N a - finiteVariance a| ≤ 2 * C ^ 2 / (c * N) := by
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hsNR : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hNpos : (0 : ℝ) < N := by linarith
  have hspos : 0 < (s : ℝ) - 1 := by linarith
  have hcN : 0 < c * N := mul_pos hc hNpos
  let f : ℝ := ((N : ℝ) - s) / ((N : ℝ) * ((s : ℝ) - 1))
  have hf : 0 ≤ f := div_nonneg (by linarith) (by positivity)
  have hf1 : f ≤ 1 / ((s : ℝ) - 1) := by
    dsimp [f]
    apply (div_le_iff₀ (mul_pos hNpos hspos)).2
    field_simp [ne_of_gt hspos]
    nlinarith
  have hf2 : 1 / ((s : ℝ) - 1) ≤ 2 / (c * N) := by
    apply (div_le_div_iff₀ hspos hcN).2
    nlinarith
  have hvar := GP022B1b_variance_bounds (by omega : 0 < s) a C ha
  have heq : marginalVarianceEstimate N a - finiteVariance a = f * finiteVariance a := by
    have hsum : (∑ i, (a i - finiteMean a) ^ 2) = (s : ℝ) * finiteVariance a := by
      simpa only [Fintype.card_fin, finiteVariance, finiteMean] using
        (Fintype.card_mul_expect (fun i => (a i - finiteMean a) ^ 2)).symm
    unfold marginalVarianceEstimate sampleVariance
    rw [hsum]
    dsimp [f]
    field_simp [ne_of_gt hNpos, ne_of_gt hspos]
    <;> ring
  rw [heq, abs_of_nonneg (mul_nonneg hf hvar.1)]
  calc
    f * finiteVariance a ≤ (2 / (c * N)) * C ^ 2 :=
      mul_le_mul (hf1.trans hf2) hvar.2 hvar.1 (by positivity)
    _ = _ := by ring

lemma GP022B1b_deterministic (d : Design) (y1 y0 : Fin d.N → ℝ)
    (C c : ℝ) (hC : 0 ≤ C) (hy : ∀ i, |y1 i| ≤ C ∧ |y0 i| ≤ C)
    (hc : 0 < c) (hm : c * d.N ≤ d.m) (hk : c * d.N ≤ d.k) (B : BoundSide)
    (π : Assignment d) :
    (d.N : ℝ) * |estimatedVariance d y1 y0 B π - populationBound d y1 y0 B| ≤
      (16 / c + 8) * C * (integratedCDFError C y1 (observedTreatment d y1 π) +
        integratedCDFError C y0 (observedControl d y0 π)) + 8 * C ^ 2 / (c ^ 2 * d.N) := by
  have hNnat : 0 < d.N := by have := d.population_min; omega
  have hmnat : 0 < d.m := by have := d.treatment_min; omega
  have hknat : 0 < d.k := by have := d.control_min; omega
  have hNR : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
  have hN : (0 : ℝ) < d.N := by positivity
  have hN1 : 0 < (d.N : ℝ) - 1 := by linarith
  have hmR : (0 : ℝ) < d.m := by exact_mod_cast hmnat
  have hkR : (0 : ℝ) < d.k := by exact_mod_cast hknat
  have hmN : (d.m : ℝ) ≤ d.N := by exact_mod_cast (show d.m ≤ d.N by have := d.sample_le; omega)
  have hkN : (d.k : ℝ) ≤ d.N := by exact_mod_cast (show d.k ≤ d.N by have := d.sample_le; omega)
  let a := observedTreatment d y1 π
  let b := observedControl d y0 π
  let D1 := integratedCDFError C y1 a
  let D0 := integratedCDFError C y0 b
  have hD1 : 0 ≤ D1 := intervalIntegral.integral_nonneg_of_forall
    (by linarith : -C ≤ C) (fun _ => abs_nonneg _)
  have hD0 : 0 ≤ D0 := intervalIntegral.integral_nonneg_of_forall
    (by linarith : -C ≤ C) (fun _ => abs_nonneg _)
  have ha : ∀ i, |a i| ≤ C := fun i => (hy _).1
  have hb : ∀ i, |b i| ≤ C := fun i => (hy _).2
  have hv1 := GP022B1b_variance_transport hmnat hNnat a y1 C hC ha (fun i => (hy i).1)
  have hv0 := GP022B1b_variance_transport hknat hNnat b y0 C hC hb (fun i => (hy i).2)
  have hc1 := GP022B1b_marginal_correction d.population_min d.treatment_min
    (by have := d.sample_le; omega) a C c ha hc hm
  have hc0 := GP022B1b_marginal_correction d.population_min d.control_min
    (by have := d.sample_le; omega) b C c hb hc hk
  have he1 : |marginalVarianceEstimate d.N a - finiteVariance y1| ≤
      8 * C * D1 + 2 * C ^ 2 / (c * d.N) := by
    have h := (abs_sub_le (marginalVarianceEstimate d.N a) (finiteVariance a)
      (finiteVariance y1)).trans (add_le_add hc1 hv1)
    change _ ≤ 8 * C * D1 + _
    change _ ≤ _ + 4 * C * D1 at h
    nlinarith [mul_nonneg hC hD1]
  have he0 : |marginalVarianceEstimate d.N b - finiteVariance y0| ≤
      8 * C * D0 + 2 * C ^ 2 / (c * d.N) := by
    have h := (abs_sub_le (marginalVarianceEstimate d.N b) (finiteVariance b)
      (finiteVariance y0)).trans (add_le_add hc0 hv0)
    change _ ≤ 8 * C * D0 + _
    change _ ≤ _ + 4 * C * D0 at h
    nlinarith [mul_nonneg hC hD0]
  have hec : |sharpCovariance a b B - sharpCovariance y1 y0 B| ≤ 2 * C * (D1 + D0) :=
    GP022B1b_covariance_transport hmnat hknat hNnat a b y1 y0 C hC ha hb
      (fun i => (hy i).1) (fun i => (hy i).2) B
  let v1 := marginalVarianceEstimate d.N a - finiteVariance y1
  let v0 := marginalVarianceEstimate d.N b - finiteVariance y0
  let cv := sharpCovariance a b B - sharpCovariance y1 y0 B
  let α := ((d.N : ℝ) - d.m) / d.m
  let β := ((d.N : ℝ) - d.k) / d.k
  have hα : 0 ≤ α := div_nonneg (sub_nonneg.mpr hmN) hmR.le
  have hβ : 0 ≤ β := div_nonneg (sub_nonneg.mpr hkN) hkR.le
  have hαc : α ≤ 1 / c := by
    apply (div_le_div_iff₀ hmR hc).2
    nlinarith
  have hβc : β ≤ 1 / c := by
    apply (div_le_div_iff₀ hkR hc).2
    nlinarith
  have hfrac : (d.N : ℝ) / ((d.N : ℝ) - 1) ≤ 2 := by
    apply (div_le_iff₀ hN1).2
    linarith
  have heq : estimatedVariance d y1 y0 B π - populationBound d y1 y0 B =
      (α * v1 + β * v0 + 2 * cv) / ((d.N : ℝ) - 1) := by
    unfold estimatedVariance estimateBound populationBound varianceExpression
    dsimp [α, β, v1, v0, cv, a, b]
    ring
  have hnum : |α * v1 + β * v0 + 2 * cv| ≤ α * |v1| + β * |v0| + 2 * |cv| := by
    calc
      _ ≤ |α * v1 + β * v0| + |2 * cv| := abs_add_le _ _
      _ ≤ (|α * v1| + |β * v0|) + |2 * cv| := add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]; norm_num
  have hnum' : |α * v1 + β * v0 + 2 * cv| ≤
      1 / c * ((8 * C * D1 + 2 * C ^ 2 / (c * d.N)) +
        (8 * C * D0 + 2 * C ^ 2 / (c * d.N))) + 4 * C * (D1 + D0) := by
    apply hnum.trans
    have h1 := mul_le_mul hαc he1 (abs_nonneg v1) (by positivity : 0 ≤ 1 / c)
    have h0 := mul_le_mul hβc he0 (abs_nonneg v0) (by positivity : 0 ≤ 1 / c)
    have h2 := mul_le_mul_of_nonneg_left hec (by norm_num : (0 : ℝ) ≤ 2)
    dsimp [v1, v0, cv] at *
    nlinarith
  rw [heq, abs_div, abs_of_pos hN1]
  calc
    _ = (d.N : ℝ) / ((d.N : ℝ) - 1) * |α * v1 + β * v0 + 2 * cv| := by ring
    _ ≤ 2 * (1 / c * ((8 * C * D1 + 2 * C ^ 2 / (c * d.N)) +
        (8 * C * D0 + 2 * C ^ 2 / (c * d.N))) + 4 * C * (D1 + D0)) :=
      mul_le_mul hfrac hnum' (abs_nonneg _) (by norm_num)
    _ = _ := by
      change 2 * (1 / c * ((8 * C * D1 + 2 * C ^ 2 / (c * d.N)) +
        (8 * C * D0 + 2 * C ^ 2 / (c * d.N))) + 4 * C * (D1 + D0)) =
        (16 / c + 8) * C * (D1 + D0) + 8 * C ^ 2 / (c ^ 2 * d.N)
      field_simp
      <;> ring

/-! Integrated CDF second moments under the actual permutation design. -/

private lemma GP022B1b_block_moments (d : Design) {s : ℕ} (hs : 0 < s)
    (e : Fin s → Fin d.N) (he : Function.Injective e) (z : Fin d.N → ℝ) :
    designExpectation d (fun π => finiteMean (fun j => z (π (e j)))) = finiteMean z ∧
    designExpectation d (fun π =>
      (finiteMean (fun j => z (π (e j))) - finiteMean z) ^ 2) =
      ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) * finiteVariance z := by
  classical
  letI : NeZero s := ⟨ne_of_gt hs⟩
  have hNnat : 0 < d.N := by have := d.population_min; omega
  have hN : (0 : ℝ) < d.N := by exact_mod_cast hNnat
  have hN₁ : (0 : ℝ) < (d.N : ℝ) - 1 := by
    have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · unfold designExpectation finiteMean
    rw [Finset.expect_comm]
    simp_rw [permutation_eval_mean hNnat]
    exact Fintype.expect_const _
  · let μ : ℝ := finiteMean z
    let w : Fin d.N → ℝ := fun i => z i - μ
    have hsumz : (∑ i, z i) = (d.N : ℝ) * μ := by
      simpa only [Fintype.card_fin, μ, finiteMean] using
        (Fintype.card_mul_expect z).symm
    have hw : ∑ i, w i = 0 := by
      dsimp [w]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hsumz]
      ring
    have hsumw : (∑ i, w i ^ 2) = (d.N : ℝ) * finiteVariance z := by
      simpa only [Fintype.card_fin, finiteVariance, finiteMean, w, μ] using
        (Fintype.card_mul_expect (fun i => w i ^ 2)).symm
    have hcenter : ∀ π : Assignment d,
        finiteMean (fun j => z (π (e j))) - finiteMean z =
          (∑ j, w (π (e j))) / (s : ℝ) := by
      intro π
      change (𝔼 j : Fin s, z (π (e j))) - μ =
        (∑ j : Fin s, (z (π (e j)) - μ)) / (s : ℝ)
      rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp [ne_of_gt hsR]
      <;> ring
    have hblock := StatLean.HypothesisTesting.avg_perm_blockSum_sq
      (show 2 ≤ d.N by have := d.population_min; omega) e he w hw
    have havg : designExpectation d (fun π => (∑ j, w (π (e j))) ^ 2) =
        (s : ℝ) * ((d.N : ℝ) - s) / ((d.N : ℝ) * ((d.N : ℝ) - 1)) *
          ∑ i, w i ^ 2 := by
      simpa only [designExpectation, Fintype.expect_eq_sum_div_card,
        div_eq_inv_mul] using hblock
    calc
      designExpectation d (fun π =>
          (finiteMean (fun j => z (π (e j))) - finiteMean z) ^ 2) =
          designExpectation d (fun π => (∑ j, w (π (e j))) ^ 2 / (s : ℝ) ^ 2) := by
        unfold designExpectation
        apply Finset.expect_congr rfl
        intro π _
        rw [hcenter π, div_pow]
      _ = designExpectation d (fun π => (∑ j, w (π (e j))) ^ 2) / (s : ℝ) ^ 2 := by
        unfold designExpectation
        exact (Finset.expect_div _ _ _).symm
      _ = ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) * finiteVariance z := by
        rw [havg, hsumw]
        field_simp [ne_of_gt hN, ne_of_gt hN₁, ne_of_gt hsR]
        <;> ring

private lemma GP022B1b_cdf_good {s : ℕ} (a : Fin s → ℝ) :
    GP022B1b_Good (empiricalCDF a) := by
  classical
  have hm : Monotone (empiricalCDF a) := by
    intro x y hxy
    apply Finset.expect_le_expect
    intro i _
    by_cases hi : a i ≤ x
    · simp only [if_pos hi, if_pos (hi.trans hxy), le_refl]
    · simp only [if_neg hi]
      split_ifs <;> norm_num
  refine ⟨hm.measurable, ?_⟩
  let F : (Fin s → Bool) → ℝ := fun v => finiteMean (fun i => if v i then 1 else 0)
  apply (Set.finite_range F).subset
  rintro _ ⟨x, rfl⟩
  refine ⟨fun i => decide (a i ≤ x), ?_⟩
  simp [F, empiricalCDF]

private lemma GP022B1b_cdf_error_good {s t : ℕ} (a : Fin s → ℝ) (b : Fin t → ℝ) :
    GP022B1b_Good (fun x => |empiricalCDF a x - empiricalCDF b x|) :=
  GP022B1b_good_binary (GP022B1b_cdf_good a) (GP022B1b_cdf_good b)
    (fun p => |p.1 - p.2|) (by fun_prop)

private lemma GP022B1b_integral_square (f : ℝ → ℝ) (hf : GP022B1b_Good f)
    (C : ℝ) (hC : 0 ≤ C) :
    (∫ x in (-C)..C, f x) ^ 2 ≤ 2 * C * (∫ x in (-C)..C, f x ^ 2) := by
  by_cases hc : C = 0
  · simp [hc]
  have hcp : 0 < 2 * C := by positivity
  let D := ∫ x in (-C)..C, f x
  have hf2 := GP022B1b_good_binary hf hf (fun p => p.1 ^ 2) (by fun_prop)
  have hfi := GP022B1b_good_integrable hf (-C) C
  have hf2i := GP022B1b_good_integrable hf2 (-C) C
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) (by linarith : -C ≤ C)
    (fun x => sq_nonneg (2 * C * f x - D))
  have heq : (fun x => (2 * C * f x - D) ^ 2) =
      (fun x => (2 * C) ^ 2 * f x ^ 2 - (4 * C * D) * f x + D ^ 2) := by
    funext x
    ring
  rw [heq, intervalIntegral.integral_add (hf2i.const_mul _ |>.sub (hfi.const_mul _))
    intervalIntegrable_const, intervalIntegral.integral_sub (hf2i.const_mul _) (hfi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hn
  simp only [smul_eq_mul] at hn
  have hp : 0 ≤ (2 * C) * (2 * C * (∫ x in (-C)..C, f x ^ 2) - D ^ 2) := by
    change 0 ≤ (2 * C) ^ 2 * (∫ x in (-C)..C, f x ^ 2) - 4 * C * D * D + (C - -C) * D ^ 2 at hn
    nlinarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hcp).mp hp)

private lemma GP022B1b_integral_expect {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (a b : ℝ) (hf : ∀ i, IntervalIntegrable (f i) volume a b) :
    (∫ x in a..b, 𝔼 i, f i x) = 𝔼 i, ∫ x in a..b, f i x := by
  simp only [Fintype.expect_eq_sum_div_card]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum]
  intro i _
  exact hf i

private lemma GP022B1b_expect_integrable {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (a b : ℝ) (hf : ∀ i, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => 𝔼 i, f i x) volume a b := by
  simp only [Fintype.expect_eq_sum_div_card]
  simpa only [Finset.sum_apply] using
    (IntervalIntegrable.sum Finset.univ (fun i _ => hf i)).div_const (Fintype.card ι : ℝ)

lemma GP022B1b_integrated_moment (d : Design) {s : ℕ} (hs : 0 < s)
    (e : Fin s → Fin d.N) (he : Function.Injective e) (y : Fin d.N → ℝ)
    (C : ℝ) (hC : 0 ≤ C) :
    designExpectation d (fun π =>
      integratedCDFError C y (fun i => y (π (e i))) ^ 2) ≤
      C ^ 2 * ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) := by
  classical
  let f : Assignment d → ℝ → ℝ := fun π x =>
    |empiricalCDF (fun i => y (π (e i))) x - empiricalCDF y x|
  have hf (π : Assignment d) : GP022B1b_Good (f π) := GP022B1b_cdf_error_good _ _
  have hf2 (π : Assignment d) : IntervalIntegrable (fun x => f π x ^ 2) volume (-C) C :=
    GP022B1b_good_integrable (GP022B1b_good_binary (hf π) (hf π)
      (fun p => p.1 ^ 2) (by fun_prop)) (-C) C
  have hNnat : 0 < d.N := by have := d.population_min; omega
  have hNR : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsN : s ≤ d.N := by simpa using Fintype.card_le_of_injective e he
  have hsNR : (s : ℝ) ≤ d.N := by exact_mod_cast hsN
  let R : ℝ := ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s)
  have hR : 0 ≤ R := div_nonneg (by linarith) (mul_nonneg (by linarith) hsR.le)
  have hpoint (x : ℝ) : (𝔼 π : Assignment d, f π x ^ 2) ≤ R / 4 := by
    have h := (GP022B1b_block_moments d hs e he
      (fun i => if y i ≤ x then (1 : ℝ) else 0)).2
    rw [indicator_population_variance hNnat y x] at h
    have h' : (𝔼 π : Assignment d, f π x ^ 2) =
        R * (empiricalCDF y x * (1 - empiricalCDF y x)) := by
      simpa only [f, sq_abs, empiricalCDF, designExpectation, R] using h
    rw [h']
    have hh := mul_le_mul_of_nonneg_left (bernoulli_variance_bound (empiricalCDF y x)).1 hR
    linarith
  calc
    _ ≤ 𝔼 π : Assignment d, 2 * C * (∫ x in (-C)..C, f π x ^ 2) := by
      apply Finset.expect_le_expect
      intro π _
      exact GP022B1b_integral_square (f π) (hf π) C hC
    _ = 2 * C * (∫ x in (-C)..C, 𝔼 π : Assignment d, f π x ^ 2) := by
      rw [← Finset.mul_expect, GP022B1b_integral_expect _ (-C) C hf2]
    _ ≤ 2 * C * (∫ _ in (-C)..C, R / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact intervalIntegral.integral_mono (by linarith : -C ≤ C)
        (GP022B1b_expect_integrable _ (-C) C hf2) intervalIntegrable_const hpoint
    _ = _ := by
      rw [intervalIntegral.integral_const]
      dsimp [R]
      simp only [smul_eq_mul, div_eq_mul_inv] <;> ring

private lemma GP022B1b_allocation_bound (N s : ℕ) (hs : 0 < s) (hsN : s ≤ N)
    (hN : 4 ≤ N) (c : ℝ) (hc : 0 < c) (hm : c * N ≤ s) (C : ℝ) :
    C ^ 2 * ((N : ℝ) - s) / (((N : ℝ) - 1) * s) ≤ C ^ 2 / (c * N) := by
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsR1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsNR : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hn : (0 : ℝ) < N := by linarith
  have hNm1 : 0 < (N : ℝ) - 1 := by linarith
  have h1 : ((N : ℝ) - s) / (((N : ℝ) - 1) * s) ≤ 1 / (s : ℝ) := by
    apply (div_le_iff₀ (mul_pos hNm1 hsR)).2
    field_simp [ne_of_gt hsR]
    nlinarith
  have h2 : 1 / (s : ℝ) ≤ 1 / (c * N) :=
    one_div_le_one_div_of_le (mul_pos hc hn) hm
  calc
    _ = C ^ 2 * (((N : ℝ) - s) / (((N : ℝ) - 1) * s)) := by ring
    _ ≤ C ^ 2 * (1 / (c * N)) := mul_le_mul_of_nonneg_left (h1.trans h2) (sq_nonneg _)
    _ = _ := by ring

/-! Finite Markov bound, allocation limits, and the exact final statement. -/

private lemma GP022B1b_probability_mono (d : Design) (E F : Assignment d → Prop)
    (h : ∀ π, E π → F π) : designProbability d E ≤ designProbability d F := by
  classical
  apply Finset.expect_le_expect
  intro π _
  by_cases hE : E π
  · simp [hE, h π hE]
  · simp only [if_neg hE]
    split_ifs <;> norm_num

lemma GP022B1b_finite_rate (d : Design) (y1 y0 : Fin d.N → ℝ) (C c : ℝ)
    (hC : 0 ≤ C) (hy : ∀ i, |y1 i| ≤ C ∧ |y0 i| ≤ C)
    (hc : 0 < c) (hm : c * d.N ≤ d.m) (hk : c * d.N ≤ d.k)
    (ε : ℝ) (hε : 0 < ε) (hT : 16 * C ^ 2 / (c ^ 2 * ε) ≤ (d.N : ℝ))
    (B : BoundSide) :
    designProbability d (fun π => ε ≤ (d.N : ℝ) *
      |estimatedVariance d y1 y0 B π - populationBound d y1 y0 B|) ≤
      16 * (16 / c + 8) ^ 2 * C ^ 4 / (c * d.N * ε ^ 2) := by
  classical
  have hNnat : 0 < d.N := by have := d.population_min; omega
  have hmnat : 0 < d.m := by have := d.treatment_min; omega
  have hknat : 0 < d.k := by have := d.control_min; omega
  have hN : (0 : ℝ) < d.N := by exact_mod_cast hNnat
  let e1 : Fin d.m → Fin d.N := fun i =>
    ⟨i.val, by have := i.isLt; have := d.sample_le; omega⟩
  let e0 : Fin d.k → Fin d.N := fun i =>
    ⟨d.m + i.val, by have := i.isLt; have := d.sample_le; omega⟩
  have he1 : Function.Injective e1 := by
    intro i j hij
    have h := congrArg (fun q : Fin d.N => q.val) hij
    exact Fin.ext h
  have he0 : Function.Injective e0 := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    dsimp [e0] at h
    omega
  let D1 : Assignment d → ℝ := fun π => integratedCDFError C y1 (observedTreatment d y1 π)
  let D0 : Assignment d → ℝ := fun π => integratedCDFError C y0 (observedControl d y0 π)
  have hD1 : designExpectation d (fun π => D1 π ^ 2) ≤ C ^ 2 / (c * d.N) := by
    exact (GP022B1b_integrated_moment d hmnat e1 he1 y1 C hC).trans
      (GP022B1b_allocation_bound d.N d.m hmnat (by have := d.sample_le; omega)
        d.population_min c hc hm C)
  have hD0 : designExpectation d (fun π => D0 π ^ 2) ≤ C ^ 2 / (c * d.N) := by
    exact (GP022B1b_integrated_moment d hknat e0 he0 y0 C hC).trans
      (GP022B1b_allocation_bound d.N d.k hknat (by have := d.sample_le; omega)
        d.population_min c hc hk C)
  have hDs : designExpectation d (fun π => (D1 π + D0 π) ^ 2) ≤ 4 * C ^ 2 / (c * d.N) := by
    have h : designExpectation d (fun π => (D1 π + D0 π) ^ 2) ≤
        designExpectation d (fun π => 2 * D1 π ^ 2 + 2 * D0 π ^ 2) := by
      apply Finset.expect_le_expect
      intro π _
      nlinarith [sq_nonneg (D1 π - D0 π)]
    simp only [designExpectation, Finset.expect_add_distrib, ← Finset.mul_expect] at *
    linarith only [h, hD1, hD0,
      (by ring : 4 * C ^ 2 / (c * d.N) = 4 * (C ^ 2 / (c * d.N)))]
  let A : ℝ := (16 / c + 8) * C
  have hcor : 8 * C ^ 2 / (c ^ 2 * d.N) ≤ ε / 2 := by
    have h := (div_le_iff₀ (mul_pos (sq_pos_of_pos hc) hε)).mp hT
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hc) hN)).2
    nlinarith
  have hcontain (π : Assignment d) (hπ : ε ≤ (d.N : ℝ) *
      |estimatedVariance d y1 y0 B π - populationBound d y1 y0 B|) :
      ε / 2 ≤ |A * (D1 π + D0 π)| := by
    have hbound := GP022B1b_deterministic d y1 y0 C c hC hy hc hm hk B π
    change _ ≤ A * (D1 π + D0 π) + _ at hbound
    have habs := le_abs_self (A * (D1 π + D0 π))
    linarith
  apply (GP022B1b_probability_mono d _ _ hcontain).trans
  apply (finite_squared_markov d (fun π => A * (D1 π + D0 π)) (ε / 2)
    (by positivity)).trans
  have hmoment : designExpectation d (fun π => (A * (D1 π + D0 π)) ^ 2) ≤
      A ^ 2 * (4 * C ^ 2 / (c * d.N)) := by
    simp only [mul_pow, designExpectation, ← Finset.mul_expect]
    exact mul_le_mul_of_nonneg_left hDs (sq_nonneg _)
  calc
    _ ≤ (A ^ 2 * (4 * C ^ 2 / (c * d.N))) / (ε / 2) ^ 2 :=
      div_le_div_of_nonneg_right hmoment (sq_nonneg _)
    _ = _ := by
      dsimp [A]
      field_simp
      <;> ring

lemma GP022B1b_size_atTop (S : ExperimentSequence) :
    Tendsto (fun q => ((S.design q).N : ℝ)) atTop atTop := by
  have hshift : Tendsto (fun q : ℕ => q + 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat 4).2 tendsto_id
  simpa only [S.size, Function.comp_def] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hshift

lemma GP022B1b_control_ratio (S : ExperimentSequence) (θ ρ : ℝ)
    (hm : Tendsto (fun q => ((S.design q).m : ℝ) / (S.design q).N)
      atTop (𝓝 (θ * ρ)))
    (hn : Tendsto (fun q => (((S.design q).m : ℝ) + (S.design q).k) /
      (S.design q).N) atTop (𝓝 θ)) :
    Tendsto (fun q => ((S.design q).k : ℝ) / (S.design q).N)
      atTop (𝓝 (θ * (1 - ρ))) := by
  convert hn.sub hm using 1
  · funext q
    ring
  · ring

lemma GP022B1b_eventual_sizes (S : ExperimentSequence) (θ ρ c : ℝ)
    (hm : Tendsto (fun q => ((S.design q).m : ℝ) / (S.design q).N)
      atTop (𝓝 (θ * ρ)))
    (hn : Tendsto (fun q => (((S.design q).m : ℝ) + (S.design q).k) /
      (S.design q).N) atTop (𝓝 θ))
    (hc : c < min (θ * ρ) (θ * (1 - ρ))) :
    ∀ᶠ q in atTop, c * (S.design q).N ≤ (S.design q).m ∧
      c * (S.design q).N ≤ (S.design q).k := by
  have hmc : c < θ * ρ := lt_of_lt_of_le hc (min_le_left _ _)
  have hkc : c < θ * (1 - ρ) := lt_of_lt_of_le hc (min_le_right _ _)
  have hme := hm.eventually (eventually_gt_nhds hmc)
  have hke := (GP022B1b_control_ratio S θ ρ hm hn).eventually
    (eventually_gt_nhds hkc)
  filter_upwards [hme, hke] with q hmq hkq
  have hN : (0 : ℝ) < (S.design q).N := by
    exact_mod_cast (show 0 < (S.design q).N by
      have := (S.design q).population_min
      omega)
  exact ⟨((lt_div_iff₀ hN).mp hmq).le, ((lt_div_iff₀ hN).mp hkq).le⟩

/-- P022-T3: condition 1 and bounded outcomes alone give the explicit limsup
bound in the corrected proof of Proposition 2. No weak limit or atom-value
hypotheses occur. -/
lemma GP022B1b_asymptotic_rate :
    (∀ (S : ExperimentSequence)
      (θ ρ C : ℝ)
      (hθ : 0 < θ ∧ θ ≤ 1)
      (hρ : 0 < ρ ∧ ρ < 1)
      (hm : Tendsto (fun q => ((S.design q).m : ℝ) / (S.design q).N) atTop (𝓝 (θ * ρ)))
      (hn : Tendsto (fun q => (((S.design q).m : ℝ) + (S.design q).k) / (S.design q).N) atTop (𝓝 θ))
      (hC : 0 ≤ C)
      (hy : ∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C),
      ∀ ε c, 0 < ε → 0 < c → c < min (θ * ρ) (θ * (1 - ρ)) → ∀ B,
      scaledProbabilityLimsup S (fun q π => ε ≤ ((S.design q).N : ℝ) *
        |estimatedVariance (S.design q) (rowOutcomes S true q)
          (rowOutcomes S false q) B π - populationBound (S.design q)
            (rowOutcomes S true q) (rowOutcomes S false q) B|) ≤
        ENNReal.ofReal (16 * (16 / c + 8) ^ 2 * C ^ 4 / (c * ε ^ 2))) := by
  intro S θ ρ C hθ hρ hm hn hC hy ε c hε hc hcmin B
  have hsize := GP022B1b_size_atTop S
  have heT := hsize.eventually (eventually_ge_atTop (16 * C ^ 2 / (c ^ 2 * ε)))
  have heA := GP022B1b_eventual_sizes S θ ρ c hm hn hcmin
  unfold scaledProbabilityLimsup
  apply Filter.limsup_le_of_le (by isBoundedDefault)
  filter_upwards [heT, heA] with q hT hA
  apply ENNReal.ofReal_le_ofReal
  have hrow : ∀ i : Fin (S.design q).N,
      |rowOutcomes S true q i| ≤ C ∧ |rowOutcomes S false q i| ≤ C := by
    intro i
    exact hy i.val
  have hp := GP022B1b_finite_rate (S.design q) (rowOutcomes S true q)
    (rowOutcomes S false q) C c hC hrow hc hA.1 hA.2 ε hε hT B
  have hNpos : (0 : ℝ) < (S.design q).N := by
    exact_mod_cast (show 0 < (S.design q).N by
      have := (S.design q).population_min
      omega)
  calc
    _ ≤ ((S.design q).N : ℝ) *
        (16 * (16 / c + 8) ^ 2 * C ^ 4 / (c * (S.design q).N * ε ^ 2)) :=
      mul_le_mul_of_nonneg_left hp hNpos.le
    _ = _ := by
      field_simp [ne_of_gt hNpos]
      <;> ring

private lemma GP022B1b_small_allocation (θ ρ : ℝ)
    (hθ : 0 < θ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    0 < min (θ * ρ) (θ * (1 - ρ)) / 2 ∧
    min (θ * ρ) (θ * (1 - ρ)) / 2 < min (θ * ρ) (θ * (1 - ρ)) := by
  have ha : 0 < θ * ρ := mul_pos hθ hρ
  have hb : 0 < θ * (1 - ρ) := mul_pos hθ (by linarith)
  have hh : 0 < min (θ * ρ) (θ * (1 - ρ)) := lt_min ha hb
  constructor <;> linarith

private lemma GP022B1b_rate_constant_nonneg (c : ℝ) (hc : 0 < c) :
    0 ≤ 16 * (16 / c + 8) ^ 2 / c := by positivity

private lemma GP022B1b_tolerance_comparison (D C ε ε1 ε2 ε3 : ℝ)
    (hD : 0 ≤ D) (h1 : 0 < ε1) (h2 : 0 < ε2) (h3 : 0 < ε3)
    (he : ε1 + ε2 + ε3 = ε) :
    D * C ^ 4 / ε ^ 2 ≤ C ^ 4 * (D / ε1 ^ 2) ∧
    D * C ^ 4 / ε ^ 2 ≤ C ^ 4 * (1 / ε1 ^ 2 + D / ε2 ^ 2 + 0) := by
  have hepos : 0 < ε := by linarith
  have he1 : ε1 ≤ ε := by linarith
  have he2 : ε2 ≤ ε := by linarith
  have hs1 : ε1 ^ 2 ≤ ε ^ 2 := by nlinarith
  have hs2 : ε2 ^ 2 ≤ ε ^ 2 := by nlinarith
  have hh1 : D / ε ^ 2 ≤ D / ε1 ^ 2 :=
    div_le_div_of_nonneg_left hD (sq_pos_of_pos h1) hs1
  have hh2 : D / ε ^ 2 ≤ D / ε2 ^ 2 :=
    div_le_div_of_nonneg_left hD (sq_pos_of_pos h2) hs2
  have hC4 : 0 ≤ C ^ 4 := by positivity
  have hbase : D * C ^ 4 / ε ^ 2 = C ^ 4 * (D / ε ^ 2) := by ring
  rw [hbase]
  constructor
  · exact mul_le_mul_of_nonneg_left hh1 hC4
  · apply mul_le_mul_of_nonneg_left _ hC4
    have hp : 0 ≤ 1 / ε1 ^ 2 := by positivity
    linarith

theorem proposition2_proof (H : JointLaw) (θ ρ C : ℝ) (hC : 0 ≤ C) :
    ∃ κ1 κ2 κ3 : ℝ → ℝ, (∀ ε, 0 < ε → 0 ≤ κ1 ε ∧ 0 ≤ κ2 ε ∧ 0 ≤ κ3 ε) ∧
    ∀ S : ExperimentSequence, Conditions123 S H θ ρ →
    (∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C) →
    ∀ ε ε1 ε2 ε3, 0 < ε1 → 0 < ε2 → 0 < ε3 → ε1 + ε2 + ε3 = ε →
    scaledProbabilityLimsup S (fun q π => ε ≤ ((S.design q).N : ℝ) *
      |estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H π -
        populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H|) ≤
      ENNReal.ofReal (C ^ 4 * κ1 ε1) ∧
    scaledProbabilityLimsup S (fun q π => ε ≤ ((S.design q).N : ℝ) *
      |estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .L π -
        populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .L|) ≤
      ENNReal.ofReal (C ^ 4 * (1 / ε1 ^ 2 + κ2 ε2 + κ3 ε3)) := by
  classical
  by_cases hp : (0 < θ ∧ θ ≤ 1) ∧ (0 < ρ ∧ ρ < 1)
  · let c : ℝ := min (θ * ρ) (θ * (1 - ρ)) / 2
    let D : ℝ := 16 * (16 / c + 8) ^ 2 / c
    have hc : 0 < c := (GP022B1b_small_allocation θ ρ hp.1.1 hp.2.1 hp.2.2).1
    have hcmin : c < min (θ * ρ) (θ * (1 - ρ)) :=
      (GP022B1b_small_allocation θ ρ hp.1.1 hp.2.1 hp.2.2).2
    have hD : 0 ≤ D := GP022B1b_rate_constant_nonneg c hc
    refine ⟨(fun x => D / x ^ 2), (fun x => D / x ^ 2), (fun _ => 0), ?_, ?_⟩
    · intro x hx
      exact ⟨div_nonneg hD (sq_nonneg x), div_nonneg hD (sq_nonneg x), le_rfl⟩
    · intro S hS hy ε ε1 ε2 ε3 h1 h2 h3 he
      have hepos : 0 < ε := by linarith
      have hrate : ∀ B,
          scaledProbabilityLimsup S (fun q π => ε ≤ ((S.design q).N : ℝ) *
            |estimatedVariance (S.design q) (rowOutcomes S true q)
                (rowOutcomes S false q) B π - populationBound (S.design q)
                  (rowOutcomes S true q) (rowOutcomes S false q) B|) ≤
            ENNReal.ofReal (16 * (16 / c + 8) ^ 2 * C ^ 4 / (c * ε ^ 2)) := by
        exact GP022B1b_asymptotic_rate S θ ρ C hp.1 hp.2
          hS.2.2.2.2.1 hS.2.2.2.2.2.1 hC hy ε c hepos hc hcmin
      have hconstant : 16 * (16 / c + 8) ^ 2 * C ^ 4 / (c * ε ^ 2) =
          D * C ^ 4 / ε ^ 2 := by
        dsimp [D]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      have hcomp := GP022B1b_tolerance_comparison D C ε ε1 ε2 ε3 hD h1 h2 h3 he
      constructor
      · exact (hrate .H).trans (ENNReal.ofReal_le_ofReal (by
          rw [hconstant]
          exact hcomp.1))
      · exact (hrate .L).trans (ENNReal.ofReal_le_ofReal (by
          rw [hconstant]
          exact hcomp.2))
  · refine ⟨(fun _ => 0), (fun _ => 0), (fun _ => 0), ?_, ?_⟩
    · intro ε hε
      exact ⟨le_rfl, le_rfl, le_rfl⟩
    · intro S hS
      exact False.elim (hp ⟨⟨hS.1, hS.2.1⟩, ⟨hS.2.2.1, hS.2.2.2.1⟩⟩)

end

end AronowAudit.P022.Wave1
