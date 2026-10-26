import AronowAudit.P022.P022_Variance
import AronowAudit.P022.Wave1.SharpBounds.N1
import AronowAudit.P022.Wave1.SharpBounds.N2
import AronowAudit.P022.Wave1.SharpBounds.N3
import AronowAudit.P022.Wave1.SharpBounds.N4
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Group.MinMax

namespace AronowAudit.P022.Wave1
open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option autoImplicit false
noncomputable section

lemma GP022B2b_mean_integral {n : ℕ} (f : Fin n → ℝ → ℝ) (a b : ℝ)
    (hf : ∀ i, IntervalIntegrable (f i) volume a b) :
    (∫ x in a..b, finiteMean (fun i => f i x)) =
      finiteMean (fun i => ∫ x in a..b, f i x) := by
  simp only [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finset_sum]
  exact fun i _ => hf i

lemma GP022B2b_step_integrable (v a b : ℝ) :
    IntervalIntegrable (fun x => if v ≤ x then (1 : ℝ) else 0) volume a b := by
  apply Monotone.intervalIntegrable
  intro x y hxy
  dsimp only
  split_ifs <;> norm_num <;> linarith

lemma GP022B2b_step_integral (C v : ℝ) (hv : |v| ≤ C) :
    (∫ x in (-C)..C, if v ≤ x then (1 : ℝ) else 0) = C - v := by
  have hv' := abs_le.mp hv
  have hleft : (∫ x in (-C)..v, if v ≤ x then (1 : ℝ) else 0) = 0 := by
    calc
      _ = ∫ _ in (-C)..v, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        rw [Set.uIoo_of_le hv'.1]
        intro x hx
        simp only [if_neg (not_le.mpr hx.2)]
      _ = 0 := intervalIntegral.integral_zero
  have hright : (∫ x in v..C, if v ≤ x then (1 : ℝ) else 0) = C - v := by
    calc
      _ = ∫ _ in v..C, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        rw [Set.uIoo_of_le hv'.2]
        intro x hx
        simp only [if_pos hx.1.le]
      _ = C - v := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (GP022B2b_step_integrable v (-C) v) (GP022B2b_step_integrable v v C),
    hleft, hright, zero_add]

lemma GP022B2b_common_cell {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (j : Fin (m * k)) (u : ℝ)
    (hl : (j : ℝ) / (m * k) < u) (hu : u < ((j : ℝ) + 1) / (m * k)) :
    empiricalQuantile a u = sortedValues a
      ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlow : ((j.val / k : ℕ) : ℝ) * k ≤ j := by
    exact_mod_cast Nat.div_mul_le_self j.val k
  have hupp : (j : ℝ) + 1 ≤ (((j.val / k : ℕ) : ℝ) + 1) * k := by
    exact_mod_cast (show j.val + 1 ≤ (j.val / k + 1) * k by
      rw [Nat.add_mul, one_mul, Nat.mul_comm (j.val / k) k]
      have := Nat.mod_lt j.val hk
      have := Nat.mod_add_div j.val k
      omega)
  have hl' := (div_lt_iff₀ (mul_pos hmR hkR)).mp hl
  have hu' := (lt_div_iff₀ (mul_pos hmR hkR)).mp hu
  apply (SharpBounds.n3_proof a _ u ?_ ?_).1
  · apply (div_lt_iff₀ hmR).mpr
    nlinarith
  · apply (lt_div_iff₀ hmR).mpr
    nlinarith

lemma GP022B2b_lift_mean {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (f : ℝ → ℝ) :
    finiteMean (fun j : Fin (m * k) => f (sortedValues a
      ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩)) = finiteMean (fun i => f (a i)) := by
  letI : NeZero (m * k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm hk)⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  calc
    _ = ∫ u in (0 : ℝ)..1, f (empiricalQuantile a u) := by
      symm
      apply SharpBounds.n4_proof
      intro j u hl hu
      exact congrArg f (GP022B2b_common_cell hm hk a j u (by exact_mod_cast hl)
        (by exact_mod_cast hu))
    _ = finiteMean (fun i => f (sortedValues a i)) := by
      apply SharpBounds.n4_proof
      intro j u hl hu
      exact congrArg f (SharpBounds.n3_proof a j u hl hu).1
    _ = _ := SharpBounds.n1_proof _ _ (SharpBounds.n2_proof a).1 f

lemma GP022B2b_lower_joint {n : ℕ} (a b : Fin n → ℝ)
    (ha : Monotone a) (hb : Monotone b) (x y : ℝ) :
    finiteMean (fun i => if a i ≤ x ∧ b i ≤ y then (1 : ℝ) else 0) =
      min (empiricalCDF a x) (empiricalCDF b y) := by
  classical
  have hnested : (∀ i, a i ≤ x → b i ≤ y) ∨ (∀ i, b i ≤ y → a i ≤ x) := by
    by_cases h : ∀ i, a i ≤ x → b i ≤ y
    · exact Or.inl h
    · right
      push_neg at h
      obtain ⟨i, hi, hbi⟩ := h
      intro j hj
      have hji : j ≤ i := by
        by_contra h'
        exact (not_le.mpr hbi) (le_trans (hb (le_of_not_ge h')) hj)
      exact (ha hji).trans hi
  rcases hnested with h | h
  · have hle : empiricalCDF a x ≤ empiricalCDF b y := by
      apply Finset.expect_le_expect
      intro i _
      split_ifs <;> simp_all
    rw [min_eq_left hle]
    unfold empiricalCDF finiteMean
    apply Finset.expect_congr rfl
    intro i _
    by_cases hi : a i ≤ x
    · simp [hi, h i hi]
    · simp [hi]
  · have hle : empiricalCDF b y ≤ empiricalCDF a x := by
      apply Finset.expect_le_expect
      intro i _
      split_ifs <;> simp_all
    rw [min_eq_right hle]
    unfold empiricalCDF finiteMean
    apply Finset.expect_congr rfl
    intro i _
    by_cases hi : b i ≤ y
    · simp [hi, h i hi]
    · simp [hi]

lemma GP022B2b_pair_integral {n : ℕ} (a b : Fin n → ℝ) (C : ℝ)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ i, |b i| ≤ C) :
    (∫ x in (-C)..C, ∫ y in (-C)..C,
      finiteMean (fun i => if a i ≤ x ∧ b i ≤ y then (1 : ℝ) else 0)) =
      finiteMean (fun i => (C - a i) * (C - b i)) := by
  have hinner (x : ℝ) : (∫ y in (-C)..C,
      finiteMean (fun i => if a i ≤ x ∧ b i ≤ y then (1 : ℝ) else 0)) =
      finiteMean (fun i => (if a i ≤ x then (1 : ℝ) else 0) * (C - b i)) := by
    rw [GP022B2b_mean_integral]
    · congr 1
      funext i
      by_cases hi : a i ≤ x
      · simp only [hi, true_and, if_pos, one_mul, GP022B2b_step_integral C (b i) (hb i)]
      · simp only [hi, false_and, if_false, intervalIntegral.integral_zero, zero_mul]
    · intro i
      by_cases hi : a i ≤ x
      · simpa only [hi, true_and] using GP022B2b_step_integrable (b i) (-C) C
      · simpa only [hi, false_and, if_false] using
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-C) C)
  simp_rw [hinner]
  rw [GP022B2b_mean_integral]
  · congr 1
    funext i
    rw [intervalIntegral.integral_mul_const, GP022B2b_step_integral C (a i) (ha i)]
  · intro i
    exact (GP022B2b_step_integrable (a i) (-C) C).mul_const _


/-- Bounded raw quantile product, proved on the common rank grid. -/
lemma GP022B2b_bounded_raw_quantile_product {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ i, |b i| ≤ C) :
    (∫ u in (0 : ℝ)..1, empiricalQuantile a u * empiricalQuantile b u) =
      -C ^ 2 + C * (finiteMean a + finiteMean b) +
        ∫ x in (-C)..C, ∫ y in (-C)..C,
          min (empiricalCDF a x) (empiricalCDF b y) := by
  classical
  letI : NeZero (m * k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm hk)⟩
  let A : Fin (m * k) → ℝ := fun j => sortedValues a
    ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩
  let B : Fin (m * k) → ℝ := fun j => sortedValues b
    ⟨j.val / m, (Nat.div_lt_iff_lt_mul hm).mpr (by simpa [Nat.mul_comm] using j.isLt)⟩
  have hA (f : ℝ → ℝ) : finiteMean (fun j => f (A j)) = finiteMean (fun i => f (a i)) :=
    GP022B2b_lift_mean hm hk a f
  have hB (f : ℝ → ℝ) : finiteMean (fun j => f (B j)) = finiteMean (fun i => f (b i)) := by
    calc
      _ = finiteMean (fun j : Fin (k * m) => f (sortedValues b
          ⟨j.val / m, (Nat.div_lt_iff_lt_mul hm).mpr j.isLt⟩)) := by
        exact Fintype.expect_equiv (finCongr (Nat.mul_comm m k)) _ _ (fun _ => rfl)
      _ = _ := GP022B2b_lift_mean hk hm b f
  have hmonoA : Monotone A := fun i j hij =>
    (SharpBounds.n2_proof a).2.2 (Nat.div_le_div_right hij)
  have hmonoB : Monotone B := fun i j hij =>
    (SharpBounds.n2_proof b).2.2 (Nat.div_le_div_right hij)
  have hAb : ∀ j, |A j| ≤ C := by
    intro j
    have hj : A j ∈ List.ofFn a := (SharpBounds.n2_proof a).1.mem_iff.mp
      (List.mem_ofFn.mpr ⟨_, rfl⟩)
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hj
    simpa only [hi] using ha i
  have hBb : ∀ j, |B j| ≤ C := by
    intro j
    have hj : B j ∈ List.ofFn b := (SharpBounds.n2_proof b).1.mem_iff.mp
      (List.mem_ofFn.mpr ⟨_, rfl⟩)
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hj
    simpa only [hi] using hb i
  have hprod : (∫ u in (0 : ℝ)..1, empiricalQuantile a u * empiricalQuantile b u) =
      finiteMean (fun j => A j * B j) := by
    apply SharpBounds.n4_proof
    intro j u hl hu
    have hqa := GP022B2b_common_cell hm hk a j u (by exact_mod_cast hl) (by exact_mod_cast hu)
    have hqb := GP022B2b_common_cell hk hm b
      ⟨j.val, by simpa [Nat.mul_comm] using j.isLt⟩ u
      (by simpa only [Nat.cast_mul, mul_comm] using hl)
      (by simpa only [Nat.cast_mul, mul_comm] using hu)
    exact congrArg₂ (· * ·) hqa hqb
  have hcdf (x y : ℝ) : min (empiricalCDF a x) (empiricalCDF b y) =
      finiteMean (fun i => if A i ≤ x ∧ B i ≤ y then (1 : ℝ) else 0) := by
    rw [GP022B2b_lower_joint A B hmonoA hmonoB]
    exact congrArg₂ min (hA (fun z => if z ≤ x then (1 : ℝ) else 0)).symm
      (hB (fun z => if z ≤ y then (1 : ℝ) else 0)).symm
  simp_rw [hcdf]
  rw [GP022B2b_pair_integral A B C hAb hBb, hprod]
  have hexpand : finiteMean (fun i => (C - A i) * (C - B i)) =
      C ^ 2 - C * (finiteMean a + finiteMean b) + finiteMean (fun i => A i * B i) := by
    have heq : (fun i => (C - A i) * (C - B i)) =
        (fun i => C ^ 2 - C * (A i + B i) + A i * B i) := by funext i; ring
    rw [heq]
    simp only [finiteMean, Finset.expect_add_distrib, Finset.expect_sub_distrib,
      ← Finset.mul_expect, Finset.expect_const Finset.univ_nonempty]
    change C ^ 2 - C * (finiteMean A + finiteMean B) + _ = _
    have hAm : finiteMean A = finiteMean a := by simpa using hA id
    have hBm : finiteMean B = finiteMean b := by simpa using hB id
    rw [hAm, hBm]
    rfl
  rw [hexpand]
  ring

lemma GP022B2b_proposition2_corrected_finite_empiricalCDF_mono {s : ℕ} (a : Fin s → ℝ) :
    Monotone (empiricalCDF a) := by
  classical
  intro x y hxy
  unfold empiricalCDF finiteMean
  apply Finset.expect_le_expect
  intro i _
  by_cases hix : a i ≤ x
  · simp only [if_pos hix, if_pos (hix.trans hxy), le_refl]
  · simp only [if_neg hix]
    split_ifs <;> norm_num

lemma GP022B2b_proposition2_corrected_finite_cdfDistance_bdd {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) :
    BddAbove (Set.range (fun x => |empiricalCDF a x - empiricalCDF b x|)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨ha₀, ha₁⟩ := empirical_cdf_bounds hm a x
  obtain ⟨hb₀, hb₁⟩ := empirical_cdf_bounds hk b x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma GP022B2b_proposition2_corrected_finite_cdfDistance_pointwise {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (x : ℝ) :
    |empiricalCDF a x - empiricalCDF b x| ≤
      cdfDistance (empiricalCDF a) (empiricalCDF b) := by
  exact le_csSup (GP022B2b_proposition2_corrected_finite_cdfDistance_bdd hm hk a b) ⟨x, rfl⟩

/-- Every inner min-CDF integral is integrable. This uses monotonicity,
so no continuity at the empirical jumps is needed. -/
lemma GP022B2b_proposition2_corrected_finite_inner_integrable {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (C x : ℝ) :
    IntervalIntegrable (fun y => min (empiricalCDF a x) (empiricalCDF b y))
      volume (-C) C := by
  have hmono : Monotone (fun y => min (empiricalCDF a x) (empiricalCDF b y)) :=
    monotone_const.min (GP022B2b_proposition2_corrected_finite_empiricalCDF_mono b)
  exact hmono.intervalIntegrable

lemma GP022B2b_proposition2_corrected_finite_outer_integrable {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (C : ℝ) (hC : 0 ≤ C) :
    IntervalIntegrable (fun x => ∫ y in (-C)..C,
      min (empiricalCDF a x) (empiricalCDF b y)) volume (-C) C := by
  have hmono : Monotone (fun x => ∫ y in (-C)..C,
      min (empiricalCDF a x) (empiricalCDF b y)) := by
    intro x x' hxx'
    apply intervalIntegral.integral_mono (by linarith : -C ≤ C)
      (GP022B2b_proposition2_corrected_finite_inner_integrable a b C x)
      (GP022B2b_proposition2_corrected_finite_inner_integrable a b C x')
    intro y
    exact min_le_min ((GP022B2b_proposition2_corrected_finite_empiricalCDF_mono a) hxx') le_rfl
  exact hmono.intervalIntegrable

/-- Linearity for the actual iterated CDF integral in T7. -/
lemma GP022B2b_proposition2_corrected_finite_double_integral_sub {m k N : ℕ}
    (a : Fin m → ℝ) (b : Fin k → ℝ) (y1 y0 : Fin N → ℝ)
    (C : ℝ) (hC : 0 ≤ C) :
    (∫ x in (-C)..C, ∫ y in (-C)..C,
      min (empiricalCDF a x) (empiricalCDF b y) -
        min (empiricalCDF y1 x) (empiricalCDF y0 y)) =
      (∫ x in (-C)..C, ∫ y in (-C)..C,
        min (empiricalCDF a x) (empiricalCDF b y)) -
      (∫ x in (-C)..C, ∫ y in (-C)..C,
        min (empiricalCDF y1 x) (empiricalCDF y0 y)) := by
  have hinner : ∀ x,
      (∫ y in (-C)..C, min (empiricalCDF a x) (empiricalCDF b y) -
        min (empiricalCDF y1 x) (empiricalCDF y0 y)) =
      (∫ y in (-C)..C, min (empiricalCDF a x) (empiricalCDF b y)) -
        (∫ y in (-C)..C, min (empiricalCDF y1 x) (empiricalCDF y0 y)) := by
    intro x
    exact intervalIntegral.integral_sub
      (GP022B2b_proposition2_corrected_finite_inner_integrable a b C x)
      (GP022B2b_proposition2_corrected_finite_inner_integrable y1 y0 C x)
  simp_rw [hinner]
  exact intervalIntegral.integral_sub
    (GP022B2b_proposition2_corrected_finite_outer_integrable a b C hC)
    (GP022B2b_proposition2_corrected_finite_outer_integrable y1 y0 C hC)

/-- A deterministic identity for the defined finite-population correction. -/
lemma GP022B2b_proposition2_corrected_finite_marginal_as_variance {s : ℕ} (N : ℕ) (a : Fin s → ℝ) :
    marginalVarianceEstimate N a =
      (((N : ℝ) - 1) / N) *
        ((s : ℝ) * finiteVariance a / ((s : ℝ) - 1)) := by
  have hsum : (∑ i, (a i - finiteMean a) ^ 2) =
      (s : ℝ) * finiteVariance a := by
    simpa only [Fintype.card_fin, finiteVariance, finiteMean] using
      (Fintype.card_mul_expect (fun i => (a i - finiteMean a) ^ 2)).symm
  unfold marginalVarianceEstimate sampleVariance
  rw [hsum]


lemma GP022B2b_proposition2_corrected_finite_seven_term_identity (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hy : ∀ i, |y1 i| ≤ C ∧ |y0 i| ≤ C)
    (π : Assignment d) :
    (d.N : ℝ) * (estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H) =
      sevenTotal (sevenTerms d y1 y0 C π) := by
  classical
  have hNnat : 0 < d.N := by have := d.population_min; omega
  have hmnat : 0 < d.m := by have := d.treatment_min; omega
  have hknat : 0 < d.k := by have := d.control_min; omega
  have hN : (0 : ℝ) < d.N := by exact_mod_cast hNnat
  have hm : (0 : ℝ) < d.m := by exact_mod_cast hmnat
  have hk : (0 : ℝ) < d.k := by exact_mod_cast hknat
  have hN₁ : (0 : ℝ) < (d.N : ℝ) - 1 := by
    have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  have hm₁ : (0 : ℝ) < (d.m : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ d.m := by exact_mod_cast d.treatment_min
    linarith
  have hk₁ : (0 : ℝ) < (d.k : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ d.k := by exact_mod_cast d.control_min
    linarith
  let a := observedTreatment d y1 π
  let b := observedControl d y0 π
  have ha : ∀ i, |a i| ≤ C := by
    intro i
    exact (hy (π ⟨i.val, by have := d.sample_le; have := i.isLt; omega⟩)).1
  have hb : ∀ i, |b i| ≤ C := by
    intro i
    exact (hy (π ⟨d.m + i.val, by have := d.sample_le; have := i.isLt; omega⟩)).2
  have hrawa := GP022B2b_bounded_raw_quantile_product hmnat hknat a b C hC ha hb
  have hrawy := GP022B2b_bounded_raw_quantile_product hNnat hNnat y1 y0 C hC
    (fun i => (hy i).1) (fun i => (hy i).2)
  have hcov : sharpCovariance a b .H - sharpCovariance y1 y0 .H =
      C * (finiteMean a - finiteMean y1 + finiteMean b - finiteMean y0) -
      (finiteMean a * finiteMean b - finiteMean y1 * finiteMean y0) +
      (∫ x in (-C)..C, ∫ y in (-C)..C,
        min (empiricalCDF a x) (empiricalCDF b y) -
          min (empiricalCDF y1 x) (empiricalCDF y0 y)) := by
    simp only [sharpCovariance, if_pos rfl, ite_true]
    rw [hrawa, hrawy, GP022B2b_proposition2_corrected_finite_double_integral_sub a b y1 y0 C hC]
    ring
  -- Separate the covariance difference before expanding the marginal terms.
  have hsplit : (d.N : ℝ) *
      (estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H) =
      (d.N : ℝ) / ((d.N : ℝ) - 1) *
        (((d.N : ℝ) - d.m) / d.m *
          (marginalVarianceEstimate d.N a - finiteVariance y1) +
         ((d.N : ℝ) - d.k) / d.k *
          (marginalVarianceEstimate d.N b - finiteVariance y0) +
         2 * (sharpCovariance a b .H - sharpCovariance y1 y0 .H)) := by
    dsimp [estimatedVariance, estimateBound, populationBound, varianceExpression, a, b]
    ring
  rw [hsplit, hcov, GP022B2b_proposition2_corrected_finite_marginal_as_variance d.N a,
    GP022B2b_proposition2_corrected_finite_marginal_as_variance d.N b,
    finite_variance_second_moment hmnat a,
    finite_variance_second_moment hknat b,
    finite_variance_second_moment hNnat y1,
    finite_variance_second_moment hNnat y0]
  simp [sevenTotal, sevenTerms, lastIntegralTerm, frechetCDF]
  dsimp only [a, b]
  field_simp [ne_of_gt hN, ne_of_gt hm, ne_of_gt hk,
    ne_of_gt hN₁, ne_of_gt hm₁, ne_of_gt hk₁]
  <;> ring

/-- A finite union bound expressed directly in the actual assignment average. -/
lemma GP022B2b_proposition2_corrected_finite_finite_union_bound (d : Design) (E : Assignment d → Prop)
    (F : Fin 7 → Assignment d → Prop) (h : ∀ π, E π → ∃ j, F j π) :
    designProbability d E ≤ ∑ j, designProbability d (F j) := by
  classical
  unfold designProbability designExpectation
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro π _
  by_cases hE : E π
  · rw [if_pos hE]
    obtain ⟨j, hj⟩ := h π hE
    calc
      (1 : ℝ) = if F j π then 1 else 0 := by rw [if_pos hj]
      _ ≤ ∑ i : Fin 7, if F i π then (1 : ℝ) else 0 := by
        exact Finset.single_le_sum (f := fun i : Fin 7 => if F i π then (1 : ℝ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
  · rw [if_neg hE]
    apply Finset.sum_nonneg
    intro j _
    dsimp only
    split_ifs <;> norm_num

lemma GP022B2b_proposition2_corrected_finite_last_integral_sup_bound (d : Design) (y1 y0 : Fin d.N → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (π : Assignment d) :
    |lastIntegralTerm d y1 y0 C π| ≤
      (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) *
        max (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1))
          (cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0)) := by
  have hNnat : 0 < d.N := by have := d.population_min; omega
  have hmnat : 0 < d.m := by have := d.treatment_min; omega
  have hknat : 0 < d.k := by have := d.control_min; omega
  have hN : (0 : ℝ) < d.N := by exact_mod_cast hNnat
  have hN₁ : (0 : ℝ) < (d.N : ℝ) - 1 := by
    have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  let a := observedTreatment d y1 π
  let b := observedControl d y0 π
  let M := max (cdfDistance (empiricalCDF a) (empiricalCDF y1))
    (cdfDistance (empiricalCDF b) (empiricalCDF y0))
  let f : ℝ → ℝ → ℝ := fun x y =>
    min (empiricalCDF a x) (empiricalCDF b y) -
      min (empiricalCDF y1 x) (empiricalCDF y0 y)
  have hpoint : ∀ x y, |f x y| ≤ M := by
    intro x y
    exact (abs_min_sub_min_le_max _ _ _ _).trans
      (max_le_max
        (GP022B2b_proposition2_corrected_finite_cdfDistance_pointwise hmnat hNnat a y1 x)
        (GP022B2b_proposition2_corrected_finite_cdfDistance_pointwise hknat hNnat b y0 y))
  have hlen : |C - -C| = 2 * C := by
    rw [abs_of_nonneg (by linarith : 0 ≤ C - -C)]
    ring
  have hinner : ∀ x, |∫ y in (-C)..C, f x y| ≤ M * (2 * C) := by
    intro x
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -C) (b := C) (f := f x) (C := M)
      (fun y _ => by simpa only [Real.norm_eq_abs] using hpoint x y)
    simpa only [Real.norm_eq_abs, hlen] using h
  have houter : |∫ x in (-C)..C, ∫ y in (-C)..C, f x y| ≤
      (M * (2 * C)) * (2 * C) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -C) (b := C) (f := fun x => ∫ y in (-C)..C, f x y)
      (C := M * (2 * C))
      (fun x _ => by simpa only [Real.norm_eq_abs] using hinner x)
    simpa only [Real.norm_eq_abs, hlen] using h
  have hcoef : 0 ≤ 2 * (d.N : ℝ) / ((d.N : ℝ) - 1) := by positivity
  change |(2 * (d.N : ℝ) / ((d.N : ℝ) - 1)) *
    (∫ x in (-C)..C, ∫ y in (-C)..C, f x y)| ≤
      (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) * M
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    (2 * (d.N : ℝ) / ((d.N : ℝ) - 1)) *
        |∫ x in (-C)..C, ∫ y in (-C)..C, f x y| ≤
        (2 * (d.N : ℝ) / ((d.N : ℝ) - 1)) * ((M * (2 * C)) * (2 * C)) :=
      mul_le_mul_of_nonneg_left houter hcoef
    _ = (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) * M := by ring

theorem proposition2_corrected_finite_proof (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hy : ∀ i, |y1 i| ≤ C ∧ |y0 i| ≤ C) :
    (∀ π, ((d.N : ℝ) * (estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H)) =
      sevenTotal (sevenTerms d y1 y0 C π)) ∧
    (∀ a : Fin 7 → ℝ, ∀ ε, (∀ j, 0 < a j) → (∑ j, a j) ≤ ε →
      designProbability d (fun π => ε ≤ (d.N : ℝ) *
        |estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H|) ≤
      ∑ j, designProbability d (fun π => a j ≤ |sevenTerms d y1 y0 C π j|)) ∧
    (∀ π, |lastIntegralTerm d y1 y0 C π| ≤
      (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) *
        max (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1))
          (cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0))) ∧
    (∀ x, 0 < x → ∀ π, x ≤ |lastIntegralTerm d y1 y0 C π| →
      ((d.N : ℝ) - 1) * x / (8 * d.N * C ^ 2) ≤
        cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1) ∨
      ((d.N : ℝ) - 1) * x / (8 * d.N * C ^ 2) ≤
        cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0)) := by
  classical
  have hN : (0 : ℝ) < d.N := by
    exact_mod_cast (show 0 < d.N by have := d.population_min; omega)
  have hN₁ : (0 : ℝ) < (d.N : ℝ) - 1 := by
    have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  have hidentity := GP022B2b_proposition2_corrected_finite_seven_term_identity d y1 y0 C hC hy
  have hsup := GP022B2b_proposition2_corrected_finite_last_integral_sup_bound d y1 y0 C hC
  refine ⟨hidentity, ?_, hsup, ?_⟩
  · intro a ε ha hbudget
    apply GP022B2b_proposition2_corrected_finite_finite_union_bound d
    intro π hlarge
    have habs : (d.N : ℝ) *
        |estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H| =
        |sevenTotal (sevenTerms d y1 y0 C π)| := by
      rw [← hidentity π, abs_mul, abs_of_pos hN]
    rw [habs] at hlarge
    exact seven_term_budget (sevenTerms d y1 y0 C π) a ε ha hbudget hlarge
  · intro x hx π hlarge
    by_cases hzero : C = 0
    · have hz : lastIntegralTerm d y1 y0 C π = 0 := by
        simp only [lastIntegralTerm, hzero, neg_zero, intervalIntegral.integral_same,
          mul_zero]
      rw [hz, abs_zero] at hlarge
      exact False.elim (not_le_of_gt hx hlarge)
    · have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
      have hden : 0 < 8 * (d.N : ℝ) * C ^ 2 := by positivity
      have hmax : ((d.N : ℝ) - 1) * x / (8 * d.N * C ^ 2) ≤
          max (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1))
            (cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0)) := by
        apply (div_le_iff₀ hden).2
        have hbound := hlarge.trans (hsup π)
        have hcleared := (le_div_iff₀ hN₁).mp
          (show x ≤
            (8 * d.N * C ^ 2 *
              max (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1))
                (cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0))) /
                ((d.N : ℝ) - 1) by
            convert hbound using 1 <;> ring)
        nlinarith [hcleared]
      exact le_max_iff.mp hmax

end
end AronowAudit.P022.Wave1
