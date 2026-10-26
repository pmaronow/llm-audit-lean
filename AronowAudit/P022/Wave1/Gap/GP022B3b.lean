import AronowAudit.P022.P022_Variance
import AronowAudit.P022.Wave1.SharpBounds.N1
import AronowAudit.P022.Wave1.SharpBounds.N2
import AronowAudit.P022.Wave1.SharpBounds.N3
import AronowAudit.P022.Wave1.SharpBounds.N4
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
The corrected Proposition 2 limit step.
The finite covariance/CDF identity is proved on a common rank grid, using
only the sorting and empirical rank-cell integration lemmas.
-/

namespace AronowAudit.P022.Wave1

open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option autoImplicit false
noncomputable section

private lemma GP022B3b_quantile_law {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ)
    (f : ℝ → ℝ) :
    (∫ u in (0 : ℝ)..1, f (empiricalQuantile a u)) = finiteMean (fun i => f (a i)) := by
  letI GP022B3b_neZeroM : NeZero m := ⟨hm.ne'⟩
  calc
    _ = finiteMean (fun i => f (sortedValues a i)) := by
      apply SharpBounds.n4_proof
      intro j u hl hu
      rw [(SharpBounds.n3_proof a j u hl hu).1]
    _ = _ := SharpBounds.n1_proof _ _ (SharpBounds.n2_proof a).1 f

private def GP022B3b_expand {m : ℕ} (a : Fin m → ℝ) (k : ℕ) (hk : 0 < k) :
    Fin (m * k) → ℝ := fun j => sortedValues a
      ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).2 j.isLt⟩

private lemma GP022B3b_expand_cell {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (j : Fin (m * k)) (u : ℝ)
    (hl : (j : ℝ) / (m * k : ℕ) < u)
    (hu : u < ((j : ℝ) + 1) / (m * k : ℕ)) :
    empiricalQuantile a u = GP022B3b_expand a k hk j := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hL := (div_lt_iff₀ (mul_pos hmR hkR)).mp (show
      (j : ℝ) / ((m : ℝ) * k) < u by simpa using hl)
  have hU := (lt_div_iff₀ (mul_pos hmR hkR)).mp (show
      u < ((j : ℝ) + 1) / ((m : ℝ) * k) by simpa using hu)
  have hlo : (j.val / k : ℕ) * k ≤ j.val := Nat.div_mul_le_self _ _
  have hhi : j.val + 1 ≤ (j.val / k + 1) * k := by
    simpa only [Nat.mul_comm] using Nat.succ_le_of_lt (Nat.lt_mul_div_succ j.val hk)
  have hloR : ((j.val / k : ℕ) : ℝ) * k ≤ j.val := by exact_mod_cast hlo
  have hhiR : (j.val : ℝ) + 1 ≤ (((j.val / k : ℕ) : ℝ) + 1) * k := by
    exact_mod_cast hhi
  apply (SharpBounds.n3_proof a
    ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).2 j.isLt⟩ u ?_ ?_).1
  · apply (div_lt_iff₀ hmR).2
    change ((j.val / k : ℕ) : ℝ) < u * m
    nlinarith
  · apply (lt_div_iff₀ hmR).2
    change u * m < ((j.val / k : ℕ) : ℝ) + 1
    nlinarith

private lemma GP022B3b_expand_law {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (f : ℝ → ℝ) :
    finiteMean (fun j => f (GP022B3b_expand a k hk j)) = finiteMean (fun i => f (a i)) := by
  letI GP022B3b_neZeroExpand : NeZero (m * k) := ⟨(Nat.mul_pos hm hk).ne'⟩
  rw [← GP022B3b_quantile_law hm a f]
  symm
  apply SharpBounds.n4_proof
  intro j u hl hu
  rw [GP022B3b_expand_cell hm hk a j u hl hu]

private lemma GP022B3b_expand_mono {m k : ℕ} (a : Fin m → ℝ) (hk : 0 < k) :
    Monotone (GP022B3b_expand a k hk) := by
  intro i j hij
  apply (SharpBounds.n2_proof a).2.2
  exact Nat.div_le_div_right hij

private lemma GP022B3b_min_cdf {n : ℕ} (a b : Fin n → ℝ)
    (ha : Monotone a) (hb : Monotone b) (x y : ℝ) :
    min (empiricalCDF a x) (empiricalCDF b y) =
      finiteMean (fun i => if a i ≤ x ∧ b i ≤ y then 1 else 0) := by
  classical
  by_cases h : ∀ i, a i ≤ x → b i ≤ y
  · have hle : empiricalCDF a x ≤ empiricalCDF b y := by
      apply Finset.expect_le_expect
      intro i _
      change (if a i ≤ x then (1 : ℝ) else 0) ≤ (if b i ≤ y then 1 else 0)
      split_ifs with hax hby hby <;> simp_all
    rw [min_eq_left hle]
    unfold empiricalCDF finiteMean
    apply Finset.expect_congr rfl
    intro i _
    by_cases hi : a i ≤ x <;> simp [hi, h i]
  · push_neg at h
    obtain ⟨i, hi, hbi⟩ := h
    have h' : ∀ j, b j ≤ y → a j ≤ x := by
      intro j hj
      by_cases hij : i ≤ j
      · exact False.elim (not_le.mpr hbi ((hb hij).trans hj))
      · exact (ha (le_of_not_ge hij)).trans hi
    have hle : empiricalCDF b y ≤ empiricalCDF a x := by
      apply Finset.expect_le_expect
      intro j _
      change (if b j ≤ y then (1 : ℝ) else 0) ≤ (if a j ≤ x then 1 else 0)
      split_ifs with hby hax hax <;> simp_all
    rw [min_eq_right hle]
    unfold empiricalCDF finiteMean
    apply Finset.expect_congr rfl
    intro j _
    by_cases hj : b j ≤ y <;> simp [hj, h' j]

private lemma GP022B3b_indicator_integrable (q a b : ℝ) :
    IntervalIntegrable (fun x => if q ≤ x then (1 : ℝ) else 0) volume a b := by
  have hmono : Monotone (fun x : ℝ => if q ≤ x then (1 : ℝ) else 0) := by
    intro x y hxy
    dsimp only
    by_cases hx : q ≤ x
    · simp only [if_pos hx, if_pos (hx.trans hxy), le_refl]
    · rw [if_neg hx]
      split_ifs <;> norm_num
  exact hmono.intervalIntegrable

private lemma GP022B3b_indicator_integral (q C : ℝ) (hq : |q| ≤ C) :
    (∫ x in (-C)..C, if q ≤ x then (1 : ℝ) else 0) = C - q := by
  have hq' := abs_le.mp hq
  have hleft : (∫ x in (-C)..q, if q ≤ x then (1 : ℝ) else 0) = 0 := by
    calc
      _ = ∫ _ : ℝ in (-C)..q, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        rw [Set.uIoo_of_le hq'.1]
        intro x hx
        simp [not_le.mpr hx.2]
      _ = 0 := by simp
  have hright : (∫ x in q..C, if q ≤ x then (1 : ℝ) else 0) = C - q := by
    calc
      _ = ∫ _ : ℝ in q..C, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        rw [Set.uIoo_of_le hq'.2]
        intro x hx
        simp [hx.1.le]
      _ = C - q := by simp
  have heq := intervalIntegral.integral_add_adjacent_intervals
    (GP022B3b_indicator_integrable q (-C) q) (GP022B3b_indicator_integrable q q C)
  rw [hleft, hright, zero_add] at heq
  exact heq.symm

private lemma GP022B3b_integral_mean {n : ℕ} (f : Fin n → ℝ → ℝ) (a b : ℝ)
    (hf : ∀ i, IntervalIntegrable (f i) volume a b) :
    (∫ x in a..b, finiteMean (fun i => f i x)) = finiteMean (fun i => ∫ x in a..b, f i x) := by
  simp only [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum (fun i _ => hf i)]

private lemma GP022B3b_joint_integral {n : ℕ} (a b : Fin n → ℝ) (C : ℝ)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ i, |b i| ≤ C) :
    (∫ x in (-C)..C, ∫ y in (-C)..C,
      finiteMean (fun i => if a i ≤ x ∧ b i ≤ y then (1 : ℝ) else 0)) =
      finiteMean (fun i => (C - a i) * (C - b i)) := by
  classical
  have hid (i : Fin n) (x y : ℝ) :
      (if a i ≤ x ∧ b i ≤ y then (1 : ℝ) else 0) =
        (if a i ≤ x then (1 : ℝ) else 0) * (if b i ≤ y then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [hid]
  have hi (x : ℝ) : (∫ y in (-C)..C,
      finiteMean (fun i => (if a i ≤ x then (1 : ℝ) else 0) *
        (if b i ≤ y then 1 else 0))) =
      finiteMean (fun i => (if a i ≤ x then (1 : ℝ) else 0) * (C - b i)) := by
    rw [GP022B3b_integral_mean _ _ _ (fun i =>
      (GP022B3b_indicator_integrable (b i) (-C) C).const_mul _)]
    simp_rw [intervalIntegral.integral_const_mul, GP022B3b_indicator_integral _ C (hb _)]
  simp_rw [hi]
  rw [GP022B3b_integral_mean _ _ _ (fun i =>
    (GP022B3b_indicator_integrable (a i) (-C) C).mul_const _)]
  simp_rw [intervalIntegral.integral_mul_const, GP022B3b_indicator_integral _ C (ha _)]

private lemma GP022B3b_sorted_bound {m : ℕ} (a : Fin m → ℝ) (C : ℝ)
    (ha : ∀ i, |a i| ≤ C) (i : Fin m) : |sortedValues a i| ≤ C := by
  have hmem : sortedValues a i ∈ List.ofFn a :=
    (SharpBounds.n2_proof a).1.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩)
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmem
  rw [← hj]
  exact ha j

/-- Bounded aligned empirical product identity, including atomic marginals. -/
private lemma GP022B3b_raw_product {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (C : ℝ)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ i, |b i| ≤ C) :
    (∫ u in (0 : ℝ)..1, empiricalQuantile a u * empiricalQuantile b u) =
      -C ^ 2 + C * (finiteMean a + finiteMean b) +
        ∫ x in (-C)..C, ∫ y in (-C)..C,
          min (empiricalCDF a x) (empiricalCDF b y) := by
  letI GP022B3b_neZeroProduct : NeZero (m * k) := ⟨(Nat.mul_pos hm hk).ne'⟩
  let A : Fin (m * k) → ℝ := GP022B3b_expand a k hk
  let e : Fin (m * k) ≃ Fin (k * m) := finCongr (Nat.mul_comm m k)
  let B : Fin (m * k) → ℝ := fun j => GP022B3b_expand b m hm (e j)
  have hla (f : ℝ → ℝ) : finiteMean (fun j => f (A j)) = finiteMean (fun i => f (a i)) :=
    GP022B3b_expand_law hm hk a f
  have hlb (f : ℝ → ℝ) : finiteMean (fun j => f (B j)) = finiteMean (fun i => f (b i)) := by
    calc
      _ = finiteMean (fun j => f (GP022B3b_expand b m hm j)) :=
        Fintype.expect_equiv e _ _ (fun _ => rfl)
      _ = _ := GP022B3b_expand_law hk hm b f
  have hAm : Monotone A := GP022B3b_expand_mono a hk
  have hBm : Monotone B := by
    intro i j hij
    apply GP022B3b_expand_mono b hm
    exact hij
  have hAb (i) : |A i| ≤ C := GP022B3b_sorted_bound a C ha _
  have hBb (i) : |B i| ≤ C := GP022B3b_sorted_bound b C hb _
  have hmin (x y : ℝ) : min (empiricalCDF a x) (empiricalCDF b y) =
      finiteMean (fun i => if A i ≤ x ∧ B i ≤ y then (1 : ℝ) else 0) := by
    have hax : empiricalCDF A x = empiricalCDF a x := hla (fun z => if z ≤ x then 1 else 0)
    have hby : empiricalCDF B y = empiricalCDF b y := hlb (fun z => if z ≤ y then 1 else 0)
    rw [← hax, ← hby]
    exact GP022B3b_min_cdf A B hAm hBm x y
  have hprod : (∫ u in (0 : ℝ)..1, empiricalQuantile a u * empiricalQuantile b u) =
      finiteMean (fun i => A i * B i) := by
    apply SharpBounds.n4_proof
    intro j u hl hu
    have ha' := GP022B3b_expand_cell hm hk a j u hl hu
    have hb' := GP022B3b_expand_cell hk hm b (e j) u
      (by simpa [e, Nat.mul_comm] using hl) (by simpa [e, Nat.mul_comm] using hu)
    rw [ha', hb']
  have hint : (∫ x in (-C)..C, ∫ y in (-C)..C,
      min (empiricalCDF a x) (empiricalCDF b y)) =
      finiteMean (fun i => (C - A i) * (C - B i)) := by
    simp_rw [hmin]
    exact GP022B3b_joint_integral A B C hAb hBb
  have hmean : finiteMean (fun i => (C - A i) * (C - B i)) =
      C ^ 2 - C * (finiteMean A + finiteMean B) + finiteMean (fun i => A i * B i) := by
    have hp (i) : (C - A i) * (C - B i) = C ^ 2 - C * A i - C * B i + A i * B i := by ring
    simp_rw [hp]
    simp only [finiteMean, Finset.expect_add_distrib, Finset.expect_sub_distrib,
      ← Finset.mul_expect, Fintype.expect_const]
    ring
  rw [hint, hmean, hprod, hla (fun z => z), hlb (fun z => z)]
  ring

private lemma GP022B3b_empiricalCDF_mono {s : ℕ} (a : Fin s → ℝ) :
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

/-- Every inner min-CDF integral is integrable. This uses monotonicity,
so no continuity at the empirical jumps is needed. -/
private lemma GP022B3b_inner_integrable {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (C x : ℝ) :
    IntervalIntegrable (fun y => min (empiricalCDF a x) (empiricalCDF b y))
      volume (-C) C := by
  have hmono : Monotone (fun y => min (empiricalCDF a x) (empiricalCDF b y)) :=
    monotone_const.min (GP022B3b_empiricalCDF_mono b)
  exact hmono.intervalIntegrable

private lemma GP022B3b_outer_integrable {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (C : ℝ) (hC : 0 ≤ C) :
    IntervalIntegrable (fun x => ∫ y in (-C)..C,
      min (empiricalCDF a x) (empiricalCDF b y)) volume (-C) C := by
  have hmono : Monotone (fun x => ∫ y in (-C)..C,
      min (empiricalCDF a x) (empiricalCDF b y)) := by
    intro x x' hxx'
    apply intervalIntegral.integral_mono (by linarith : -C ≤ C)
      (GP022B3b_inner_integrable a b C x)
      (GP022B3b_inner_integrable a b C x')
    intro y
    exact min_le_min ((GP022B3b_empiricalCDF_mono a) hxx') le_rfl
  exact hmono.intervalIntegrable

/-- Linearity for the actual iterated CDF integral in T7. -/
private lemma GP022B3b_double_integral_sub {m k N : ℕ}
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
      (GP022B3b_inner_integrable a b C x)
      (GP022B3b_inner_integrable y1 y0 C x)
  simp_rw [hinner]
  exact intervalIntegral.integral_sub
    (GP022B3b_outer_integrable a b C hC)
    (GP022B3b_outer_integrable y1 y0 C hC)

/-- A deterministic identity for the defined finite-population correction. -/
private lemma GP022B3b_marginal_as_variance {s : ℕ} (N : ℕ) (a : Fin s → ℝ) :
    marginalVarianceEstimate N a =
      (((N : ℝ) - 1) / N) *
        ((s : ℝ) * finiteVariance a / ((s : ℝ) - 1)) := by
  have hsum : (∑ i, (a i - finiteMean a) ^ 2) =
      (s : ℝ) * finiteVariance a := by
    simpa only [Fintype.card_fin, finiteVariance, finiteMean] using
      (Fintype.card_mul_expect (fun i => (a i - finiteMean a) ^ 2)).symm
  unfold marginalVarianceEstimate sampleVariance
  rw [hsum]


/-- The seven terms decompose the actual defined estimator. -/
private lemma GP022B3b_decomposition (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hy : ∀ i, |y1 i| ≤ C ∧ |y0 i| ≤ C) (π : Assignment d) :
    ((d.N : ℝ) * (estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H)) =
      sevenTotal (sevenTerms d y1 y0 C π) := by
  let a := observedTreatment d y1 π
  let b := observedControl d y0 π
  have hN : (0 : ℝ) < d.N := by exact_mod_cast (show 0 < d.N by have := d.population_min; omega)
  have hN1 : (d.N : ℝ) - 1 ≠ 0 := by
    have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  have hm : (0 : ℝ) < d.m := by exact_mod_cast (show 0 < d.m by have := d.treatment_min; omega)
  have hk : (0 : ℝ) < d.k := by exact_mod_cast (show 0 < d.k by have := d.control_min; omega)
  have hm1 : (d.m : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ d.m := by exact_mod_cast d.treatment_min
    linarith
  have hk1 : (d.k : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ d.k := by exact_mod_cast d.control_min
    linarith
  have ha (i) : |a i| ≤ C := (hy _).1
  have hb (i) : |b i| ≤ C := (hy _).2
  have hab := GP022B3b_raw_product (by exact_mod_cast hm) (by exact_mod_cast hk) a b C ha hb
  have hpop := GP022B3b_raw_product (by exact_mod_cast hN) (by exact_mod_cast hN)
    y1 y0 C (fun i => (hy i).1) (fun i => (hy i).2)
  have hdiff := GP022B3b_double_integral_sub a b y1 y0 C hC
  have hc : sharpCovariance a b .H - sharpCovariance y1 y0 .H =
      C * (finiteMean a - finiteMean y1 + finiteMean b - finiteMean y0) -
        (finiteMean a * finiteMean b - finiteMean y1 * finiteMean y0) +
        (∫ x in (-C)..C, ∫ y in (-C)..C,
          min (empiricalCDF a x) (empiricalCDF b y) -
            min (empiricalCDF y1 x) (empiricalCDF y0 y)) := by
    simp only [sharpCovariance, ite_true] 
    rw [hab, hpop, hdiff]
    ring
  unfold estimatedVariance estimateBound populationBound varianceExpression
  rw [GP022B3b_marginal_as_variance, GP022B3b_marginal_as_variance]
  change (d.N : ℝ) *
    (((((d.N : ℝ) - d.m) / d.m * ((((d.N : ℝ) - 1) / d.N) *
        ((d.m : ℝ) * finiteVariance a / ((d.m : ℝ) - 1))) +
      ((d.N : ℝ) - d.k) / d.k * ((((d.N : ℝ) - 1) / d.N) *
        ((d.k : ℝ) * finiteVariance b / ((d.k : ℝ) - 1))) + 2 * sharpCovariance a b .H) /
          ((d.N : ℝ) - 1)) -
    ((((d.N : ℝ) - d.m) / d.m * finiteVariance y1 +
      ((d.N : ℝ) - d.k) / d.k * finiteVariance y0 + 2 * sharpCovariance y1 y0 .H) /
          ((d.N : ℝ) - 1))) = _
  have hcovalg (v w s t ca cb : ℝ) :
      (v + w + 2 * ca) / ((d.N : ℝ) - 1) -
        (s + t + 2 * cb) / ((d.N : ℝ) - 1) =
      (v + w - s - t + 2 * (ca - cb)) / ((d.N : ℝ) - 1) := by ring
  rw [hcovalg, hc]
  rw [finite_variance_second_moment (by exact_mod_cast hm),
    finite_variance_second_moment (by exact_mod_cast hk),
    finite_variance_second_moment (by exact_mod_cast hN),
    finite_variance_second_moment (by exact_mod_cast hN)]
  simp [sevenTotal, sevenTerms, lastIntegralTerm, frechetCDF]
  dsimp only [a, b] at *
  field_simp [hN.ne', hm.ne', hk.ne', hN1, hm1, hk1]
  <;> ring

private theorem GP022B3b_probability_mono (d : Design) (E F : Assignment d → Prop)
    (hEF : ∀ π, E π → F π) : designProbability d E ≤ designProbability d F := by
  classical
  unfold designProbability designExpectation
  apply Finset.expect_le_expect
  intro π _
  by_cases he : E π
  · simp only [if_pos he, if_pos (hEF π he), le_refl]
  · rw [if_neg he]
    split_ifs <;> norm_num

private theorem GP022B3b_probability_union (d : Design) {n : ℕ}
    (E : Assignment d → Prop) (F : Fin n → Assignment d → Prop)
    (hEF : ∀ π, E π → ∃ j, F j π) :
    designProbability d E ≤ ∑ j, designProbability d (F j) := by
  classical
  unfold designProbability designExpectation
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro π _
  by_cases he : E π
  · obtain ⟨j, hj⟩ := hEF π he
    rw [if_pos he]
    calc
      (1 : ℝ) = (if F j π then 1 else 0) := by simp [hj]
      _ ≤ ∑ i : Fin n, if F i π then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun i : Fin n => if F i π then (1 : ℝ) else 0) (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
  · simp only [if_neg he]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

private theorem GP022B3b_scaled_mono (S : ExperimentSequence)
    (E F : (q : ℕ) → Assignment (S.design q) → Prop)
    (hEF : ∀ᶠ q in atTop, ∀ π, E q π → F q π) :
    scaledProbabilityLimsup S E ≤ scaledProbabilityLimsup S F := by
  unfold scaledProbabilityLimsup
  refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [hEF] with q hq
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (GP022B3b_probability_mono _ _ _ hq) (Nat.cast_nonneg _))

/-- Finite-union limsup calculus, using finite real upper bounds.
This epsilon argument works for `atTop`; it does not assume that `atTop`
is a countable-intersection filter. -/
private theorem GP022B3b_scaled_union {n : ℕ} (S : ExperimentSequence)
    (E : (q : ℕ) → Assignment (S.design q) → Prop)
    (F : Fin n → (q : ℕ) → Assignment (S.design q) → Prop)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hF : ∀ j, scaledProbabilityLimsup S (F j) ≤ ENNReal.ofReal (r j))
    (hEF : ∀ᶠ q in atTop, ∀ π, E q π → ∃ j, F j q π) :
    scaledProbabilityLimsup S E ≤ ENNReal.ofReal (∑ j, r j) := by
  classical
  apply ENNReal.le_of_forall_pos_le_add
  intro e he _
  let δ : ℝ := (e : ℝ) / (n + 1 : ℕ)
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have hδ : 0 < δ := div_pos heR (by positivity)
  have hj : ∀ j, ∀ᶠ q in atTop,
      ((S.design q).N : ℝ) * designProbability (S.design q) (F j q) < r j + δ := by
    intro j
    have hlt : scaledProbabilityLimsup S (F j) < ENNReal.ofReal (r j + δ) :=
      (hF j).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith [hr j])).2
        (by linarith))
    have hv := Filter.eventually_lt_of_limsup_lt hlt
    filter_upwards [hv] with q hq
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [hr j])).1 hq
  have hall : ∀ᶠ q in atTop, ∀ j, ((S.design q).N : ℝ) *
      designProbability (S.design q) (F j q) < r j + δ :=
    Filter.eventually_all.mpr hj
  have hb : ∀ᶠ q in atTop, ENNReal.ofReal (((S.design q).N : ℝ) *
      designProbability (S.design q) (E q)) ≤ ENNReal.ofReal ((∑ j, r j) + (e : ℝ)) := by
    filter_upwards [hEF, hall] with q hq hqF
    apply ENNReal.ofReal_le_ofReal
    calc
      ((S.design q).N : ℝ) * designProbability (S.design q) (E q)
          ≤ ((S.design q).N : ℝ) * ∑ j, designProbability (S.design q) (F j q) :=
        mul_le_mul_of_nonneg_left (GP022B3b_probability_union _ _ _ hq) (Nat.cast_nonneg _)
      _ = ∑ j, ((S.design q).N : ℝ) * designProbability (S.design q) (F j q) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ j, (r j + δ) := Finset.sum_le_sum (fun j _ => (hqF j).le)
      _ = (∑ j, r j) + n * δ := by simp [Finset.sum_add_distrib]
      _ ≤ (∑ j, r j) + (e : ℝ) := by
        have hn : (n : ℝ) / (n + 1 : ℕ) ≤ 1 :=
          (div_le_one (by positivity)).2 (by push_cast; linarith)
        have hh := mul_le_mul_of_nonneg_right hn heR.le
        have hnd : (n : ℝ) * δ ≤ (e : ℝ) := by
          calc
            (n : ℝ) * δ = ((n : ℝ) / (n + 1 : ℕ)) * (e : ℝ) := by dsimp [δ]; ring
            _ ≤ (e : ℝ) := by simpa only [one_mul] using hh
        linarith
  have hs : 0 ≤ ∑ j, r j := Finset.sum_nonneg (fun j _ => hr j)
  calc
    scaledProbabilityLimsup S E ≤ ENNReal.ofReal ((∑ j, r j) + (e : ℝ)) :=
      Filter.limsup_le_of_le (by isBoundedDefault) hb
    _ = ENNReal.ofReal (∑ j, r j) + e := by
      rw [ENNReal.ofReal_add hs heR.le]
      simp

private theorem GP022B3b_law_bounds (H : JointLaw) (t : Bool) (x : ℝ) :
    0 ≤ lawCDF H t x ∧ lawCDF H t x ≤ 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · unfold lawCDF
    have hm : (H : Measure (ℝ × ℝ)) {p | (if t then p.1 else p.2) ≤ x} ≤ 1 := by
      simpa using (measure_mono (μ := (H : Measure (ℝ × ℝ))) (Set.subset_univ _))
    exact (ENNReal.toReal_mono (by simp) hm).trans_eq (by simp)

private theorem GP022B3b_cdf_bdd (A B : ℝ → ℝ)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ 1) :
    BddAbove (Set.range (fun x => |A x - B x|)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [abs_sub_le_iff]
  constructor <;> linarith [(hA x).1, (hA x).2, (hB x).1, (hB x).2]

private theorem GP022B3b_cdf_point (A B : ℝ → ℝ)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ 1) (x : ℝ) :
    |A x - B x| ≤ cdfDistance A B :=
  le_csSup (GP022B3b_cdf_bdd A B hA hB) (Set.mem_range_self x)

/-- The orientation is chosen for sample/population versus law/sample. -/
private theorem GP022B3b_cdf_triangle (A P L : ℝ → ℝ)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1) (hP : ∀ x, 0 ≤ P x ∧ P x ≤ 1)
    (hL : ∀ x, 0 ≤ L x ∧ L x ≤ 1) :
    cdfDistance A P ≤ cdfDistance L A + cdfDistance L P := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  calc
    |A x - P x| ≤ |A x - L x| + |L x - P x| := abs_sub_le _ _ _
    _ = |L x - A x| + |L x - P x| := by rw [abs_sub_comm (A x)]
    _ ≤ cdfDistance L A + cdfDistance L P :=
      add_le_add (GP022B3b_cdf_point L A hL hA x) (GP022B3b_cdf_point L P hL hP x)

private theorem GP022B3b_min_lipschitz (a b c d M : ℝ)
    (ha : |a - c| ≤ M) (hb : |b - d| ≤ M) : |min a b - min c d| ≤ M := by
  rw [abs_le] at ha hb ⊢
  constructor
  · have hh : min c d - M ≤ min a b := by
      apply le_min <;> linarith [min_le_left c d, min_le_right c d]
    linarith
  · have hh : min a b ≤ min c d + M := by
      by_cases hcd : c ≤ d
      · rw [min_eq_left hcd]; linarith [min_le_left a b]
      · rw [min_eq_right (le_of_not_ge hcd)]; linarith [min_le_right a b]
    linarith

/-- No integrability premise is needed for this norm upper bound: the
Bochner integral is totalized, and the interval norm bound is unconditional. -/
private theorem GP022B3b_last_integral_bound (d : Design) (y1 y0 : Fin d.N → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (π : Assignment d) :
    |lastIntegralTerm d y1 y0 C π| ≤
      (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) *
        max (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1))
          (cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0)) := by
  let M := max (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1))
    (cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0))
  have hN : (1 : ℝ) < d.N := by exact_mod_cast (show 1 < d.N by have := d.population_min; omega)
  have hm : 0 < d.m := by have := d.treatment_min; omega
  have hk : 0 < d.k := by have := d.control_min; omega
  have hn : 0 < d.N := by have := d.population_min; omega
  have hnm : 0 < (d.N : ℝ) - 1 := sub_pos.mpr hN
  have hinner : ∀ x, |∫ y in (-C)..C,
      frechetCDF (empiricalCDF (observedTreatment d y1 π))
        (empiricalCDF (observedControl d y0 π)) .H x y -
      frechetCDF (empiricalCDF y1) (empiricalCDF y0) .H x y| ≤ M * (2 * C) := by
    intro x
    have hpoint : ∀ y : ℝ, ‖frechetCDF
        (empiricalCDF (observedTreatment d y1 π))
        (empiricalCDF (observedControl d y0 π)) .H x y -
        frechetCDF (empiricalCDF y1) (empiricalCDF y0) .H x y‖ ≤ M := by
      intro y
      simp only [Real.norm_eq_abs, frechetCDF, if_pos rfl]
      apply GP022B3b_min_lipschitz
      · exact (GP022B3b_cdf_point _ _ (empirical_cdf_bounds hm _) (empirical_cdf_bounds hn _) x).trans
          (le_max_left _ _)
      · exact (GP022B3b_cdf_point _ _ (empirical_cdf_bounds hk _) (empirical_cdf_bounds hn _) y).trans
          (le_max_right _ _)
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -C) (b := C) (C := M) (fun y _ => hpoint y)
    simpa only [Real.norm_eq_abs, sub_neg_eq_add,
      abs_of_nonneg (by linarith : 0 ≤ C + C), two_mul] using hnorm
  have hout : |∫ x in (-C)..C, ∫ y in (-C)..C,
      frechetCDF (empiricalCDF (observedTreatment d y1 π))
        (empiricalCDF (observedControl d y0 π)) .H x y -
      frechetCDF (empiricalCDF y1) (empiricalCDF y0) .H x y| ≤ (M * (2 * C)) * (2 * C) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -C) (b := C) (f := fun x => ∫ y in (-C)..C,
        frechetCDF (empiricalCDF (observedTreatment d y1 π))
          (empiricalCDF (observedControl d y0 π)) .H x y -
        frechetCDF (empiricalCDF y1) (empiricalCDF y0) .H x y) (C := M * (2 * C))
      (fun x _ => by simpa only [Real.norm_eq_abs] using hinner x)
    simpa only [Real.norm_eq_abs, sub_neg_eq_add,
      abs_of_nonneg (by linarith : 0 ≤ C + C), two_mul] using hh
  have hfac : 0 ≤ 2 * (d.N : ℝ) / ((d.N : ℝ) - 1) := by positivity
  unfold lastIntegralTerm
  rw [abs_mul, abs_of_nonneg hfac]
  calc
    _ ≤ (2 * d.N / ((d.N : ℝ) - 1)) * ((M * (2 * C)) * (2 * C)) :=
      mul_le_mul_of_nonneg_left hout hfac
    _ = (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) * M := by ring

private theorem GP022B3b_last_integral_event (d : Design) (y1 y0 : Fin d.N → ℝ)
    (C x : ℝ) (hC : 0 < C) (hx : 0 < x) (π : Assignment d)
    (hlarge : x ≤ |lastIntegralTerm d y1 y0 C π|) :
    ((d.N : ℝ) - 1) * x / (8 * d.N * C ^ 2) ≤
      cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1) ∨
    ((d.N : ℝ) - 1) * x / (8 * d.N * C ^ 2) ≤
      cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0) := by
  have hn : 0 < (d.N : ℝ) := by exact_mod_cast (show 0 < d.N by have := d.population_min; omega)
  have hnm : 0 < (d.N : ℝ) - 1 := by
    have h4 : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  have hbound := hlarge.trans (GP022B3b_last_integral_bound d y1 y0 C hC.le π)
  have hh : ((d.N : ℝ) - 1) * x / (8 * d.N * C ^ 2) ≤
      max (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1))
        (cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0)) := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * (d.N : ℝ) * C ^ 2)).2
    have hh := (le_div_iff₀ hnm).1 (show x ≤
      (8 * (d.N : ℝ) * C ^ 2 * max
        (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1))
        (cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0))) /
          ((d.N : ℝ) - 1) by convert hbound using 1 <;> ring)
    nlinarith [hh]
  exact le_max_iff.mp hh

private theorem GP022B3b_last_to_limit (S : ExperimentSequence) (H : JointLaw)
    (C ε1 ξ : ℝ) (hC : 0 < C) (hε1 : 0 < ε1)
    (hξ : 0 < ξ ∧ ξ < ε1 / (16 * C ^ 2))
    (hpop : ∀ t, Tendsto (fun q => cdfDistance (lawCDF H t)
      (empiricalCDF (rowOutcomes S t q))) atTop (𝓝 0)) :
    ∀ᶠ q in atTop, ∀ π,
      ε1 / 2 ≤ |lastIntegralTerm (S.design q) (rowOutcomes S true q)
        (rowOutcomes S false q) C π| →
      (ε1 / (16 * C ^ 2) - ξ ≤ cdfDistance (lawCDF H true) (sampledCDF S true q π) ∨
       ε1 / (16 * C ^ 2) - ξ ≤ cdfDistance (lawCDF H false) (sampledCDF S false q π)) := by
  let a : ℝ := ε1 / (16 * C ^ 2)
  have hshift : Tendsto (fun q : ℕ => q + 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat 4).2 tendsto_id
  have hsmall : Tendsto (fun q => a / ((S.design q).N : ℝ)) atTop (𝓝 0) := by
    simpa only [S.size, Function.comp_def] using (tendsto_const_div_atTop_nhds_zero_nat a).comp hshift
  have hb : ∀ t : Bool, ∀ᶠ q in atTop,
      cdfDistance (lawCDF H t) (empiricalCDF (rowOutcomes S t q)) +
        a / ((S.design q).N : ℝ) < ξ := by
    intro t
    have ht : Tendsto (fun q => cdfDistance (lawCDF H t)
        (empiricalCDF (rowOutcomes S t q)) + a / ((S.design q).N : ℝ)) atTop (𝓝 0) := by
      simpa only [zero_add] using (hpop t).add hsmall
    exact ht.eventually (gt_mem_nhds hξ.1)
  filter_upwards [hb true, hb false] with q hb1 hb0
  intro π hlarge
  let d := S.design q
  have hN : 0 < (d.N : ℝ) := by
    exact_mod_cast (show 0 < d.N by have := d.population_min; omega)
  have hthreshold : ((d.N : ℝ) - 1) * (ε1 / 2) / (8 * d.N * C ^ 2) =
      a - a / (d.N : ℝ) := by
    dsimp [a]
    field_simp [ne_of_gt hC, ne_of_gt hN]
    <;> ring
  have hcases := GP022B3b_last_integral_event d (rowOutcomes S true q)
    (rowOutcomes S false q) C (ε1 / 2) hC (by positivity) π hlarge
  rw [hthreshold] at hcases
  have hn : 0 < d.N := by exact_mod_cast hN
  have hm : 0 < d.m := by have := d.treatment_min; omega
  have hk : 0 < d.k := by have := d.control_min; omega
  rcases hcases with h1 | h0
  · left
    have htri := GP022B3b_cdf_triangle
      (empiricalCDF (observedTreatment d (rowOutcomes S true q) π))
      (empiricalCDF (rowOutcomes S true q)) (lawCDF H true)
      (empirical_cdf_bounds hm _) (empirical_cdf_bounds hn _) (GP022B3b_law_bounds H true)
    change a - ξ ≤ cdfDistance (lawCDF H true)
      (empiricalCDF (observedTreatment d (rowOutcomes S true q) π))
    change cdfDistance (lawCDF H true) (empiricalCDF (rowOutcomes S true q)) +
      a / (d.N : ℝ) < ξ at hb1
    linarith
  · right
    have htri := GP022B3b_cdf_triangle
      (empiricalCDF (observedControl d (rowOutcomes S false q) π))
      (empiricalCDF (rowOutcomes S false q)) (lawCDF H false)
      (empirical_cdf_bounds hk _) (empirical_cdf_bounds hn _) (GP022B3b_law_bounds H false)
    change a - ξ ≤ cdfDistance (lawCDF H false)
      (empiricalCDF (observedControl d (rowOutcomes S false q) π))
    change cdfDistance (lawCDF H false) (empiricalCDF (rowOutcomes S false q)) +
      a / (d.N : ℝ) < ξ at hb0
    linarith

private theorem GP022B3b_coefficient_nonneg (S : ExperimentSequence) (H : JointLaw)
    (θ ρ : ℝ) (h : Conditions123 S H θ ρ) :
    0 ≤ 1 - θ * ρ ∧ 0 ≤ 1 - θ * (1 - ρ) ∧
      ∀ i, 0 ≤ termRateCoefficient θ ρ i := by
  rcases h with ⟨hθ, hθ1, hρ, hρ1, _⟩
  have hρ0 : 0 < 1 - ρ := by linarith
  have h1 : θ * ρ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hθ1 hρ.le
    nlinarith [hh]
  have h0 : θ * (1 - ρ) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hθ1 hρ0.le
    nlinarith [hh]
  have hn1 : 0 ≤ 1 - θ * ρ := by linarith
  have hn0 : 0 ≤ 1 - θ * (1 - ρ) := by linarith
  refine ⟨hn1, hn0, ?_⟩
  intro i
  fin_cases i <;> simp [termRateCoefficient] <;> positivity



theorem proposition2_corrected_limit_proof (S : ExperimentSequence) (H : JointLaw) (θ ρ C : ℝ)
    (h : Conditions123 S H θ ρ) (hC : 0 < C)
    (hy : ∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C)
    (hLemma : Lemma2Conclusions S H θ ρ) (ε1 ξ : ℝ)
    (hε1 : 0 < ε1) (hξ : 0 < ξ ∧ ξ < ε1 / (16 * C ^ 2)) :
    ∃ K1 K0 : ℝ → ℕ, ∃ κ : ℝ,
      (∀ η, 0 < η →
        scaledProbabilityLimsup S (fun q π => η ≤
          cdfDistance (lawCDF H true) (sampledCDF S true q π)) ≤
          ENNReal.ofReal ((1 - θ * ρ) * K1 η / (θ * ρ * η ^ 2)) ∧
        scaledProbabilityLimsup S (fun q π => η ≤
          cdfDistance (lawCDF H false) (sampledCDF S false q π)) ≤
          ENNReal.ofReal ((1 - θ * (1 - ρ)) * K0 η / (θ * (1 - ρ) * η ^ 2))) ∧
      (let η := ε1 / (16 * C ^ 2) - ξ
       C ^ 4 * κ = (1 - θ * ρ) * K1 η / (θ * ρ * η ^ 2) +
         (1 - θ * (1 - ρ)) * K0 η / (θ * (1 - ρ) * η ^ 2)) ∧
      scaledProbabilityLimsup S (fun q π => ε1 / 2 ≤
        |lastIntegralTerm (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) C π|) ≤
          ENNReal.ofReal (C ^ 4 * κ) ∧
      (∀ ν : Fin 8 → ℝ, (∀ i, 0 < ν i) → (∑ i, ν i) = ε1 / 2 →
        (∀ j : Fin 6,
          scaledProbabilityLimsup S (fun q π => correctedAllocation ν ε1
            ⟨j.val, by omega⟩ ≤ |sevenTerms (S.design q)
              (rowOutcomes S true q) (rowOutcomes S false q) C π ⟨j.val, by omega⟩|) ≤
            ENNReal.ofReal (C ^ 4 * (match j.val with
              | 0 => termRateCoefficient θ ρ 0 / (ν 0) ^ 2
              | 1 => termRateCoefficient θ ρ 1 / (ν 1) ^ 2
              | 2 => termRateCoefficient θ ρ 2 / (ν 2) ^ 2
              | 3 => termRateCoefficient θ ρ 3 / (ν 3) ^ 2
              | 4 => termRateCoefficient θ ρ 4 / (ν 4) ^ 2 + termRateCoefficient θ ρ 5 / (ν 5) ^ 2
              | _ => termRateCoefficient θ ρ 6 / (ν 6) ^ 2 + termRateCoefficient θ ρ 7 / (ν 7) ^ 2))) →
        ∀ ε, ε1 < ε →
        scaledProbabilityLimsup S (fun q π => ε ≤ ((S.design q).N : ℝ) *
          |estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H π -
            populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H|) ≤
        scaledProbabilityLimsup S (fun q π => ε1 ≤ ((S.design q).N : ℝ) *
          |estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H π -
            populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H|) ∧
        scaledProbabilityLimsup S (fun q π => ε1 ≤ ((S.design q).N : ℝ) *
          |estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H π -
            populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H|) ≤
          ENNReal.ofReal (C ^ 4 * ((∑ i, termRateCoefficient θ ρ i / (ν i) ^ 2) + κ))) := by
  classical
  obtain ⟨hpop, K1, K0, hKpos, hKanti, hK1, hK0⟩ := hLemma
  let η : ℝ := ε1 / (16 * C ^ 2) - ξ
  have hη : 0 < η := sub_pos.mpr hξ.2
  let r1 : ℝ := (1 - θ * ρ) * K1 η / (θ * ρ * η ^ 2)
  let r0 : ℝ := (1 - θ * (1 - ρ)) * K0 η / (θ * (1 - ρ) * η ^ 2)
  let κ : ℝ := (r1 + r0) / C ^ 4
  obtain ⟨hn1, hn0, hcoeff⟩ := GP022B3b_coefficient_nonneg S H θ ρ h
  have hθ : 0 < θ := h.1
  have hρ : 0 < ρ := h.2.2.1
  have hρ0 : 0 < 1 - ρ := sub_pos.mpr h.2.2.2.1
  have hr1 : 0 ≤ r1 := by dsimp [r1]; positivity
  have hr0 : 0 ≤ r0 := by dsimp [r0]; positivity
  have hκ : 0 ≤ κ := div_nonneg (add_nonneg hr1 hr0) (by positivity)
  have hκeq : C ^ 4 * κ = r1 + r0 := by
    dsimp [κ]
    field_simp [ne_of_gt hC]
  have hlast : scaledProbabilityLimsup S (fun q π => ε1 / 2 ≤
      |lastIntegralTerm (S.design q) (rowOutcomes S true q)
        (rowOutcomes S false q) C π|) ≤ ENNReal.ofReal (C ^ 4 * κ) := by
    rw [hκeq]
    let F : Fin 2 → (q : ℕ) → Assignment (S.design q) → Prop :=
      fun j q π => η ≤ cdfDistance (lawCDF H (decide (j = 0)))
        (sampledCDF S (decide (j = 0)) q π)
    let r : Fin 2 → ℝ := fun j => if j = 0 then r1 else r0
    have hr : ∀ j, 0 ≤ r j := by intro j; dsimp [r]; split_ifs <;> assumption
    have hf : ∀ j, scaledProbabilityLimsup S (F j) ≤ ENNReal.ofReal (r j) := by
      intro j
      fin_cases j
      · simpa [F, r, r1] using hK1 η hη
      · simpa [F, r, r0] using hK0 η hη
    have hi : ∀ᶠ q in atTop, ∀ π,
        ε1 / 2 ≤ |lastIntegralTerm (S.design q) (rowOutcomes S true q)
          (rowOutcomes S false q) C π| → ∃ j, F j q π := by
      filter_upwards [GP022B3b_last_to_limit S H C ε1 ξ hC hε1 hξ hpop] with q hq
      intro π hp
      rcases hq π hp with h1 | h0
      · exact ⟨0, by simpa [F, η] using h1⟩
      · exact ⟨1, by simpa [F, η] using h0⟩
    simpa [r, Fin.sum_univ_succ] using GP022B3b_scaled_union S _ F r hr hf hi
  refine ⟨K1, K0, κ, (fun ε hε => ⟨hK1 ε hε, hK0 ε hε⟩), hκeq, hlast, ?_⟩
  intro ν hν hsum hearlier ε hε
  constructor
  · apply GP022B3b_scaled_mono
    exact Filter.Eventually.of_forall (fun q π hp => le_trans hε.le hp)
  · let F : Fin 7 → (q : ℕ) → Assignment (S.design q) → Prop :=
      fun j q π => correctedAllocation ν ε1 j ≤
        |sevenTerms (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) C π j|
    let r : Fin 7 → ℝ := fun j => C ^ 4 * (match j.val with
      | 0 => termRateCoefficient θ ρ 0 / (ν 0) ^ 2
      | 1 => termRateCoefficient θ ρ 1 / (ν 1) ^ 2
      | 2 => termRateCoefficient θ ρ 2 / (ν 2) ^ 2
      | 3 => termRateCoefficient θ ρ 3 / (ν 3) ^ 2
      | 4 => termRateCoefficient θ ρ 4 / (ν 4) ^ 2 + termRateCoefficient θ ρ 5 / (ν 5) ^ 2
      | 5 => termRateCoefficient θ ρ 6 / (ν 6) ^ 2 + termRateCoefficient θ ρ 7 / (ν 7) ^ 2
      | _ => κ)
    have hr : ∀ j, 0 ≤ r j := by
      have hc0 := hcoeff (0 : Fin 8)
      have hc1 := hcoeff (1 : Fin 8)
      have hc2 := hcoeff (2 : Fin 8)
      have hc3 := hcoeff (3 : Fin 8)
      have hc4 := hcoeff (4 : Fin 8)
      have hc5 := hcoeff (5 : Fin 8)
      have hc6 := hcoeff (6 : Fin 8)
      have hc7 := hcoeff (7 : Fin 8)
      intro j
      fin_cases j <;> simp [r] <;> positivity
    have hF : ∀ j, scaledProbabilityLimsup S (F j) ≤ ENNReal.ofReal (r j) := by
      intro j
      by_cases hj : j.val < 6
      · have ht := hearlier ⟨j.val, hj⟩
        fin_cases j <;> norm_num at hj <;> simpa [F, r] using ht
      · have hj6 : j = (6 : Fin 7) := Fin.ext (by omega)
        subst j
        simpa [F, r, correctedAllocation, sevenTerms] using hlast
    have hpos : ∀ j, 0 < correctedAllocation ν ε1 j := by
      intro j
      fin_cases j
      · exact hν 0
      · exact hν 1
      · exact hν 2
      · exact hν 3
      · exact add_pos (hν 4) (hν 5)
      · exact add_pos (hν 6) (hν 7)
      · exact div_pos hε1 (by norm_num)
    have hbudget : (∑ j, correctedAllocation ν ε1 j) ≤ ε1 :=
      (corrected_allocation_sum ν ε1 hsum).le
    have hi : ∀ᶠ q in atTop, ∀ π, ε1 ≤ ((S.design q).N : ℝ) *
        |estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H π -
          populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H| →
        ∃ j, F j q π := by
      apply Filter.Eventually.of_forall
      intro q π hp
      have hyq : ∀ i, |rowOutcomes S true q i| ≤ C ∧ |rowOutcomes S false q i| ≤ C := by
        intro i
        simpa only [rowOutcomes, if_true, Bool.false_eq_true, if_false] using hy i.val
      have hdecomp := GP022B3b_decomposition (S.design q)
        (rowOutcomes S true q) (rowOutcomes S false q) C hC.le hyq π
      have habs : ε1 ≤ |sevenTotal (sevenTerms (S.design q)
          (rowOutcomes S true q) (rowOutcomes S false q) C π)| := by
        rw [← hdecomp, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact hp
      exact seven_term_budget _ _ ε1 hpos hbudget habs
    have hbound := GP022B3b_scaled_union S _ F r hr hF hi
    have hrsum : (∑ j, r j) = C ^ 4 *
        ((∑ i, termRateCoefficient θ ρ i / (ν i) ^ 2) + κ) := by
      simp [Fin.sum_univ_succ, r]
      <;> ring
    simpa only [hrsum] using hbound

end
end AronowAudit.P022.Wave1
