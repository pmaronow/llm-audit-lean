import AronowAudit.P022.Wave1.Gap.TailBCorollaryMoments
import AronowAudit.Shared.MapTailB.PermutationArray

/-! The actual two-arm contrast as a doubly centered permutation array. -/
namespace AronowAudit.P022.Wave1
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
open RandomizationVariance
noncomputable section

/-- Subtract the slot means as well as the outcome means. -/
def tb13_array (d : Design) (y1 y0 : Fin d.N → ℝ) : Matrix (Fin d.N) (Fin d.N) ℝ :=
  fun s i => ((treatCoef d s - 1/(d.N : ℝ))*(y1 i-finiteMean y1) +
    (ctrlCoef d s + 1/(d.N : ℝ))*(y0 i-finiteMean y0)) /
      Real.sqrt (trueVariance d y1 y0)

theorem tb13_centered_sum {N : ℕ} [NeZero N] (y : Fin N → ℝ) :
    (∑ i, (y i-finiteMean y)) = 0 := by
  have h := finiteMean_centered (NeZero.pos N) y
  simpa only [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    div_eq_zero_iff, Nat.cast_eq_zero, NeZero.ne N, or_false] using h

/-- Both sets of array margins vanish exactly. -/
theorem tb13_array_margins (d : Design) (y1 y0 : Fin d.N → ℝ) :
    (∀ s, ∑ i, tb13_array d y1 y0 s i = 0) ∧
    (∀ i, ∑ s, tb13_array d y1 y0 s i = 0) := by
  letI tb13_population_nonzero : NeZero d.N := ⟨by have := d.population_min; omega⟩
  have hn : (d.N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d.N
  obtain ⟨ht, _, hc, _, _⟩ := n4_proof d
  constructor
  · intro s
    simp only [tb13_array, ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum, tb13_centered_sum, mul_zero, zero_add, zero_div]
  · intro i
    simp only [tb13_array, ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ht, hc]
    field_simp
    ring

/-- The permutation statistic is precisely the actual-variance standardized error. -/
theorem tb13_array_statistic (d : Design) (y1 y0 : Fin d.N → ℝ) (π : Assignment d) :
    (∑ s, tb13_array d y1 y0 s (π s)) =
      (estimatedEffect d y1 y0 π-averageEffect d y1 y0) /
        Real.sqrt (trueVariance d y1 y0) := by
  letI tb13_population_nonzero : NeZero d.N := ⟨by have := d.population_min; omega⟩
  simp only [tb13_array]
  rw [← Finset.sum_div, n2_proof d y1 y0 π]
  congr 1
  have h1 : (∑ s, (y1 (π s)-finiteMean y1)) = 0 := by
    calc
      _ = ∑ i, (y1 i-finiteMean y1) := Equiv.sum_comp π (fun i => y1 i-finiteMean y1)
      _ = 0 := tb13_centered_sum y1
  have h0 : (∑ s, (y0 (π s)-finiteMean y0)) = 0 := by
    calc
      _ = ∑ i, (y0 i-finiteMean y0) := Equiv.sum_comp π (fun i => y0 i-finiteMean y0)
      _ = 0 := tb13_centered_sum y0
  simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, h1, h0, mul_zero, sub_zero, add_zero]

/-- Exact energy normalization follows from the array second moment
and the independently defined randomization variance. -/
theorem tb13_array_energy (d : Design) (y1 y0 : Fin d.N → ℝ)
    (hv : 0 < trueVariance d y1 y0) :
    (∑ s, ∑ i, tb13_array d y1 y0 s i ^ 2) = (d.N : ℝ)-1 := by
  open AronowAudit.MapTailB.PermutationArray in
  have hm := (array_second_moments (by have := d.population_min; omega)
    (tb13_array d y1 y0) (tb13_array_margins d y1 y0).1
      (tb13_array_margins d y1 y0).2).1
  have hs : designExpectation d (fun π =>
      ((estimatedEffect d y1 y0 π-averageEffect d y1 y0) /
        Real.sqrt (trueVariance d y1 y0))^2) = 1 := by
    simp_rw [div_pow]
    rw [show (Real.sqrt (trueVariance d y1 y0))^2 = trueVariance d y1 y0 from
      Real.sq_sqrt hv.le]
    unfold designExpectation
    rw [← Finset.expect_div]
    have he : (𝔼 π, (estimatedEffect d y1 y0 π-averageEffect d y1 y0)^2) =
        trueVariance d y1 y0 := by
      rw [trueVariance, designVariance,
        (sharp_bounds_variance_and_all_couplings d y1 y0).1]
      rfl
    rw [he, div_self hv.ne']
  have he : AronowAudit.MapTailB.PermutationArray.average (fun π =>
      (AronowAudit.MapTailB.PermutationArray.statistic (tb13_array d y1 y0) π)^2) = 1 := by
    simpa only [AronowAudit.MapTailB.PermutationArray.average,
      AronowAudit.MapTailB.PermutationArray.statistic, tb13_array_statistic,
      designExpectation, Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm] using hs
  rw [he] at hm
  have hn : (d.N : ℝ)-1 ≠ 0 := by
    have hnr : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  exact (div_eq_one_iff_eq hn).mp hm.symm

/-- A finite mean stays within any common absolute bound. -/
theorem tb13_mean_abs_bound {N : ℕ} [NeZero N] (y : Fin N → ℝ) (C : ℝ)
    (hy : ∀ i, |y i| ≤ C) : |finiteMean y| ≤ C := by
  apply abs_le.mpr
  constructor
  · have hh : finiteMean (fun i => -C) ≤ finiteMean y :=
      Finset.expect_le_expect (fun i _ => (abs_le.mp (hy i)).1)
    simpa only [finiteMean, Finset.expect_const Finset.univ_nonempty] using hh
  · exact Finset.expect_le Finset.univ_nonempty (fun i _ => (abs_le.mp (hy i)).2)

/-- A third-moment bound controls every entry at the root-population scale,
using only repeated square roots rather than fractional-power conventions. -/
theorem tb13_entry_bound {N : ℕ} [NeZero N] (y : Fin N → ℝ) (M : ℝ)
    (hM : finiteMean (fun i => |y i|^3) ≤ M) (i : Fin N) :
    |y i| ≤ Real.sqrt N *
      Real.sqrt (1/Real.sqrt N + M/Real.sqrt (Real.sqrt N)) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hs := Real.sqrt_pos.mpr hn
  have htail := third_moment_tail_bound y (Real.sqrt N) hs
  have hy : y i ^ 2 / (N : ℝ) ≤
      1/Real.sqrt N + M/Real.sqrt (Real.sqrt N) := by
    have hq : Real.sqrt N / (N : ℝ) = 1/Real.sqrt N := by
      have hh := Real.sq_sqrt hn.le
      field_simp
      nlinarith
    by_cases ht : Real.sqrt N ≤ y i ^ 2
    · have hsingle : y i^2/(N : ℝ) ≤
          finiteMean (fun j => if Real.sqrt N ≤ y j^2 then y j^2 else 0) := by
        unfold finiteMean
        rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
        apply div_le_div_of_nonneg_right _ hn.le
        convert Finset.single_le_sum (fun j _ => show 0 ≤
          (if Real.sqrt N ≤ y j^2 then y j^2 else 0) by split_ifs <;> positivity)
          (Finset.mem_univ i) using 1
        rw [if_pos ht]
      have hb := hsingle.trans (htail.trans
        (div_le_div_of_nonneg_right hM (Real.sqrt_nonneg _)))
      linarith [one_div_pos.mpr hs]
    · have hh := div_le_div_of_nonneg_right (le_of_not_ge ht) hn.le
      rw [hq] at hh
      have hM0 : 0 ≤ M := (Finset.expect_nonneg (fun j _ => by positivity)).trans hM
      exact hh.trans (le_add_of_nonneg_right (by positivity))
  have hpos : 0 ≤ 1/Real.sqrt N + M/Real.sqrt (Real.sqrt N) :=
    (div_nonneg (sq_nonneg _) hn.le).trans hy
  have hh := (div_le_iff₀ hn).mp hy
  have hsq := Real.sq_sqrt hpos
  have hN := Real.sq_sqrt hn.le
  have hB := mul_nonneg (Real.sqrt_nonneg (N : ℝ))
    (Real.sqrt_nonneg (1/Real.sqrt N+M/Real.sqrt (Real.sqrt N)))
  have hprod : (Real.sqrt (N : ℝ) *
      Real.sqrt (1/Real.sqrt N+M/Real.sqrt (Real.sqrt N)))^2 =
      (N : ℝ)*(1/Real.sqrt N+M/Real.sqrt (Real.sqrt N)) := by
    rw [mul_pow, hN, hsq]
  nlinarith [sq_abs (y i)]

/-- A uniform bound on both centered outcome columns. -/
theorem tb13_centered_entry_bound {N : ℕ} [NeZero N] (y : Fin N → ℝ) (C : ℝ)
    (hy : ∀ i, |y i| ≤ C) (i : Fin N) : |y i-finiteMean y| ≤ 2*C := by
  exact (abs_sub _ _).trans (by linarith [hy i, tb13_mean_abs_bound y C hy])

/-- Array entries have an explicit bound with a vanishing outcome factor. -/
theorem tb13_array_bound (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ)
    (h1 : ∀ i, |y1 i| ≤ Real.sqrt d.N*C)
    (h0 : ∀ i, |y0 i| ≤ Real.sqrt d.N*C) (hv : 0 < trueVariance d y1 y0)
    (s i : Fin d.N) : |tb13_array d y1 y0 s i| ≤
      2*C*((d.N : ℝ)/d.m+(d.N : ℝ)/d.k+2) /
        Real.sqrt ((d.N : ℝ)*trueVariance d y1 y0) := by
  letI tb13_population_nonzero : NeZero d.N := ⟨by have := d.population_min; omega⟩
  have hn : (0 : ℝ) < d.N := by exact_mod_cast NeZero.pos d.N
  have hm : (0 : ℝ) < d.m := by exact_mod_cast (show 0 < d.m by have := d.treatment_min; omega)
  have hk : (0 : ℝ) < d.k := by exact_mod_cast (show 0 < d.k by have := d.control_min; omega)
  have hC : 0 ≤ C := by
    have h := h1 ⟨0, NeZero.pos d.N⟩
    nlinarith [abs_nonneg (y1 ⟨0, NeZero.pos d.N⟩), Real.sqrt_pos.mpr hn]
  have ha : |treatCoef d s-1/(d.N : ℝ)| ≤ 1/(d.m : ℝ)+1/(d.N : ℝ) := by
    apply (abs_sub _ _).trans
    simp only [treatCoef]
    split_ifs <;> simp [abs_of_pos (one_div_pos.mpr hm),
      abs_of_pos (one_div_pos.mpr hn)]
  have hb : |ctrlCoef d s+1/(d.N : ℝ)| ≤ 1/(d.k : ℝ)+1/(d.N : ℝ) := by
    apply (abs_add_le _ _).trans
    simp only [ctrlCoef]
    split_ifs <;> simp [abs_neg, abs_of_pos (one_div_pos.mpr hk),
      abs_of_pos (one_div_pos.mpr hn)]
  have hbd : |tb13_array d y1 y0 s i| ≤
      ((1/(d.m : ℝ)+1/(d.N : ℝ))*(2*(Real.sqrt d.N*C))+
        (1/(d.k : ℝ)+1/(d.N : ℝ))*(2*(Real.sqrt d.N*C))) /
          Real.sqrt (trueVariance d y1 y0) := by
    rw [tb13_array, abs_div, abs_of_pos (Real.sqrt_pos.mpr hv)]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul ha (tb13_centered_entry_bound y1 _ h1 i) (abs_nonneg _) (by positivity))
      (mul_le_mul hb (tb13_centered_entry_bound y0 _ h0 i) (abs_nonneg _) (by positivity))
  apply hbd.trans_eq
  rw [Real.sqrt_mul hn.le]
  have hs := Real.sq_sqrt hn.le
  field_simp
  rw [hs]
  ring


/-- The max-entry permutation CLT applies to the actual two-arm design. -/
theorem tb13_actual_variance_clt (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (h3 : BoundedThirdMoments S)
    (hns : NonsingularLaw H) :
    weakStandardNormal S (fun q π =>
      (estimatedEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) π -
        averageEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)) /
          Real.sqrt (trueVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q))) := by
  have hUI := tb13_square_integrability S h3
  have hs := tb13_limiting_variance_pos S H θ ρ h hUI hns
  have hv := tb13_true_variance_limit S H θ ρ h hUI
  obtain ⟨M, hM⟩ := h3
  let C (q : ℕ) := Real.sqrt (1/Real.sqrt (S.design q).N +
    M/Real.sqrt (Real.sqrt (S.design q).N))
  let V (q : ℕ) := trueVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)
  let β (q : ℕ) := 2*C q*
    (((S.design q).N : ℝ)/(S.design q).m+((S.design q).N : ℝ)/(S.design q).k+2) /
      Real.sqrt (((S.design q).N : ℝ)*V q)
  have hN := GP022B1b_size_atTop S
  have hc : Tendsto C atTop (𝓝 0) := by
    have ht := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop (Real.tendsto_sqrt_atTop.comp hN)).add
      ((tendsto_const_nhds (x := M)).div_atTop
        (Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hN)))
    simpa only [C, Function.comp_def, one_div, zero_add, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp ht
  have hm : Tendsto (fun q => ((S.design q).N : ℝ)/(S.design q).m)
      atTop (𝓝 (1/(θ*ρ))) := by
    have ht := h.2.2.2.2.1.inv₀ (mul_pos h.1 h.2.2.1).ne'
    simpa only [inv_div, one_div] using ht
  have hk : Tendsto (fun q => ((S.design q).N : ℝ)/(S.design q).k)
      atTop (𝓝 (1/(θ*(1-ρ)))) := by
    have ht := (GP022B1b_control_ratio S θ ρ h.2.2.2.2.1 h.2.2.2.2.2.1).inv₀
      (mul_pos h.1 (sub_pos.mpr h.2.2.2.1)).ne'
    simpa only [inv_div, one_div] using ht
  have hβ : Tendsto β atTop (𝓝 0) := by
    have ht := ((hc.const_mul 2).mul ((hm.add hk).add_const 2)).div
      (Real.continuous_sqrt.continuousAt.tendsto.comp hv) (Real.sqrt_pos.mpr hs).ne'
    simpa only [β, V, Function.comp_def, Pi.div_def, zero_mul, mul_zero, zero_div] using ht
  have hpos : ∀ᶠ q in atTop, 0 < V q := by
    filter_upwards [hv.eventually_const_lt hs] with q hq
    exact pos_of_mul_pos_right hq (Nat.cast_nonneg _)
  have hh := TailB_permutation_array_clt (fun q => (S.design q).N)
    (by simpa only [S.size] using (tendsto_add_atTop_nat 4))
    (fun q => tb13_array (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)) β hβ
    (by
      filter_upwards [hpos] with q hq
      refine ⟨by have := (S.design q).population_min; omega,
        (tb13_array_margins _ _ _).1, (tb13_array_margins _ _ _).2,
        tb13_array_energy _ _ _ hq, ?_⟩
      intro s i
      exact tb13_array_bound _ _ _ (C q)
        (fun j => tb13_entry_bound _ M (hM q true) j)
        (fun j => tb13_entry_bound _ M (hM q false) j) hq s i)
  intro f
  simpa only [designExpectation, Fintype.expect_eq_sum_div_card, tb13_array_statistic] using hh f

end
end AronowAudit.P022.Wave1
