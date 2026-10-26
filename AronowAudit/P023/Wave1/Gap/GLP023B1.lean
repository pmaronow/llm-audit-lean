import AronowAudit.P023.Wave1.Gap.GP023B1b
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

namespace AronowAudit.P023.Wave1

noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
local instance instDecidableGLP023B1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false

/-! Polynomial projection algebra under uniform margins. -/
private theorem t3_poly_integrable (p : Polynomial ℝ) :
    Integrable (fun x => p.eval x) uniformMargins := by
  exact p.continuous.integrableOn_Icc.smul_measure (by norm_num)

private theorem t3_piecewise_integrable (p q : Polynomial ℝ) :
    Integrable (fun x => if 0 ≤ x then p.eval x else q.eval x) uniformMargins := by
  exact Integrable.piecewise measurableSet_Ici
    (t3_poly_integrable p).integrableOn (t3_poly_integrable q).integrableOn

private theorem t3_residual_mul_integrable (p q : Polynomial ℝ) :
    Integrable (fun x => (party x - p.eval x) * q.eval x) uniformMargins := by
  convert t3_piecewise_integrable ((1 - p) * q) (-p * q) using 1
  funext x
  by_cases hx : 0 ≤ x <;> simp [party, hx] <;> ring

private theorem t3_poly_mul_integrable (p q : Polynomial ℝ) :
    Integrable (fun x => p.eval x * q.eval x) uniformMargins := by
  simpa only [Polynomial.eval_mul] using t3_poly_integrable (p * q)

private theorem t3_poly_power_integrable (p : Polynomial ℝ) (j : ℕ) :
    Integrable (fun x => p.eval x * x ^ j) uniformMargins := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    t3_poly_mul_integrable p (Polynomial.X ^ j)

private theorem t3_residual_power_integrable (p : Polynomial ℝ) (j : ℕ) :
    Integrable (fun x => (party x - p.eval x) * x ^ j) uniformMargins := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    t3_residual_mul_integrable p (Polynomial.X ^ j)

private theorem t3_eq_interval (f : ℝ → ℝ) :
    expectation uniformMargins f = (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, f x := by
  unfold expectation uniformMargins
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  norm_num

private theorem t3_reflect_integral (f : ℝ → ℝ) :
    expectation uniformMargins (fun x => f (-x)) = expectation uniformMargins f := by
  rw [t3_eq_interval, t3_eq_interval, intervalIntegral.integral_comp_neg]
  norm_num

private theorem t3_power (j : ℕ) :
    expectation uniformMargins (fun x => x ^ j) =
      (1 / 2 : ℝ) * ((1 : ℝ) ^ (j + 1) - (-1 : ℝ) ^ (j + 1)) / (j + 1) := by
  rw [t3_eq_interval, integral_pow]
  ring

private theorem t3_party_power (j : ℕ) :
    expectation uniformMargins (fun x => party x * x ^ j) = 1 / (2 * (j + 1)) := by
  have he : (fun x : ℝ => party x * x ^ j) = (Ici (0 : ℝ)).indicator (fun x => x ^ j) := by
    funext x
    by_cases hx : 0 ≤ x <;> simp [party, hx, Set.indicator]
  have hi : Ici (0 : ℝ) ∩ Icc (-1 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨h0, _, h1⟩
      exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h0, by linarith, h1⟩
  unfold expectation uniformMargins
  rw [integral_smul_measure, he, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, hi, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero j)]
  norm_num <;> ring

private def t3_poly (J : ℕ) (a : Fin (J + 1) → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

private theorem t3_poly_eval (J : ℕ) (a : Fin (J + 1) → ℝ) (x : ℝ) :
    (t3_poly J a).eval x = ∑ i, a i * x ^ (i : ℕ) := by
  simp [t3_poly, Polynomial.eval_finset_sum]

private theorem t3_poly_degree (J : ℕ) (a : Fin (J + 1) → ℝ) :
    (t3_poly J a).natDegree ≤ J := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

private theorem t3_poly_coeff (J : ℕ) (a : Fin (J + 1) → ℝ) (i : Fin (J + 1)) :
    (t3_poly J a).coeff i = a i := by
  classical
  simp [t3_poly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    ← Fin.ext_iff]

private theorem t3_eval_expansion (p : Polynomial ℝ) (J : ℕ) (hp : p.natDegree ≤ J)
    (x : ℝ) : p.eval x = ∑ i : Fin (J + 1), p.coeff i * x ^ (i : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (show p.natDegree < J + 1 by omega)]
  exact (Fin.sum_univ_eq_sum_range _ _).symm
  

private theorem t3_test (J : ℕ) (p q : Polynomial ℝ)
    (hp : IsProjection uniformMargins J p) (hq : q.natDegree ≤ J) :
    expectation uniformMargins (fun x => (party x - p.eval x) * q.eval x) = 0 := by
  classical
  have he : (fun x => (party x - p.eval x) * q.eval x) =
      (fun x => ∑ i : Fin (J + 1), q.coeff i * ((party x - p.eval x) * x ^ (i : ℕ))) := by
    funext x
    rw [t3_eval_expansion q J hq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold expectation
  rw [he, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_const_mul]
    change q.coeff i * expectation uniformMargins _ = 0
    rw [hp.2 i (by omega), mul_zero]
  · intro i _
    exact (t3_residual_power_integrable p i).const_mul _

private theorem t3_square_zero (p : Polynomial ℝ)
    (hz : expectation uniformMargins (fun x => p.eval x ^ 2) = 0) : p = 0 := by
  have hint : Integrable (fun x => p.eval x ^ 2) uniformMargins := by
    apply (t3_poly_integrable (p ^ 2)).congr
    exact Filter.Eventually.of_forall (fun x => Polynomial.eval_pow 2)
  have hae : ∀ᵐ x ∂uniformMargins, p.eval x = 0 := by
    have hs := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (p.eval x)) hint).mp hz
    filter_upwards [hs] with x hx
    exact (sq_eq_zero_iff).mp hx
  have hae' : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1), p.eval x = 0 := by
    exact (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)).mp hae
  have heq : EqOn (fun x => p.eval x) (fun _ => (0 : ℝ)) (Icc (-1 : ℝ) 1) :=
    Measure.eqOn_Icc_of_ae_eq volume (by norm_num) hae'
      p.continuous.continuousOn continuous_const.continuousOn
  apply p.eq_zero_of_infinite_isRoot
  exact (Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).mono
    (fun x hx => heq ⟨hx.1.le, hx.2.le⟩)

private theorem t3_unique (J : ℕ) (p q : Polynomial ℝ)
    (hp : IsProjection uniformMargins J p) (hq : IsProjection uniformMargins J q) : p = q := by
  have hdeg : (p - q).natDegree ≤ J :=
    (Polynomial.natDegree_sub_le p q).trans (max_le hp.1 hq.1)
  have h1 := t3_test J p (p - q) hp hdeg
  have h2 := t3_test J q (p - q) hq hdeg
  have hs : expectation uniformMargins (fun x => (p - q).eval x ^ 2) = 0 := by
    have he : (fun x => (p - q).eval x ^ 2) =
        (fun x => (party x - q.eval x) * (p - q).eval x -
          (party x - p.eval x) * (p - q).eval x) := by
      funext x
      simp only [Polynomial.eval_sub]
      ring
    unfold expectation at *
    rw [he, integral_sub (t3_residual_mul_integrable q (p - q))
      (t3_residual_mul_integrable p (p - q)), h2, h1, sub_self]
  exact sub_eq_zero.mp (t3_square_zero (p - q) hs)

private theorem t3_exists_core (μ : Measure ℝ)
    (hpoly : ∀ (p : Polynomial ℝ) (j : ℕ), Integrable (fun x => p.eval x * x ^ j) μ)
    (hparty : ∀ j : ℕ, Integrable (fun x => party x * x ^ j) μ)
    (hzero : ∀ p : Polynomial ℝ, expectation μ (fun x => p.eval x ^ 2) = 0 → p = 0)
    (J : ℕ) : ∃ p, IsProjection μ J p := by
  classical
  let A : (Fin (J + 1) → ℝ) →ₗ[ℝ] (Fin (J + 1) → ℝ) :=
    { toFun := fun a j => expectation μ (fun x => (t3_poly J a).eval x * x ^ (j : ℕ))
      map_add' := by
        intro a b
        funext j
        have he : (fun x => (t3_poly J (a + b)).eval x * x ^ (j : ℕ)) =
            (fun x => (t3_poly J a).eval x * x ^ (j : ℕ) +
              (t3_poly J b).eval x * x ^ (j : ℕ)) := by
          funext x
          simp [t3_poly_eval, add_mul, Finset.sum_add_distrib]
        exact (congrArg (expectation μ) he).trans
          (integral_add (hpoly (t3_poly J a) j)
            (hpoly (t3_poly J b) j))
      map_smul' := by
        intro r a
        funext j
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        change expectation μ _ = r * expectation μ _
        have he : (fun x => (t3_poly J (r • a)).eval x * x ^ (j : ℕ)) =
            (fun x => r * ((t3_poly J a).eval x * x ^ (j : ℕ))) := by
          funext x
          simp only [t3_poly_eval, Pi.smul_apply, smul_eq_mul]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          ring
        rw [he]
        exact integral_const_mul _ _ }
  have hker : ∀ a, A a = 0 → a = 0 := by
    intro a ha
    have hs : expectation μ (fun x => (t3_poly J a).eval x ^ 2) = 0 := by
      have he : (fun x => (t3_poly J a).eval x ^ 2) =
          (fun x => ∑ j : Fin (J + 1), a j * ((t3_poly J a).eval x * x ^ (j : ℕ))) := by
        funext x
        rw [pow_two, t3_poly_eval J a x, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      unfold expectation
      rw [he, integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro j _
        rw [integral_const_mul]
        have hj : expectation μ
            (fun x => (t3_poly J a).eval x * x ^ (j : ℕ)) = 0 := congrFun ha j
        change a j * expectation μ _ = 0
        rw [hj, mul_zero]
      · intro j _
        exact (hpoly (t3_poly J a) j).const_mul _
    have hz := hzero (t3_poly J a) hs
    funext i
    have hi := congrArg (fun p : Polynomial ℝ => p.coeff i) hz
    simpa only [t3_poly_coeff, Polynomial.coeff_zero, Pi.zero_apply] using hi
  have hinj : Function.Injective A := by
    intro a b hab
    have hz := hker (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp hz
  obtain ⟨a, ha⟩ := LinearMap.surjective_of_injective hinj
    (fun j => expectation μ (fun x => party x * x ^ (j : ℕ)))
  refine ⟨t3_poly J a, t3_poly_degree J a, ?_⟩
  intro j hj
  have hm := congrFun ha (⟨j, by omega⟩ : Fin (J + 1))
  change expectation μ (fun x => (t3_poly J a).eval x * x ^ j) =
    expectation μ (fun x => party x * x ^ j) at hm
  unfold expectation at *
  simp_rw [sub_mul]
  rw [integral_sub]
  · exact sub_eq_zero.mpr hm.symm
  · exact hparty j
  · exact hpoly _ j

private theorem t3_exists (J : ℕ) : ∃ p, IsProjection uniformMargins J p := by
  apply t3_exists_core uniformMargins t3_poly_power_integrable _ t3_square_zero J
  intro j
  simpa using t3_residual_power_integrable 0 j

private theorem t3_chosen_spec (J : ℕ) :
    IsProjection uniformMargins J (projection uniformMargins J) :=
  Classical.epsilon_spec (t3_exists J)

private theorem t3_party_reflection (x : ℝ) (hx : x ≠ 0) : party (-x) = 1 - party x := by
  rcases lt_or_gt_of_ne hx with h | h
  · simp [party, h.le, not_le.mpr h, (neg_pos.mpr h).le]
  · simp [party, h.le, not_le.mpr (neg_neg_of_pos h)]

private theorem t3_reflection (J : ℕ) (x : ℝ) :
    (projection uniformMargins J).eval x = 1 - (projection uniformMargins J).eval (-x) := by
  let q := projection uniformMargins J
  let qstar : Polynomial ℝ := 1 - q.comp (-Polynomial.X)
  have hq := t3_chosen_spec J
  have hd : qstar.natDegree ≤ J := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact Polynomial.natDegree_comp_le.trans (by simpa using hq.1)
  have hp : IsProjection uniformMargins J qstar := by
    refine ⟨hd, ?_⟩
    intro j hj
    have hn : ∀ᵐ t ∂uniformMargins, t ≠ (0 : ℝ) := by
      have hm : uniformMargins {0} = 0 := by
        simp [uniformMargins, Measure.smul_apply, Measure.restrict_apply, measurableSet_singleton]
      rw [ae_iff]
      simpa using hm
    have he : (fun t => (party t - qstar.eval t) * t ^ j) =ᵐ[uniformMargins]
        (fun t => -((-1 : ℝ) ^ j) * ((party (-t) - q.eval (-t)) * (-t) ^ j)) := by
      filter_upwards [hn] with t ht
      have hparty := t3_party_reflection t ht
      simp only [qstar, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_comp,
        Polynomial.eval_neg, Polynomial.eval_X]
      rw [neg_pow t j]
      rw [hparty]
      have hsign : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        _ = (party t - 1 + q.eval (-t)) * t ^ j := by ring
        _ = (party t - 1 + q.eval (-t)) *
            (((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) * t ^ j) := by rw [hsign, one_mul]
        _ = _ := by ring
    unfold expectation
    rw [integral_congr_ae he, integral_const_mul]
    change -((-1 : ℝ) ^ j) * expectation uniformMargins
      (fun t => (party (-t) - q.eval (-t)) * (-t) ^ j) = 0
    rw [t3_reflect_integral (fun t => (party t - q.eval t) * t ^ j), hq.2 j hj, mul_zero]
  have hsame := t3_unique J q qstar hq hp
  have := congrArg (fun p : Polynomial ℝ => p.eval x) hsame
  simpa only [qstar, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_comp,
    Polynomial.eval_neg, Polynomial.eval_X] using this

private theorem t3_normal_formula (J : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ J) (j : ℕ) :
    expectation uniformMargins (fun x => (party x - p.eval x) * x ^ j) =
      1 / (2 * (j + 1)) - ∑ i : Fin (J + 1), p.coeff i *
        ((1 / 2 : ℝ) * (1 - (-1 : ℝ) ^ ((i : ℕ) + j + 1)) / ((i : ℕ) + j + 1)) := by
  have he : (fun x => p.eval x * x ^ j) =
      (fun x => ∑ i : Fin (J + 1), p.coeff i * x ^ ((i : ℕ) + j)) := by
    funext x
    rw [t3_eval_expansion p J hp, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]
    ring
  unfold expectation
  simp_rw [sub_mul]
  rw [integral_sub]
  · change expectation uniformMargins (fun x => party x * x ^ j) - _ = _
    rw [t3_party_power, he, integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul]
      change p.coeff i * expectation uniformMargins _ = _
      rw [t3_power]
      simp only [one_pow, Nat.cast_add]
    · intro i _
      simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
        (t3_poly_integrable (Polynomial.X ^ ((i : ℕ) + j))).const_mul (p.coeff i)
  · simpa using t3_residual_power_integrable 0 j
  · exact t3_poly_power_integrable p j

private def t3_q1 : Polynomial ℝ := Polynomial.C (1 / 2) + Polynomial.C (3 / 4) * Polynomial.X

private def t3_q7 : Polynomial ℝ := Polynomial.C (1 / 2) + Polynomial.C (1 / 4096) *
  (Polynomial.C 11025 * Polynomial.X - Polynomial.C 40425 * Polynomial.X ^ 3 +
    Polynomial.C 63063 * Polynomial.X ^ 5 - Polynomial.C 32175 * Polynomial.X ^ 7)

private theorem t3_q1_spec : IsProjection uniformMargins 1 t3_q1 := by
  have hd : t3_q1.natDegree ≤ 1 := by unfold t3_q1; compute_degree
  refine ⟨hd, ?_⟩
  intro j hj
  interval_cases j <;> rw [t3_normal_formula 1 t3_q1 hd] <;>
    norm_num [t3_q1, pow_two, Fin.sum_univ_succ, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]

private theorem t3_q7_spec : IsProjection uniformMargins 7 t3_q7 := by
  have hd : t3_q7.natDegree ≤ 7 := by unfold t3_q7; compute_degree
  refine ⟨hd, ?_⟩
  intro j hj
  interval_cases j <;> rw [t3_normal_formula 7 t3_q7 hd] <;>
    norm_num [t3_q7, Fin.sum_univ_succ, Polynomial.coeff_add,
      Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]


private def t3_smooth (J : ℕ) (c : Fin (J+2) → ℝ) : Polynomial ℝ :=
  ∑ j, if j.val = 1 then 0 else Polynomial.C (c j) *
    Polynomial.X ^ (if j.val = 0 then 0 else j.val - 1)


private theorem t3_predict (J : ℕ) (c : Fin (J+2) → ℝ) (x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) c x =
      (t3_smooth J c).eval x + c 1 * party x := by
  have hone : (∑ j : Fin (J+2), if j.val = 1 then c 1 * party x else 0) = c 1 * party x := by
    have he (j : Fin (J+2)) : (j.val = 1) ↔ j = 1 := by
      constructor
      · intro h; apply Fin.ext; simpa using h
      · intro h; subst j; simp
    simp_rw [he]
    simp
  have heval : (t3_smooth J c).eval x = ∑ j : Fin (J+2),
      if j.val = 1 then 0 else c j * x ^ (if j.val = 0 then 0 else j.val - 1) := by
    unfold t3_smooth
    rw [Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val = 1
    · simp only [if_pos hj, Polynomial.eval_zero]
    · simp only [if_neg hj, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
  rw [heval, ← hone, ← Finset.sum_add_distrib]
  unfold predict
  apply Finset.sum_congr rfl
  intro j _
  by_cases h0 : j.val = 0
  · simp [polynomialDesign, h0]
  · by_cases h1 : j.val = 1
    · have hj : j = 1 := Fin.ext h1
      simp [polynomialDesign, h0, h1, hj, mul_comm]
    · simp [polynomialDesign, h0, h1, mul_comm]

private theorem t3_smooth_coeff (J : ℕ) (c : Fin (J+2) → ℝ)
    (j : Fin (J+2)) (hj : j.val ≠ 1) :
    (t3_smooth J c).coeff (if j.val = 0 then 0 else j.val - 1) = c j := by
  unfold t3_smooth
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · simp only [if_neg hj, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_true, mul_one]
  · intro i _ hij
    by_cases hi : i.val = 1
    · simp [hi]
    · have he : (if i.val = 0 then 0 else i.val - 1) ≠
          (if j.val = 0 then 0 else j.val - 1) := by
        intro h
        have hval : i.val = j.val := by split_ifs at h <;> omega
        exact hij (Fin.ext hval)
      simp only [if_neg hi, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm he), mul_zero]
  · simp


private theorem t3_fit_square_integrable (J : ℕ) (c : Fin (J+2) → ℝ) :
    Integrable (fun x => predict (polynomialDesign J (fun x : ℝ => x) party) c x ^ 2) uniformMargins := by
  convert t3_piecewise_integrable ((t3_smooth J c + Polynomial.C (c 1))^2)
    ((t3_smooth J c)^2) using 1
  funext x
  rw [t3_predict]
  by_cases hx : 0 ≤ x <;> simp [party, hx]

private theorem t3_fit_zero (J : ℕ) (c : Fin (J+2) → ℝ)
    (hz : expectation uniformMargins (fun x =>
      predict (polynomialDesign J (fun x : ℝ => x) party) c x ^ 2) = 0) : c = 0 := by
  have hae : ∀ᵐ x ∂uniformMargins,
      predict (polynomialDesign J (fun x : ℝ => x) party) c x = 0 := by
    have h := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
      (t3_fit_square_integrable J c)).mp hz
    filter_upwards [h] with x hx using sq_eq_zero_iff.mp hx
  have haev : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1),
      predict (polynomialDesign J (fun x : ℝ => x) party) c x = 0 :=
    (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1/2 : ℝ≥0∞) ≠ 0)).mp hae
  have hneg : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (-1 : ℝ) (-1/2)),
      (t3_smooth J c).eval x = 0 := by
    have hsub : Icc (-1 : ℝ) (-1/2) ⊆ Icc (-1 : ℝ) 1 := by intro x hx; constructor <;> linarith [hx.1, hx.2]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub haev,
      ae_restrict_mem measurableSet_Icc] with x hx hxs
    rw [t3_predict, party, if_neg (by linarith [hxs.2]), mul_zero, add_zero] at hx
    exact hx
  have heq := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (-1 : ℝ) ≠ -1/2) hneg
    (t3_smooth J c).continuous.continuousOn continuous_const.continuousOn
  have hp : t3_smooth J c = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact (Ioo_infinite (show (-1 : ℝ) < -1/2 by norm_num)).mono
      (fun x hx => heq ⟨hx.1.le, hx.2.le⟩)
  have hpos : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (1/2 : ℝ) 1), c 1 = 0 := by
    have hsub : Icc (1/2 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := by intro x hx; constructor <;> linarith [hx.1, hx.2]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub haev,
      ae_restrict_mem measurableSet_Icc] with x hx hxs
    simpa [t3_predict, hp, party, show 0 ≤ x by linarith [hxs.1]] using hx
  have hc1 : c 1 = 0 := by
    have h := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (1/2 : ℝ) ≠ 1)
      hpos continuous_const.continuousOn continuous_const.continuousOn
    exact h (show (1/2 : ℝ) ∈ Icc (1/2 : ℝ) 1 by norm_num)
  funext j
  by_cases hj : j.val = 1
  · have hje : j = 1 := Fin.ext hj
    simpa [hje] using hc1
  · have h := t3_smooth_coeff J c j hj
    rw [hp, Polynomial.coeff_zero] at h
    exact h.symm

private theorem t3_moment_pos (J : ℕ) : MomentPositiveDefinite uniformMargins J := by
  intro c hc
  have hn : 0 ≤ expectation uniformMargins (fun x =>
    predict (polynomialDesign J (fun x : ℝ => x) party) c x ^ 2) := integral_nonneg (fun x => sq_nonneg _)
  exact lt_of_le_of_ne hn (fun hz => hc (t3_fit_zero J c hz.symm))

private theorem t3_column_fit_integrable (J : ℕ) (c : Fin (J+2) → ℝ) (j : Fin (J+2)) :
    Integrable (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
      predict (polynomialDesign J (fun x : ℝ => x) party) c x) uniformMargins := by
  apply GP023B1b_supported_integrable _ uniform_law_normalized.1 uniform_law_normalized.2
    ((GP023B1b_column_measurable J j).mul (GP023B1b_predict_measurable J c)) (∑ j, |c j|)
  intro x hx
  change |polynomialDesign J (fun x : ℝ => x) party x j * predict (polynomialDesign J (fun x : ℝ => x) party) c x| ≤ _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (GP023B1b_column_bound J j x hx) (abs_nonneg _)).trans
    (by simpa using GP023B1b_predict_bound J c x hx)

private theorem t3_fit_linear (J : ℕ) (a b : Fin (J+2) → ℝ) (r : ℝ) (x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) (a + r • b) x =
      predict (polynomialDesign J (fun x : ℝ => x) party) a x +
        r * predict (polynomialDesign J (fun x : ℝ => x) party) b x := by
  simp [predict, Pi.add_apply, Pi.smul_apply, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, mul_left_comm, mul_assoc]

private theorem t3_normal_exists (J : ℕ) (m : ℝ → ℝ)
    (hm : ∀ j : Fin (J+2), Integrable (fun x =>
      polynomialDesign J (fun x : ℝ => x) party x j * m x) uniformMargins) :
    ∃ c, PopNormal uniformMargins J m c := by
  let A : (Fin (J+2) → ℝ) →ₗ[ℝ] (Fin (J+2) → ℝ) :=
    { toFun := fun c j => expectation uniformMargins (fun x =>
        polynomialDesign J (fun x : ℝ => x) party x j *
          predict (polynomialDesign J (fun x : ℝ => x) party) c x)
      map_add' := by
        intro a b
        funext j
        simp only [Pi.add_apply]
        have he := t3_fit_linear J a b 1
        simp only [one_smul, one_mul] at he
        simp_rw [he, mul_add]
        exact integral_add (t3_column_fit_integrable J a j) (t3_column_fit_integrable J b j)
      map_smul' := by
        intro r a
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        have he (x : ℝ) : predict (polynomialDesign J (fun x : ℝ => x) party) (r • a) x =
            r * predict (polynomialDesign J (fun x : ℝ => x) party) a x := by
          simpa [predict] using t3_fit_linear J 0 a r x
        simp_rw [he, mul_left_comm _ r]
        exact integral_const_mul _ _ }
  have ker : ∀ c, A c = 0 → c = 0 := by
    intro c hc
    apply t3_fit_zero J c
    have he : (fun x => predict (polynomialDesign J (fun x : ℝ => x) party) c x ^ 2) =
        fun x => ∑ j, c j * (polynomialDesign J (fun x : ℝ => x) party x j *
          predict (polynomialDesign J (fun x : ℝ => x) party) c x) := by
      funext x
      rw [pow_two, predict, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    unfold expectation
    rw [he, integral_finsetSum _ (fun j _ => (t3_column_fit_integrable J c j).const_mul (c j))]
    apply Finset.sum_eq_zero
    intro j _
    rw [integral_const_mul]
    have hj : expectation uniformMargins (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
      predict (polynomialDesign J (fun x : ℝ => x) party) c x) = 0 := congrFun hc j
    change c j * expectation uniformMargins _ = 0
    rw [hj, mul_zero]
  have inj : Function.Injective A := by
    intro a b h
    exact sub_eq_zero.mp (ker (a-b) (by rw [map_sub, h, sub_self]))
  obtain ⟨c, hc⟩ := LinearMap.surjective_of_injective inj (fun j => expectation uniformMargins
    (fun x => polynomialDesign J (fun x : ℝ => x) party x j * m x))
  refine ⟨c, fun j => ?_⟩
  have hj := congrFun hc j
  unfold expectation at *
  simp_rw [mul_sub]
  rw [integral_sub (hm j) (t3_column_fit_integrable J c j)]
  exact sub_eq_zero.mpr hj.symm

private theorem t3_normal_unique (J : ℕ) (m : ℝ → ℝ)
    (hm : ∀ j : Fin (J+2), Integrable (fun x =>
      polynomialDesign J (fun x : ℝ => x) party x j * m x) uniformMargins)
    (a b : Fin (J+2) → ℝ) (ha : PopNormal uniformMargins J m a)
    (hb : PopNormal uniformMargins J m b) : a = b := by
  have hz (j : Fin (J+2)) : expectation uniformMargins
      (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
        predict (polynomialDesign J (fun x : ℝ => x) party) (a-b) x) = 0 := by
    have he (x : ℝ) : predict (polynomialDesign J (fun x : ℝ => x) party) (a-b) x =
        predict (polynomialDesign J (fun x : ℝ => x) party) a x -
          predict (polynomialDesign J (fun x : ℝ => x) party) b x := by
      simpa [sub_eq_add_neg] using t3_fit_linear J a b (-1) x
    have h1 := ha j
    have h2 := hb j
    unfold expectation at *
    simp_rw [mul_sub] at h1 h2
    rw [integral_sub (hm j) (t3_column_fit_integrable J a j)] at h1
    rw [integral_sub (hm j) (t3_column_fit_integrable J b j)] at h2
    simp_rw [he, mul_sub]
    rw [integral_sub (t3_column_fit_integrable J a j) (t3_column_fit_integrable J b j)]
    linarith
  apply sub_eq_zero.mp
  apply t3_fit_zero J (a-b)
  have he : (fun x => predict (polynomialDesign J (fun x : ℝ => x) party) (a-b) x ^ 2) =
      fun x => ∑ j, (a-b) j * (polynomialDesign J (fun x : ℝ => x) party x j *
        predict (polynomialDesign J (fun x : ℝ => x) party) (a-b) x) := by
    funext x
    rw [pow_two, predict, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold expectation
  rw [he, integral_finsetSum _ (fun j _ => (t3_column_fit_integrable J (a-b) j).const_mul _)]
  apply Finset.sum_eq_zero
  intro j _
  rw [integral_const_mul]
  change (a-b) j * expectation uniformMargins _ = 0
  rw [hz, mul_zero]

private theorem t3_chosen1 : projection uniformMargins 1 = t3_q1 :=
  t3_unique 1 _ _ (t3_chosen_spec 1) t3_q1_spec
private theorem t3_chosen7 : projection uniformMargins 7 = t3_q7 :=
  t3_unique 7 _ _ (t3_chosen_spec 7) t3_q7_spec

private theorem t3_square_abs (J : ℕ) (x : ℝ) :
    popResidual uniformMargins J x ^ 2 = (1 - (projection uniformMargins J).eval |x|)^2 := by
  by_cases hx : 0 ≤ x
  · simp [popResidual, party, hx, abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), t3_reflection]
    simp only [popResidual, party, if_neg hx, zero_sub, neg_sq]
    ring

private theorem t3_even_integral (g : ℝ → ℝ) (hg : Continuous g) :
    expectation uniformMargins (fun x => g |x|) = ∫ x in (0 : ℝ)..1, g x := by
  rw [GP023B1b_uniform_halves (fm := fun x => g (-x)) (fp := g)
    (hg.comp continuous_neg) hg
    (fun x hx => by rw [abs_of_neg hx.2])
    (fun x hx => by rw [abs_of_pos hx.1])]
  have he : (∫ x in (-1 : ℝ)..0, g (-x)) = ∫ x in (0 : ℝ)..1, g x := by
    rw [intervalIntegral.integral_comp_neg]
    norm_num
  rw [he]
  ring

private theorem t3_variance_half (J : ℕ) :
    residualVariance uniformMargins J =
      ∫ x in (0 : ℝ)..1, (1 - (projection uniformMargins J).eval x)^2 := by
  unfold residualVariance
  simp_rw [t3_square_abs]
  exact t3_even_integral _ ((continuous_const.sub (projection uniformMargins J).continuous).pow 2)

private theorem t3_tail_half (J : ℕ) :
    expectation uniformMargins (fun x => if 1/2 ≤ |x| then popResidual uniformMargins J x ^ 2 else 0) =
      ∫ x in (1/2 : ℝ)..1, (1 - (projection uniformMargins J).eval x)^2 := by
  let g : ℝ → ℝ := fun x => (1 - (projection uniformMargins J).eval x)^2
  have hg : Continuous g := (continuous_const.sub (projection uniformMargins J).continuous).pow 2
  have he : (fun x => if 1/2 ≤ |x| then popResidual uniformMargins J x ^ 2 else 0) =
      fun x => (Iic (-1/2 : ℝ)).indicator (fun x => g (-x)) x +
        (Ici (1/2 : ℝ)).indicator g x := by
    funext x
    rw [t3_square_abs]
    change (if (1/2:ℝ) ≤ |x| then g |x| else 0) =
      (if x ≤ (-1/2:ℝ) then g (-x) else 0) + (if (1/2:ℝ) ≤ x then g x else 0)
    by_cases hx : x ≤ -1/2
    · have hx0 : x < 0 := by linarith
      rw [if_pos hx, if_neg (by linarith : ¬ (1/2:ℝ) ≤ x),
        abs_of_neg hx0, if_pos (by linarith : (1/2:ℝ) ≤ -x), add_zero]
    · by_cases hp : (1/2:ℝ) ≤ x
      · rw [if_neg hx, if_pos hp, abs_of_nonneg (by linarith : 0 ≤ x), if_pos hp, zero_add]
      · have hb : |x| < (1/2:ℝ) := abs_lt.mpr ⟨by linarith, by linarith⟩
        rw [if_neg hx, if_neg hp, if_neg (not_le.mpr hb), add_zero]
  have hi : Iic (-1/2 : ℝ) ∩ Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) (-1/2) := by
    ext x
    simp only [mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h, hl, hu⟩; exact ⟨hl,h⟩
    · rintro ⟨hl,hu⟩; exact ⟨hu,hl,by linarith⟩
  have hp : Ici (1/2 : ℝ) ∩ Icc (-1 : ℝ) 1 = Icc (1/2 : ℝ) 1 := by
    ext x; simp only [mem_inter_iff, Set.mem_Ici, Set.mem_Icc]; constructor <;> intro h
    · exact ⟨h.1, h.2.2⟩
    · exact ⟨h.1, by linarith [h.1], h.2⟩
  have him : Integrable ((Iic (-1/2:ℝ)).indicator (fun x => g (-x)))
      ((volume:Measure ℝ).restrict (Icc (-1:ℝ) 1)) :=
    (hg.comp continuous_neg).integrableOn_Icc.indicator measurableSet_Iic
  have hip : Integrable ((Ici (1/2:ℝ)).indicator g)
      ((volume:Measure ℝ).restrict (Icc (-1:ℝ) 1)) :=
    hg.integrableOn_Icc.indicator measurableSet_Ici
  change expectation uniformMargins _ = ∫ x in (1/2:ℝ)..1, g x
  unfold expectation
  rw [he]
  rw [uniformMargins, integral_smul_measure,
    integral_add him hip,
    integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Iic, Measure.restrict_restrict measurableSet_Ici,
    hi, hp, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ -1/2 by norm_num),
    ← intervalIntegral.integral_of_le (show (1/2 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_comp_neg]
  norm_num [smul_eq_mul]
  ring

private theorem t3_square_integral1 (a b : ℝ) :
    (∫ x in a..b, (1-t3_q1.eval x)^2) =
      (1/4:ℝ) * (b^1-a^1) / 1 + (-3/4:ℝ) * (b^2-a^2) / 2 + (9/16:ℝ) * (b^3-a^3) / 3 := by
  have he (x : ℝ) : (1-t3_q1.eval x)^2 =
      (1/4:ℝ) + (-3/4:ℝ) * x^1 + (9/16:ℝ) * x^2 := by
    simp only [t3_q1, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    ring
  simp_rw [he]
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, integral_pow, integral_id, smul_eq_mul]
  ring

private theorem t3_square_integral7 (a b : ℝ) :
    (∫ x in a..b, (1-t3_q7.eval x)^2) =
      (1/4:ℝ) * (b^1-a^1) / 1 +
        (-11025/4096:ℝ) * (b^2-a^2) / 2 +
        (121550625/16777216:ℝ) * (b^3-a^3) / 3 +
        (40425/4096:ℝ) * (b^4-a^4) / 4 +
        (-445685625/8388608:ℝ) * (b^5-a^5) / 5 +
        (-63063/4096:ℝ) * (b^6-a^6) / 6 +
        (3024719775/16777216:ℝ) * (b^7-a^7) / 7 +
        (32175/4096:ℝ) * (b^8-a^8) / 8 +
        (-1452025575/4194304:ℝ) * (b^9-a^9) / 9 +
        (6578290719/16777216:ℝ) * (b^11-a^11) / 11 +
        (-2029052025/8388608:ℝ) * (b^13-a^13) / 13 +
        (1035230625/16777216:ℝ) * (b^15-a^15) / 15 := by
  have he (x : ℝ) : (1-t3_q7.eval x)^2 =
      (1/4:ℝ) +
        (-11025/4096:ℝ) * x^1 +
        (121550625/16777216:ℝ) * x^2 +
        (40425/4096:ℝ) * x^3 +
        (-445685625/8388608:ℝ) * x^4 +
        (-63063/4096:ℝ) * x^5 +
        (3024719775/16777216:ℝ) * x^6 +
        (32175/4096:ℝ) * x^7 +
        (-1452025575/4194304:ℝ) * x^8 +
        (6578290719/16777216:ℝ) * x^10 +
        (-2029052025/8388608:ℝ) * x^12 +
        (1035230625/16777216:ℝ) * x^14 := by
    simp only [t3_q7, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    ring
  simp_rw [he]
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, integral_pow, integral_id, smul_eq_mul]
  ring

private theorem t3_variances : residualVariance uniformMargins 1 = 1/16 ∧
    residualVariance uniformMargins 7 = 1225/65536 := by
  constructor
  · rw [t3_variance_half, t3_chosen1, t3_square_integral1]; norm_num
  · rw [t3_variance_half, t3_chosen7, t3_square_integral7]; norm_num

private theorem t3_tails :
    expectation uniformMargins (fun x => if 1/2 ≤ |x| then popResidual uniformMargins 1 x^2 else 0) = 1/128 ∧
    expectation uniformMargins (fun x => if 1/2 ≤ |x| then popResidual uniformMargins 7 x^2 else 0) = 572158921/549755813888 := by
  constructor
  · rw [t3_tail_half, t3_chosen1, t3_square_integral1]; norm_num
  · rw [t3_tail_half, t3_chosen7, t3_square_integral7]; norm_num

private theorem t3_exact_coefficient (J : ℕ) (c : Fin (J+2) → ℝ) :
    populationCoefficient uniformMargins J
      (predict (polynomialDesign J (fun x : ℝ => x) party) c) = c 1 := by
  have hm := t3_column_fit_integrable J c
  have hc : PopNormal uniformMargins J (predict (polynomialDesign J (fun x : ℝ => x) party) c) c := by
    intro j
    simp [expectation]
  have hs := Classical.epsilon_spec (t3_normal_exists J _ hm)
  rw [populationCoefficient, t3_normal_unique J _ hm _ c hs hc]
  congr 1

private theorem t3_mean_coefficients :
    populationCoefficient uniformMargins 1 (fun x => 1/2 + (1/10)*party x + x/20) = 1/10 ∧
    populationCoefficient uniformMargins 7 (fun x => 1/2 + (1/10)*party x + x/20+x^7/100) = 1/10 := by
  constructor
  · have he : (fun x : ℝ => 1/2 + (1/10)*party x + x/20) =
        predict (polynomialDesign 1 (fun x : ℝ => x) party) ![1/2,1/10,1/20] := by
      funext x
      norm_num [predict, polynomialDesign, Fin.sum_univ_succ]
      ring
    rw [he, t3_exact_coefficient]
    rfl
  · have he : (fun x : ℝ => 1/2 + (1/10)*party x + x/20+x^7/100) =
        predict (polynomialDesign 7 (fun x : ℝ => x) party) ![1/2,1/10,1/20,0,0,0,0,0,1/100] := by
      funext x
      norm_num [predict, polynomialDesign, Fin.sum_univ_succ]
      ring
    rw [he, t3_exact_coefficient]
    rfl

private theorem t3_rd_halves (m fm fp : ℝ → ℝ) (k : ℝ) (hk : 0 < k) (hk1 : k ≤ 1)
    (hem : ∀ x ∈ Ioo (-k) 0, m x = fm x)
    (hep : ∀ x ∈ Ioo 0 k, m x = fp x) :
    populationRD uniformMargins m k =
      (∫ x in (0 : ℝ)..k, fp x) / k - (∫ x in (-k)..(0 : ℝ), fm x) / k := by
  have hp : Ioc (0 : ℝ) k ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx; exact ⟨by linarith [hx.1], hx.2.trans hk1⟩
  have hm : Ioo (-k) (0 : ℝ) ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx; constructor <;> linarith [hx.1, hx.2]
  have hips : (∫ x in Ioc 0 k, m x ∂uniformMargins) = (1/2 : ℝ) * ∫ x in (0 : ℝ)..k, fp x := by
    rw [uniformMargins, Measure.restrict_smul, integral_smul_measure,
      Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hp,
      ← intervalIntegral.integral_of_le hk.le]
    norm_num only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr_uIoo
    rwa [uIoo_of_le hk.le]
  have hims : (∫ x in Ioo (-k) 0, m x ∂uniformMargins) = (1/2 : ℝ) * ∫ x in (-k)..(0 : ℝ), fm x := by
    rw [uniformMargins, Measure.restrict_smul, integral_smul_measure,
      Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hm,
      ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith : -k ≤ 0)]
    norm_num only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr_uIoo
    rwa [uIoo_of_le (by linarith : -k ≤ 0)]
  unfold populationRD
  rw [hips, hims, (GP023B1b_uniform_window k hk hk1).1, (GP023B1b_uniform_window k hk hk1).2]
  ring

private theorem t3_windows (k : ℝ) (hk : 0 < k) (hk1 : k ≤ 1) :
    populationRD uniformMargins (fun x => 1/2 + (1/10)*party x + x/20) k = 1/10+k/20 ∧
    populationRD uniformMargins (fun x => 1/2 + (1/10)*party x + x/20+x^7/100) k = 1/10+k/20+k^7/400 := by
  constructor
  · rw [t3_rd_halves _ (fun x => 1/2+x/20) (fun x => 3/5+x/20) k hk hk1
      (fun x hx => by simp [party, not_le.mpr hx.2])
      (fun x hx => by simp [party, hx.1.le]; ring)]
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [intervalIntegral.integral_add, intervalIntegral.integral_div,
        intervalIntegral.integral_const, integral_id, smul_eq_mul]
    field_simp [hk.ne']
    <;> ring
  · rw [t3_rd_halves _ (fun x => 1/2+x/20+x^7/100) (fun x => 3/5+x/20+x^7/100) k hk hk1
      (fun x hx => by simp [party, not_le.mpr hx.2])
      (fun x hx => by simp [party, hx.1.le]; ring)]
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [intervalIntegral.integral_add, intervalIntegral.integral_div,
        intervalIntegral.integral_const, integral_id, integral_pow, smul_eq_mul]
    field_simp [hk.ne']
    <;> ring

theorem uniform_common_target_distant_information_proof :
    (∀ x, (projection uniformMargins 1).eval x = projection1 x) ∧
    (∀ x, (projection uniformMargins 7).eval x = projection7 x) ∧
    residualVariance uniformMargins 1 = 1/16 ∧ residualVariance uniformMargins 7 = 1225/65536 ∧
    popResidual uniformMargins 1 (9/10) / residualVariance uniformMargins 1 = -14/5 ∧
    popResidual uniformMargins 7 (9/10) / residualVariance uniformMargins 7 = -20283449/6125000 ∧
    expectation uniformMargins (fun x => if 1/2 ≤ |x| then popResidual uniformMargins 1 x^2 else 0) /
      residualVariance uniformMargins 1 = 1/8 ∧
    expectation uniformMargins (fun x => if 1/2 ≤ |x| then popResidual uniformMargins 7 x^2 else 0) /
      residualVariance uniformMargins 7 = 572158921/10276044800 ∧
    populationCoefficient uniformMargins 1 (fun x => 1/2 + (1/10)*party x + x/20) = 1/10 ∧
    populationCoefficient uniformMargins 7 (fun x => 1/2 + (1/10)*party x + x/20+x^7/100) = 1/10 ∧
    (∀ k, 0 < k → k ≤ 1 →
      populationRD uniformMargins (fun x => 1/2 + (1/10)*party x + x/20) k = 1/10+k/20 ∧
      populationRD uniformMargins (fun x => 1/2 + (1/10)*party x + x/20+x^7/100) k = 1/10+k/20+k^7/400) ∧
    Tendsto (populationRD uniformMargins (fun x => 1/2 + (1/10)*party x+x/20)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1/10)) ∧
    Tendsto (populationRD uniformMargins (fun x => 1/2 + (1/10)*party x+x/20+x^7/100)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1/10)) := by
  have h1 (x : ℝ) : (projection uniformMargins 1).eval x = projection1 x := by
    rw [t3_chosen1]
    simp [t3_q1, projection1]
  have h7 (x : ℝ) : (projection uniformMargins 7).eval x = projection7 x := by
    rw [t3_chosen7]
    simp [t3_q7, projection7]
    ring
  have lim1 : Tendsto (populationRD uniformMargins (fun x => 1/2+(1/10)*party x+x/20))
      (nhdsWithin 0 (Ioi 0)) (nhds (1/10)) := by
    have hp : Tendsto (fun k : ℝ => 1/10+k/20) (nhdsWithin 0 (Ioi 0)) (nhds (1/10)) := by
      have hc : Continuous (fun k : ℝ => 1/10+k/20) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    apply hp.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
    exact (t3_windows k hk.1 hk.2.le).1.symm
  have lim7 : Tendsto (populationRD uniformMargins (fun x => 1/2+(1/10)*party x+x/20+x^7/100))
      (nhdsWithin 0 (Ioi 0)) (nhds (1/10)) := by
    have hp : Tendsto (fun k : ℝ => 1/10+k/20+k^7/400) (nhdsWithin 0 (Ioi 0)) (nhds (1/10)) := by
      have hc : Continuous (fun k : ℝ => 1/10+k/20+k^7/400) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    apply hp.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
    exact (t3_windows k hk.1 hk.2.le).2.symm
  refine ⟨h1, h7, t3_variances.1, t3_variances.2, ?_, ?_, ?_, ?_,
    t3_mean_coefficients.1, t3_mean_coefficients.2, t3_windows, lim1, lim7⟩
  · norm_num [popResidual, h1, projection1, party, t3_variances.1]
  · norm_num [popResidual, h7, projection7, party, t3_variances.2]
  · rw [t3_tails.1, t3_variances.1]; norm_num
  · rw [t3_tails.2, t3_variances.2]; norm_num

/-! Population FWL, the supported witness, and sigmoid integration. -/
private def t4_span (J : ℕ) : Fin (J+2) → ℝ :=
  fun j => (if j = 1 then 1 else 0) -
    liftSmooth J (fun i => (projection uniformMargins J).coeff i) j

private theorem t4_span_predict (J : ℕ) (x : ℝ) :
    predict (polynomialDesign J (fun x : ℝ => x) party) (t4_span J) x =
      popResidual uniformMargins J x := by
  have ht : predict (polynomialDesign J (fun x : ℝ => x) party)
      (fun j => if j = 1 then 1 else 0) x = party x := by
    simp [predict, mul_ite, polynomialDesign]
  simp only [t4_span, predict, mul_sub, Finset.sum_sub_distrib]
  change predict (polynomialDesign J (fun x : ℝ => x) party) (fun j => if j=1 then 1 else 0) x -
    predict (polynomialDesign J (fun x : ℝ => x) party)
      (liftSmooth J (fun i => (projection uniformMargins J).coeff i)) x = _
  have hlift : predict (polynomialDesign J (fun x : ℝ => x) party)
      (liftSmooth J (fun i => (projection uniformMargins J).coeff i)) x =
      ∑ i : Fin (J+1), x^(i:ℕ) * (projection uniformMargins J).coeff i := by
    simp [predict, polynomialDesign, liftSmooth, Fin.sum_univ_succ]
  rw [ht, hlift]
  rw [show (∑ i : Fin (J+1), x ^ (i:ℕ) * (projection uniformMargins J).coeff i) =
      (projection uniformMargins J).eval x by
    rw [t3_eval_expansion _ J (t3_chosen_spec J).1]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rfl

private theorem t4_variance_pos (J : ℕ) : 0 < residualVariance uniformMargins J := by
  have hn : t4_span J ≠ 0 := by
    intro h
    have he := congrFun h 1
    norm_num [t4_span, liftSmooth] at he
  have h := t3_moment_pos J (t4_span J) hn
  simpa only [t4_span_predict, residualVariance] using h

private theorem t4_rmul_integrable (J : ℕ) (m : ℝ → ℝ)
    (hm : ∀ j : Fin (J+2), Integrable (fun x =>
      polynomialDesign J (fun x : ℝ => x) party x j * m x) uniformMargins) :
    Integrable (fun x => popResidual uniformMargins J x * m x) uniformMargins := by
  simp_rw [← t4_span_predict, predict, Finset.sum_mul]
  exact integrable_finsetSum _ (fun j _ => by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hm j).const_mul (t4_span J j))

private theorem t4_rmul_sum (J : ℕ) (m : ℝ → ℝ)
    (hm : ∀ j : Fin (J+2), Integrable (fun x =>
      polynomialDesign J (fun x : ℝ => x) party x j * m x) uniformMargins) :
    expectation uniformMargins (fun x => popResidual uniformMargins J x * m x) =
      ∑ j, t4_span J j * expectation uniformMargins
        (fun x => polynomialDesign J (fun x : ℝ => x) party x j * m x) := by
  simp_rw [← t4_span_predict, predict, Finset.sum_mul]
  unfold expectation
  rw [integral_finsetSum _ (fun j _ => by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hm j).const_mul (t4_span J j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (fun x => polynomialDesign J (fun x : ℝ => x) party x j * t4_span J j * m x) =
    (fun x => t4_span J j * (polynomialDesign J (fun x : ℝ => x) party x j * m x)) by funext x; ring,
    integral_const_mul]

private theorem t4_rparty_integrable (J : ℕ) :
    Integrable (fun x => popResidual uniformMargins J x * party x) uniformMargins := by
  convert t3_piecewise_integrable (1-projection uniformMargins J) 0 using 1
  funext x
  by_cases hx : 0 ≤ x <;> simp [popResidual, party, hx]

private theorem t4_rparty (J : ℕ) :
    expectation uniformMargins (fun x => popResidual uniformMargins J x * party x) =
      residualVariance uniformMargins J := by
  have hq := t3_test J _ _ (t3_chosen_spec J) (t3_chosen_spec J).1
  have he (x : ℝ) : popResidual uniformMargins J x ^ 2 =
      popResidual uniformMargins J x * party x -
        popResidual uniformMargins J x * (projection uniformMargins J).eval x := by
    unfold popResidual
    ring
  unfold residualVariance expectation
  simp_rw [he]
  have hri : Integrable (fun x => popResidual uniformMargins J x * (projection uniformMargins J).eval x) uniformMargins := by
    simpa only [popResidual] using t3_residual_mul_integrable (projection uniformMargins J) (projection uniformMargins J)
  rw [integral_sub (t4_rparty_integrable J) hri]
  change _ = _ - expectation uniformMargins _
  change expectation uniformMargins (fun x => popResidual uniformMargins J x * (projection uniformMargins J).eval x) = 0 at hq
  rw [hq, sub_zero]

private theorem t4_rcolumn (J : ℕ) (j : Fin (J+2)) :
    expectation uniformMargins (fun x => popResidual uniformMargins J x *
      polynomialDesign J (fun x : ℝ => x) party x j) =
      if j = 1 then residualVariance uniformMargins J else 0 := by
  by_cases h0 : j.val = 0
  · have hn : j ≠ 1 := by intro h; simp [h] at h0
    have h := (t3_chosen_spec J).2 0 (Nat.zero_le J)
    simpa [polynomialDesign, h0, hn, pow_zero, popResidual] using h
  · by_cases h1 : j.val = 1
    · have hj : j = 1 := Fin.ext h1
      simpa [polynomialDesign, h0, h1, hj] using t4_rparty J
    · have hn : j ≠ 1 := by intro h; simp [h] at h1
      simpa [polynomialDesign, h0, h1, hn, popResidual] using
        (t3_chosen_spec J).2 (j.val-1) (by omega)

private theorem t4_fwl (J : ℕ) (m : ℝ → ℝ)
    (hm : ∀ j : Fin (J+2), Integrable (fun x =>
      polynomialDesign J (fun x : ℝ => x) party x j * m x) uniformMargins) :
    populationCoefficient uniformMargins J m =
      expectation uniformMargins (fun x => popResidual uniformMargins J x * m x) /
        residualVariance uniformMargins J := by
  let c := Classical.epsilon (PopNormal uniformMargins J m)
  have hc : PopNormal uniformMargins J m c := Classical.epsilon_spec (t3_normal_exists J m hm)
  have hs : expectation uniformMargins (fun x => popResidual uniformMargins J x *
      (m x-predict (polynomialDesign J (fun x : ℝ => x) party) c x)) = 0 := by
    rw [t4_rmul_sum J _ (fun j => by
      convert (hm j).sub (t3_column_fit_integrable J c j) using 1
      funext x
      dsimp only [Pi.sub_apply]
      ring)]
    apply Finset.sum_eq_zero
    intro j _
    rw [hc j, mul_zero]
  have hi (j : Fin (J+2)) : Integrable (fun x => popResidual uniformMargins J x *
      polynomialDesign J (fun x : ℝ => x) party x j) uniformMargins := by
    have h := t3_column_fit_integrable J (t4_span J) j
    simpa only [t4_span_predict, mul_comm] using h
  have hp : expectation uniformMargins (fun x => popResidual uniformMargins J x *
      predict (polynomialDesign J (fun x : ℝ => x) party) c x) = c 1 * residualVariance uniformMargins J := by
    unfold predict expectation
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [integral_finsetSum _ (fun j _ => (hi j).mul_const (c j))]
    simp_rw [integral_mul_const]
    change (∑ j, expectation uniformMargins (fun x => popResidual uniformMargins J x *
      polynomialDesign J (fun x : ℝ => x) party x j) * c j) = _
    simp_rw [t4_rcolumn]
    simp [mul_comm]
  unfold expectation at hs
  simp_rw [mul_sub] at hs
  rw [integral_sub (t4_rmul_integrable J m hm)
    (t4_rmul_integrable J _ (t3_column_fit_integrable J c))] at hs
  change expectation uniformMargins _ - expectation uniformMargins _ = 0 at hs
  rw [hp] at hs
  change c 1 = _
  exact (eq_div_iff (t4_variance_pos J).ne').mpr (by linarith)

private theorem t4_sigmoid_response_integrable (J : ℕ) (a η : ℝ) (ha : 0 ≤ a)
    (j : Fin (J+2)) : Integrable (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
      (1/2+sigmoid a η x)) uniformMargins := by
  apply GP023B1b_supported_integrable _ uniform_law_normalized.1 uniform_law_normalized.2
    ((GP023B1b_column_measurable J j).mul (measurable_const.add (GP023B1b_continuous a η).measurable)) (1/2+a)
  intro x hx
  change |polynomialDesign J (fun x : ℝ => x) party x j * (1/2+sigmoid a η x)| ≤ _
  rw [abs_mul]
  have hb : |(1/2:ℝ)+sigmoid a η x| ≤ 1/2+a := by
    calc
      _ ≤ |(1/2:ℝ)|+|sigmoid a η x| := abs_add_le _ _
      _ ≤ _ := by norm_num; exact GP023B1b_abs_le a η x ha
  exact (mul_le_mul_of_nonneg_right (GP023B1b_column_bound J j x hx) (abs_nonneg _)).trans
    (by simpa using hb)

private theorem t4_numerator_half (J : ℕ) (a η : ℝ) :
    expectation uniformMargins (fun x => popResidual uniformMargins J x * (1/2+sigmoid a η x)) =
      ∫ x in (0 : ℝ)..1, (1-(projection uniformMargins J).eval x) * sigmoid a η x := by
  let R : ℝ → ℝ := fun x => 1-(projection uniformMargins J).eval x
  have hR : Continuous R := continuous_const.sub (projection uniformMargins J).continuous
  have hsig := GP023B1b_continuous a η
  rw [GP023B1b_uniform_halves (fm := fun x => -R (-x)*(1/2+sigmoid a η x))
    (fp := fun x => R x*(1/2+sigmoid a η x))
    (by fun_prop) (by fun_prop)
    (fun x hx => by
      rw [popResidual, party, if_neg (not_le.mpr hx.2)]
      dsimp [R]
      rw [t3_reflection]
      ring)
    (fun x hx => by simp [popResidual, party, hx.1.le, R])]
  have he : (∫ x in (-1 : ℝ)..0, -R (-x)*(1/2+sigmoid a η x)) =
      ∫ x in (0 : ℝ)..1, -R x*(1/2-sigmoid a η x) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun x => -R (-x)*(1/2+sigmoid a η x)) (a := (0:ℝ)) (b := 1)
    simp only [neg_zero, neg_neg, GP023B1b_sigmoid_odd, ← sub_eq_add_neg] at h
    exact h.symm
  rw [he, ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp [R]
  ring

private theorem t4_R_integral (J : ℕ) :
    (∫ x in (0 : ℝ)..1, 1-(projection uniformMargins J).eval x) = 2 * residualVariance uniformMargins J := by
  have h := t4_rparty J
  rw [GP023B1b_uniform_halves (fm := fun _ => 0)
    (fp := fun x => 1-(projection uniformMargins J).eval x)
    continuous_const (continuous_const.sub (projection uniformMargins J).continuous)
    (fun x hx => by simp [party, popResidual, not_le.mpr hx.2])
    (fun x hx => by simp [party, popResidual, hx.1.le]), intervalIntegral.integral_zero] at h
  linarith

private theorem t4_correction (a η : ℝ) (ha : 0 ≤ a) (hη : 0 < η ∧ η ≤ 1) (J : ℕ) :
    populationCoefficient uniformMargins J (fun x => 1/2+sigmoid a η x) =
      2*a - (a / residualVariance uniformMargins J) *
        (∫ x in Icc 0 η, popResidual uniformMargins J x * (1-x/η)) := by
  let R : ℝ → ℝ := fun x => 1-(projection uniformMargins J).eval x
  have hR : Continuous R := continuous_const.sub (projection uniformMargins J).continuous
  have hsig := GP023B1b_continuous a η
  have hprod : Continuous (fun x => R x*sigmoid a η x) := by fun_prop
  have hi : (∫ x in Icc 0 η, popResidual uniformMargins J x * (1-x/η)) =
      ∫ x in (0 : ℝ)..η, R x*(1-x/η) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hη.1.le]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hη.1.le] at hx
    simp [popResidual, party, hx.1, R]
  rw [t4_fwl J _ (t4_sigmoid_response_integrable J a η ha), t4_numerator_half, hi]
  change (∫ x in (0:ℝ)..1, R x*sigmoid a η x) / _ = _
  have hn : (∫ x in (0:ℝ)..1, R x*sigmoid a η x) =
      a*(∫ x in (0:ℝ)..1, R x) - a*(∫ x in (0:ℝ)..η, R x*(1-x/η)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hprod.intervalIntegrable 0 η)
      (hprod.intervalIntegrable η 1),
      ← intervalIntegral.integral_add_adjacent_intervals (hR.intervalIntegrable 0 η) (hR.intervalIntegrable η 1)]
    have hnear : (∫ x in (0:ℝ)..η, R x*sigmoid a η x) =
        a*(∫ x in (0:ℝ)..η, R x) - a*(∫ x in (0:ℝ)..η, R x*(1-x/η)) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop)]
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [uIcc_of_le hη.1.le] at hx
      rw [GP023B1b_positive_clip a η x hη.1 hx.1,
        min_eq_right ((div_le_one hη.1).mpr hx.2)]
      ring
    have hfar : (∫ x in η..(1:ℝ), R x*sigmoid a η x) = a*(∫ x in η..(1:ℝ), R x) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [uIcc_of_le hη.2] at hx
      rw [GP023B1b_positive_clip a η x hη.1 (hη.1.le.trans hx.1),
        min_eq_left ((one_le_div hη.1).mpr hx.1)]
      ring
    rw [hnear, hfar]
    ring
  rw [hn, t4_R_integral]
  field_simp [(t4_variance_pos J).ne']
  <;> ring

private theorem t4_tent_monomial (n : ℕ) (η : ℝ) (hη : 0 < η) :
    (∫ x in (0:ℝ)..η, x^n*(1-x/η)) =
      η^(n+1)/(((n:ℝ)+1)*((n:ℝ)+2)) := by
  have he (x : ℝ) : x^n*(1-x/η) = x^n-x^(n+1)/η := by rw [pow_succ]; ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_div, integral_pow, integral_pow]
  simp only [zero_pow (by omega : n+1 ≠ 0), zero_pow (by omega : n+1+1 ≠ 0), sub_zero,
    Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  field_simp [hη.ne', ne_of_gt (show (0:ℝ) < (n:ℝ)+1 by positivity),
    ne_of_gt (show (0:ℝ) < (n:ℝ)+1+1 by positivity)]
  <;> ring

private theorem t4_tent_poly (p : Polynomial ℝ) (J : ℕ) (hp : p.natDegree ≤ J)
    (η : ℝ) (hη : 0 < η) :
    (∫ x in (0:ℝ)..η, p.eval x*(1-x/η)) =
      ∑ j : Fin (J+1), p.coeff j * η^((j:ℕ)+1) / (((j:ℝ)+1)*((j:ℝ)+2)) := by
  simp_rw [t3_eval_expansion p J hp, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun j _ => by apply Continuous.intervalIntegrable; fun_prop)]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, t4_tent_monomial j η hη]
  ring

private theorem t4_tent_residual (J : ℕ) (η : ℝ) (hη : 0 < η) :
    (∫ x in Icc 0 η, popResidual uniformMargins J x*(1-x/η)) =
      ∑ j : Fin (J+1), (1-projection uniformMargins J).coeff j * η^((j:ℕ)+1) /
        (((j:ℝ)+1)*((j:ℝ)+2)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hη.le]
  have he : (∫ x in (0:ℝ)..η, popResidual uniformMargins J x*(1-x/η)) =
      ∫ x in (0:ℝ)..η, (1-projection uniformMargins J).eval x*(1-x/η) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hη.le] at hx
    simp [popResidual, party, hx.1]
  rw [he]
  exact t4_tent_poly _ J ((Polynomial.natDegree_sub_le _ _).trans
    (max_le (by simp) (t3_chosen_spec J).1)) η hη

private theorem t4_degree1 (a η : ℝ) (ha : 0 ≤ a) (hη : 0 < η ∧ η ≤ 1) :
    populationCoefficient uniformMargins 1 (fun x => 1/2+sigmoid a η x) = 2*a*(1-η)^2 := by
  rw [t4_correction a η ha hη 1, t4_tent_residual 1 η hη.1, t3_chosen1, t3_variances.1]
  norm_num [t3_q1, Fin.sum_univ_succ, Polynomial.coeff_sub, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
  ring

private theorem t4_family_limit (J : ℕ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun η => populationCoefficient uniformMargins J (fun x => 1/2+sigmoid a η x))
      (nhdsWithin 0 (Ioi 0)) (nhds (2*a)) := by
  let f : ℝ → ℝ := fun η => 2*a - (a/residualVariance uniformMargins J) *
    ∑ j : Fin (J+1), (1-projection uniformMargins J).coeff j * η^((j:ℕ)+1) /
      (((j:ℝ)+1)*((j:ℝ)+2))
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hf : f 0 = 2*a := by simp [f]
  rw [← hf]
  apply ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with η hη
  rw [t4_correction a η ha.le ⟨hη.1,hη.2.le⟩ J, t4_tent_residual J η hη.1]

private theorem t4_lipschitz (a η : ℝ) (ha : 0 < a) (hη : 0 < η) (x y : ℝ) :
    |sigmoid a η x - sigmoid a η y| ≤ (a/η)*|x-y| := by
  have hc := (((LipschitzWith.id (α := ℝ)).const_min (1:ℝ)).const_max (-1:ℝ)).dist_le_mul (x/η) (y/η)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc
  rw [sigmoid, sigmoid, ← mul_sub, abs_mul, abs_of_pos ha]
  calc
    _ ≤ a*|x/η-y/η| := mul_le_mul_of_nonneg_left hc ha.le
    _ = _ := by rw [← sub_div, abs_div, abs_of_pos hη]; ring

/-- Split the supported two-point noise law first. The witness map is
measurable; its coordinates are bounded on [-1,1] × {-1/10,1/10}, a set
of full source measure. These branch integrability checks also cover every
bounded measurable test and do not assert a global bound on the witness map. -/
private theorem t4_conditional_mean (a η : ℝ) :
    ConditionalMean (witnessLaw uniformMargins (sigmoid a η)) (fun x => 1/2+sigmoid a η x) := by
  letI instProbabilityConditionalT4 : IsProbabilityMeasure uniformMargins := ⟨uniform_law_normalized.1⟩
  have hm := (GP023B1b_continuous a η).measurable
  have hbase : Integrable (fun x => 1/2+sigmoid a η x) uniformMargins :=
    (continuous_const.add (GP023B1b_continuous a η)).integrableOn_Icc.smul_measure (by norm_num)
  have hy : Integrable (fun z : ℝ×ℝ => z.2) (witnessLaw uniformMargins (sigmoid a η)) := by
    apply (GP023B1b_integrable_witness_iff _ hm measurable_snd).mpr
    exact ⟨hbase.add (integrable_const _), hbase.add (integrable_const _)⟩
  have hmean : Measurable (fun z : ℝ×ℝ => (1/2:ℝ)+sigmoid a η z.1) :=
    measurable_const.add (hm.comp measurable_fst)
  have hmi : Integrable (fun z : ℝ×ℝ => 1/2+sigmoid a η z.1)
      (witnessLaw uniformMargins (sigmoid a η)) := by
    exact (GP023B1b_integrable_witness_iff _ hm hmean).mpr ⟨hbase,hbase⟩
  refine ⟨hy,hmi,?_⟩
  intro t ht hB
  obtain ⟨B,hB⟩ := hB
  have htb : ∀ᵐ z ∂witnessLaw uniformMargins (sigmoid a η), ‖t z.1‖ ≤ B :=
    ae_of_all _ (fun z => by simpa using hB z.1)
  have hts : ∀ᵐ x ∂uniformMargins, ‖t x‖ ≤ B := ae_of_all _ (fun x => by simpa using hB x)
  have hiY := hy.bdd_mul (ht.comp measurable_fst).aestronglyMeasurable htb
  have hiM := hmi.bdd_mul (ht.comp measurable_fst).aestronglyMeasurable htb
  have hit : Integrable t uniformMargins :=
    (integrable_const B).mono' ht.aestronglyMeasurable hts
  have hitm := hbase.bdd_mul ht.aestronglyMeasurable hts
  have hgY : Measurable (fun z : ℝ×ℝ => t z.1*z.2) := (ht.comp measurable_fst).mul measurable_snd
  have hgM : Measurable (fun z : ℝ×ℝ => t z.1*(1/2+sigmoid a η z.1)) := (ht.comp measurable_fst).mul hmean
  change (∫ z, t z.1*z.2 ∂witnessLaw uniformMargins (sigmoid a η)) =
    ∫ z, t z.1*(1/2+sigmoid a η z.1) ∂witnessLaw uniformMargins (sigmoid a η)
  rw [GP023B1b_integral_witness _ hm hgY hiY,
    GP023B1b_integral_witness _ hm hgM hiM]
  have he (u : ℝ) : (∫ x, t x*(1/2+sigmoid a η x+u) ∂uniformMargins) =
      (∫ x, t x*(1/2+sigmoid a η x) ∂uniformMargins) + u*(∫ x, t x ∂uniformMargins) := by
    rw [show (fun x => t x*(1/2+sigmoid a η x+u)) =
        (fun x => t x*(1/2+sigmoid a η x)+t x*u) by funext x; ring]
    rw [integral_add hitm (hit.mul_const u), integral_mul_const]
    ring
  simp only [Prod.fst, Prod.snd]
  rw [he,he]
  ring

private theorem t4_rd (a η k : ℝ) (hη : 0 < η ∧ η ≤ 1) (hk : 0 < k) (hkη : k ≤ η) :
    populationRD uniformMargins (fun x => 1/2+sigmoid a η x) k = a*k/η := by
  have hs (x : ℝ) (hxl : -k < x) (hxu : x < k) : sigmoid a η x = a*x/η := by
    have hl : (-1:ℝ) ≤ x/η := (le_div_iff₀ hη.1).mpr (by linarith)
    have hu : x/η ≤ 1 := (div_le_one hη.1).mpr (by linarith)
    rw [sigmoid, min_eq_right hu, max_eq_right hl]
    ring
  rw [t3_rd_halves _ (fun x => 1/2+a*x/η) (fun x => 1/2+a*x/η) k hk (hkη.trans hη.2)
    (fun x hx => by rw [hs x hx.1 (by linarith [hx.2])])
    (fun x hx => by rw [hs x (by linarith [hx.1]) hx.2])]
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_id, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id, integral_id]
  field_simp [hk.ne', hη.1.ne']
  <;> ring

private theorem t4_rd_limit (a η : ℝ) (hη : 0 < η ∧ η ≤ 1) :
    Tendsto (populationRD uniformMargins (fun x => 1/2+sigmoid a η x))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hc : Continuous (fun k : ℝ => a*k/η) := by fun_prop
  have hl : Tendsto (fun k : ℝ => a*k/η) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply hl.congr'
  filter_upwards [Ioo_mem_nhdsGT hη.1] with k hk
  exact (t4_rd a η k hη hk.1 hk.2.le).symm

private theorem t4_infimum (a η : ℝ) (hη : 0 < η ∧ η ≤ 1) (J : ℕ) :
    0 ≤ sInf {e | ∃ c : Fin (J+2) → ℝ, e = expectation uniformMargins
      (fun x => (1/2+sigmoid a η x-predict (polynomialDesign J (fun x : ℝ => x) party) c x)^2)} ∧
    sInf {e | ∃ c : Fin (J+2) → ℝ, e = expectation uniformMargins
      (fun x => (1/2+sigmoid a η x-predict (polynomialDesign J (fun x : ℝ => x) party) c x)^2)} ≤ a^2*η/3 := by
  let S : Set ℝ := {e | ∃ c : Fin (J+2) → ℝ, e = expectation uniformMargins
    (fun x => (1/2+sigmoid a η x-predict (polynomialDesign J (fun x : ℝ => x) party) c x)^2)}
  have hnonneg : ∀ e ∈ S, 0 ≤ e := by
    rintro e ⟨c,rfl⟩
    exact integral_nonneg (fun x => sq_nonneg _)
  have hmem : a^2*η/3 ∈ S := by
    refine ⟨GP023B1b_feasible J a, ?_⟩
    simp_rw [GP023B1b_feasible_predict]
    convert (GP023B1b_error_integral a η hη).symm using 1
    congr 1
    funext x
    congr 1
    ring
  exact ⟨le_csInf ⟨_,hmem⟩ hnonneg, csInf_le ⟨0,hnonneg⟩ hmem⟩

private theorem t4_outcomes :
    ∀ᵐ z ∂witnessLaw uniformMargins (sigmoid (1/20) (1/10000)), 7/20 ≤ z.2 ∧ z.2 ≤ 13/20 := by
  letI instProbabilityOutcomesT4 : IsProbabilityMeasure uniformMargins := ⟨uniform_law_normalized.1⟩
  have hm := (GP023B1b_continuous (1/20) (1/10000)).measurable
  rw [GP023B1b_witness_split _ hm, ae_add_measure_iff]
  have hs : MeasurableSet {z : ℝ×ℝ | (7/20:ℝ) ≤ z.2 ∧ z.2 ≤ 13/20} := by
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hf (u : ℝ) : Measurable (fun x : ℝ => (x,1/2+sigmoid (1/20) (1/10000) x+u)) :=
    measurable_id.prodMk ((measurable_const.add hm).add measurable_const)
  constructor <;> rw [Measure.ae_ennreal_smul_measure_iff (by norm_num : (1/2:ℝ≥0∞) ≠ 0)]
  all_goals
    rw [ae_map_iff (hf _).aemeasurable hs]
    apply ae_of_all
    intro x
    have hb := abs_le.mp (GP023B1b_abs_le (1/20) (1/10000) x (by norm_num))
    constructor <;> dsimp only <;> linarith [hb.1,hb.2]

theorem sigmoid_counterexample_proof :
    (∀ a η : ℝ, 0 < a → 0 < η → η ≤ 1 →
      Continuous (sigmoid a η) ∧ sigmoid a η 0 = 0 ∧
      (∀ x, sigmoid a η (-x) = -sigmoid a η x) ∧
      (∀ x x', |sigmoid a η x - sigmoid a η x'| ≤ (a / η) * |x - x'|) ∧
      ConditionalMean (witnessLaw uniformMargins (sigmoid a η)) (fun x => 1 / 2 + sigmoid a η x) ∧
      (∀ k, 0 < k → k ≤ η → populationRD uniformMargins (fun x => 1 / 2 + sigmoid a η x) k = a*k/η) ∧
      Tendsto (populationRD uniformMargins (fun x => 1 / 2 + sigmoid a η x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      (∀ J, 1 ≤ J → populationCoefficient uniformMargins J (fun x => 1 / 2 + sigmoid a η x) =
        2*a - (a / residualVariance uniformMargins J) *
          (∫ x in Set.Icc 0 η, popResidual uniformMargins J x * (1 - x/η))) ∧
      populationCoefficient uniformMargins 1 (fun x => 1 / 2 + sigmoid a η x) = 2*a*(1-η)^2 ∧
      expectation uniformMargins (fun x => (sigmoid a η x - a*(2*party x-1))^2) = a^2*η/3 ∧
      (∀ J, 1 ≤ J →
        0 ≤ sInf {e | ∃ c : Fin (J+2) → ℝ, e = expectation uniformMargins
          (fun x => (1 / 2 + sigmoid a η x - predict (polynomialDesign J (fun x : ℝ => x) party) c x)^2)} ∧
        sInf {e | ∃ c : Fin (J+2) → ℝ, e = expectation uniformMargins
          (fun x => (1 / 2 + sigmoid a η x - predict (polynomialDesign J (fun x : ℝ => x) party) c x)^2)} ≤ a^2*η/3)) ∧
    populationCoefficient uniformMargins 1 (fun x => 1 / 2 + sigmoid (1 / 20) (1 / 10000) x) = 99980001 / 1000000000 ∧
    populationCoefficient uniformMargins 7 (fun x => 1 / 2 + sigmoid (1 / 20) (1 / 10000) x) =
      4896723787999993532000048047999857 / 49000000000000000000000000000000000 ∧
    (∀ᵐ z ∂witnessLaw uniformMargins (sigmoid (1 / 20) (1 / 10000)), 7 / 20 ≤ z.2 ∧ z.2 ≤ 13 / 20) ∧
    ((1 / 20 : ℝ)^2 * (1 / 10000) / 3 = 1 / 12000000) ∧
    (∀ J a, 1 ≤ J → 0 < a →
      Tendsto (fun η => populationCoefficient uniformMargins J (fun x => 1 / 2 + sigmoid a η x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (2*a))) := by
  refine ⟨?_, ?_, ?_, t4_outcomes, sigmoid_rational_certificates.2.2, ?_⟩
  · intro a η ha hη hη1
    refine ⟨GP023B1b_continuous a η, ?_, GP023B1b_sigmoid_odd a η,
      t4_lipschitz a η ha hη, t4_conditional_mean a η,
      (fun k hk hkη => t4_rd a η k ⟨hη,hη1⟩ hk hkη),
      t4_rd_limit a η ⟨hη,hη1⟩, ?_, t4_degree1 a η ha.le ⟨hη,hη1⟩,
      GP023B1b_error_integral a η ⟨hη,hη1⟩, ?_⟩
    · simp [sigmoid]
    · intro J _
      exact t4_correction a η ha.le ⟨hη,hη1⟩ J
    · intro J _
      exact t4_infimum a η ⟨hη,hη1⟩ J
  · rw [t4_degree1 _ _ (by norm_num) ⟨by norm_num,by norm_num⟩]
    exact sigmoid_rational_certificates.1
  · rw [GP023B1b_degree7_coefficient _ ⟨by norm_num,by norm_num⟩]
    exact sigmoid_rational_certificates.2.1
  · intro J a _ ha
    exact t4_family_limit J a ha

end
end AronowAudit.P023.Wave1
