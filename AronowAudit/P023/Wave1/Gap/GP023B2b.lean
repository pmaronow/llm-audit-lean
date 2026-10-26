import AronowAudit.P023.P023_Audit
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

/-!
Uniform residual symmetry, explicit residual formulas at degrees one and seven,
and risk bounds for clustered margins.
-/

namespace AronowAudit.P023.Wave1

noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter

local instance GP023B2b_decidable (p : Prop) : Decidable p := Classical.propDecidable p

set_option maxRecDepth 2048

/-! Uniform residual symmetry. -/

private theorem GP023B2b_urs_poly_integrable (p : Polynomial ℝ) :
    Integrable (fun x => p.eval x) uniformMargins := by
  exact p.continuous.integrableOn_Icc.smul_measure (by norm_num)

private theorem GP023B2b_urs_piecewise_integrable (p q : Polynomial ℝ) :
    Integrable (fun x => if 0 ≤ x then p.eval x else q.eval x) uniformMargins := by
  exact Integrable.piecewise measurableSet_Ici
    (GP023B2b_urs_poly_integrable p).integrableOn (GP023B2b_urs_poly_integrable q).integrableOn

private theorem GP023B2b_urs_residual_mul_integrable (p q : Polynomial ℝ) :
    Integrable (fun x => (party x - p.eval x) * q.eval x) uniformMargins := by
  convert GP023B2b_urs_piecewise_integrable ((1 - p) * q) (-p * q) using 1
  funext x
  by_cases hx : 0 ≤ x <;> simp [party, hx] <;> ring

private theorem GP023B2b_urs_poly_mul_integrable (p q : Polynomial ℝ) :
    Integrable (fun x => p.eval x * q.eval x) uniformMargins := by
  simpa only [Polynomial.eval_mul] using GP023B2b_urs_poly_integrable (p * q)

private theorem GP023B2b_urs_poly_power_integrable (p : Polynomial ℝ) (j : ℕ) :
    Integrable (fun x => p.eval x * x ^ j) uniformMargins := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    GP023B2b_urs_poly_mul_integrable p (Polynomial.X ^ j)

private theorem GP023B2b_urs_residual_power_integrable (p : Polynomial ℝ) (j : ℕ) :
    Integrable (fun x => (party x - p.eval x) * x ^ j) uniformMargins := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    GP023B2b_urs_residual_mul_integrable p (Polynomial.X ^ j)

private theorem GP023B2b_urs_eq_interval (f : ℝ → ℝ) :
    expectation uniformMargins f = (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, f x := by
  unfold expectation uniformMargins
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  norm_num

private theorem GP023B2b_urs_reflect_integral (f : ℝ → ℝ) :
    expectation uniformMargins (fun x => f (-x)) = expectation uniformMargins f := by
  rw [GP023B2b_urs_eq_interval, GP023B2b_urs_eq_interval, intervalIntegral.integral_comp_neg]
  norm_num

private theorem GP023B2b_urs_power (j : ℕ) :
    expectation uniformMargins (fun x => x ^ j) =
      (1 / 2 : ℝ) * ((1 : ℝ) ^ (j + 1) - (-1 : ℝ) ^ (j + 1)) / (j + 1) := by
  rw [GP023B2b_urs_eq_interval, integral_pow]
  ring

private theorem GP023B2b_urs_party_power (j : ℕ) :
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

private def GP023B2b_urs_poly (J : ℕ) (a : Fin (J + 1) → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

private theorem GP023B2b_urs_poly_eval (J : ℕ) (a : Fin (J + 1) → ℝ) (x : ℝ) :
    (GP023B2b_urs_poly J a).eval x = ∑ i, a i * x ^ (i : ℕ) := by
  simp [GP023B2b_urs_poly, Polynomial.eval_finset_sum]

private theorem GP023B2b_urs_poly_degree (J : ℕ) (a : Fin (J + 1) → ℝ) :
    (GP023B2b_urs_poly J a).natDegree ≤ J := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

private theorem GP023B2b_urs_poly_coeff (J : ℕ) (a : Fin (J + 1) → ℝ) (i : Fin (J + 1)) :
    (GP023B2b_urs_poly J a).coeff i = a i := by
  classical
  simp [GP023B2b_urs_poly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    ← Fin.ext_iff]

private theorem GP023B2b_urs_eval_expansion (p : Polynomial ℝ) (J : ℕ) (hp : p.natDegree ≤ J)
    (x : ℝ) : p.eval x = ∑ i : Fin (J + 1), p.coeff i * x ^ (i : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (show p.natDegree < J + 1 by omega)]
  exact (Fin.sum_univ_eq_sum_range _ _).symm
  

private theorem GP023B2b_urs_test (J : ℕ) (p q : Polynomial ℝ)
    (hp : IsProjection uniformMargins J p) (hq : q.natDegree ≤ J) :
    expectation uniformMargins (fun x => (party x - p.eval x) * q.eval x) = 0 := by
  classical
  have he : (fun x => (party x - p.eval x) * q.eval x) =
      (fun x => ∑ i : Fin (J + 1), q.coeff i * ((party x - p.eval x) * x ^ (i : ℕ))) := by
    funext x
    rw [GP023B2b_urs_eval_expansion q J hq, Finset.mul_sum]
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
    exact (GP023B2b_urs_residual_power_integrable p i).const_mul _

private theorem GP023B2b_urs_square_zero (p : Polynomial ℝ)
    (hz : expectation uniformMargins (fun x => p.eval x ^ 2) = 0) : p = 0 := by
  have hint : Integrable (fun x => p.eval x ^ 2) uniformMargins := by
    apply (GP023B2b_urs_poly_integrable (p ^ 2)).congr
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

private theorem GP023B2b_urs_unique (J : ℕ) (p q : Polynomial ℝ)
    (hp : IsProjection uniformMargins J p) (hq : IsProjection uniformMargins J q) : p = q := by
  have hdeg : (p - q).natDegree ≤ J :=
    (Polynomial.natDegree_sub_le p q).trans (max_le hp.1 hq.1)
  have h1 := GP023B2b_urs_test J p (p - q) hp hdeg
  have h2 := GP023B2b_urs_test J q (p - q) hq hdeg
  have hs : expectation uniformMargins (fun x => (p - q).eval x ^ 2) = 0 := by
    have he : (fun x => (p - q).eval x ^ 2) =
        (fun x => (party x - q.eval x) * (p - q).eval x -
          (party x - p.eval x) * (p - q).eval x) := by
      funext x
      simp only [Polynomial.eval_sub]
      ring
    unfold expectation at *
    rw [he, integral_sub (GP023B2b_urs_residual_mul_integrable q (p - q))
      (GP023B2b_urs_residual_mul_integrable p (p - q)), h2, h1, sub_self]
  exact sub_eq_zero.mp (GP023B2b_urs_square_zero (p - q) hs)

private theorem GP023B2b_urs_exists_core (μ : Measure ℝ)
    (hpoly : ∀ (p : Polynomial ℝ) (j : ℕ), Integrable (fun x => p.eval x * x ^ j) μ)
    (hparty : ∀ j : ℕ, Integrable (fun x => party x * x ^ j) μ)
    (hzero : ∀ p : Polynomial ℝ, expectation μ (fun x => p.eval x ^ 2) = 0 → p = 0)
    (J : ℕ) : ∃ p, IsProjection μ J p := by
  classical
  let A : (Fin (J + 1) → ℝ) →ₗ[ℝ] (Fin (J + 1) → ℝ) :=
    { toFun := fun a j => expectation μ (fun x => (GP023B2b_urs_poly J a).eval x * x ^ (j : ℕ))
      map_add' := by
        intro a b
        funext j
        have he : (fun x => (GP023B2b_urs_poly J (a + b)).eval x * x ^ (j : ℕ)) =
            (fun x => (GP023B2b_urs_poly J a).eval x * x ^ (j : ℕ) +
              (GP023B2b_urs_poly J b).eval x * x ^ (j : ℕ)) := by
          funext x
          simp [GP023B2b_urs_poly_eval, add_mul, Finset.sum_add_distrib]
        exact (congrArg (expectation μ) he).trans
          (integral_add (hpoly (GP023B2b_urs_poly J a) j)
            (hpoly (GP023B2b_urs_poly J b) j))
      map_smul' := by
        intro r a
        funext j
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        change expectation μ _ = r * expectation μ _
        have he : (fun x => (GP023B2b_urs_poly J (r • a)).eval x * x ^ (j : ℕ)) =
            (fun x => r * ((GP023B2b_urs_poly J a).eval x * x ^ (j : ℕ))) := by
          funext x
          simp only [GP023B2b_urs_poly_eval, Pi.smul_apply, smul_eq_mul]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          ring
        rw [he]
        exact integral_const_mul _ _ }
  have hker : ∀ a, A a = 0 → a = 0 := by
    intro a ha
    have hs : expectation μ (fun x => (GP023B2b_urs_poly J a).eval x ^ 2) = 0 := by
      have he : (fun x => (GP023B2b_urs_poly J a).eval x ^ 2) =
          (fun x => ∑ j : Fin (J + 1), a j * ((GP023B2b_urs_poly J a).eval x * x ^ (j : ℕ))) := by
        funext x
        rw [pow_two, GP023B2b_urs_poly_eval J a x, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      unfold expectation
      rw [he, integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro j _
        rw [integral_const_mul]
        have hj : expectation μ
            (fun x => (GP023B2b_urs_poly J a).eval x * x ^ (j : ℕ)) = 0 := congrFun ha j
        change a j * expectation μ _ = 0
        rw [hj, mul_zero]
      · intro j _
        exact (hpoly (GP023B2b_urs_poly J a) j).const_mul _
    have hz := hzero (GP023B2b_urs_poly J a) hs
    funext i
    have hi := congrArg (fun p : Polynomial ℝ => p.coeff i) hz
    simpa only [GP023B2b_urs_poly_coeff, Polynomial.coeff_zero, Pi.zero_apply] using hi
  have hinj : Function.Injective A := by
    intro a b hab
    have hz := hker (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp hz
  obtain ⟨a, ha⟩ := LinearMap.surjective_of_injective hinj
    (fun j => expectation μ (fun x => party x * x ^ (j : ℕ)))
  refine ⟨GP023B2b_urs_poly J a, GP023B2b_urs_poly_degree J a, ?_⟩
  intro j hj
  have hm := congrFun ha (⟨j, by omega⟩ : Fin (J + 1))
  change expectation μ (fun x => (GP023B2b_urs_poly J a).eval x * x ^ j) =
    expectation μ (fun x => party x * x ^ j) at hm
  unfold expectation at *
  simp_rw [sub_mul]
  rw [integral_sub]
  · exact sub_eq_zero.mpr hm.symm
  · exact hparty j
  · exact hpoly _ j

private theorem GP023B2b_urs_exists (J : ℕ) : ∃ p, IsProjection uniformMargins J p := by
  apply GP023B2b_urs_exists_core uniformMargins GP023B2b_urs_poly_power_integrable _ GP023B2b_urs_square_zero J
  intro j
  simpa using GP023B2b_urs_residual_power_integrable 0 j

private theorem GP023B2b_urs_chosen_spec (J : ℕ) :
    IsProjection uniformMargins J (projection uniformMargins J) :=
  Classical.epsilon_spec (GP023B2b_urs_exists J)

private theorem GP023B2b_urs_party_reflection (x : ℝ) (hx : x ≠ 0) : party (-x) = 1 - party x := by
  rcases lt_or_gt_of_ne hx with h | h
  · simp [party, h.le, not_le.mpr h, (neg_pos.mpr h).le]
  · simp [party, h.le, not_le.mpr (neg_neg_of_pos h)]

private theorem GP023B2b_urs_reflection (J : ℕ) (x : ℝ) :
    (projection uniformMargins J).eval x = 1 - (projection uniformMargins J).eval (-x) := by
  let q := projection uniformMargins J
  let qstar : Polynomial ℝ := 1 - q.comp (-Polynomial.X)
  have hq := GP023B2b_urs_chosen_spec J
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
      have hparty := GP023B2b_urs_party_reflection t ht
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
    rw [GP023B2b_urs_reflect_integral (fun t => (party t - q.eval t) * t ^ j), hq.2 j hj, mul_zero]
  have hsame := GP023B2b_urs_unique J q qstar hq hp
  have := congrArg (fun p : Polynomial ℝ => p.eval x) hsame
  simpa only [qstar, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_comp,
    Polynomial.eval_neg, Polynomial.eval_X] using this

private theorem GP023B2b_urs_normal_formula (J : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ J) (j : ℕ) :
    expectation uniformMargins (fun x => (party x - p.eval x) * x ^ j) =
      1 / (2 * (j + 1)) - ∑ i : Fin (J + 1), p.coeff i *
        ((1 / 2 : ℝ) * (1 - (-1 : ℝ) ^ ((i : ℕ) + j + 1)) / ((i : ℕ) + j + 1)) := by
  have he : (fun x => p.eval x * x ^ j) =
      (fun x => ∑ i : Fin (J + 1), p.coeff i * x ^ ((i : ℕ) + j)) := by
    funext x
    rw [GP023B2b_urs_eval_expansion p J hp, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]
    ring
  unfold expectation
  simp_rw [sub_mul]
  rw [integral_sub]
  · change expectation uniformMargins (fun x => party x * x ^ j) - _ = _
    rw [GP023B2b_urs_party_power, he, integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul]
      change p.coeff i * expectation uniformMargins _ = _
      rw [GP023B2b_urs_power]
      simp only [one_pow, Nat.cast_add]
    · intro i _
      simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
        (GP023B2b_urs_poly_integrable (Polynomial.X ^ ((i : ℕ) + j))).const_mul (p.coeff i)
  · simpa using GP023B2b_urs_residual_power_integrable 0 j
  · exact GP023B2b_urs_poly_power_integrable p j

private def GP023B2b_urs_q1 : Polynomial ℝ := Polynomial.C (1 / 2) + Polynomial.C (3 / 4) * Polynomial.X

private def GP023B2b_urs_q7 : Polynomial ℝ := Polynomial.C (1 / 2) + Polynomial.C (1 / 4096) *
  (Polynomial.C 11025 * Polynomial.X - Polynomial.C 40425 * Polynomial.X ^ 3 +
    Polynomial.C 63063 * Polynomial.X ^ 5 - Polynomial.C 32175 * Polynomial.X ^ 7)

private theorem GP023B2b_urs_q1_spec : IsProjection uniformMargins 1 GP023B2b_urs_q1 := by
  have hd : GP023B2b_urs_q1.natDegree ≤ 1 := by unfold GP023B2b_urs_q1; compute_degree
  refine ⟨hd, ?_⟩
  intro j hj
  interval_cases j <;> rw [GP023B2b_urs_normal_formula 1 GP023B2b_urs_q1 hd] <;>
    norm_num [GP023B2b_urs_q1, Fin.sum_univ_succ, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]

private theorem GP023B2b_urs_q7_spec : IsProjection uniformMargins 7 GP023B2b_urs_q7 := by
  have hd : GP023B2b_urs_q7.natDegree ≤ 7 := by unfold GP023B2b_urs_q7; compute_degree
  refine ⟨hd, ?_⟩
  intro j hj
  interval_cases j <;> rw [GP023B2b_urs_normal_formula 7 GP023B2b_urs_q7 hd] <;>
    norm_num [GP023B2b_urs_q7, Fin.sum_univ_succ, Polynomial.coeff_add,
      Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]

/-- P023-T4: uniform residual symmetry and explicit formulas at degrees one and seven. -/
theorem uniform_residual_symmetry_proof :
    (∀ J, 1 ≤ J → ∀ x, x ≠ 0 → popResidual uniformMargins J (-x) = -popResidual uniformMargins J x) ∧
    (∀ x, 0<x → popResidual uniformMargins 1 x=1/2-(3/4)*x ∧
      popResidual uniformMargins 7 x=1/2-(11025*x-40425*x^3+63063*x^5-32175*x^7)/4096) := by
  constructor
  · intro J _ x hx
    have hp := GP023B2b_urs_party_reflection x hx
    have hq := GP023B2b_urs_reflection J x
    unfold popResidual
    linarith
  · intro x hx
    have h1 := GP023B2b_urs_unique 1 (projection uniformMargins 1) GP023B2b_urs_q1 (GP023B2b_urs_chosen_spec 1) GP023B2b_urs_q1_spec
    have h7 := GP023B2b_urs_unique 7 (projection uniformMargins 7) GP023B2b_urs_q7 (GP023B2b_urs_chosen_spec 7) GP023B2b_urs_q7_spec
    constructor
    · simp only [popResidual, h1, GP023B2b_urs_q1, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X, party, if_pos hx.le]
      ring
    · simp only [popResidual, h7, GP023B2b_urs_q7, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        party, if_pos hx.le]
      ring

/-! Clustered fit bound. -/

private theorem GP023B2b_cfb_positive_bound (d x : ℝ) (hd : 0 < d) :
    |clusterPositive d x| ≤ d / 2 := by
  unfold clusterPositive
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

private theorem GP023B2b_cfb_smooth_bound (d x : ℝ) (hd : 0 < d) :
    |clusterSmooth d x| ≤ d / 2 := by
  unfold clusterSmooth
  split_ifs
  · simpa only [abs_neg] using GP023B2b_cfb_positive_bound d (-x) hd
  · exact GP023B2b_cfb_positive_bound d x hd

private theorem GP023B2b_cfb_smooth_measurable (d : ℝ) : Measurable (clusterSmooth d) := by
  have hp : Measurable (clusterPositive d) := by
    unfold clusterPositive
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_le measurable_id measurable_const)
        ((measurable_const.sub measurable_const).sub measurable_id)
        (Measurable.ite (measurableSet_le measurable_id measurable_const)
          (measurable_id.sub measurable_const)
          (Measurable.ite (measurableSet_le measurable_id measurable_const)
            (measurable_const.sub measurable_id) measurable_const)))
  unfold clusterSmooth
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (hp.comp measurable_neg).neg hp

private theorem GP023B2b_cfb_triangle_continuous (a w : ℝ) : Continuous (triangular a w) := by
  exact ((continuous_const.sub (continuous_id.sub continuous_const).abs).max
    continuous_const).div_const _

private theorem GP023B2b_cfb_triangle_mass (a w : ℝ) (hw : 0 < w)
    (hl : -1 ≤ a - w) (hr : a + w ≤ 1) :
    (∫ x in Icc (-1 : ℝ) 1, triangular a w x) = 1 := by
  have hsub : Icc (a - w) (a + w) ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨hl.trans hx.1, hx.2.trans hr⟩
  have hout : ∀ x ∈ Icc (-1 : ℝ) 1 \ Icc (a - w) (a + w), triangular a w x = 0 := by
    intro x hx
    have he : w ≤ |x - a| := by
      by_cases hh : x < a - w
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · have hh' : a + w < x := by
          by_contra hn
          exact hx.2 ⟨le_of_not_gt hh, le_of_not_gt hn⟩
        rw [abs_of_nonneg (by linarith)]
        linarith
    simp only [triangular, max_eq_right (sub_nonpos.mpr he), zero_div]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub hout,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show a - w ≤ a + w by linarith)]
  have hint (u v : ℝ) : IntervalIntegrable (triangular a w) volume u v :=
    (GP023B2b_cfb_triangle_continuous a w).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (a - w) a) (hint a (a + w))]
  have hleft : (∫ x in (a - w)..a, triangular a w x) =
      (∫ x in (a - w)..a, (w + x - a) / w ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (show a - w ≤ a by linarith)] at hx
    have ha : |x - a| = a - x := by rw [abs_of_nonpos (by linarith [hx.2])]; ring
    rw [triangular, ha, max_eq_left (by linarith [hx.1])]
    ring
  have hright : (∫ x in a..(a + w), triangular a w x) =
      (∫ x in a..(a + w), (w - x + a) / w ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (show a ≤ a + w by linarith)] at hx
    rw [triangular, abs_of_nonneg (by linarith [hx.1]), max_eq_left (by linarith [hx.2])]
    ring
  rw [hleft, hright, intervalIntegral.integral_div, intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_sub]
  all_goals try { exact (continuous_const.add continuous_id).intervalIntegrable _ _ }
  all_goals try { exact (continuous_const.sub continuous_id).intervalIntegrable _ _ }
  all_goals try { exact continuous_const.intervalIntegrable _ _ }
  all_goals try { exact continuous_id.intervalIntegrable _ _ }
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
  field_simp [ne_of_gt hw] <;> ring

private theorem GP023B2b_cfb_density_continuous (d : ℝ) : Continuous (clusterDensity d) :=
  continuous_const.add (continuous_const.mul
    ((GP023B2b_cfb_triangle_continuous _ _).add (GP023B2b_cfb_triangle_continuous _ _)))

private theorem GP023B2b_cfb_density_nonneg (d x : ℝ) (hd : 0 < d ∧ d ≤ 1 / 2) :
    0 ≤ clusterDensity d x := by
  have hs : d ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := (sq_le_sq₀ hd.1.le (by norm_num)).mpr hd.2
  have hs4 := (sq_le_sq₀ (sq_nonneg d) (sq_nonneg (1 / 2 : ℝ))).mpr hs
  have hpow : d ^ 4 ≤ 1 := by nlinarith [hs4]
  have hmix : 0 ≤ 1 - d ^ 4 := sub_nonneg.mpr hpow
  unfold clusterDensity triangular
  positivity

private theorem GP023B2b_cfb_cluster_probability (d : ℝ) (hd : 0 < d ∧ d ≤ 1 / 2) :
    ProbabilityLaw (clusteredMargins d) := by
  have ht1 := GP023B2b_cfb_triangle_mass (1 / 2) (d / 2) (by linarith) (by linarith) (by linarith)
  have ht2 := GP023B2b_cfb_triangle_mass (-1 / 2) (d / 2) (by linarith) (by linarith) (by linarith)
  have hint : IntegrableOn (clusterDensity d) (Icc (-1 : ℝ) 1) volume :=
    (GP023B2b_cfb_density_continuous d).integrableOn_Icc
  have hi1 : IntegrableOn (triangular (1 / 2) (d / 2)) (Icc (-1 : ℝ) 1) volume :=
    (GP023B2b_cfb_triangle_continuous _ _).integrableOn_Icc
  have hi2 : IntegrableOn (triangular (-1 / 2) (d / 2)) (Icc (-1 : ℝ) 1) volume :=
    (GP023B2b_cfb_triangle_continuous _ _).integrableOn_Icc
  have hm : (∫ x in Icc (-1 : ℝ) 1, clusterDensity d x) = 1 := by
    unfold clusterDensity
    have hiadd : IntegrableOn
        (fun x => triangular (1 / 2) (d / 2) x + triangular (-1 / 2) (d / 2) x)
        (Icc (-1 : ℝ) 1) volume := hi1.add hi2
    have himul : IntegrableOn
        (fun x => (1 - d ^ 4) / 2 *
          (triangular (1 / 2) (d / 2) x + triangular (-1 / 2) (d / 2) x))
        (Icc (-1 : ℝ) 1) volume := hiadd.const_mul _
    rw [integral_add (integrable_const _) himul, integral_const_mul,
      integral_add hi1 hi2, ht1, ht2]
    norm_num [Real.volume_Icc, measureReal_def] <;> ring
  unfold ProbabilityLaw clusteredMargins
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun x => GP023B2b_cfb_density_nonneg d x hd)), hm]
  norm_num

private theorem GP023B2b_cfb_witness_eq (μ : Measure ℝ) [SFinite μ] (h : ℝ → ℝ) (hh : Measurable h) :
    witnessLaw μ h =
      (1 / 2 : ℝ≥0∞) • Measure.map (fun x => (x, 1 / 2 + h x - 1 / 10)) μ +
      (1 / 2 : ℝ≥0∞) • Measure.map (fun x => (x, 1 / 2 + h x + 1 / 10)) μ := by
  have hmap : Measurable (fun z : ℝ × ℝ => (z.1, 1 / 2 + h z.1 + z.2)) :=
    measurable_fst.prodMk ((measurable_const.add (hh.comp measurable_fst)).add measurable_snd)
  unfold witnessLaw noiseLaw
  rw [Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_dirac, Measure.prod_dirac, Measure.map_add _ _ hmap,
    Measure.map_smul _ hmap.aemeasurable, Measure.map_smul _ hmap.aemeasurable,
    Measure.map_map hmap (by fun_prop : Measurable (fun x : ℝ => (x, (-1 / 10 : ℝ)))),
    Measure.map_map hmap (by fun_prop : Measurable (fun x : ℝ => (x, (1 / 10 : ℝ))))]
  simp only [Function.comp_def, sub_eq_add_neg, neg_div]

private theorem GP023B2b_cfb_witness_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ℝ → ℝ) (hh : Measurable h) :
    ProbabilityLaw (witnessLaw μ h) ∧ marginLaw (witnessLaw μ h) = μ := by
  have hl : Measurable (fun x => (x, 1 / 2 + h x - 1 / 10)) :=
    measurable_id.prodMk ((measurable_const.add hh).sub measurable_const)
  have hr : Measurable (fun x => (x, 1 / 2 + h x + 1 / 10)) :=
    measurable_id.prodMk ((measurable_const.add hh).add measurable_const)
  rw [GP023B2b_cfb_witness_eq μ h hh]
  constructor
  · simp only [ProbabilityLaw, Measure.add_apply, Measure.smul_apply,
      Measure.map_apply hl MeasurableSet.univ, Measure.map_apply hr MeasurableSet.univ,
      preimage_univ, measure_univ, mul_one]
    simpa only [smul_eq_mul, mul_one, one_div] using ENNReal.inv_two_add_inv_two
  · unfold marginLaw
    rw [Measure.map_add _ _ measurable_fst,
      Measure.map_smul _ measurable_fst.aemeasurable,
      Measure.map_smul _ measurable_fst.aemeasurable,
      Measure.map_map measurable_fst hl, Measure.map_map measurable_fst hr]
    simp only [Function.comp_def, Measure.map_id]
    rw [← add_smul]
    norm_num only [one_div, ENNReal.inv_two_add_inv_two, one_smul]
    exact Measure.map_id

private theorem GP023B2b_cfb_risk_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h f : ℝ → ℝ) (hh : Measurable h) (hf : Measurable f)
    (B : ℝ) (hB : ∀ x, |1 / 2 + h x - f x| ≤ B) :
    Integrable (fun z => (z.2 - f z.1) ^ 2) (witnessLaw μ h) := by
  have hm : Measurable (fun z : ℝ × ℝ => (z.2 - f z.1) ^ 2) :=
    (measurable_snd.sub (hf.comp measurable_fst)).pow_const 2
  rw [GP023B2b_cfb_witness_eq μ h hh, integrable_add_measure]
  constructor
  all_goals
    apply Integrable.smul_measure _ (by norm_num)
    apply (integrable_map_measure hm.aestronglyMeasurable
      (by fun_prop : Measurable _).aemeasurable).mpr
    apply (integrable_const ((B + 1 / 10) ^ 2)).mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    simp only [Function.comp_def, Real.norm_eq_abs, abs_pow, sq_abs]
    have hb := hB x
    have hb0 : 0 ≤ B := (abs_nonneg _).trans hb
    have hsmall : |1 / 2 + h x - f x - 1 / 10| ≤ B + 1 / 10 := by
      calc
        _ ≤ |1 / 2 + h x - f x| + |(1 / 10 : ℝ)| := abs_sub _ _
        _ ≤ B + 1 / 10 := by norm_num <;> linarith
    have hlarge : |1 / 2 + h x - f x + 1 / 10| ≤ B + 1 / 10 := by
      calc
        _ ≤ |1 / 2 + h x - f x| + |(1 / 10 : ℝ)| := abs_add_le _ _
        _ ≤ B + 1 / 10 := by norm_num <;> linarith
    have hs1 := (sq_le_sq₀ (abs_nonneg (1 / 2 + h x - f x - 1 / 10))
      (show 0 ≤ B + 1 / 10 by positivity)).mpr hsmall
    have hs2 := (sq_le_sq₀ (abs_nonneg (1 / 2 + h x - f x + 1 / 10))
      (show 0 ≤ B + 1 / 10 by positivity)).mpr hlarge
    nlinarith [sq_abs (1 / 2 + h x - f x - 1 / 10),
      sq_abs (1 / 2 + h x - f x + 1 / 10)]

private theorem GP023B2b_cfb_risk_formula (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h f : ℝ → ℝ) (hh : Measurable h) (hf : Measurable f)
    (hint : Integrable (fun z => (z.2 - f z.1) ^ 2) (witnessLaw μ h)) :
    predictionRisk (witnessLaw μ h) f =
      1 / 100 + expectation μ (fun x => (1 / 2 + h x - f x) ^ 2) := by
  have hl : Measurable (fun x => (x, 1 / 2 + h x - 1 / 10)) := by fun_prop
  have hr : Measurable (fun x => (x, 1 / 2 + h x + 1 / 10)) := by fun_prop
  have hm : Measurable (fun z : ℝ × ℝ => (z.2 - f z.1) ^ 2) := by fun_prop
  rw [GP023B2b_cfb_witness_eq μ h hh, integrable_add_measure] at hint
  have hil := hint.1
  have hir := hint.2
  have hl' : Integrable (fun x => (1 / 2 + h x - 1 / 10 - f x) ^ 2) μ := by
    apply (integrable_map_measure hm.aestronglyMeasurable hl.aemeasurable).mp
    exact (integrable_smul_measure (by norm_num) (by norm_num)).mp hil
  have hr' : Integrable (fun x => (1 / 2 + h x + 1 / 10 - f x) ^ 2) μ := by
    apply (integrable_map_measure hm.aestronglyMeasurable hr.aemeasurable).mp
    exact (integrable_smul_measure (by norm_num) (by norm_num)).mp hir
  have he (x : ℝ) :
      (1 / 2 : ℝ) * (1 / 2 + h x - 1 / 10 - f x) ^ 2 +
        (1 / 2 : ℝ) * (1 / 2 + h x + 1 / 10 - f x) ^ 2 =
        1 / 100 + (1 / 2 + h x - f x) ^ 2 := by ring
  have hi : Integrable (fun x => (1 / 2 + h x - f x) ^ 2) μ := by
    convert ((hl'.const_mul (1 / 2)).add (hr'.const_mul (1 / 2))).sub
      (integrable_const (1 / 100 : ℝ)) using 1
    funext x
    dsimp only [Pi.sub_apply, Pi.add_apply]
    rw [he]
    ring
  unfold predictionRisk
  rw [GP023B2b_cfb_witness_eq μ h hh, integral_add_measure hil hir,
    integral_smul_measure, integral_smul_measure,
    integral_map hl.aemeasurable hm.aestronglyMeasurable,
    integral_map hr.aemeasurable hm.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hl'.const_mul (1 / 2)) (hr'.const_mul (1 / 2))]
  simp_rw [he]
  rw [integral_add (integrable_const _) hi]
  simp [expectation]

private theorem GP023B2b_cfb_constant_predictor (J : ℕ) :
    ∃ a : Fin (J + 2) → ℝ,
      predict (polynomialDesign J (fun x : ℝ => x) party) a = (fun _ => 1 / 2) := by
  classical
  refine ⟨fun j => if (j : ℕ) = 0 then 1 / 2 else 0, ?_⟩
  funext x
  unfold predict
  rw [Finset.sum_eq_single (0 : Fin (J + 2))]
  · norm_num [polynomialDesign]
  · intro j _ hj
    have hv : (j : ℕ) ≠ 0 := fun hv => hj (Fin.ext hv)
    simp only [hv, if_false, mul_zero]
  · simp

private theorem GP023B2b_cfb_fitted_le_constant (ν : Measure (ℝ × ℝ)) (J : ℕ) :
    fittedRisk ν J ≤ predictionRisk ν (fun _ => 1 / 2) := by
  have hb : BddBelow {e | ∃ a : Fin (J + 2) → ℝ,
      e = predictionRisk ν (predict (polynomialDesign J (fun x : ℝ => x) party) a)} := by
    refine ⟨0, ?_⟩
    rintro e ⟨a, rfl⟩
    exact integral_nonneg (fun z => sq_nonneg _)
  obtain ⟨a, ha⟩ := GP023B2b_cfb_constant_predictor J
  exact csInf_le hb ⟨a, by rw [ha]⟩

/-- P023-T5(vi): bounds on risk improvement for clustered margins. -/
theorem clustered_fit_bound_proof (d : ℝ) (hd : 0 < d ∧ d ≤ 1/2) :
    let ν := witnessLaw (clusteredMargins d) (clusterSmooth d)
    ProbabilityLaw ν ∧ marginLaw ν = clusteredMargins d ∧
    predictionRisk ν (fun x => 1/2+clusterSmooth d x) = 1/100 ∧
    predictionRisk ν (fun _ => 1/2) = 1/100+expectation (clusteredMargins d) (fun x => clusterSmooth d x^2) ∧
    (∀ f : ℝ → ℝ, Measurable f → Integrable (fun z => (z.2-f z.1)^2) ν →
      predictionRisk ν (fun _ => 1/2)-predictionRisk ν f ≤ (d/2)^2) ∧
    (∀ J, 1 ≤ J → fittedRisk ν J ≤ predictionRisk ν (fun _ => 1/2) ∧
      (∀ f : ℝ → ℝ, Measurable f → Integrable (fun z => (z.2-f z.1)^2) ν →
        fittedRisk ν J-predictionRisk ν f ≤ (d/2)^2)) := by
  let μ := clusteredMargins d
  let ν := witnessLaw μ (clusterSmooth d)
  have hprob : ProbabilityLaw μ := GP023B2b_cfb_cluster_probability d hd
  letI : IsProbabilityMeasure μ := ⟨hprob⟩
  have hm := GP023B2b_cfb_smooth_measurable d
  have hwitness := GP023B2b_cfb_witness_probability μ (clusterSmooth d) hm
  have hmean : Measurable (fun x => 1 / 2 + clusterSmooth d x) := measurable_const.add hm
  have hmi : Integrable (fun z => (z.2 - (1 / 2 + clusterSmooth d z.1)) ^ 2) ν := by
    exact GP023B2b_cfb_risk_integrable μ _ _ hm hmean 0 (by intro x; simp)
  have hci : Integrable (fun z => (z.2 - (1 / 2 : ℝ)) ^ 2) ν := by
    apply GP023B2b_cfb_risk_integrable μ _ _ hm measurable_const (d / 2)
    intro x
    simpa only [add_sub_cancel_left] using GP023B2b_cfb_smooth_bound d x hd.1
  have hmr : predictionRisk ν (fun x => 1 / 2 + clusterSmooth d x) = 1 / 100 := by
    rw [GP023B2b_cfb_risk_formula μ _ _ hm hmean hmi]
    simp [expectation]
  have hcr : predictionRisk ν (fun _ => 1 / 2) =
      1 / 100 + expectation μ (fun x => clusterSmooth d x ^ 2) := by
    simpa only [add_sub_cancel_left] using GP023B2b_cfb_risk_formula μ _ _ hm measurable_const hci
  have hsq : Integrable (fun x => clusterSmooth d x ^ 2) μ := by
    apply (integrable_const ((d / 2) ^ 2)).mono' (hm.pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    have hx := (sq_le_sq₀ (abs_nonneg (clusterSmooth d x)) (by linarith [hd.1])).mpr
      (GP023B2b_cfb_smooth_bound d x hd.1)
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hx
  have heb : expectation μ (fun x => clusterSmooth d x ^ 2) ≤ (d / 2) ^ 2 := by
    calc
      _ ≤ ∫ _ : ℝ, (d / 2) ^ 2 ∂μ := by
        apply integral_mono_ae hsq (integrable_const _)
        apply Filter.Eventually.of_forall
        intro x
        have hx := (sq_le_sq₀ (abs_nonneg (clusterSmooth d x)) (by linarith [hd.1])).mpr
          (GP023B2b_cfb_smooth_bound d x hd.1)
        simpa only [sq_abs] using hx
      _ = (d / 2) ^ 2 := by simp
  have himprove : ∀ f : ℝ → ℝ, Measurable f →
      Integrable (fun z => (z.2 - f z.1) ^ 2) ν →
      predictionRisk ν (fun _ => 1 / 2) - predictionRisk ν f ≤ (d / 2) ^ 2 := by
    intro f hf hi
    have hfr := GP023B2b_cfb_risk_formula μ _ _ hm hf hi
    have hn : 0 ≤ expectation μ (fun x => (1 / 2 + clusterSmooth d x - f x) ^ 2) :=
      integral_nonneg (fun x => sq_nonneg _)
    rw [hcr, hfr]
    linarith
  refine ⟨hwitness.1, hwitness.2, hmr, hcr, himprove, ?_⟩
  intro J _
  have hfit := GP023B2b_cfb_fitted_le_constant ν J
  refine ⟨hfit, ?_⟩
  intro f hf hi
  exact (sub_le_sub_right hfit _).trans (himprove f hf hi)

end
end AronowAudit.P023.Wave1
