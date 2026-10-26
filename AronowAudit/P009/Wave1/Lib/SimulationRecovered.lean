
import AronowAudit.P009.P009_FullBiasCompletion
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace AronowAudit.P009.Wave1

open scoped BigOperators
open Filter MeasureTheory

noncomputable section

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized restricted Lebesgue law used for one coordinate. -/
def t23_uniform (L : ℝ) : Measure ℝ :=
  (ENNReal.ofReal L)⁻¹ • volume.restrict (Set.Icc 0 L)

lemma t23_uniform_probability (L : ℝ) (hL : 0 < L) :
    IsProbabilityMeasure (t23_uniform L) := by
  constructor
  simp only [t23_uniform, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hL))
    ENNReal.ofReal_ne_top

lemma t23_baselines_probability (n : ℕ) : IsProbabilityMeasure (uniformBaselines n) := by
  letI : IsProbabilityMeasure (t23_uniform 3) := t23_uniform_probability 3 (by norm_num)
  letI : IsProbabilityMeasure (t23_uniform 7) := t23_uniform_probability 7 (by norm_num)
  have h : IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin n => t23_uniform 3)).prod
        (Measure.pi (fun _ : Fin n => t23_uniform 7))) := inferInstance
  norm_num [t23_uniform, uniformBaselines] at h ⊢
  exact h

def t23_cube (n : ℕ) (L : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => t23_uniform L)

lemma t23_cube_probability (n : ℕ) (L : ℝ) (hL : 0 < L) :
    IsProbabilityMeasure (t23_cube n L) := by
  haveI := t23_uniform_probability L hL
  unfold t23_cube
  infer_instance

lemma t23_baselines_eq (n : ℕ) :
    uniformBaselines n = (t23_cube n 3).prod (t23_cube n 7) := by
  norm_num [uniformBaselines, t23_cube, t23_uniform]

lemma t23_uniform_integrable_pow (L : ℝ) (hL : 0 < L) (k : ℕ) :
    Integrable (fun u : ℝ => u^k) (t23_uniform L) := by
  change Integrable (fun u : ℝ => u^k)
    ((ENNReal.ofReal L)⁻¹ • volume.restrict (Set.Icc 0 L))
  have h : Integrable (fun u : ℝ => u^k) (volume.restrict (Set.Icc 0 L)) :=
    (continuous_id.pow k).integrableOn_Icc
  exact h.smul_measure
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hL)))

lemma t23_uniform_moment (L : ℝ) (hL : 0 < L) (k : ℕ) :
    (∫ u, u^k ∂t23_uniform L) = L^k / ((k : ℝ) + 1) := by
  rw [t23_uniform, integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL.le, integral_pow]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hL.le,
    Nat.cast_add, Nat.cast_one, smul_eq_mul]
  rw [zero_pow (by omega : k + 1 ≠ 0), sub_zero, pow_succ]
  field_simp

lemma t23_cube_integrable_pow (n : ℕ) (L : ℝ) (hL : 0 < L) (i : Fin n) (k : ℕ) :
    Integrable (fun x : Fin n → ℝ => (x i)^k) (t23_cube n L) := by
  haveI := t23_uniform_probability L hL
  exact integrable_comp_eval (t23_uniform_integrable_pow L hL k)

lemma t23_cube_moment (n : ℕ) (L : ℝ) (hL : 0 < L) (i : Fin n) (k : ℕ) :
    (∫ x, (x i)^k ∂t23_cube n L) = L^k / ((k : ℝ) + 1) := by
  haveI := t23_uniform_probability L hL
  exact (integral_comp_eval (t23_uniform_integrable_pow L hL k).aestronglyMeasurable).trans
    (t23_uniform_moment L hL k)

lemma t23_cube_cross {n : ℕ} (L : ℝ) (hL : 0 < L) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun x : Fin n → ℝ => x i * x j) (t23_cube n L) ∧
    (∫ x, x i * x j ∂t23_cube n L) = (L / 2)^2 := by
  haveI := t23_uniform_probability L hL
  let f : Fin n → ℝ → ℝ := fun k u =>
    (if k = i then u else 1) * (if k = j then u else 1)
  have hf (k : Fin n) : Integrable (f k) (t23_uniform L) := by
    by_cases hi : k = i
    · subst k
      simpa [f, hij] using t23_uniform_integrable_pow L hL 1
    · by_cases hj : k = j
      · subst k
        simpa [f, Ne.symm hij] using t23_uniform_integrable_pow L hL 1
      · simpa [f, hi, hj] using integrable_const (μ := t23_uniform L) (1 : ℝ)
  have he (x : Fin n → ℝ) : (∏ k, f k (x k)) = x i * x j := by
    simp only [f, Finset.prod_mul_distrib]
    simp
  have hm (k : Fin n) :
      (∫ u, f k u ∂t23_uniform L) =
        (if k = i then L / 2 else 1) * (if k = j then L / 2 else 1) := by
    by_cases hi : k = i
    · subst k
      simpa [f, hij, show (1 : ℝ) + 1 = 2 by norm_num] using t23_uniform_moment L hL 1
    · by_cases hj : k = j
      · subst k
        simpa [f, Ne.symm hij, show (1 : ℝ) + 1 = 2 by norm_num] using
          t23_uniform_moment L hL 1
      · simp [f, hi, hj]
  constructor
  · simpa only [he, t23_cube] using Integrable.fintype_prod hf
  · calc
      _ = ∫ x, ∏ k, f k (x k) ∂t23_cube n L := by simp only [he]
      _ = ∏ k, ∫ u, f k u ∂t23_uniform L := integral_fintype_prod_eq_prod f
      _ = _ := by
        simp only [hm, Finset.prod_mul_distrib]
        simp [pow_two]

lemma t23_cube_product {n : ℕ} (L : ℝ) (hL : 0 < L) (i j : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i * x j) (t23_cube n L) ∧
    (∫ x, x i * x j ∂t23_cube n L) =
      if i = j then L^2 / 3 else L^2 / 4 := by
  by_cases hij : i = j
  · subst j
    constructor
    · simpa only [pow_two] using t23_cube_integrable_pow n L hL i 2
    · simpa [pow_two, show (2 : ℝ) + 1 = 3 by norm_num] using t23_cube_moment n L hL i 2
  · refine ⟨(t23_cube_cross L hL i j hij).1, ?_⟩
    rw [(t23_cube_cross L hL i j hij).2, if_neg hij]
    ring

/-- Second products under the actual independent uniform baseline law. -/
lemma t23_baseline_product {n : ℕ} (i j : Fin n) :
    Integrable (fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      (b.1 i + b.2 i) * (b.1 j + b.2 j)) (uniformBaselines n) ∧
    (∫ b, (b.1 i + b.2 i) * (b.1 j + b.2 j) ∂uniformBaselines n) =
      if i = j then 179 / 6 else 25 := by
  haveI := t23_cube_probability n 3 (by norm_num)
  haveI := t23_cube_probability n 7 (by norm_num)
  have hx (k : Fin n) : Integrable (fun x : Fin n → ℝ => x k) (t23_cube n 3) := by
    simpa only [pow_one] using t23_cube_integrable_pow n 3 (by norm_num) k 1
  have he (k : Fin n) : Integrable (fun e : Fin n → ℝ => e k) (t23_cube n 7) := by
    simpa only [pow_one] using t23_cube_integrable_pow n 7 (by norm_num) k 1
  have hxx := ((t23_cube_product 3 (by norm_num) i j).1).comp_fst (t23_cube n 7)
  have hee := ((t23_cube_product 7 (by norm_num) i j).1).comp_snd (t23_cube n 3)
  have hxe := (hx i).mul_prod (he j)
  have hex := (hx j).mul_prod (he i)
  have hex' : Integrable
      (fun b : (Fin n → ℝ) × (Fin n → ℝ) => b.2 i * b.1 j)
      ((t23_cube n 3).prod (t23_cube n 7)) := by
    simpa only [mul_comm] using hex
  have hp (b : (Fin n → ℝ) × (Fin n → ℝ)) :
      (b.1 i + b.2 i) * (b.1 j + b.2 j) =
        (b.1 i * b.1 j + b.1 i * b.2 j) + b.2 i * b.1 j + b.2 i * b.2 j := by ring
  rw [t23_baselines_eq]
  constructor
  · simpa only [hp] using ((hxx.fun_add hxe).fun_add hex').fun_add hee
  · simp_rw [hp]
    have hxxe : Integrable
        (fun b : (Fin n → ℝ) × (Fin n → ℝ) => b.1 i * b.1 j + b.1 i * b.2 j)
        ((t23_cube n 3).prod (t23_cube n 7)) := by
      exact hxx.fun_add hxe
    have hxxee : Integrable
        (fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
          b.1 i * b.1 j + b.1 i * b.2 j + b.2 i * b.1 j)
        ((t23_cube n 3).prod (t23_cube n 7)) := by
      exact hxxe.fun_add hex'
    rw [integral_add hxxee hee, integral_add hxxe hex', integral_add hxx hxe]
    rw [integral_fun_fst (fun x : Fin n → ℝ => x i * x j),
      integral_fun_snd (fun e : Fin n → ℝ => e i * e j),
      integral_prod_mul (fun x : Fin n → ℝ => x i) (fun e : Fin n → ℝ => e j)]
    have hrev :
        (∫ b : (Fin n → ℝ) × (Fin n → ℝ), b.2 i * b.1 j
          ∂(t23_cube n 3).prod (t23_cube n 7)) =
          (∫ x, x j ∂t23_cube n 3) * ∫ e, e i ∂t23_cube n 7 := by
      simpa only [mul_comm] using
        (integral_prod_mul (μ := t23_cube n 3) (ν := t23_cube n 7)
          (fun x => x j) (fun e => e i))
    rw [hrev]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
      (t23_cube_product 3 (by norm_num) i j).2,
      (t23_cube_product 7 (by norm_num) i j).2]
    have hmean (L : ℝ) (hL : 0 < L) (k : Fin n) :
        (∫ x, x k ∂t23_cube n L) = L / 2 := by
      simpa [show (1 : ℝ) + 1 = 2 by norm_num] using t23_cube_moment n L hL k 1
    rw [hmean 3 (by norm_num), hmean 7 (by norm_num),
      hmean 3 (by norm_num), hmean 7 (by norm_num)]
    split_ifs <;> norm_num

lemma t23_linear_square {n : ℕ} (a : Fin n → ℝ) :
    Integrable (fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      (∑ i, a i * (b.1 i + b.2 i))^2) (uniformBaselines n) ∧
    (∫ b, (∑ i, a i * (b.1 i + b.2 i))^2 ∂uniformBaselines n) =
      25 * (∑ i, a i)^2 + (29 / 6 : ℝ) * ∑ i, a i^2 := by
  have hp (b : (Fin n → ℝ) × (Fin n → ℝ)) :
      (∑ i, a i * (b.1 i + b.2 i))^2 =
        ∑ i, ∑ j, (a i * a j) * ((b.1 i + b.2 i) * (b.1 j + b.2 j)) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : Fin n) := ((t23_baseline_product i j).1).const_mul (a i * a j)
  constructor
  · simp_rw [hp]
    exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))
  · simp_rw [hp]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
    simp_rw [integral_finset_sum _ (fun j _ => hi _ j), integral_const_mul,
      (t23_baseline_product _ _).2]
    have ht (i j : Fin n) :
        a i * a j * (if i = j then (179 / 6 : ℝ) else 25) =
          25 * (a i * a j) + if j = i then (29 / 6 : ℝ) * a i^2 else 0 := by
      by_cases hij : i = j
      · subst j
        simp
        ring
      · simp [hij, Ne.symm hij]
        ring
    simp_rw [ht, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ← Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_mul_sum, ← pow_two]
    rw [← Finset.sum_mul]
    ring


lemma t23_paired_baseline {n : ℕ} (P : Law (Assignment n)) (ρ : Pairing n)
    (b : Fin n → ℝ)
    (hPair : Paired (⟨P, fullOutcome (fun _ => 0)⟩ : Experiment n) ρ) :
    Paired (⟨P, fullOutcome b⟩ : Experiment n) ρ := hPair

/-- Both estimators have the same design variance, by equality on design support. -/
lemma t23_variance_support {Ω : Type*} [Fintype Ω] (P : Law Ω) (T H : Ω → ℝ)
    (h : ∀ z, 0 < P.mass z → T z = H z) : var P T = var P H := by
  have hm := CompleteConditional.mean_support_congr P T H h
  unfold var cov
  rw [hm]
  apply CompleteConditional.mean_support_congr
  intro z hz
  rw [h z hz]

/-- The fixed-population part of T23, without any sampling moment assumptions. -/
lemma t23_fixed_baseline {n : ℕ} (hn : 0 < n) (heven : Even n)
    (E : Experiment n) (b : Fin n → ℝ) (hy : E.outcome = fullOutcome b)
    (hDesign : Complete E (n / 2) ∨ ∃ ρ : Pairing n, Paired E ρ) :
    mean E.design (ht E) - eate E = -1 ∧
    mean E.design (hajek E) - eate E = -1 ∧
    var E.design (hajek E) = var E.design (ht E) ∧
    mean E.design (fun z => (ht E z - eate E)^2) = var E.design (ht E) + 1 ∧
    mean E.design (fun z => (hajek E z - eate E)^2) = var E.design (ht E) + 1 := by
  have h := FullBiasCompletion.full_interference_bias_completed hn heven E b hy hDesign
  have hv : var E.design (hajek E) = var E.design (ht E) :=
    (t23_variance_support E.design _ _ (fun z hz => (h.2.1 z hz).2.2.1)).symm
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, hv, h.2.2.2.2.2.2.1,
    (h.2.2.2.2.2.2.2).trans (congrArg (fun v : ℝ => v + 1) hv)⟩

def t23_sign (a : Bool) : ℝ := 2 * bit a - 1

lemma t23_sign_square (a : Bool) : t23_sign a ^ 2 = 1 := by
  cases a <;> norm_num [t23_sign, bit]

lemma t23_sign_mean {n : ℕ} (E : Experiment n) (i : Fin n)
    (hm : marginal E i true = 1 / 2) :
    mean E.design (fun z => t23_sign (z i)) = 0 := by
  have he : mean E.design (fun z => bit (z i)) = marginal E i true := by
    unfold marginal prob
    congr 1
    funext z
    cases hz : z i <;> simp [bit, hz]
  simp only [t23_sign]
  rw [mean_sub, mean_const_mul, mean_const, he, hm]
  norm_num

/-- The exact covariance matrix of the paired treatment signs. -/
lemma t23_paired_sign_product {n : ℕ} (E : Experiment n) (ρ : Pairing n)
    (hPair : Paired E ρ) (i j : Fin n) :
    mean E.design (fun z => t23_sign (z i) * t23_sign (z j)) =
      if j = i then 1 else if j = ρ.partner i then -1 else 0 := by
  by_cases hji : j = i
  · subst j
    simp only [if_pos rfl]
    calc
      _ = mean E.design (fun _ => 1) := by
        congr 1
        funext z
        simpa only [pow_two] using t23_sign_square (z i)
      _ = 1 := mean_const _ _
  rw [if_neg hji]
  by_cases hjp : j = ρ.partner i
  · rw [if_pos hjp]
    apply (CompleteConditional.mean_support_congr E.design _ (fun _ => -1) ?_).trans
      (mean_const _ _)
    intro z hz
    have ho := PairedCompletion.supported_opposite E ρ hPair z hz i
    rw [hjp]
    cases hi : z i <;> cases hp : z (ρ.partner i) <;>
      simp_all [t23_sign, bit] <;> norm_num
  rw [if_neg hjp]
  let S : Set (Fin n) := {i, ρ.partner i}
  have hS (k : Fin n) : ρ.partner k ∈ S ↔ k ∈ S := by
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · right
        rw [← h, ρ.involution]
      · exact Or.inl (ρ.partner.injective h)
    · rintro (rfl | rfl)
      · exact Or.inr rfl
      · exact Or.inl (ρ.involution i)
  have h := PairedCompletion.mean_product_of_closed_partition E ρ hPair S hS
    (fun z => t23_sign (z i)) (fun z => t23_sign (z j))
    (by intro z w h; exact congrArg t23_sign (h i (by simp [S])))
    (by intro z w h; exact congrArg t23_sign (h j (by simp [S, hji, hjp])))
  rw [h, t23_sign_mean E i (PairedCompletion.marginal_half E ρ hPair i true), zero_mul]

lemma t23_paired_square_sum {n : ℕ} (E : Experiment n) (ρ : Pairing n)
    (hPair : Paired E ρ) (b : Fin n → ℝ) :
    mean E.design (fun z => (∑ i, t23_sign (z i) * b i)^2) =
      (1 / 2 : ℝ) * ∑ i, (b i - b (ρ.partner i))^2 := by
  have he (z : Assignment n) :
      (∑ i, t23_sign (z i) * b i)^2 =
        ∑ i, ∑ j, (b i * b j) * (t23_sign (z i) * t23_sign (z j)) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he, mean_sum, mean_const_mul, t23_paired_sign_product E ρ hPair]
  have hinner (i : Fin n) :
      (∑ j, b i * b j * (if j = i then 1 else if j = ρ.partner i then -1 else 0)) =
        b i ^ 2 - b i * b (ρ.partner i) := by
    have hterm (j : Fin n) :
        b i * b j * (if j = i then 1 else if j = ρ.partner i then -1 else 0) =
          (if j = i then b i ^ 2 else 0) -
            (if j = ρ.partner i then b i * b (ρ.partner i) else 0) := by
      by_cases hi : j = i
      · subst j
        simp [Ne.symm (ρ.no_fixed i)]
        ring
      · by_cases hp : j = ρ.partner i <;> simp [hi, hp, ρ.no_fixed i]
    simp_rw [hterm]
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [hinner]
  have hp : (∑ i, b (ρ.partner i)^2) = ∑ i, b i^2 :=
    ρ.partner.sum_comp (fun i => b i^2)
  calc
    _ = (1 / 2 : ℝ) *
        ((∑ i, b i^2) - 2 * (∑ i, b i * b (ρ.partner i)) + ∑ i, b (ρ.partner i)^2) := by
      rw [Finset.sum_sub_distrib, hp]
      ring
    _ = _ := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- A finite paired-design calculation, before averaging over sampled baselines. -/
lemma t23_paired_baseline_variance {n : ℕ} (hn : 0 < n) (heven : Even n)
    (E : Experiment n) (ρ : Pairing n) (hPair : Paired E ρ)
    (b : Fin n → ℝ) (hy : E.outcome = fullOutcome b) :
    var E.design (ht E) = 2 / (n : ℝ)^2 * ∑ i, (b i - b (ρ.partner i))^2 := by
  have h := FullBiasCompletion.full_interference_bias_completed hn heven E b hy
    (Or.inr ⟨ρ, hPair⟩)
  rw [variance_second_moment, h.2.2.1, sq, zero_mul, sub_zero]
  calc
    _ = mean E.design (fun z =>
        (2 / (n : ℝ))^2 * (∑ i, t23_sign (z i) * b i)^2) := by
      apply CompleteConditional.mean_support_congr
      intro z hz
      rw [(h.2.1 z hz).2.2.2]
      simp only [t23_sign, mul_pow]
    _ = _ := by
      rw [mean_const_mul, t23_paired_square_sum E ρ hPair]
      ring

/-- Integrating first over the baseline law avoids a two-unit inclusion calculation. -/
lemma t23_complete_sampling_average {n : ℕ} (hn : 0 < n) (heven : Even n)
    (P : Law (Assignment n))
    (hCR : Complete (⟨P, fullOutcome (fun _ => 0)⟩ : Experiment n) (n / 2)) :
    Integrable (fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      var P (ht (⟨P, fullOutcome (fun i => b.1 i + b.2 i)⟩ : Experiment n)))
      (uniformBaselines n) ∧
    (∫ b, var P (ht (⟨P, fullOutcome (fun i => b.1 i + b.2 i)⟩ : Experiment n))
      ∂uniformBaselines n) = 58 / (3 * (n : ℝ)) := by
  let E : ((Fin n → ℝ) × (Fin n → ℝ)) → Experiment n :=
    fun b => ⟨P, fullOutcome (fun i => b.1 i + b.2 i)⟩
  have hv (b) : var P (ht (E b)) =
      mean P (fun z => (2 / (n : ℝ))^2 *
        (∑ i, t23_sign (z i) * (b.1 i + b.2 i))^2) := by
    have h := FullBiasCompletion.full_interference_bias_completed hn heven (E b)
      (fun i => b.1 i + b.2 i) rfl (Or.inl hCR)
    rw [variance_second_moment, h.2.2.1, sq, zero_mul, sub_zero]
    apply CompleteConditional.mean_support_congr
    intro z hz
    rw [(h.2.1 z hz).2.2.2]
    simp only [t23_sign, mul_pow]
  have hi (z : Assignment n) : Integrable
      (fun b : (Fin n → ℝ) × (Fin n → ℝ) => P.mass z *
        ((2 / (n : ℝ))^2 * (∑ i, t23_sign (z i) * (b.1 i + b.2 i))^2))
      (uniformBaselines n) :=
    (((t23_linear_square (fun i => t23_sign (z i))).1).const_mul _).const_mul _
  change Integrable (fun b => var P (ht (E b))) (uniformBaselines n) ∧
    (∫ b, var P (ht (E b)) ∂uniformBaselines n) = 58 / (3 * (n : ℝ))
  constructor
  · simp_rw [hv]
    unfold mean
    exact integrable_finset_sum _ (fun z _ => hi z)
  · simp_rw [hv]
    unfold mean
    rw [integral_finset_sum _ (fun z _ => hi z)]
    simp_rw [integral_const_mul, (t23_linear_square _).2]
    change mean P (fun z => (2 / (n : ℝ))^2 *
      (25 * (∑ i, t23_sign (z i))^2 + (29 / 6 : ℝ) * ∑ i, t23_sign (z i)^2)) = _
    have hsupport (z : Assignment n) (hz : 0 < P.mass z) :
        (2 / (n : ℝ))^2 *
          (25 * (∑ i, t23_sign (z i))^2 + (29 / 6 : ℝ) * ∑ i, t23_sign (z i)^2) =
            58 / (3 * (n : ℝ)) := by
      have hc := (FullBiasCompletion.balanced_design_facts hn heven
        (⟨P, fullOutcome (fun _ => 0)⟩ : Experiment n) (Or.inl hCR)).2 z hz
      have hs : (∑ i, t23_sign (z i)) = 0 := by
        simp only [t23_sign, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rw [hc]
        simp
        ring
      rw [hs]
      simp only [t23_sign_square, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, zero_pow (by norm_num : 2 ≠ 0),
        mul_zero, zero_add]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
      ring
    exact (CompleteConditional.mean_support_congr P _ _ hsupport).trans (mean_const P _)

/-- Each region of the canonical label-tied sorting permutation is Borel. -/
lemma t23_sort_region {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurableSet {x : Fin n → ℝ | Tuple.sort x = σ} := by
  have he : {x : Fin n → ℝ | Tuple.sort x = σ} =
      {x : Fin n → ℝ | Monotone (x ∘ σ) ∧
        ∀ i j, i < j → x (σ i) = x (σ j) → σ i < σ j} := by
    ext x
    exact (eq_comm.trans Tuple.eq_sort_iff)
  rw [he]
  have hm (i j : Fin n) :
      MeasurableSet {x : Fin n → ℝ | i ≤ j → x (σ i) ≤ x (σ j)} :=
    (MeasurableSet.const (i ≤ j)).imp
      (measurableSet_le (show Measurable (fun x : Fin n → ℝ => x (σ i)) from
        measurable_pi_apply _) (measurable_pi_apply _))
  have ht (i j : Fin n) :
      MeasurableSet {x : Fin n → ℝ |
        i < j → x (σ i) = x (σ j) → σ i < σ j} :=
    (MeasurableSet.const (i < j)).imp
      ((measurableSet_eq_fun (show Measurable (fun x : Fin n → ℝ => x (σ i)) from
        measurable_pi_apply _) (measurable_pi_apply _)).imp
          (MeasurableSet.const (σ i < σ j)))
  have hm' : MeasurableSet {x : Fin n → ℝ | Monotone (x ∘ σ)} := by
    convert MeasurableSet.iInter (fun i => MeasurableSet.iInter (hm i)) using 1
    ext x
    simp [Monotone]
  have ht' : MeasurableSet {x : Fin n → ℝ |
      ∀ i j, i < j → x (σ i) = x (σ j) → σ i < σ j} := by
    convert MeasurableSet.iInter (fun i => MeasurableSet.iInter (ht i)) using 1
    ext x
    simp
  exact hm'.inter ht'

lemma t23_sorted_measurable {n : ℕ} (i : Fin n) :
    Measurable (fun x : Fin n → ℝ => x (Tuple.sort x i)) := by
  have hm : Measurable (fun x : Fin n → ℝ =>
      ∑ σ : Equiv.Perm (Fin n), if Tuple.sort x = σ then x (σ i) else 0) := by
    exact Finset.measurable_sum _ fun σ _ =>
      Measurable.ite (t23_sort_region σ) (measurable_pi_apply (σ i)) measurable_const
  simpa using hm

/-- Distinct coordinate hyperplanes are null for the actual ambient volume. -/
lemma t23_ties_volume {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    volume {x : Fin n → ℝ | x i = x j} = 0 := by
  let W : Submodule ℝ (Fin n → ℝ) :=
    LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)
  have hW : W ≠ ⊤ := by
    intro h
    have hp : Pi.single i (1 : ℝ) ∈ W := by rw [h]; trivial
    have hp' : (Pi.single i (1 : ℝ) : Fin n → ℝ) i -
        (Pi.single i (1 : ℝ) : Fin n → ℝ) j = 0 := by
      exact hp
    simp [Pi.single_apply, hij, Ne.symm hij] at hp'
  have he : (W : Set (Fin n → ℝ)) = {x | x i = x j} := by
    ext x
    change x i - x j = 0 ↔ x i = x j
    exact sub_eq_zero
  rw [← he]
  exact Measure.addHaar_submodule volume W hW

lemma t23_cube_density {n : ℕ} (L : ℝ) (hL : 0 < L) :
    t23_cube n L = (ENNReal.ofReal L)⁻¹ ^ n •
      volume.restrict (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => L)) := by
  haveI := t23_uniform_probability L hL
  have he : Measure.pi (fun _ : Fin n => t23_uniform L) =
      (ENNReal.ofReal L)⁻¹ ^ n •
        Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc 0 L)) := by
    apply Measure.pi_eq
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, t23_uniform,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [t23_cube, he]
  congr 1
  rw [← Measure.restrict_pi_pi]
  congr 1
  ext x
  simp [Set.mem_Icc, Pi.le_def]

lemma t23_cube_ae_injective (n : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ x : Fin n → ℝ ∂t23_cube n L, Function.Injective x := by
  have h (i j : Fin n) : ∀ᵐ x : Fin n → ℝ ∂t23_cube n L, x i = x j → i = j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ _ => hij)
    · have hv : ∀ᵐ x : Fin n → ℝ ∂volume, x i ≠ x j :=
        (ae_iff.mpr (by simpa using t23_ties_volume i j hij))
      rw [t23_cube_density L hL]
      filter_upwards [Measure.ae_smul_measure (ae_restrict_of_ae hv) _] with x hx
      exact fun he => (hx he).elim
  filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (h i))]
    with x hx
  exact hx

lemma t23_cube_ae_bounds (n : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ x : Fin n → ℝ ∂t23_cube n L, ∀ i, 0 ≤ x i ∧ x i ≤ L := by
  haveI := t23_uniform_probability L hL
  have h : ∀ᵐ u : ℝ ∂t23_uniform L, u ∈ Set.Icc 0 L :=
    Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  exact Filter.eventually_all.mpr fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => t23_uniform L) (i := i)).eventually h

def t23_gap {n : ℕ} (x : Fin n → ℝ) (j : ℕ) (hj : j + 1 < n) : ℝ :=
  x (Tuple.sort x ⟨j + 1, hj⟩) - x (Tuple.sort x ⟨j, by omega⟩)

lemma t23_gap_integrable {n : ℕ} (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : j + 1 < n) :
    Integrable (fun x : Fin n → ℝ => (t23_gap x j hj)^2) (t23_cube n L) := by
  haveI := t23_cube_probability n L hL
  have hm : AEStronglyMeasurable (fun x : Fin n → ℝ => (t23_gap x j hj)^2)
      (t23_cube n L) :=
    (((t23_sorted_measurable ⟨j + 1, hj⟩).sub
      (t23_sorted_measurable ⟨j, by omega⟩)).pow_const 2).aestronglyMeasurable
  apply Integrable.mono' (integrable_const (L^2)) hm
  filter_upwards [t23_cube_ae_bounds n L hL] with x hx
  have hg0 : 0 ≤ t23_gap x j hj := by
    exact sub_nonneg.mpr (Tuple.monotone_sort x (show
      (⟨j, by omega⟩ : Fin n) ≤ ⟨j + 1, hj⟩ by simp))
  have hgL : t23_gap x j hj ≤ L := by
    dsimp [t23_gap]
    linarith [(hx (Tuple.sort x ⟨j + 1, hj⟩)).2,
      (hx (Tuple.sort x ⟨j, by omega⟩)).1]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- The second-moment identity for adjacent uniform order-statistic spacings.
The measure is the product of normalized restricted Lebesgue laws, and the
sorting rule is Mathlib's deterministic ordering by value and then label. -/
def t23_UniformSpacingSecondMoment : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (L : ℝ), 0 < L → ∀ (j : ℕ) (hj : j + 1 < n),
    Integrable (fun x : Fin n → ℝ => (t23_gap x j hj)^2) (t23_cube n L) ∧
      (∫ x, (t23_gap x j hj)^2 ∂t23_cube n L) =
        2 * L^2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

/-- The nine target conjuncts that do not require the spacing-moment identity. -/
lemma t23_sampling_without_paired_average {n : ℕ} (hn : 0 < n) (heven : Even n)
    (P : Law (Assignment n))
    (hCR : Complete (⟨P, fullOutcome (fun _ => 0)⟩ : Experiment n) (n/2))
    (ρ : (Fin n → ℝ) → Pairing n)
    (Q : (Fin n → ℝ) → Law (Assignment n))
    (hPair : ∀ x, Paired (⟨Q x, fullOutcome (fun _ => 0)⟩ : Experiment n) (ρ x)) :
    let cr := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      (⟨P, fullOutcome (fun i => b.1 i+b.2 i)⟩ : Experiment n)
    let pair := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      (⟨Q b.1, fullOutcome (fun i => b.1 i+b.2 i)⟩ : Experiment n)
    (∫ b, mean (cr b).design (ht (cr b))-eate (cr b) ∂uniformBaselines n) = -1 ∧
    (∫ b, mean (pair b).design (ht (pair b))-eate (pair b) ∂uniformBaselines n) = -1 ∧
    (∫ b, mean (cr b).design (hajek (cr b))-eate (cr b) ∂uniformBaselines n) = -1 ∧
    (∫ b, mean (pair b).design (hajek (pair b))-eate (pair b) ∂uniformBaselines n) = -1 ∧
    (∫ b, var (cr b).design (ht (cr b)) ∂uniformBaselines n) = 58/(3*(n:ℝ)) ∧
    (∫ b, var (cr b).design (hajek (cr b)) ∂uniformBaselines n) = 58/(3*(n:ℝ)) ∧
    (∫ b, mean (cr b).design (fun z => (ht (cr b) z-eate (cr b))^2)
      ∂uniformBaselines n) = 58/(3*(n:ℝ))+1 ∧
    (∫ b, mean (cr b).design (fun z => (hajek (cr b) z-eate (cr b))^2)
      ∂uniformBaselines n) = 58/(3*(n:ℝ))+1 ∧
    1/(58/(3*(n:ℝ))) = 3*(n:ℝ)/58 := by
  let cr := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
    (⟨P, fullOutcome (fun i => b.1 i+b.2 i)⟩ : Experiment n)
  let pair := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
    (⟨Q b.1, fullOutcome (fun i => b.1 i+b.2 i)⟩ : Experiment n)
  haveI := t23_baselines_probability n
  have hc (b) := t23_fixed_baseline hn heven (cr b) (fun i => b.1 i + b.2 i) rfl
    (Or.inl hCR)
  have hp (b) := t23_fixed_baseline hn heven (pair b) (fun i => b.1 i + b.2 i) rfl
    (Or.inr ⟨ρ b.1, hPair b.1⟩)
  have hv := t23_complete_sampling_average hn heven P hCR
  have hb : (∫ _ : (Fin n → ℝ) × (Fin n → ℝ), (-1 : ℝ) ∂uniformBaselines n) = -1 := by
    simp
  have hmse : (∫ b, var P (ht (cr b)) + 1 ∂uniformBaselines n) =
      58 / (3 * (n : ℝ)) + 1 := by
    rw [integral_add hv.1 (integrable_const 1), hv.2]
    simp
  refine ⟨?_, ?_, ?_, ?_, hv.2, ?_, ?_, ?_, ?_⟩
  · exact (integral_congr_ae (Filter.Eventually.of_forall (fun b => (hc b).1))).trans hb
  · exact (integral_congr_ae (Filter.Eventually.of_forall (fun b => (hp b).1))).trans hb
  · exact (integral_congr_ae (Filter.Eventually.of_forall (fun b => (hc b).2.1))).trans hb
  · exact (integral_congr_ae (Filter.Eventually.of_forall (fun b => (hp b).2.1))).trans hb
  · exact (integral_congr_ae (Filter.Eventually.of_forall (fun b => (hc b).2.2.1))).trans hv.2
  · exact (integral_congr_ae (Filter.Eventually.of_forall (fun b => (hc b).2.2.2.1))).trans hmse
  · exact (integral_congr_ae (Filter.Eventually.of_forall (fun b => (hc b).2.2.2.2))).trans hmse
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp


end
end AronowAudit.P009.Wave1
