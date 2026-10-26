import AronowAudit.P016.P016_Interference
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Finite iid rejection probabilities for the power-of-two SSR witness (P016-T13). -/

namespace AronowAudit.P016.Wave1

open scoped BigOperators
open scoped Classical
open Finset MeasureTheory

noncomputable def t13b_cdfPoly (B c : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range (c+1), bernsteinPolynomial ℝ B k

noncomputable def t13b_cdf (B c : ℕ) (x : ℝ) : ℝ :=
  (t13b_cdfPoly B c).eval x

lemma t13b_cdf_eq (B c : ℕ) (x : ℝ) :
    t13b_cdf B c x = ∑ k ∈ range (c+1),
      (B.choose k : ℝ) * x^k * (1-x)^(B-k) := by
  simp [t13b_cdf, t13b_cdfPoly, Polynomial.eval_finset_sum, bernsteinPolynomial]

lemma t13b_cdfPoly_derivative (B c : ℕ) :
    (t13b_cdfPoly B c).derivative =
      -(B : Polynomial ℝ) * bernsteinPolynomial ℝ (B-1) c := by
  induction c with
  | zero => simp [t13b_cdfPoly, bernsteinPolynomial.derivative_zero]
  | succ c ih =>
    have h : t13b_cdfPoly B (c+1) =
        t13b_cdfPoly B c + bernsteinPolynomial ℝ B (c+1) := by
      simp only [t13b_cdfPoly, sum_range_succ]
    rw [h, Polynomial.derivative_add, ih, bernsteinPolynomial.derivative_succ]
    ring

lemma t13b_cdf_hasDerivAt (B c : ℕ) (x : ℝ) :
    HasDerivAt (t13b_cdf B c)
      (-(B : ℝ) * (B-1).choose c * x^c * (1-x)^(B-1-c)) x := by
  convert (t13b_cdfPoly B c).hasDerivAt x using 1
  · rfl
  · simp [t13b_cdfPoly_derivative, bernsteinPolynomial]
    ring

lemma t13b_cdf_continuous (B c : ℕ) : Continuous (t13b_cdf B c) :=
  (t13b_cdfPoly B c).continuous

lemma t13b_cdf_zero (B c : ℕ) : t13b_cdf B c 0 = 1 := by
  simp [t13b_cdf, t13b_cdfPoly, Polynomial.eval_finset_sum,
    bernsteinPolynomial.eval_at_0]

lemma t13b_cdf_one {B c : ℕ} (hc : c < B) : t13b_cdf B c 1 = 0 := by
  simp only [t13b_cdf, t13b_cdfPoly, Polynomial.eval_finset_sum,
    bernsteinPolynomial.eval_at_1]
  apply sum_eq_zero
  intro k hk
  have : k ≠ B := by have := mem_range.mp hk; omega
  simp [this]

lemma t13b_cdf_antitone (B c : ℕ) : AntitoneOn (t13b_cdf B c) (Set.Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (t13b_cdf_continuous B c).continuousOn
  · intro x _
    exact (t13b_cdf_hasDerivAt B c x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(t13b_cdf_hasDerivAt B c x).deriv]
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
    have h : 0 ≤ (B : ℝ) * (B-1).choose c * x^c * (1-x)^(B-1-c) := by
      have := hx'.1
      have : 0 ≤ 1-x := sub_nonneg.mpr hx'.2
      positivity
    nlinarith

lemma t13b_basis_integral {B k : ℕ} (hk : k ≤ B) :
    (∫ x in (0 : ℝ)..1, (B.choose k : ℝ) * x^k * (1-x)^(B-k)) =
      1/(B+1 : ℝ) := by
  have hd (x : ℝ) : HasDerivAt (t13b_cdf (B+1) k)
      (-(B+1 : ℝ) * ((B.choose k : ℝ) * x^k * (1-x)^(B-k))) x := by
    convert t13b_cdf_hasDerivAt (B+1) k x using 1 <;> simp <;> ring
  have hi : IntervalIntegrable
      (fun x : ℝ => (B.choose k : ℝ) * x^k * (1-x)^(B-k)) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hi.const_mul (-(B+1 : ℝ)))
  rw [intervalIntegral.integral_const_mul, t13b_cdf_one (by omega), t13b_cdf_zero] at he
  have hB : (B+1 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

lemma t13b_cdf_integral {B c : ℕ} (hc : c < B) :
    (∫ x in (0 : ℝ)..1, t13b_cdf B c x) = (c+1 : ℝ)/(B+1) := by
  simp only [t13b_cdf_eq]
  rw [intervalIntegral.integral_finset_sum]
  · have h : ∀ k ∈ range (c+1),
        (∫ x in (0 : ℝ)..1, (B.choose k : ℝ) * x^k * (1-x)^(B-k)) =
          1/(B+1 : ℝ) := by
      intro k hk
      apply t13b_basis_integral
      have := mem_range.mp hk
      omega
    rw [sum_congr rfl h]
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  · intro k _
    exact (by fun_prop : Continuous _).intervalIntegrable _ _

lemma t13b_mixture_cdf (M B c : ℕ) :
    binomialMixture M B c = 2/(M : ℝ) *
      ∑ r ∈ range M, t13b_cdf B c ((r+1 : ℕ)/M) := by
  unfold binomialMixture
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  apply sum_congr rfl
  intro r _
  rw [t13b_cdf_eq]
  by_cases hM : M = 0
  · subst M
    exact Fin.elim0 r
  · have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
    congr 1
    ext k
    congr 1
    field_simp
    push_cast
    ring

lemma t13b_mixture_grid_bounds {M B c : ℕ} (hM : 0 < M) (hc : c < B) :
    2*(c+1 : ℝ)/(B+1)-2/(M : ℝ) ≤ binomialMixture M B c ∧
      binomialMixture M B c ≤ 2*(c+1 : ℝ)/(B+1) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  let f : ℝ → ℝ := fun x => t13b_cdf B c (x/M)
  have ha : AntitoneOn f (Set.Icc 0 (0+(M : ℝ))) := by
    intro x hx z hz hxz
    apply t13b_cdf_antitone B c
    · exact ⟨div_nonneg hx.1 hMr.le, (div_le_one hMr).mpr (by simpa using hx.2)⟩
    · exact ⟨div_nonneg hz.1 hMr.le, (div_le_one hMr).mpr (by simpa using hz.2)⟩
    · exact div_le_div_of_nonneg_right hxz hMr.le
  have hI : (∫ x in (0 : ℝ)..0+M, f x) =
      (M : ℝ) * ((c+1 : ℝ)/(B+1)) := by
    dsimp [f]
    rw [intervalIntegral.integral_comp_div _ hMr.ne']
    simp only [zero_div, zero_add, div_self hMr.ne', smul_eq_mul, t13b_cdf_integral hc]
  have hL := ha.integral_le_sum
  have hR := ha.sum_le_integral
  simp only [zero_add] at hL hR hI
  rw [hI] at hL hR
  have hzero : f 0 = 1 := by simp [f, t13b_cdf_zero]
  have hone : f M = 0 := by simp [f, hMr.ne', t13b_cdf_one hc]
  have hshift : (∑ r ∈ range M, f r) =
      (∑ r ∈ range M, f (r+1 : ℕ)) + 1 := by
    have h := sum_range_succ' (fun r : ℕ => f r) M
    rw [sum_range_succ, hone, add_zero, Nat.cast_zero, hzero] at h
    exact h
  rw [hshift] at hL
  rw [t13b_mixture_cdf]
  change 2*(c+1 : ℝ)/(B+1)-2/(M : ℝ) ≤
      2/(M : ℝ)*(∑ r ∈ range M, f (r+1 : ℕ)) ∧
    2/(M : ℝ)*(∑ r ∈ range M, f (r+1 : ℕ)) ≤ 2*(c+1 : ℝ)/(B+1)
  constructor
  · have h := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 2/(M : ℝ))
    field_simp at h ⊢
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 2/(M : ℝ))
    field_simp at h ⊢
    nlinarith

lemma t13b_trapezoid_cell {f d A D : ℝ → ℝ} {K a b : ℝ}
    (hab : a ≤ b) (hdf : ∀ x, HasDerivAt f (d x) x) (hd : Continuous d)
    (hA : MonotoneOn A (Set.Icc a b)) (hD : MonotoneOn D (Set.Icc a b))
    (he : ∀ x ∈ Set.Icc a b, d x = A x-D x+K) :
    |(b-a)/2*(f a+f b)-(∫ x in a..b, f x)| ≤
      (b-a)^2/4*(A b-A a+D b-D a) := by
  let m : ℝ := (a+b)/2
  let q : ℝ := (A a+A b-D a-D b)/2+K
  let V : ℝ := A b-A a+D b-D a
  have haa : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hV : 0 ≤ V := by dsimp [V]; linarith [hA haa hbb hab, hD haa hbb hab]
  have hf : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hdf x).continuousAt)
  have hlin : Continuous (fun x : ℝ => x-m) := by fun_prop
  have hlin0 : (∫ x in a..b, x-m) = 0 := by
    rw [intervalIntegral.integral_sub
      (f := fun x : ℝ => x) (g := fun _ : ℝ => m)
      (continuous_id'.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b), integral_id]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    dsimp [m]
    ring
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hlin.continuousOn hf.continuousOn
    (fun x _ => (hasDerivAt_id x).sub_const m) (fun x _ => hdf x)
    (intervalIntegrable_const) (hd.intervalIntegrable a b)
  simp only [one_mul] at hparts
  have hi : (∫ x in a..b, (x-m)*(d x-q)) =
      (b-a)/2*(f a+f b)-(∫ x in a..b, f x) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub
      (f := fun x : ℝ => (x-m)*d x) (g := fun x : ℝ => (x-m)*q)
      ((by fun_prop : Continuous (fun x : ℝ => (x-m)*d x)).intervalIntegrable a b)
      ((by fun_prop : Continuous (fun x : ℝ => (x-m)*q)).intervalIntegrable a b),
      intervalIntegral.integral_mul_const, hlin0, zero_mul, sub_zero, hparts]
    dsimp [m]
    ring
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |(x-m)*(d x-q)| ≤ (b-a)*V/4 := by
    have ha1 := hA haa hx hx.1
    have ha2 := hA hx hbb hx.2
    have hd1 := hD haa hx hx.1
    have hd2 := hD hx hbb hx.2
    have hx1 : |x-m| ≤ (b-a)/2 := by
      apply abs_le.mpr
      dsimp [m]
      constructor <;> linarith [hx.1, hx.2]
    have hx2 : |d x-q| ≤ V/2 := by
      rw [he x hx]
      apply abs_le.mpr
      dsimp [q, V]
      constructor <;> linarith
    rw [abs_mul]
    calc
      _ ≤ ((b-a)/2)*(V/2) := mul_le_mul hx1 hx2 (abs_nonneg _) (by linarith)
      _ = _ := by ring
  have hiBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun x => (x-m)*(d x-q))
    (C := (b-a)*V/4) (fun x hx => by
      rw [Real.norm_eq_abs]
      apply hbound x
      exact ⟨(Set.mem_Ioc.mp ((Set.uIoc_of_le hab) ▸ hx)).1.le,
        (Set.mem_Ioc.mp ((Set.uIoc_of_le hab) ▸ hx)).2⟩)
  rw [Real.norm_eq_abs, hi, abs_of_nonneg (sub_nonneg.mpr hab)] at hiBound
  dsimp [V] at hiBound
  nlinarith

lemma t13b_telescope (f : ℕ → ℝ) (n : ℕ) :
    (∑ r ∈ range n, (f (r+1)-f r)) = f n-f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

lemma t13b_trapezoid_grid {f d A D : ℝ → ℝ} {K : ℝ} {M : ℕ}
    (hM : 0 < M) (hdf : ∀ x, HasDerivAt f (d x) x) (hd : Continuous d)
    (hA : MonotoneOn A (Set.Icc 0 1)) (hD : MonotoneOn D (Set.Icc 0 1))
    (he : ∀ x ∈ Set.Icc 0 1, d x = A x-D x+K)
    (hf0 : f 0 = 1) (hf1 : f 1 = 0) :
    2*(∫ x in (0 : ℝ)..1, f x)-1/(M : ℝ)-
        (A 1-A 0+D 1-D 0)/(2*(M : ℝ)^2) ≤
      2/(M : ℝ)*(∑ r ∈ range M, f ((r+1 : ℕ)/M)) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  let a : ℕ → ℝ := fun r => (r : ℝ)/M
  have ha0 : a 0 = 0 := by simp [a]
  have haM : a M = 1 := by simp [a, hMr.ne']
  have had (r : ℕ) : a (r+1)-a r = 1/(M : ℝ) := by dsimp [a]; push_cast; ring
  have hle (r : ℕ) : a r ≤ a (r+1) := by have := had r; linarith [one_div_pos.mpr hMr]
  have hmem {r : ℕ} (hr : r ≤ M) : a r ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by dsimp [a]; positivity, ?_⟩
    exact (div_le_one hMr).mpr (Nat.cast_le.mpr hr)
  have hcell {r : ℕ} (hr : r < M) :
      -(1/(M : ℝ))^2/4*(A (a (r+1))-A (a r)+D (a (r+1))-D (a r)) ≤
        (1/(M : ℝ))/2*(f (a r)+f (a (r+1)))-
          (∫ x in a r..a (r+1), f x) := by
    have hsub : Set.Icc (a r) (a (r+1)) ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Icc_subset_Icc (hmem (Nat.le_of_lt hr)).1 (hmem (by omega)).2
    have hb := (abs_le.mp (t13b_trapezoid_cell (hle r) hdf hd
      (hA.mono hsub) (hD.mono hsub) (fun x hx => he x (hsub hx)))).1
    rw [had] at hb
    nlinarith
  have hs := sum_le_sum (fun r hr => hcell (mem_range.mp hr))
  have htelA := t13b_telescope (fun r => A (a r)) M
  have htelD := t13b_telescope (fun r => D (a r)) M
  have hvar : (∑ r ∈ range M,
      (A (a (r+1))-A (a r)+D (a (r+1))-D (a r))) =
        A 1-A 0+D 1-D 0 := by
    simp_rw [show ∀ r, A (a (r+1))-A (a r)+D (a (r+1))-D (a r) =
      (A (a (r+1))-A (a r))+(D (a (r+1))-D (a r)) by intro r; ring]
    rw [sum_add_distrib, htelA, htelD, ha0, haM]
    ring
  have hf : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hdf x).continuousAt)
  have hint : (∑ r ∈ range M, ∫ x in a r..a (r+1), f x) =
      ∫ x in (0 : ℝ)..1, f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun r _ => hf.intervalIntegrable (a r) (a (r+1))), ha0, haM]
  have hshift : (∑ r ∈ range M, f (a r)) =
      (∑ r ∈ range M, f (a (r+1)))+1 := by
    have ht := sum_range_succ' (fun r => f (a r)) M
    rw [sum_range_succ, haM, hf1, add_zero, ha0, hf0] at ht
    exact ht
  simp only [← mul_sum, sum_sub_distrib, sum_add_distrib] at hs
  simp only [sum_sub_distrib, sum_add_distrib] at hvar
  rw [hvar, hint, hshift] at hs
  change 2*(∫ x in (0 : ℝ)..1, f x)-1/(M : ℝ)-
      (A 1-A 0+D 1-D 0)/(2*(M : ℝ)^2) ≤
    2/(M : ℝ)*(∑ r ∈ range M, f (a (r+1)))
  have hfrac : (A 1-A 0+D 1-D 0)/(2*(M : ℝ)^2) =
      2*((1/(M : ℝ))^2/4*(A 1-A 0+D 1-D 0)) := by field_simp; ring
  rw [hfrac]
  linear_combination 2*hs

noncomputable def t13b_pmf (n k : ℕ) (x : ℝ) : ℝ :=
  (n.choose k : ℝ)*x^k*(1-x)^(n-k)

lemma t13b_pmf_nonneg (n k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    0 ≤ t13b_pmf n k x := by
  dsimp [t13b_pmf]
  have := hx.1
  have : 0 ≤ 1-x := sub_nonneg.mpr hx.2
  positivity

lemma t13b_pmf_sum (n : ℕ) (x : ℝ) :
    (∑ k ∈ range (n+1), t13b_pmf n k x) = 1 := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ n)
  simpa [Polynomial.eval_finset_sum, bernsteinPolynomial, t13b_pmf] using h

lemma t13b_pmf_adjacent {n k : ℕ} (hk : k < n) (x : ℝ) :
    (k+1 : ℝ)*(1-x)*t13b_pmf n (k+1) x =
      (n-k : ℕ)*x*t13b_pmf n k x := by
  have he : n-k = (n-(k+1))+1 := by omega
  have hc : (n.choose (k+1) : ℝ)*(k+1 : ℝ) =
      (n.choose k : ℝ)*(n-k : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  rw [he] at hc
  unfold t13b_pmf
  rw [he, pow_succ, pow_succ]
  generalize x^k = u
  generalize (1-x)^(n-(k+1)) = v
  linear_combination u*v*x*(1-x)*hc

lemma t13b_neighbor_left {k : ℕ} (hk0 : 240 ≤ k) (hk1 : k < 250) :
    (24/25 : ℝ)*t13b_pmf 9999 (k+1) (250/9999) ≤
      t13b_pmf 9999 k (250/9999) := by
  have hk : k < 9999 := by omega
  have he := t13b_pmf_adjacent hk (250/9999)
  rw [Nat.cast_sub hk.le] at he
  have he' : (k+1 : ℝ)*9749*t13b_pmf 9999 (k+1) (250/9999) =
      (9999-(k : ℝ))*250*t13b_pmf 9999 k (250/9999) := by
    linear_combination 9999*he
  have hkn : (k : ℝ) < 250 := Nat.cast_lt.mpr hk1
  have hkz : (240 : ℝ) ≤ k := Nat.cast_le.mpr hk0
  have hq : (24/25 : ℝ)*((9999-(k : ℝ))*250) ≤ (k+1 : ℝ)*9749 := by linarith
  have hp := t13b_pmf_nonneg 9999 (k+1)
    (by norm_num : (250/9999 : ℝ) ∈ Set.Icc 0 1)
  apply (mul_le_mul_iff_right₀ (by linarith : 0 < (9999-(k : ℝ))*250)).mp
  calc
    ((9999-(k : ℝ))*250)*(24/25*t13b_pmf 9999 (k+1) (250/9999)) =
        ((24/25)*((9999-(k : ℝ))*250))*t13b_pmf 9999 (k+1) (250/9999) := by ring
    _ ≤ ((k+1 : ℝ)*9749)*t13b_pmf 9999 (k+1) (250/9999) :=
      mul_le_mul_of_nonneg_right hq hp
    _ = _ := by linear_combination he'

lemma t13b_neighbor_right {k : ℕ} (hk0 : 250 ≤ k) (hk1 : k < 260) :
    (24/25 : ℝ)*t13b_pmf 9999 k (250/9999) ≤
      t13b_pmf 9999 (k+1) (250/9999) := by
  have hk : k < 9999 := by omega
  have he := t13b_pmf_adjacent hk (250/9999)
  rw [Nat.cast_sub hk.le] at he
  have he' : (k+1 : ℝ)*9749*t13b_pmf 9999 (k+1) (250/9999) =
      (9999-(k : ℝ))*250*t13b_pmf 9999 k (250/9999) := by
    linear_combination 9999*he
  have hkn : (k : ℝ) ≤ 259 := by exact_mod_cast (show k ≤ 259 by omega)
  have hkz : (250 : ℝ) ≤ k := Nat.cast_le.mpr hk0
  have hq : (24/25 : ℝ)*((k+1 : ℝ)*9749) ≤ (9999-(k : ℝ))*250 := by linarith
  have hp := t13b_pmf_nonneg 9999 k
    (by norm_num : (250/9999 : ℝ) ∈ Set.Icc 0 1)
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < (k+1 : ℝ)*9749)).mp
  calc
    ((k+1 : ℝ)*9749)*(24/25*t13b_pmf 9999 k (250/9999)) =
        ((24/25)*((k+1 : ℝ)*9749))*t13b_pmf 9999 k (250/9999) := by ring
    _ ≤ ((9999-(k : ℝ))*250)*t13b_pmf 9999 k (250/9999) :=
      mul_le_mul_of_nonneg_right hq hp
    _ = _ := by linear_combination -he'

lemma t13b_neighbor_powers (s : ℕ) (hs : s ≤ 10) :
    (24/25 : ℝ)^s*t13b_pmf 9999 250 (250/9999) ≤
        t13b_pmf 9999 (250-s) (250/9999) ∧
      (24/25 : ℝ)^s*t13b_pmf 9999 250 (250/9999) ≤
        t13b_pmf 9999 (250+s) (250/9999) := by
  induction s with
  | zero => simp
  | succ s ih =>
    obtain ⟨hl,hr⟩ := ih (by omega)
    have hleft := t13b_neighbor_left (k := 250-(s+1)) (by omega) (by omega)
    have hright := t13b_neighbor_right (k := 250+s) (by omega) (by omega)
    rw [show 250-(s+1)+1 = 250-s by omega] at hleft
    have hp : (0 : ℝ) ≤ 24/25 := by norm_num
    constructor
    · calc
        _ = (24/25)*((24/25 : ℝ)^s*t13b_pmf 9999 250 (250/9999)) := by rw [pow_succ] <;> ring
        _ ≤ _ := (mul_le_mul_of_nonneg_left hl hp).trans hleft
    · calc
        _ = (24/25)*((24/25 : ℝ)^s*t13b_pmf 9999 250 (250/9999)) := by rw [pow_succ] <;> ring
        _ ≤ t13b_pmf 9999 (250+s+1) (250/9999) :=
          (mul_le_mul_of_nonneg_left hr hp).trans hright
        _ = _ := by congr 1 <;> omega

lemma t13b_mode_height : 10000*t13b_pmf 9999 250 (250/9999) ≤ (20000/21 : ℝ) := by
  have hp0 := t13b_pmf_nonneg 9999 250
    (by norm_num : (250/9999 : ℝ) ∈ Set.Icc 0 1)
  have hhalf (s : ℕ) (hs : s ≤ 10) : (1/2 : ℝ) ≤ (24/25 : ℝ)^s :=
    le_trans (by norm_num : (1/2 : ℝ) ≤ (24/25 : ℝ)^10)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hs)
  have hpoint (k : ℕ) (hk : k ∈ Icc 240 260) :
      t13b_pmf 9999 250 (250/9999)/2 ≤ t13b_pmf 9999 k (250/9999) := by
    obtain ⟨hk0,hk1⟩ := mem_Icc.mp hk
    by_cases h : k ≤ 250
    · have hs : 250-k ≤ 10 := by omega
      have he : 250-(250-k) = k := by omega
      have ht := (t13b_neighbor_powers (250-k) hs).1
      rw [he] at ht
      have hm := mul_le_mul_of_nonneg_right (hhalf (250-k) hs) hp0
      linarith
    · have hs : k-250 ≤ 10 := by omega
      have he : 250+(k-250) = k := by omega
      have ht := (t13b_neighbor_powers (k-250) hs).2
      rw [he] at ht
      have hm := mul_le_mul_of_nonneg_right (hhalf (k-250) hs) hp0
      linarith
  have hs := sum_le_sum (fun k hk => hpoint k hk)
  have hsub : Icc 240 260 ⊆ range 10000 := by
    intro k hk
    simp only [mem_Icc, mem_range] at *
    omega
  have htotal : (∑ k ∈ Icc 240 260, t13b_pmf 9999 k (250/9999)) ≤ 1 := by
    rw [← t13b_pmf_sum 9999 (250/9999)]
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro k _ _
    exact t13b_pmf_nonneg _ _ (by norm_num)
  norm_num only [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.cast_add, Nat.cast_sub,
    Nat.cast_one, Nat.cast_ofNat] at hs
  linarith

noncomputable def t13b_g (x : ℝ) : ℝ :=
  10000*((9999 : ℕ).choose 250 : ℝ)*x^250*(1-x)^9749

lemma t13b_g_eq (x : ℝ) : t13b_g x = 10000*t13b_pmf 9999 250 x := by
  simp only [t13b_g, t13b_pmf, Nat.reduceSub, mul_assoc]

lemma t13b_g_hasDerivAt (x : ℝ) :
    HasDerivAt t13b_g
      (10000*((9999 : ℕ).choose 250 : ℝ)*x^249*(1-x)^9748*(250-9999*x)) x := by
  have hd := (((hasDerivAt_id x).pow 250).const_mul
    (10000*((9999 : ℕ).choose 250 : ℝ))).mul
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow 9749)
  convert hd using 1
  · rfl
  · norm_num only [Nat.cast_ofNat, Nat.reduceSub, mul_one, zero_sub,
      Pi.pow_apply, Pi.sub_apply, id_eq]
    rw [show x^250 = x^249*x by rw [← pow_succ],
      show (1-x)^9749 = (1-x)^9748*(1-x) by rw [← pow_succ]]
    generalize x^249 = u
    generalize (1-x)^9748 = v
    generalize ((9999 : ℕ).choose 250 : ℝ) = C
    ring

lemma t13b_g_continuous : Continuous t13b_g := by unfold t13b_g; fun_prop

lemma t13b_g_unimodal :
    MonotoneOn t13b_g (Set.Icc 0 (250/9999)) ∧
      AntitoneOn t13b_g (Set.Icc (250/9999) 1) := by
  constructor
  · apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      t13b_g_continuous.continuousOn
    · intro x _
      exact (t13b_g_hasDerivAt x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(t13b_g_hasDerivAt x).deriv]
      have hx' : x ∈ Set.Icc (0 : ℝ) (250/9999) := interior_subset hx
      have hx0 := hx'.1
      have hq : 0 ≤ 1-x := by linarith [hx'.2]
      have hf : 0 ≤ 250-9999*x := by linarith [hx'.2]
      positivity
  · apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      t13b_g_continuous.continuousOn
    · intro x _
      exact (t13b_g_hasDerivAt x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(t13b_g_hasDerivAt x).deriv]
      have hx' : x ∈ Set.Icc (250/9999 : ℝ) 1 := interior_subset hx
      have hx0 : 0 ≤ x := by linarith [hx'.1]
      have hq : 0 ≤ 1-x := by linarith [hx'.2]
      have hf : 250-9999*x ≤ 0 := by linarith [hx'.1]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hf

lemma t13b_10000_weak : (1/20 : ℝ) < binomialMixture 6435 10000 250 := by
  let p : ℝ := 250/9999
  let A : ℝ → ℝ := fun x => -t13b_g (max x p)
  let D : ℝ → ℝ := fun x => t13b_g (min x p)
  have hp0 : 0 ≤ p := by norm_num [p]
  have hp1 : p ≤ 1 := by norm_num [p]
  have hA : MonotoneOn A (Set.Icc 0 1) := by
    intro x hx z hz hxz
    apply neg_le_neg
    exact t13b_g_unimodal.2 ⟨le_max_right _ _, max_le hx.2 hp1⟩
      ⟨le_max_right _ _, max_le hz.2 hp1⟩ (max_le_max hxz le_rfl)
  have hD : MonotoneOn D (Set.Icc 0 1) := by
    intro x hx z hz hxz
    exact t13b_g_unimodal.1 ⟨le_min hx.1 hp0, min_le_right _ _⟩
      ⟨le_min hz.1 hp0, min_le_right _ _⟩ (min_le_min hxz le_rfl)
  have he (x : ℝ) (_ : x ∈ Set.Icc 0 1) :
      -t13b_g x = A x-D x+t13b_g p := by
    dsimp [A, D]
    rcases le_total x p with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]; ring
  have hdf (x : ℝ) : HasDerivAt (t13b_cdf 10000 250) (-t13b_g x) x := by
    simpa only [t13b_g, Nat.reduceSub, Nat.cast_ofNat, neg_mul] using
      t13b_cdf_hasDerivAt 10000 250 x
  have hb := t13b_trapezoid_grid (M := 6435) (by decide) hdf
    t13b_g_continuous.neg hA hD he (t13b_cdf_zero _ _) (t13b_cdf_one (by decide))
  have hg0 : t13b_g 0 = 0 := by
    simp only [t13b_g, zero_pow (by decide : 250 ≠ 0), mul_zero, zero_mul]
  have hg1 : t13b_g 1 = 0 := by
    simp only [t13b_g, sub_self, zero_pow (by decide : 9749 ≠ 0), mul_zero]
  have hvar : A 1-A 0+D 1-D 0 = 2*t13b_g p := by
    dsimp [A, D]
    rw [max_eq_left hp1, max_eq_right hp0, min_eq_right hp1,
      min_eq_left hp0, hg0, hg1]
    ring
  rw [hvar, t13b_cdf_integral (by decide), ← t13b_mixture_cdf] at hb
  have hg : t13b_g p ≤ 1000 := by
    rw [t13b_g_eq]
    exact t13b_mode_height.trans (by norm_num)
  have hlow : (1/20 : ℝ) < 502/10001-1/6435-1000/(6435:ℝ)^2 := by norm_num
  have hstep : 502/10001-1/6435-1000/(6435:ℝ)^2 ≤
      2*((250+1 : ℝ)/(10000+1))-1/6435-(2*t13b_g p)/(2*(6435:ℝ)^2) := by
    linarith
  change 502/10001-1/6435-1000/(6435:ℝ)^2 ≤
      2*((250+1 : ℝ)/(10000+1))-1/6435-(2*t13b_g p)/(2*(6435:ℝ)^2) at hstep
  convert hlow.trans_le (hstep.trans ?_) using 1
  convert hb using 1 <;> norm_num only [Nat.cast_ofNat]

noncomputable def t13b_hits {Ω : Type} {B : ℕ} (P : Ω → Prop) (draw : Fin B → Ω) : ℕ := by
  classical
  exact ∑ b, if P (draw b) then 1 else 0

lemma t13b_binomial_coeff (s t : ℝ) (B k : ℕ) :
    ((Polynomial.C s*Polynomial.X+Polynomial.C t)^B).coeff k =
      (B.choose k : ℝ)*s^k*t^(B-k) := by
  have hterm (j : ℕ) :
      (Polynomial.C s*Polynomial.X)^j*(Polynomial.C t)^(B-j)*(B.choose j : Polynomial ℝ) =
        Polynomial.C (s^j*t^(B-j)*(B.choose j : ℝ))*Polynomial.X^j := by
    simp only [mul_pow, ← Polynomial.C_pow, ← Polynomial.C_eq_natCast,
      map_mul]
    ring
  rw [add_pow]
  simp_rw [hterm]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k < B+1
  · rw [sum_eq_single k]
    · simp; ring
    · intro j _ hj
      simp [Ne.symm hj]
    · simp [hk]
  · have hb : B < k := by omega
    rw [Nat.choose_eq_zero_of_lt hb]
    simp only [Nat.cast_zero, zero_mul]
    apply sum_eq_zero
    intro j hj
    have : k ≠ j := by have := mem_range.mp hj; omega
    simp [this]

lemma t13b_count_exact {Ω : Type} [Fintype Ω] (P : Ω → Prop) (B k : ℕ) :
    (∑ draw : Fin B → Ω, if t13b_hits P draw = k then (1 : ℝ) else 0) =
      (B.choose k : ℝ)*(∑ x, if P x then (1 : ℝ) else 0)^k *
        (∑ x, if P x then (0 : ℝ) else 1)^(B-k) := by
  classical
  let s : ℝ := ∑ x, if P x then 1 else 0
  let t : ℝ := ∑ x, if P x then 0 else 1
  have hbase : (∑ x, if P x then (Polynomial.X : Polynomial ℝ) else 1) =
      Polynomial.C s*Polynomial.X+Polynomial.C t := by
    have hpoint (x : Ω) : (if P x then (Polynomial.X : Polynomial ℝ) else 1) =
        Polynomial.C (if P x then (1 : ℝ) else 0)*Polynomial.X+
          Polynomial.C (if P x then (0 : ℝ) else 1) := by
      by_cases hx : P x <;> simp [hx]
    simp_rw [hpoint]
    rw [sum_add_distrib, ← sum_mul, ← map_sum, ← map_sum]
  have hprod (draw : Fin B → Ω) :
      (∏ b, if P (draw b) then (Polynomial.X : Polynomial ℝ) else 1) =
        Polynomial.X^(t13b_hits P draw) := by
    unfold t13b_hits
    rw [← prod_pow_eq_pow_sum]
    apply prod_congr rfl
    intro b _
    by_cases hb : P (draw b) <;> simp [hb]
  have hgen : (∑ draw : Fin B → Ω, (Polynomial.X : Polynomial ℝ)^(t13b_hits P draw)) =
      (Polynomial.C s*Polynomial.X+Polynomial.C t)^B := by
    rw [← hbase, Fintype.sum_pow]
    exact sum_congr rfl (fun draw _ => (hprod draw).symm)
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff k) hgen
  rw [Polynomial.finsetSum_coeff, t13b_binomial_coeff] at hc
  simpa only [Polynomial.coeff_X_pow, eq_comm] using hc

lemma t13b_count_cdf {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) {B c : ℕ} (hc : c < B) :
    uniformMass (Fin B → Ω) (fun draw => t13b_hits P draw ≤ c) =
      t13b_cdf B c ((∑ x, if P x then (1 : ℝ) else 0)/Fintype.card Ω) := by
  classical
  let N : ℝ := Fintype.card Ω
  let s : ℝ := ∑ x, if P x then 1 else 0
  let t : ℝ := ∑ x, if P x then 0 else 1
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hst : s+t = N := by
    dsimp [s, t, N]
    rw [← sum_add_distrib]
    simp only [show ∀ x : Ω, (if P x then (1 : ℝ) else 0)+
      (if P x then (0 : ℝ) else 1) = 1 by intro x; split_ifs <;> norm_num]
    simp
  have hdecomp (draw : Fin B → Ω) :
      (if t13b_hits P draw ≤ c then (1 : ℝ) else 0) =
        ∑ k ∈ range (c+1), if t13b_hits P draw = k then (1 : ℝ) else 0 := by
    simp only [eq_comm (a := t13b_hits P draw), sum_ite_eq', mem_range,
      Nat.lt_succ_iff]
  unfold uniformMass
  have hreplace : (∑ draw : Fin B → Ω, if t13b_hits P draw ≤ c then (1 : ℝ) else 0) =
      ∑ draw : Fin B → Ω, ∑ k ∈ range (c+1),
        if t13b_hits P draw = k then (1 : ℝ) else 0 :=
    sum_congr rfl (fun draw _ => hdecomp draw)
  convert_to (∑ draw : Fin B → Ω, if t13b_hits P draw ≤ c then (1 : ℝ) else 0)/
      Fintype.card (Fin B → Ω) = _
  · congr 1
    apply sum_congr rfl
    intro draw _
    split_ifs <;> rfl
  rw [hreplace]
  rw [sum_comm]
  simp_rw [t13b_count_exact]
  rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, sum_div, t13b_cdf_eq]
  apply sum_congr rfl
  intro k hk
  have hkb : k ≤ B := by have := mem_range.mp hk; omega
  change (B.choose k : ℝ)*s^k*t^(B-k)/N^B =
    (B.choose k : ℝ)*(s/N)^k*(1-s/N)^(B-k)
  have ht : 1-s/N = t/N := by apply (eq_div_iff hN).mpr; field_simp; linarith
  rw [ht, div_pow, div_pow]
  have hpow : N^B = N^k*N^(B-k) := by rw [← pow_add, Nat.add_sub_of_le hkb]
  rw [hpow]
  field

lemma t13b_uniform_cons {Ω : Type} [Fintype Ω] [Nonempty Ω] (B : ℕ)
    (E : (Fin (B+1) → Ω) → Prop) :
    uniformMass (Fin (B+1) → Ω) E =
      (∑ x : Ω, uniformMass (Fin B → Ω) (fun draw => E (Fin.cons x draw)))/Fintype.card Ω := by
  classical
  unfold uniformMass
  rw [← (Fin.consEquiv (fun _ : Fin (B+1) => Ω)).sum_comp
    (fun draw => if E draw then (1 : ℝ) else 0), Fintype.sum_prod_type]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ← sum_div,
    pow_succ, div_div]
  simp only [Nat.cast_mul, Nat.cast_pow]
  rfl

lemma t13b_enumerated_sum {Ω : Type} [Fintype Ω] {M d : ℕ}
    (f : Ω → ℝ) (e : Fin M ↪o ℝ)
    (he : univ.image e = univ.image f)
    (hf : ∀ v ∈ univ.image f, (univ.filter (fun x => f x = v)).card = d)
    (g : ℝ → ℝ) :
    (∑ x, g (f x)) = (d : ℝ)*∑ r : Fin M, g (e r) := by
  rw [Finset.sum_comp g f]
  calc
    (∑ v ∈ univ.image f, (univ.filter (fun x => f x = v)).card • g v) =
        ∑ v ∈ univ.image f, (d : ℝ)*g v := by
      apply sum_congr rfl
      intro v hv
      rw [hf v hv, nsmul_eq_mul]
    _ = _ := by
      rw [← he, sum_image]
      · rw [mul_sum]
      · exact fun x _ z _ hxz => e.injective hxz

lemma t13b_enum_counts {Ω : Type} [Fintype Ω] {M d : ℕ}
    (f : Ω → ℝ) (e : Fin M ↪o ℝ)
    (he : univ.image e = univ.image f)
    (hf : ∀ v ∈ univ.image f, (univ.filter (fun x => f x = v)).card = d)
    (r : Fin M) :
    (∑ x, if f x ≤ e r then (1 : ℝ) else 0) = (d : ℝ)*(r.val+1) ∧
      (∑ x, if e r ≤ f x then (1 : ℝ) else 0) = (d : ℝ)*((M : ℝ)-r.val) := by
  have hlo : univ.filter (fun j : Fin M => j ≤ r) = Iic r := by ext j; simp
  have hup : univ.filter (fun j : Fin M => r ≤ j) = Ici r := by ext j; simp
  constructor
  · rw [t13b_enumerated_sum f e he hf (fun x => if x ≤ e r then 1 else 0)]
    simp only [e.le_iff_le, ← sum_filter, sum_const, hlo, Fin.card_Iic, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, mul_one]
  · rw [t13b_enumerated_sum f e he hf (fun x => if e r ≤ x then 1 else 0)]
    simp only [e.le_iff_le, ← sum_filter, sum_const, hup, Fin.card_Ici, nsmul_eq_mul,
      Nat.cast_sub r.isLt.le, mul_one]

lemma t13b_counts_cover {B : ℕ} (ref : Fin B → ℝ) (obs : ℝ) :
    B ≤ lowerCount ref obs+upperCount ref obs := by
  rw [lowerCount, upperCount, ← sum_add_distrib]
  calc
    B = ∑ _ : Fin B, (1 : ℕ) := by simp
    _ ≤ _ := sum_le_sum (fun b _ => by
      rcases le_total (ref b) obs with h | h <;> simp [h] <;> split_ifs <;> omega)

lemma t13b_uniform_or {Ω : Type} [Fintype Ω] (E F : Ω → Prop)
    (h : ∀ x, ¬(E x ∧ F x)) :
    uniformMass Ω (fun x => E x ∨ F x) = uniformMass Ω E+uniformMass Ω F := by
  unfold uniformMass
  rw [← add_div, ← sum_add_distrib]
  apply congrArg (fun z : ℝ => z/Fintype.card Ω)
  apply sum_congr rfl
  intro x _
  by_cases he : E x <;> by_cases hf : F x <;> simp_all

lemma t13b_iid_mixture {Ω : Type} [Fintype Ω] [Nonempty Ω] {M d : ℕ}
    (hM : 0 < M) (hd : 0 < d) (f : Ω → ℝ) (e : Fin M ↪o ℝ)
    (he : univ.image e = univ.image f)
    (hf : ∀ v ∈ univ.image f, (univ.filter (fun x => f x = v)).card = d)
    (hcard : Fintype.card Ω = d*M) {B c : ℕ} (hc : 2*c < B) :
    uniformMass (Fin (B+1) → Ω) (fun draw =>
      lowerCount (fun b => f (draw b.succ)) (f (draw 0)) ≤ c ∨
      upperCount (fun b => f (draw b.succ)) (f (draw 0)) ≤ c) =
        binomialMixture M B c := by
  have hcb : c < B := by omega
  have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdr : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcr : (Fintype.card Ω : ℝ) = (d : ℝ)*M := by exact_mod_cast hcard
  have hconditional (upper : Bool) :
      uniformMass (Fin (B+1) → Ω) (fun draw =>
        (if upper then upperCount (fun b => f (draw b.succ)) (f (draw 0))
          else lowerCount (fun b => f (draw b.succ)) (f (draw 0))) ≤ c) =
        (∑ x : Ω, t13b_cdf B c
          ((∑ v, if (if upper then f x ≤ f v else f v ≤ f x) then (1 : ℝ) else 0)/
            Fintype.card Ω))/Fintype.card Ω := by
    rw [t13b_uniform_cons]
    congr 1
    apply sum_congr rfl
    intro x _
    cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact t13b_count_cdf (fun v => f v ≤ f x) hcb
    · exact t13b_count_cdf (fun v => f x ≤ f v) hcb
  have hcondEnum (upper : Bool) :
      uniformMass (Fin (B+1) → Ω) (fun draw =>
        (if upper then upperCount (fun b => f (draw b.succ)) (f (draw 0))
          else lowerCount (fun b => f (draw b.succ)) (f (draw 0))) ≤ c) =
        (1/(M : ℝ))*∑ r : Fin M, t13b_cdf B c
          (if upper then ((M : ℝ)-r.val)/M else (r.val+1 : ℝ)/M) := by
    rw [hconditional]
    rw [t13b_enumerated_sum f e he hf (fun x => t13b_cdf B c
      ((∑ v, if (if upper then x ≤ f v else f v ≤ x) then (1 : ℝ) else 0)/
        Fintype.card Ω))]
    have harg (r : Fin M) :
        (∑ v, if (if upper then e r ≤ f v else f v ≤ e r) then (1 : ℝ) else 0)/
          Fintype.card Ω =
            (if upper then ((M : ℝ)-r.val)/M else (r.val+1 : ℝ)/M) := by
      cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · rw [(t13b_enum_counts f e he hf r).1, hcr]
        field
      · rw [(t13b_enum_counts f e he hf r).2, hcr]
        field
    simp_rw [harg]
    rw [hcr]
    field
  have hrev : (∑ r : Fin M, t13b_cdf B c (((M : ℝ)-r.val)/M)) =
      ∑ r : Fin M, t13b_cdf B c ((r.val+1 : ℝ)/M) := by
    rw [← Equiv.sum_comp (Fin.revPerm : Fin M ≃ Fin M)
      (fun r : Fin M => t13b_cdf B c ((r.val+1 : ℝ)/M))]
    apply sum_congr rfl
    intro r _
    congr 2
    have hr : (Fin.revPerm r).val+1 = M-r.val := by simp [Fin.revPerm, Fin.rev]; omega
    have hr' : ((Fin.revPerm r).val : ℝ)+1 = (M : ℝ)-r.val := by
      have hh := congrArg (fun n : ℕ => (n : ℝ)) hr
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub r.isLt.le] using hh
    exact hr'.symm
  rw [t13b_uniform_or]
  · have hl := hcondEnum false
    have hu := hcondEnum true
    simp only [Bool.false_eq_true, ite_false, ite_true] at hl hu
    rw [hl, hu, hrev, t13b_mixture_cdf, ← Fin.sum_univ_eq_sum_range]
    push_cast
    ring
  · intro draw ⟨hl,hu⟩
    have := t13b_counts_cover (fun b => f (draw b.succ)) (f (draw 0))
    omega

noncomputable def t13b_ssr (z : Balanced 16 8) : ℝ :=
  rss (fun i => (2 : ℝ)^i.val) z.val

noncomputable def t13b_complement (z : Balanced 16 8) : Balanced 16 8 :=
  ⟨fun i => !(z.val i), by
    have hs := group_sizes z.val
    have ht : groupSize (fun i => !(z.val i)) true = groupSize z.val false := by
      unfold groupSize
      apply sum_congr rfl
      intro i _
      cases hi : z.val i <;> simp [hi]
    rw [ht]
    have := z.property
    omega⟩

lemma t13b_complement_ne (z : Balanced 16 8) : z ≠ t13b_complement z := by
  intro h
  have hi := congrFun (congrArg Subtype.val h) (0 : Fin 16)
  change z.val 0 = !(z.val 0) at hi
  cases hb : z.val 0 <;> simp [hb] at hi

lemma t13b_ssr_fibers (v : ℝ) (hv : v ∈ univ.image t13b_ssr) :
    (univ.filter (fun z : Balanced 16 8 => t13b_ssr z = v)).card = 2 := by
  obtain ⟨z, _, rfl⟩ := mem_image.mp hv
  have heq (w : Balanced 16 8) :
      t13b_ssr w = t13b_ssr z ↔ w = z ∨ w = t13b_complement z := by
    have hh := t13_finite_design.2.2.2.2.2 w z
    change t13b_ssr w = t13b_ssr z ↔ _ at hh
    constructor
    · intro h
      rcases hh.mp h with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact hh.mpr (Or.inl rfl)
      · exact hh.mpr (Or.inr rfl)
  have hf : univ.filter (fun w : Balanced 16 8 => t13b_ssr w = t13b_ssr z) =
      {z, t13b_complement z} := by
    ext w
    simp only [mem_filter, mem_univ, true_and, heq, mem_insert, mem_singleton]
  rw [hf, card_pair (t13b_complement_ne z)]

lemma t13b_concrete_mixture {B c : ℕ} (hc : 2*c < B) :
    uniformMass (Fin (B+1) → Balanced 16 8) (fun draw =>
      lowerCount (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0)) ≤ c ∨
      upperCount (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0)) ≤ c) =
        binomialMixture 6435 B c := by
  have hcard : Fintype.card (Balanced 16 8) = 12870 := t13_finite_design.1
  letI t13b_instNonemptyBalanced : Nonempty (Balanced 16 8) :=
    Fintype.card_pos_iff.mp (by omega)
  have hs : (univ.image t13b_ssr).card = 6435 := t13_finite_design.2.2.2.2.1
  let e : Fin 6435 ↪o ℝ := (univ.image t13b_ssr).orderEmbOfFin hs
  apply t13b_iid_mixture (d := 2) (by decide) (by decide) t13b_ssr e
    (image_orderEmbOfFin_univ _ _) t13b_ssr_fibers _ hc
  omega

lemma t13b_uniform_congr {Ω : Type} [Fintype Ω] (E F : Ω → Prop)
    (h : ∀ x, E x ↔ F x) : uniformMass Ω E = uniformMass Ω F := by
  have : E = F := funext (fun x => propext (h x))
  rw [this]

lemma t13b_strict_cutoff {B k : ℕ} (hB : 0 < B) (hk : 0 < k)
    (he : (k : ℝ) = (B : ℝ)/40) (ref : Fin B → ℝ) (obs : ℝ) :
    rawP ref obs < 1/20 ↔ lowerCount ref obs ≤ k-1 ∨ upperCount ref obs ≤ k-1 := by
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hcount (n : ℕ) : (n : ℝ)/B < 1/40 ↔ n ≤ k-1 := by
    rw [div_lt_iff₀ hBr]
    have he' : (1/40 : ℝ)*B = k := by linarith [he]
    rw [he', Nat.cast_lt]
    omega
  unfold rawP doubledP
  rw [min_lt_iff]
  have hn : ¬(1 : ℝ) < 1/20 := by norm_num
  simp only [hn, false_or]
  have hm : 2*min ((lowerCount ref obs : ℝ)/B) ((upperCount ref obs : ℝ)/B) < 1/20 ↔
      min ((lowerCount ref obs : ℝ)/B) ((upperCount ref obs : ℝ)/B) < 1/40 := by
    constructor <;> intro h <;> linarith
  rw [hm, min_lt_iff, hcount, hcount]

lemma t13b_zero_cutoff {B : ℕ} (hB : 0 < B) (ref : Fin B → ℝ) (obs : ℝ) :
    rawP ref obs = 0 ↔ lowerCount ref obs ≤ 0 ∨ upperCount ref obs ≤ 0 := by
  have hnonneg : 0 ≤ rawP ref obs := by
    unfold rawP doubledP
    exact le_min (by norm_num) (mul_nonneg (by norm_num)
      (le_min (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
  have hw := weak_integer_tail hB 0 (by norm_num) (by norm_num)
    (lowerCount ref obs) (upperCount ref obs)
  have he : rawP ref obs ≤ 0 ↔ lowerCount ref obs ≤ 0 ∨ upperCount ref obs ≤ 0 := by
    simpa only [rawP, doubledP, zero_mul, zero_div, Nat.floor_zero] using hw
  exact (show rawP ref obs = 0 ↔ rawP ref obs ≤ 0 from
    ⟨fun h => h.le, fun h => le_antisymm h hnonneg⟩).trans he

lemma t13b_zero_formula {B : ℕ} (hB : 0 < B) :
    binomialMixture 6435 B 0 =
      2*(∑ r ∈ range 6434, (6434-r : ℝ)^B)/(6435 : ℝ)^(B+1) ∧
      0 < binomialMixture 6435 B 0 := by
  have he : binomialMixture 6435 B 0 =
      2*(∑ r ∈ range 6434, (6434-r : ℝ)^B)/(6435 : ℝ)^(B+1) := by
    unfold binomialMixture
    simp only [zero_add, range_one, sum_singleton, Nat.choose_zero_right,
      Nat.cast_one, pow_zero, mul_one, one_mul, Nat.sub_zero, Nat.cast_ofNat,
      Nat.cast_add]
    have hsum := Fin.sum_univ_eq_sum_range
      (fun r : ℕ => ((6435-((r : ℝ)+1))/6435)^B) 6435
    rw [hsum, show 6435 = 6434+1 by rfl, sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    have hlast : ((6435-(6434+1 : ℝ))/6435)^B = 0 := by
      norm_num only [show (6435-(6434+1 : ℝ))/6435 = 0 by norm_num,
        zero_pow (by omega : B ≠ 0)]
    rw [hlast, add_zero]
    have hterm (r : ℕ) : ((6435-(r+1 : ℝ))/6435)^B =
        (6434-r : ℝ)^B/(6435 : ℝ)^B := by
      rw [show (6435-(r+1 : ℝ)) = 6434-r by ring, div_pow]
    simp_rw [hterm]
    rw [← sum_div, pow_succ]
    ring
  refine ⟨he, ?_⟩
  rw [he]
  have hsum : 0 < ∑ r ∈ range 6434, (6434-r : ℝ)^B := by
    apply sum_pos'
    · intro r hr
      have hr' : (r : ℝ) < 6434 := by exact_mod_cast mem_range.mp hr
      exact pow_nonneg (by linarith) _
    · refine ⟨0, by simp only [mem_range]; omega, ?_⟩
      simp only [Nat.cast_zero, sub_zero]
      positivity
  exact div_pos (mul_pos (by norm_num) hsum) (pow_pos (by norm_num) _)

set_option maxHeartbeats 800000 in
/-- P016-T13: exact iid finite-design mixture and the cutoff claims. -/
theorem t13_finite_rejection_proof :
    let y : Outcome 16 := fun i => (2 : ℝ)^i.val
    (∀ B : ℕ, 0 < B → ∀ c : ℕ, 2*c < B →
      uniformMass (Fin (B+1) → Balanced 16 8) (fun draw =>
        lowerCount (fun b => rss y (draw b.succ).val) (rss y (draw 0).val) ≤ c ∨
        upperCount (fun b => rss y (draw b.succ).val) (rss y (draw 0).val) ≤ c) =
          binomialMixture 6435 B c) ∧
    (∀ B c : ℕ, 0 < B → c < B →
      2*(c+1)/(B+1)-2/(6435 : ℝ) ≤ binomialMixture 6435 B c ∧
      binomialMixture 6435 B c ≤ 2*(c+1)/(B+1)) ∧
    (∀ B ∈ ({1000,10000} : Finset ℕ),
      uniformMass (Fin (B+1) → Balanced 16 8) (fun draw =>
        rawP (fun b => rss y (draw b.succ).val) (rss y (draw 0).val) ≤ 1/20) =
        binomialMixture 6435 B (B/40)) ∧
    (∀ B ∈ ({1000,10000} : Finset ℕ),
      uniformMass (Fin (B+1) → Balanced 16 8) (fun draw =>
        rawP (fun b => rss y (draw b.succ).val) (rss y (draw 0).val) < 1/20) =
        binomialMixture 6435 B (B/40-1)) ∧
    1/20 < binomialMixture 6435 1000 25 ∧ 1/20 < binomialMixture 6435 10000 250 ∧
    binomialMixture 6435 1000 24 < 1/20 ∧ binomialMixture 6435 10000 249 < 1/20 ∧
    (∀ B : ℕ, 0 < B → uniformMass (Fin (B+1) → Balanced 16 8) (fun draw =>
      rawP (fun b => rss y (draw b.succ).val) (rss y (draw 0).val) = 0) =
      binomialMixture 6435 B 0 ∧ binomialMixture 6435 B 0 =
        2*(∑ r ∈ Finset.range 6434, (6434-r : ℝ)^B)/(6435 : ℝ)^(B+1) ∧
      0 < binomialMixture 6435 B 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B _ c hc
    exact t13b_concrete_mixture hc
  · intro B c _ hc
    exact t13b_mixture_grid_bounds (by decide : 0 < 6435) hc
  · intro B hB
    have hcases : B = 1000 ∨ B = 10000 := by simpa only [mem_insert, mem_singleton] using hB
    have hpos : 0 < B := by rcases hcases with rfl | rfl <;> decide
    have hcut : 2*(B/40) < B := by rcases hcases with rfl | rfl <;> decide
    have hfloor : Nat.floor ((1/20 : ℝ)*B/2) = B/40 := by
      rcases hcases with rfl | rfl <;> norm_num
    have hevent (draw : Fin (B+1) → Balanced 16 8) :
        rawP (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0)) ≤ 1/20 ↔
          lowerCount (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0)) ≤ B/40 ∨
          upperCount (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0)) ≤ B/40 := by
      simpa only [rawP, doubledP, hfloor] using weak_integer_tail hpos (1/20)
        (by norm_num) (by norm_num)
        (lowerCount (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0)))
        (upperCount (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0)))
    exact (t13b_uniform_congr _ _ hevent).trans (t13b_concrete_mixture hcut)
  · intro B hB
    have hcases : B = 1000 ∨ B = 10000 := by simpa only [mem_insert, mem_singleton] using hB
    have hpos : 0 < B := by rcases hcases with rfl | rfl <;> decide
    have hk : 0 < B/40 := by rcases hcases with rfl | rfl <;> decide
    have hcut : 2*(B/40-1) < B := by rcases hcases with rfl | rfl <;> decide
    have he : (B/40 : ℕ) = (B : ℝ)/40 := by rcases hcases with rfl | rfl <;> norm_num
    have hevent (draw : Fin (B+1) → Balanced 16 8) := t13b_strict_cutoff hpos hk he
      (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0))
    exact (t13b_uniform_congr _ _ hevent).trans (t13b_concrete_mixture hcut)
  · have h := (t13b_mixture_grid_bounds (M := 6435) (B := 1000) (c := 25)
      (by decide) (by decide)).1
    norm_num at h
    linarith
  · exact t13b_10000_weak
  · have h := (t13b_mixture_grid_bounds (M := 6435) (B := 1000) (c := 24)
      (by decide) (by decide)).2
    norm_num at h
    linarith
  · have h := (t13b_mixture_grid_bounds (M := 6435) (B := 10000) (c := 249)
      (by decide) (by decide)).2
    norm_num at h
    linarith
  · intro B hB
    have hcut : 2*0 < B := by omega
    have hevent (draw : Fin (B+1) → Balanced 16 8) :
        rawP (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0)) = 0 ↔
          lowerCount (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0)) ≤ 0 ∨
          upperCount (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0)) ≤ 0 :=
      t13b_zero_cutoff hB (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0))
    have hm : uniformMass (Fin (B+1) → Balanced 16 8) (fun draw =>
        rawP (fun b => t13b_ssr (draw b.succ)) (t13b_ssr (draw 0)) = 0) =
          binomialMixture 6435 B 0 := by
      exact (t13b_uniform_congr _ _ hevent).trans
        (t13b_concrete_mixture (B := B) (c := 0) hcut)
    exact ⟨hm, (t13b_zero_formula hB).1, (t13b_zero_formula hB).2⟩

end AronowAudit.P016.Wave1
