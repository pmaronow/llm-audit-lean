import AronowAudit.P023.P023_Audit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

namespace AronowAudit.P023.Wave1

noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter

local instance instDecidableGLP023B4 (p : Prop) : Decidable p := Classical.propDecidable p

/-! The Jackson kernel with its removable singularities filled. -/

private def jka_fejer : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => 2 * Polynomial.X + 2
  | n + 2 => 2 * Polynomial.X * jka_fejer (n + 1) - jka_fejer n + 2

private lemma jka_fejer_degree (n : ℕ) : (jka_fejer n).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [jka_fejer]
  | one =>
    change (2 * Polynomial.X + 2 : Polynomial ℝ).natDegree ≤ 1
    compute_degree
  | more n ih0 ih1 =>
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · apply (Polynomial.natDegree_mul_le).trans
        have h : (2 * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by compute_degree
        omega
      · omega
    · simp

private lemma jka_fejer_one (n : ℕ) : (jka_fejer n).eval 1 = ((n : ℝ) + 1)^2 := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [jka_fejer]
  | one => norm_num [jka_fejer]
  | more n ih0 ih1 =>
    simp only [jka_fejer, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, ih0, ih1, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    ring

private lemma jka_sin_sq_recurrence (a b : ℝ) :
    Real.sin (a + b)^2 = 2 * Real.cos (2*b) * Real.sin a^2 -
      Real.sin (a-b)^2 + 2 * Real.sin b^2 := by
  rw [Real.sin_add, Real.sin_sub, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b,
    mul_nonneg (sq_nonneg (Real.sin a)) (sq_nonneg (Real.sin b))]

private lemma jka_fejer_sin (n : ℕ) (t : ℝ) :
    (jka_fejer n).eval (Real.cos t) * Real.sin (t/2)^2 =
      Real.sin (((n : ℝ)+1)*t/2)^2 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [jka_fejer]
  | one =>
    norm_num only [jka_fejer, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, Nat.cast_one]
    have h := jka_sin_sq_recurrence (t/2) (t/2)
    have hc : 2*(t/2) = t := by ring
    have hz : t/2-t/2 = 0 := by ring
    rw [hc, hz, Real.sin_zero] at h
    convert h.symm using 1 <;> ring
  | more n ih0 ih1 =>
    have ha : (((n:ℝ)+2)*t/2 + t/2) = ((n:ℝ)+3)*t/2 := by ring
    have hb : (((n:ℝ)+2)*t/2 - t/2) = ((n:ℝ)+1)*t/2 := by ring
    have hc : 2*(t/2) = t := by ring
    have h := jka_sin_sq_recurrence (((n:ℝ)+2)*t/2) (t/2)
    rw [ha, hb, hc] at h
    simp only [Nat.cast_add, Nat.cast_one] at ih1
    simp only [jka_fejer, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, Nat.cast_add, Nat.cast_ofNat]
    rw [show (n:ℝ)+1+1 = (n:ℝ)+2 by ring] at ih1
    rw [show (n:ℝ)+2+1 = (n:ℝ)+3 by ring]
    calc
      _ = 2*Real.cos t*((jka_fejer (n+1)).eval (Real.cos t)*Real.sin (t/2)^2) -
          (jka_fejer n).eval (Real.cos t)*Real.sin (t/2)^2 + 2*Real.sin (t/2)^2 := by ring
      _ = _ := by rw [ih1, ih0]; exact h.symm

private lemma jka_raw_polynomial (s : ℕ) (hs : 1 ≤ s) (t : ℝ) :
    jacksonRaw s t = ((jka_fejer (s-1)).eval (Real.cos t))^2 := by
  have hn : ((s-1 : ℕ) : ℝ) + 1 = (s : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hs
  have he := jka_fejer_sin (s-1) t
  rw [hn] at he
  unfold jacksonRaw
  split_ifs with ht
  · have hc : Real.cos t = 1 := by
      have hc := Real.cos_two_mul (t/2)
      have hid := Real.sin_sq_add_cos_sq (t/2)
      have htwo : 2*(t/2) = t := by ring
      rw [ht] at hid
      rw [htwo] at hc
      nlinarith
    rw [hc, jka_fejer_one, hn]
    ring
  · field_simp [ht] at he ⊢
    nlinarith [sq_nonneg ((jka_fejer (s-1)).eval (Real.cos t))]

private lemma jka_raw_continuous (s : ℕ) (hs : 1 ≤ s) : Continuous (jacksonRaw s) := by
  have he : jacksonRaw s = fun t => ((jka_fejer (s-1)).eval (Real.cos t))^2 :=
    funext (jka_raw_polynomial s hs)
  rw [he]
  exact ((jka_fejer (s-1)).continuous.comp Real.continuous_cos).pow 2

private lemma jka_raw_nonneg (s : ℕ) (t : ℝ) : 0 ≤ jacksonRaw s t := by
  unfold jacksonRaw
  positivity

private lemma jka_raw_even (s : ℕ) (hs : 1 ≤ s) (t : ℝ) :
    jacksonRaw s (-t) = jacksonRaw s t := by
  simp only [jka_raw_polynomial s hs, Real.cos_neg]

private lemma jka_sin_nat_bound (n : ℕ) (t : ℝ) :
    |Real.sin ((n:ℝ)*t)| ≤ (n:ℝ)*|Real.sin t| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.sin_add]
    calc
      _ ≤ |Real.sin ((n:ℝ)*t)*Real.cos t| +
          |Real.cos ((n:ℝ)*t)*Real.sin t| := abs_add_le _ _
      _ ≤ |Real.sin ((n:ℝ)*t)| + |Real.sin t| := by
        simp only [abs_mul]
        exact add_le_add
          ((mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (abs_nonneg _)).trans_eq
            (mul_one _))
          ((mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq
            (one_mul _))
      _ ≤ ((n:ℝ)+1)*|Real.sin t| := by nlinarith

private lemma jka_raw_upper (s : ℕ) (t : ℝ) : jacksonRaw s t ≤ (s:ℝ)^4 := by
  unfold jacksonRaw
  split_ifs with ht
  · rfl
  · have he := jka_sin_nat_bound s (t/2)
    have ha : |Real.sin ((s:ℝ)*t/2)/Real.sin (t/2)| ≤ (s:ℝ) := by
      rw [abs_div]
      apply (div_le_iff₀ (abs_pos.mpr ht)).mpr
      convert he using 1 <;> ring
    simpa only [show (4:ℕ) = 2*2 from rfl, pow_abs_two_mul] using pow_le_pow_left₀ (abs_nonneg _) ha 4

private lemma jka_raw_core (s : ℕ) (hs : 1 ≤ s) (t : ℝ)
    (ht : 0 ≤ t) (htop : t ≤ Real.pi/(s:ℝ)) :
    (2*(s:ℝ)/Real.pi)^4 ≤ jacksonRaw s t := by
  have hsr : 0 < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hpi := Real.pi_pos
  by_cases ht0 : t = 0
  · subst t
    simp only [jacksonRaw, zero_div, Real.sin_zero, if_true]
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_iff₀ hpi).mpr
    nlinarith [Real.pi_gt_three]
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hsmall : t/2 ≤ Real.pi/2 := by
      have hdiv : Real.pi/(s:ℝ) ≤ Real.pi :=
        (div_le_iff₀ hsr).mpr (by nlinarith [Real.pi_pos, show (1:ℝ) ≤ s by exact_mod_cast hs])
      linarith
    have hd : 0 < Real.sin (t/2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hn := Real.mul_le_sin (show 0 ≤ (s:ℝ)*t/2 by positivity)
      (show (s:ℝ)*t/2 ≤ Real.pi/2 by
        have := (le_div_iff₀ hsr).mp htop
        nlinarith)
    have hq : 2*(s:ℝ)/Real.pi ≤ Real.sin ((s:ℝ)*t/2)/Real.sin (t/2) := by
      apply (le_div_iff₀ hd).mpr
      calc
        _ ≤ (2*(s:ℝ)/Real.pi)*(t/2) :=
          mul_le_mul_of_nonneg_left (Real.sin_le (by linarith)) (by positivity)
        _ ≤ Real.sin ((s:ℝ)*t/2) := by convert hn using 1 <;> ring
    simp only [jacksonRaw, if_neg (ne_of_gt hd)]
    exact pow_le_pow_left₀ (by positivity) hq 4

private lemma jka_raw_tail (s : ℕ) (t : ℝ) (ht : 0 < t) (htop : t ≤ Real.pi) :
    jacksonRaw s t ≤ Real.pi^4/t^4 := by
  have hd : 0 < Real.sin (t/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hj := Real.mul_le_sin (show 0 ≤ t/2 by linarith)
    (show t/2 ≤ Real.pi/2 by linarith)
  have hprod : t ≤ Real.pi * Real.sin (t/2) := by
    have h := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
    field_simp at h
    nlinarith
  have ha : |Real.sin ((s:ℝ)*t/2)/Real.sin (t/2)| ≤ Real.pi/t := by
    rw [abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ht).mpr
    calc
      |Real.sin ((s:ℝ)*t/2)| * t ≤ 1*t :=
        mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) ht.le
      _ ≤ Real.pi*Real.sin (t/2) := by simpa using hprod
  simp only [jacksonRaw, if_neg (ne_of_gt hd)]
  simpa only [show (4:ℕ) = 2*2 from rfl, pow_abs_two_mul, div_pow] using pow_le_pow_left₀ (abs_nonneg _) ha 4

private lemma jka_even_integral (f : ℝ → ℝ) (hf : Continuous f)
    (he : ∀ t, f (-t) = f t) (a : ℝ) :
    (∫ t in -a..a, f t) = 2*(∫ t in 0..a, f t) := by
  have hneg : (∫ t in -a..0, f t) = ∫ t in 0..a, f t := by
    calc
      _ = ∫ t in 0..a, f (-t) := by
        rw [intervalIntegral.integral_comp_neg]
        simp
      _ = _ := by simp only [he]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-a) 0) (hf.intervalIntegrable 0 a), hneg]
  ring

private lemma jka_Icc_integral (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    (∫ t in Set.Icc a b, f t) = ∫ t in a..b, f t := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

private lemma jka_raw_mass_lower (s : ℕ) (hs : 1 ≤ s) :
    32*(s:ℝ)^3/Real.pi^3 ≤ ∫ t in Set.Icc (-Real.pi) Real.pi, jacksonRaw s t := by
  have hsr : 0 < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hb : 0 < Real.pi/(s:ℝ) := div_pos Real.pi_pos hsr
  have hbtop : Real.pi/(s:ℝ) ≤ Real.pi :=
    (div_le_iff₀ hsr).mpr (by nlinarith [Real.pi_pos, show (1:ℝ) ≤ s by exact_mod_cast hs])
  have hc := jka_raw_continuous s hs
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hb.le
    (continuous_const.intervalIntegrable 0 (Real.pi/(s:ℝ)))
    (hc.intervalIntegrable 0 (Real.pi/(s:ℝ)))
    (fun t ht => jka_raw_core s hs t ht.1 ht.2)
  have hsub := intervalIntegral.integral_mono_interval (μ := volume) (show (0:ℝ) ≤ 0 from le_rfl)
    hb.le hbtop (ae_of_all _ (jka_raw_nonneg s)) (hc.intervalIntegrable 0 Real.pi)
  rw [jka_Icc_integral _ _ _ (by linarith [Real.pi_pos]),
    jka_even_integral _ hc (jka_raw_even s hs)]
  have hid : 2*(∫ t in (0:ℝ)..Real.pi/(s:ℝ), (2*(s:ℝ)/Real.pi)^4) =
      32*(s:ℝ)^3/Real.pi^3 := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    field_simp
    <;> ring
  nlinarith [hmono, hsub]

private lemma jka_raw_mass_pos (s : ℕ) (hs : 1 ≤ s) :
    0 < ∫ t in Set.Icc (-Real.pi) Real.pi, jacksonRaw s t := by
  have hsr : 0 < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  exact lt_of_lt_of_le (by positivity) (jka_raw_mass_lower s hs)

private lemma jka_kernel_continuous (s : ℕ) (hs : 1 ≤ s) :
    Continuous (jacksonKernel s) := (jka_raw_continuous s hs).div_const _

private lemma jka_kernel_nonneg (s : ℕ) (hs : 1 ≤ s) (t : ℝ) :
    0 ≤ jacksonKernel s t := by
  exact div_nonneg (jka_raw_nonneg s t)
    (div_nonneg (jka_raw_mass_pos s hs).le (by positivity))

private lemma jka_kernel_mass (s : ℕ) (hs : 1 ≤ s) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, jacksonKernel s t) = 2*Real.pi := by
  unfold jacksonKernel
  rw [integral_div]
  field_simp [ne_of_gt (jka_raw_mass_pos s hs)]

private lemma jka_raw_moment_upper (s : ℕ) (hs : 1 ≤ s) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, |t| *jacksonRaw s t) ≤
      2*Real.pi^2*(s:ℝ)^2 := by
  have hsr : 0 < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  let b := Real.pi/(s:ℝ)
  have hb : 0 < b := div_pos Real.pi_pos hsr
  have hbtop : b ≤ Real.pi :=
    (div_le_iff₀ hsr).mpr (by nlinarith [Real.pi_pos, show (1:ℝ) ≤ s by exact_mod_cast hs])
  have hc := jka_raw_continuous s hs
  have hprod : Continuous (fun t => t*jacksonRaw s t) := continuous_id.mul hc
  have htail : ContinuousOn (fun t : ℝ => Real.pi^4/t^3) (Icc b Real.pi) :=
    continuousOn_const.div (continuousOn_id.pow 3)
      (fun t ht => pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hb ht.1)))
  have hleft := intervalIntegral.integral_mono_on (μ := volume) hb.le
    (hprod.intervalIntegrable 0 b)
    ((continuous_id.mul continuous_const).intervalIntegrable 0 b)
    (fun t ht => mul_le_mul_of_nonneg_left (jka_raw_upper s t) ht.1)
  have hright := intervalIntegral.integral_mono_on (μ := volume) hbtop
    (hprod.intervalIntegrable b Real.pi) (htail.intervalIntegrable_of_Icc hbtop)
    (fun t ht => show t*jacksonRaw s t ≤ Real.pi^4/t^3 from
      calc
        _ ≤ t*(Real.pi^4/t^4) :=
          mul_le_mul_of_nonneg_left (jka_raw_tail s t (lt_of_lt_of_le hb ht.1) ht.2)
            (le_trans hb.le ht.1)
        _ = _ := by field_simp <;> ring)
  have hleftval : (∫ t in (0:ℝ)..b, t*(s:ℝ)^4) = (s:ℝ)^4*b^2/2 := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  have hzero : (0:ℝ) ∉ Set.uIcc b Real.pi := by
    rw [Set.uIcc_of_le hbtop]
    intro h
    linarith [h.1]
  have hrightval : (∫ t in b..Real.pi, Real.pi^4/t^3) =
      Real.pi^4*(b⁻¹^2-Real.pi⁻¹^2)/2 := by
    have he : (fun t : ℝ => Real.pi^4/t^3) =
        fun t => Real.pi^4*t^(-3:ℤ) := by
      funext t
      simp [zpow_neg, div_eq_mul_inv]
    rw [he, intervalIntegral.integral_const_mul,
      integral_zpow (Or.inr ⟨by norm_num, hzero⟩)]
    norm_num
    ring
  have hfull : (∫ t in Set.Icc (-Real.pi) Real.pi, |t| *jacksonRaw s t) =
      2*((∫ t in (0:ℝ)..b, t*jacksonRaw s t) +
        ∫ t in b..Real.pi, t*jacksonRaw s t) := by
    rw [jka_Icc_integral _ _ _ (by linarith [Real.pi_pos]),
      jka_even_integral (fun t => |t| * jacksonRaw s t) (continuous_abs.mul hc)
        (fun t => by rw [abs_neg, jka_raw_even s hs])]
    congr 1
    calc
      (∫ t in (0:ℝ)..Real.pi, |t| * jacksonRaw s t) =
          ∫ t in (0:ℝ)..Real.pi, t*jacksonRaw s t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le Real.pi_pos.le] at ht
        simp only [abs_of_nonneg ht.1]
      _ = _ := (intervalIntegral.integral_add_adjacent_intervals
        (hprod.intervalIntegrable 0 b) (hprod.intervalIntegrable b Real.pi)).symm
  have hsum : (s:ℝ)^4*b^2/2 + Real.pi^4*(b⁻¹^2-Real.pi⁻¹^2)/2 ≤
      Real.pi^2*(s:ℝ)^2 := by
    dsimp [b]
    have he : (s:ℝ)^4*(Real.pi/(s:ℝ))^2/2 +
        Real.pi^4*((Real.pi/(s:ℝ))⁻¹^2-Real.pi⁻¹^2)/2 =
        Real.pi^2*(s:ℝ)^2 - Real.pi^2/2 := by
      field_simp
      <;> ring
    rw [he]
    nlinarith [sq_nonneg Real.pi]
  rw [hfull]
  change (∫ t in (0:ℝ)..b, t*jacksonRaw s t) ≤ (∫ t in (0:ℝ)..b, t*(s:ℝ)^4) at hleft
  rw [hleftval] at hleft
  rw [hrightval] at hright
  linarith

private lemma jka_kernel_moment (s : ℕ) (hs : 1 ≤ s) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, |t| *jacksonKernel s t)/(2*Real.pi) ≤
      jacksonK/(s:ℝ) := by
  have hsr : 0 < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  let B := ∫ t in Set.Icc (-Real.pi) Real.pi, jacksonRaw s t
  have hB : 0 < B := jka_raw_mass_pos s hs
  have hlow : 32*(s:ℝ)^3/Real.pi^3 ≤ B := jka_raw_mass_lower s hs
  have hu := jka_raw_moment_upper s hs
  have he : (∫ t in Set.Icc (-Real.pi) Real.pi, |t| *jacksonKernel s t)/(2*Real.pi) =
      (∫ t in Set.Icc (-Real.pi) Real.pi, |t| *jacksonRaw s t)/B := by
    simp only [jacksonKernel, ← mul_div_assoc, integral_div]
    dsimp [B]
    field_simp
  rw [he]
  apply (div_le_iff₀ hB).mpr
  have hcoef : 0 ≤ jacksonK/(s:ℝ) := by unfold jacksonK; positivity
  have hm := mul_le_mul_of_nonneg_left hlow hcoef
  apply le_trans hu
  apply le_trans _ hm
  have hp := Real.pi_pos
  have hpi : Real.pi^2 ≤ 12 := by nlinarith [Real.pi_lt_d2]
  have hident : (jacksonK/(s:ℝ))*(32*(s:ℝ)^3/Real.pi^3) =
      24*(s:ℝ)^2*(1+Real.pi^4)/Real.pi^4 := by
    unfold jacksonK
    field_simp
    <;> ring
  rw [hident]
  apply (le_div_iff₀ (pow_pos hp 4)).mpr
  have hbound : Real.pi^2*Real.pi^4 ≤ 12*(1+Real.pi^4) := by
    have hh := mul_le_mul_of_nonneg_right hpi (pow_nonneg hp.le 4)
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 2*(s:ℝ)^2 by positivity)
  convert hh using 1 <;> ring

private lemma jka_H_continuous (h : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |h x-h y| ≤ L*|x-y|) : Continuous (fun θ => h (Real.cos θ)) := by
  apply LipschitzWith.continuous (K := ⟨L, hL⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_mk]
  exact (hlip _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩).trans
    (mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le x y) hL)

private lemma jka_cosine_convolution (H : ℝ → ℝ) (hH : Continuous H)
    (hHe : ∀ t, H (-t) = H t) (hHp : Function.Periodic H (2*Real.pi))
    (j : ℕ) (θ : ℝ) :
    (∫ t in -Real.pi..Real.pi, H (θ-t)*Real.cos ((j:ℝ)*t)) =
      Real.cos ((j:ℝ)*θ)*(∫ t in -Real.pi..Real.pi, H t*Real.cos ((j:ℝ)*t)) := by
  let f := fun u => H u*Real.cos ((j:ℝ)*(θ-u))
  have hper : Function.Periodic f (2*Real.pi) := by
    intro u
    dsimp [f]
    rw [hHp u]
    congr 1
    convert Real.cos_sub_nat_mul_two_pi ((j:ℝ)*(θ-u)) j using 1 <;> congr 1 <;> ring
  have hshift := hper.intervalIntegral_add_eq (θ-Real.pi) (-Real.pi)
  have hend1 : θ-Real.pi+2*Real.pi = θ+Real.pi := by ring
  have hend2 : -Real.pi+2*Real.pi = Real.pi := by ring
  rw [hend1, hend2] at hshift
  have hsub : (∫ t in -Real.pi..Real.pi, H (θ-t)*Real.cos ((j:ℝ)*t)) =
      ∫ u in -Real.pi..Real.pi, f u := by
    calc
      _ = ∫ t in -Real.pi..Real.pi, f (θ-t) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp [f]
        congr 2
        ring
      _ = ∫ u in θ-Real.pi..θ+Real.pi, f u := by
        rw [intervalIntegral.integral_comp_sub_left]
        congr 1 <;> ring
      _ = _ := hshift
  have hsin : (∫ t in -Real.pi..Real.pi, H t*Real.sin ((j:ℝ)*t)) = 0 := by
    have he : (∫ t in -Real.pi..Real.pi, H t*Real.sin ((j:ℝ)*t)) =
        -(∫ t in -Real.pi..Real.pi, H t*Real.sin ((j:ℝ)*t)) := by
      calc
        _ = ∫ t in -Real.pi..Real.pi, H (-t)*Real.sin ((j:ℝ)*(-t)) := by
          simpa only [neg_neg] using
            (intervalIntegral.integral_comp_neg (a := -Real.pi) (b := Real.pi)
              (fun t => H t*Real.sin ((j:ℝ)*t))).symm
        _ = _ := by simp only [hHe, mul_neg, Real.sin_neg, neg_mul,
            intervalIntegral.integral_neg, mul_neg]
    linarith
  rw [hsub]
  have hexp : f = fun u =>
      Real.cos ((j:ℝ)*θ)*(H u*Real.cos ((j:ℝ)*u)) +
        Real.sin ((j:ℝ)*θ)*(H u*Real.sin ((j:ℝ)*u)) := by
    funext u
    dsimp [f]
    rw [mul_sub, Real.cos_sub]
    ring
  rw [hexp, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsin]
  · ring
  · exact (continuous_const.mul
      (hH.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _
  · exact (continuous_const.mul
      (hH.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _

private lemma jka_kernel_polynomial (s : ℕ) (hs : 1 ≤ s) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ 2*s-2 ∧
      ∀ t, jacksonKernel s t = q.eval (Real.cos t) := by
  let A := (∫ t in Set.Icc (-Real.pi) Real.pi, jacksonRaw s t)/(2*Real.pi)
  refine ⟨Polynomial.C A⁻¹ * (jka_fejer (s-1))^2, ?_, ?_⟩
  · apply (Polynomial.natDegree_mul_le).trans
    simp only [Polynomial.natDegree_C, zero_add]
    apply (Polynomial.natDegree_pow_le).trans
    have hd := jka_fejer_degree (s-1)
    omega
  · intro t
    simp only [jacksonKernel, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      jka_raw_polynomial s hs]
    dsimp [A]
    simp only [jka_raw_polynomial s hs]
    ring

private lemma jka_chebyshev_expansion (q : Polynomial ℝ) (D : ℕ) (hq : q.natDegree ≤ D) :
    ∃ d : ℕ → ℝ, q = ∑ j ∈ Finset.range (D+1),
      d j • Polynomial.Chebyshev.T ℝ (j:ℤ) := by
  have hm : q ∈ Polynomial.degreeLT ℝ (D+1) := by
    rw [Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt (Polynomial.degree_le_natDegree)
      (by exact_mod_cast (show q.natDegree < D+1 by omega))
  rw [← Polynomial.Sequence.span_degreeLT (Polynomial.Chebyshev.chebyshevTsequence ℝ)
      (by simp), show Set.Iio (D+1) = Finset.range (D+1) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hm
  obtain ⟨d, hd⟩ := hm
  exact ⟨d, hd.symm⟩

private lemma jka_convolution_polynomial (s : ℕ) (hs : 1 ≤ s)
    (h : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |h x-h y| ≤ L*|x-y|) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ 2*s-2 ∧
      ∀ θ, jacksonConvolution s h θ = p.eval (Real.cos θ) := by
  obtain ⟨q, hq, heq⟩ := jka_kernel_polynomial s hs
  obtain ⟨d, hd⟩ := jka_chebyshev_expansion q (2*s-2) hq
  let H := fun θ => h (Real.cos θ)
  have hH : Continuous H := jka_H_continuous h L hL hlip
  let a := fun j : ℕ => d j * (∫ t in -Real.pi..Real.pi, H t*Real.cos ((j:ℝ)*t))/(2*Real.pi)
  let p : Polynomial ℝ := ∑ j ∈ Finset.range (2*s-2+1), a j • Polynomial.Chebyshev.T ℝ (j:ℤ)
  refine ⟨p, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    apply (Polynomial.natDegree_smul_le _ _).trans
    simpa only [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast] using
      (show j ≤ 2*s-2 by have := Finset.mem_range.mp hj; omega)
  · intro θ
    have hker : ∀ t, jacksonKernel s t = ∑ j ∈ Finset.range (2*s-2+1),
        d j * Real.cos ((j:ℝ)*t) := by
      intro t
      rw [heq, hd, Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_smul, smul_eq_mul, Polynomial.Chebyshev.T_real_cos,
        Int.cast_natCast]
    have hcalc := fun j => jka_cosine_convolution H hH
      (fun t => by dsimp [H]; rw [Real.cos_neg])
      (fun t => by dsimp [H]; rw [Real.cos_add_two_pi]) j θ
    unfold jacksonConvolution
    rw [jka_Icc_integral _ _ _ (by linarith [Real.pi_pos])]
    simp only [hker, Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · dsimp [p]
      rw [Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_smul, smul_eq_mul, Polynomial.Chebyshev.T_real_cos,
        Int.cast_natCast, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have he : (fun t => h (Real.cos (θ-t))*(d j*Real.cos ((j:ℝ)*t))) =
          fun t => d j*(H (θ-t)*Real.cos ((j:ℝ)*t)) := by
        funext t
        dsimp [H]
        ring
      rw [he, intervalIntegral.integral_const_mul, hcalc j]
      dsimp [a]
      ring
    · intro j hj
      exact ((hH.comp (continuous_const.sub continuous_id)).mul
        (continuous_const.mul (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)))).intervalIntegrable _ _

private lemma jka_convolution_error (s : ℕ) (hs : 1 ≤ s)
    (h : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |h x-h y| ≤ L*|x-y|) (θ : ℝ) :
    |h (Real.cos θ)-jacksonConvolution s h θ| ≤ jacksonK*L/(s:ℝ) := by
  let H := fun θ => h (Real.cos θ)
  let K := jacksonKernel s
  have hH : Continuous H := jka_H_continuous h L hL hlip
  have hK : Continuous K := jka_kernel_continuous s hs
  have hKn : ∀ t, 0 ≤ K t := jka_kernel_nonneg s hs
  have hpi : 0 < 2*Real.pi := by positivity
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hmass : (∫ t in -Real.pi..Real.pi, K t) = 2*Real.pi := by
    rw [← jka_Icc_integral _ _ _ hab]
    exact jka_kernel_mass s hs
  have hdiff : Continuous (fun t => (H θ-H (θ-t))*K t) :=
    (continuous_const.sub (hH.comp (continuous_const.sub continuous_id))).mul hK
  have he : h (Real.cos θ)-jacksonConvolution s h θ =
      (∫ t in -Real.pi..Real.pi, (H θ-H (θ-t))*K t)/(2*Real.pi) := by
    simp_rw [sub_mul]
    have hi1 : IntervalIntegrable (fun t => H θ*K t) volume (-Real.pi) Real.pi :=
      (continuous_const.mul hK).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t => H (θ-t)*K t) volume (-Real.pi) Real.pi :=
      ((hH.comp (continuous_const.sub continuous_id)).mul hK).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul, hmass]
    unfold jacksonConvolution
    rw [jka_Icc_integral _ _ _ hab]
    dsimp [H, K]
    field_simp
    <;> ring
  have hbound : ∀ t, |(H θ-H (θ-t))*K t| ≤ L*(|t| *K t) := by
    intro t
    rw [abs_mul, abs_of_nonneg (hKn t)]
    have hcos := Real.abs_cos_sub_cos_le θ (θ-t)
    have hl := hlip (Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
      (Real.cos (θ-t)) ⟨Real.neg_one_le_cos (θ-t), Real.cos_le_one (θ-t)⟩
    have hx : |H θ-H (θ-t)| ≤ L*|t| := by
      apply le_trans hl
      have ht : θ-(θ-t) = t := by ring
      rw [ht] at hcos
      exact mul_le_mul_of_nonneg_left hcos hL
    exact (mul_le_mul_of_nonneg_right hx (hKn t)).trans_eq (by ring)
  calc
    _ = |∫ t in -Real.pi..Real.pi, (H θ-H (θ-t))*K t|/(2*Real.pi) := by
      rw [he, abs_div, abs_of_pos hpi]
    _ ≤ (∫ t in -Real.pi..Real.pi, |(H θ-H (θ-t))*K t|)/(2*Real.pi) :=
      div_le_div_of_nonneg_right (intervalIntegral.abs_integral_le_integral_abs hab) hpi.le
    _ ≤ (∫ t in -Real.pi..Real.pi, L*(|t| *K t))/(2*Real.pi) := by
      apply div_le_div_of_nonneg_right _ hpi.le
      exact intervalIntegral.integral_mono_on (μ := volume) hab
        (hdiff.abs.intervalIntegrable _ _)
        ((continuous_const.mul (continuous_abs.mul hK)).intervalIntegrable _ _)
        (fun t _ => hbound t)
    _ = L*((∫ t in Set.Icc (-Real.pi) Real.pi, |t| *jacksonKernel s t)/(2*Real.pi)) := by
      rw [intervalIntegral.integral_const_mul, jka_Icc_integral _ _ _ hab]
      dsimp [K]
      ring
    _ ≤ L*(jacksonK/(s:ℝ)) := mul_le_mul_of_nonneg_left (jka_kernel_moment s hs) hL
    _ = _ := by ring

/-- The explicit normalized Jackson kernel, with its convolution represented by
an algebraic polynomial and approximation bound using the constant `jacksonK`. -/
theorem jackson_kernel_approximation_proof (s : ℕ) (hs : 1 ≤ s) (h : ℝ → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |h x-h y| ≤ L*|x-y|) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, jacksonKernel s t)=2*Real.pi ∧
    (∫ t in Set.Icc (-Real.pi) Real.pi, |t| * jacksonKernel s t)/(2*Real.pi) ≤ jacksonK/(s:ℝ) ∧
    ∃ p : Polynomial ℝ, p.natDegree ≤ 2*s-2 ∧
      (∀ θ, jacksonConvolution s h θ=p.eval (Real.cos θ)) ∧
      (∀ x ∈ Set.Icc (-1) 1, |h x-p.eval x| ≤ jacksonK*L/(s:ℝ)) := by
  refine ⟨jka_kernel_mass s hs, jka_kernel_moment s hs, ?_⟩
  obtain ⟨p, hp, he⟩ := jka_convolution_polynomial s hs h L hL hlip
  refine ⟨p, hp, he, ?_⟩
  intro x hx
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  have hb := jka_convolution_error s hs h L hL hlip (Real.arccos x)
  rw [he, hcos] at hb
  exact hb

end
end AronowAudit.P023.Wave1
