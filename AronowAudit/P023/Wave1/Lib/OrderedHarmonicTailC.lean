import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Ordered harmonic sine tails.  The only unordered sums in this file are
absolutely convergent series of reciprocal differences. -/

namespace AronowAudit.P023.Wave1
noncomputable section
open Finset Set Filter
open scoped BigOperators Topology

def tc09_reciprocalDrop (m : ℕ) : ℝ := 1 / (m : ℝ) - 1 / ((m : ℝ) + 1)

theorem tc09_drop_eq (m : ℕ) (hm : 1 ≤ m) :
    tc09_reciprocalDrop m = 1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
  have hp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  dsimp [tc09_reciprocalDrop]
  field_simp
  ring

theorem tc09_drop_nonneg (m : ℕ) (hm : 1 ≤ m) : 0 ≤ tc09_reciprocalDrop m := by
  rw [tc09_drop_eq m hm]
  positivity

theorem tc09_drop_antitone {n : ℕ} (hn : 1 ≤ n) :
    AntitoneOn tc09_reciprocalDrop (Set.Ici n) := by
  intro a ha b hb hab
  change n ≤ a at ha
  change n ≤ b at hb
  rw [tc09_drop_eq a (by omega), tc09_drop_eq b (by omega)]
  have ha' : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith

theorem tc09_drop_telescope (n M : ℕ) (hnM : n ≤ M) :
    ∑ m ∈ Ico n M, tc09_reciprocalDrop m = 1 / (n : ℝ) - 1 / (M : ℝ) := by
  induction M, hnM using Nat.le_induction with
  | base => simp
  | succ M hnM ih =>
    rw [Finset.sum_Ico_succ_top hnM, ih]
    simp only [tc09_reciprocalDrop, Nat.cast_add, Nat.cast_one]
    ring

theorem tc09_drop_summable (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun k : ℕ => tc09_reciprocalDrop (n + k)) := by
  apply summable_of_sum_range_le (fun k => tc09_drop_nonneg _ (by omega))
    (c := 1 / (n : ℝ))
  intro M
  have h := tc09_drop_telescope n (n + M) (by omega)
  rw [Finset.sum_Ico_eq_sum_range] at h
  simp only [Nat.add_sub_cancel_left] at h
  simpa only [Nat.add_comm] using h.le.trans (sub_le_self _ (by positivity))

theorem tc09_reciprocal_square_tail (n M : ℕ) (hn : 1 ≤ n) (hnM : n ≤ M) :
    (∑ m ∈ Finset.Ico n M, 1 / (m : ℝ)^2) ≤ 2 / (n : ℝ) := by
  calc
    _ ≤ ∑ m ∈ Finset.Ico n M, 2 * tc09_reciprocalDrop m := by
      apply Finset.sum_le_sum
      intro m hm
      have hmn := (Finset.mem_Ico.mp hm).1
      have hp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hp' : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      rw [tc09_drop_eq m (by omega)]
      apply (div_le_iff₀ (by positivity : 0 < (m : ℝ)^2)).mpr
      field_simp
      nlinarith
    _ = 2 * (1 / (n : ℝ) - 1 / (M : ℝ)) := by
      rw [← Finset.mul_sum, tc09_drop_telescope n M hnM]
    _ ≤ _ := by
      have h : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
      calc
        _ ≤ 2 * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left (sub_le_self _ h) (by norm_num)
        _ = _ := by ring

/-- An elementary finite Abel transformation, with endpoints at `n` and `M`. -/
theorem tc09_abel_identity (w q : ℕ → ℝ) (n M : ℕ) (hnM : n ≤ M) :
    ∑ m ∈ Ico n M, w m * (q (m + 1) - q m) =
      w M * q M - w n * q n +
        ∑ m ∈ Ico n M, (w m - w (m + 1)) * q (m + 1) := by
  induction M, hnM using Nat.le_induction with
  | base => simp
  | succ M hnM ih =>
    rw [Finset.sum_Ico_succ_top hnM, Finset.sum_Ico_succ_top hnM, ih]
    ring

/-- Bounded primitives and decreasing positive weights give a uniform finite bound. -/
theorem tc09_abel_bound (w q : ℕ → ℝ) (n M : ℕ) (hnM : n ≤ M)
    (hw : ∀ m, n ≤ m → 0 ≤ w m)
    (hanti : AntitoneOn w (Set.Ici n)) (hq : ∀ m, |q m| ≤ 1) :
    |∑ m ∈ Ico n M, w m * (q (m + 1) - q m)| ≤ 2 * w n := by
  rw [tc09_abel_identity w q n M hnM]
  have hd : ∀ m ∈ Finset.Ico n M, 0 ≤ w m - w (m + 1) := by
    intro m hm
    have hmn := (Finset.mem_Ico.mp hm).1
    exact sub_nonneg.mpr (hanti hmn (show n ≤ m + 1 by omega) (Nat.le_succ m))
  have hs : (∑ m ∈ Ico n M, (w m - w (m + 1))) = w n - w M := by
    clear hd
    induction M, hnM using Nat.le_induction with
    | base => simp
    | succ M hnM ih => rw [Finset.sum_Ico_succ_top hnM, ih]; ring
  calc
    _ ≤ |w M * q M - w n * q n| +
        |∑ m ∈ Ico n M, (w m - w (m + 1)) * q (m + 1)| := abs_add_le _ _
    _ ≤ (|w M * q M| + |w n * q n|) +
        ∑ m ∈ Ico n M, |(w m - w (m + 1)) * q (m + 1)| :=
      add_le_add (abs_sub _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (w M + w n) + ∑ m ∈ Ico n M, (w m - w (m + 1)) := by
      refine add_le_add (add_le_add ?_ ?_) (Finset.sum_le_sum ?_)
      · rw [abs_mul, abs_of_nonneg (hw M hnM)]
        exact mul_le_of_le_one_right (hw M hnM) (hq M)
      · rw [abs_mul, abs_of_nonneg (hw n le_rfl)]
        exact mul_le_of_le_one_right (hw n le_rfl) (hq n)
      · intro m hm
        rw [abs_mul, abs_of_nonneg (hd m hm)]
        exact mul_le_of_le_one_right (hd m hm) (hq _)
    _ = _ := by rw [hs]; ring

def tc09_cosPhase (m : ℕ) (t : ℝ) : ℝ := Real.cos ((2 * (m : ℝ) + 1 / 2) * t)
def tc09_sinPhase (m : ℕ) (t : ℝ) : ℝ := Real.sin ((2 * (m : ℝ) + 3 / 2) * t)

theorem tc09_phase_difference (m : ℕ) (t : ℝ) :
    tc09_cosPhase m t - tc09_cosPhase (m + 1) t =
      2 * Real.sin t * tc09_sinPhase m t := by
  have h := Real.cos_sub ( (2 * (m : ℝ) + 3 / 2) * t) t
  have h' := Real.cos_add ( (2 * (m : ℝ) + 3 / 2) * t) t
  dsimp [tc09_cosPhase, tc09_sinPhase]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (2 * (m : ℝ) + 1 / 2) * t = (2 * (m : ℝ) + 3 / 2) * t - t by ring,
    show (2 * ((m : ℝ) + 1) + 1 / 2) * t = (2 * (m : ℝ) + 3 / 2) * t + t by ring]
  linarith

theorem tc09_phase_difference_second (m : ℕ) (t : ℝ) :
    tc09_sinPhase (m + 1) t - tc09_sinPhase m t =
      2 * Real.sin t * tc09_cosPhase (m + 1) t := by
  dsimp [tc09_cosPhase, tc09_sinPhase]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (2 * ((m : ℝ) + 1) + 3 / 2) * t =
      (2 * ((m : ℝ) + 1) + 1 / 2) * t + t by ring,
    show (2 * (m : ℝ) + 3 / 2) * t =
      (2 * ((m : ℝ) + 1) + 1 / 2) * t - t by ring,
    Real.sin_add, Real.sin_sub]
  ring

/-- The absolutely convergent remainder after the first Abel transformation. -/
def tc09_abelRemainder (n : ℕ) (t : ℝ) : ℝ :=
  ∑' k : ℕ, tc09_reciprocalDrop (n + k) * tc09_cosPhase (n + k + 1) t

theorem tc09_remainder_summable (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    Summable (fun k : ℕ => tc09_reciprocalDrop (n + k) *
      tc09_cosPhase (n + k + 1) t) := by
  apply (tc09_drop_summable n hn).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tc09_drop_nonneg _ (by omega))]
  exact mul_le_of_le_one_right (tc09_drop_nonneg _ (by omega)) (Real.abs_cos_le_one _)


/-- Definition by the first Abel identity. Its sine-series interpretation is ordered. -/
def tc09_harmonicTail (n : ℕ) (t : ℝ) : ℝ :=
  (tc09_cosPhase n t / (n : ℝ) - tc09_abelRemainder n t) / (2 * Real.sin t)

theorem tc09_first_abel (n M : ℕ) (hnM : n ≤ M) (t : ℝ) :
    (2 * Real.sin t) * (∑ m ∈ Ico n M, tc09_sinPhase m t / (m : ℝ)) =
      tc09_cosPhase n t / (n : ℝ) - tc09_cosPhase M t / (M : ℝ) -
        ∑ m ∈ Ico n M, tc09_reciprocalDrop m * tc09_cosPhase (m + 1) t := by
  induction M, hnM using Nat.le_induction with
  | base => simp
  | succ M hnM ih =>
    rw [Finset.sum_Ico_succ_top hnM, Finset.sum_Ico_succ_top hnM, mul_add, ih]
    have h := congrArg (fun x : ℝ => x / (M : ℝ)) (tc09_phase_difference M t)
    simp only [tc09_reciprocalDrop, Nat.cast_add, Nat.cast_one]
    linear_combination -h

theorem tc09_remainder_partial_tendsto (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    Tendsto (fun M : ℕ => ∑ m ∈ Ico n M,
      tc09_reciprocalDrop m * tc09_cosPhase (m + 1) t) atTop
      (𝓝 (tc09_abelRemainder n t)) := by
  have h := (tc09_remainder_summable n hn t).hasSum.tendsto_sum_nat
  have ht : Tendsto (fun M : ℕ => M - n) atTop atTop := tendsto_sub_atTop_nat n
  have h' := h.comp ht
  apply h'.congr'
  filter_upwards [eventually_ge_atTop n] with M hM
  rw [Finset.sum_Ico_eq_sum_range]
  rfl

/-- Ordered convergence of the actual `Ico n M` sine partial sums. -/
theorem tc09_harmonic_ordered_limit (n : ℕ) (hn : 1 ≤ n) {t : ℝ}
    (ht : Real.sin t ≠ 0) :
    Tendsto (fun M : ℕ => ∑ m ∈ Ico n M,
      Real.sin ((2 * (m : ℝ) + 3 / 2) * t) / (m : ℝ)) atTop
      (𝓝 (tc09_harmonicTail n t)) := by
  have hzero : Tendsto (fun M : ℕ => tc09_cosPhase M t / (M : ℝ)) atTop (𝓝 0) := by
    have hi : Tendsto (fun M : ℕ => 1 / (M : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
          Tendsto (fun M : ℕ => (M : ℝ)⁻¹) atTop (𝓝 0))
    apply squeeze_zero_norm (fun M => ?_) hi
    simp only [norm_div, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (M : ℝ) by positivity)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _)
      (show (0 : ℝ) ≤ (M : ℝ) by positivity)
  have h := (((tendsto_const_nhds : Tendsto
      (fun _ : ℕ => tc09_cosPhase n t / (n : ℝ)) atTop
        (𝓝 (tc09_cosPhase n t / (n : ℝ)))).sub hzero).sub
    (tc09_remainder_partial_tendsto n hn t)).div_const (2 * Real.sin t)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop n] with M hM
  apply (div_eq_iff (mul_ne_zero (by norm_num) ht)).mpr
  simpa only [tc09_sinPhase, mul_comm] using (tc09_first_abel n M hM t).symm

theorem tc09_second_abel_bound (n M : ℕ) (hn : 1 ≤ n) (hnM : n ≤ M)
    {t : ℝ} (ht : 0 < Real.sin t) :
    |∑ m ∈ Ico n M, tc09_reciprocalDrop m * tc09_cosPhase (m + 1) t| ≤
      tc09_reciprocalDrop n / Real.sin t := by
  have h := tc09_abel_bound tc09_reciprocalDrop (fun m => tc09_sinPhase m t) n M hnM
    (fun m hm => tc09_drop_nonneg m (by omega)) (tc09_drop_antitone hn)
    (fun m => Real.abs_sin_le_one _)
  simp_rw [tc09_phase_difference_second] at h
  have he : (∑ m ∈ Ico n M,
      tc09_reciprocalDrop m * (2 * Real.sin t * tc09_cosPhase (m + 1) t)) =
      (2 * Real.sin t) * (∑ m ∈ Ico n M,
        tc09_reciprocalDrop m * tc09_cosPhase (m + 1) t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [he, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.sin t)] at h
  apply (le_div_iff₀ ht).mpr
  nlinarith

theorem tc09_remainder_bound (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : 0 < Real.sin t) :
    |tc09_abelRemainder n t| ≤ tc09_reciprocalDrop n / Real.sin t := by
  apply le_of_tendsto (tc09_remainder_partial_tendsto n hn t).abs
  filter_upwards [eventually_ge_atTop n] with M hM
  exact tc09_second_abel_bound n M hn hM ht

/-- Two Abel transformations give the quantitative harmonic-tail asymptotic. -/
theorem tc09_harmonic_tail_bound (n : ℕ) (hn : 1 ≤ n) {t : ℝ}
    (ht : 0 < Real.sin t) :
    |tc09_harmonicTail n t -
      Real.cos ((2 * (n : ℝ) + 1 / 2) * t) / (2 * (n : ℝ) * Real.sin t)| ≤
      1 / ((n : ℝ)^2 * (Real.sin t)^2) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : tc09_harmonicTail n t -
      tc09_cosPhase n t / (2 * (n : ℝ) * Real.sin t) =
      -tc09_abelRemainder n t / (2 * Real.sin t) := by
    dsimp [tc09_harmonicTail]
    field_simp
    ring
  rw [← show tc09_cosPhase n t = Real.cos ((2 * (n : ℝ) + 1 / 2) * t) from rfl,
    he, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.sin t)]
  calc
    _ ≤ (tc09_reciprocalDrop n / Real.sin t) / (2 * Real.sin t) :=
      div_le_div_of_nonneg_right (tc09_remainder_bound n hn ht) (by positivity)
    _ ≤ _ := by
      rw [tc09_drop_eq n hn]
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sin t)).mpr
      apply (div_le_iff₀ ht).mpr
      field_simp
      nlinarith [sq_nonneg (Real.sin t)]

end
end AronowAudit.P023.Wave1
