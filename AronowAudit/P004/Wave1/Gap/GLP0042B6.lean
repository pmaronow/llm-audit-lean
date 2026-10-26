import AronowAudit.P004.P004_Spatial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.Compact

/-! P004-T9: the constrained boundary MLE and its finite-sample remainder
on the interval [0,1]. -/

namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Classical
open MeasureTheory Filter
noncomputable section
set_option maxHeartbeats 1000000

lemma t9b6_logistic_mono : Monotone logistic := by
  intro x y hxy
  have hx : 0 < 1 + Real.exp x := by positivity
  have hy : 0 < 1 + Real.exp y := by positivity
  change Real.exp x / (1 + Real.exp x) ≤ Real.exp y / (1 + Real.exp y)
  apply (div_le_div_iff₀ hx hy).2
  have he : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
  nlinarith

lemma t9b6_logistic_zero : logistic 0 = (1/2 : ℝ) := by
  norm_num [logistic]

lemma t9b6_logistic_lt_one (t : ℝ) : logistic t < 1 := by
  unfold logistic
  exact (div_lt_one (by positivity)).2 (by linarith)

lemma t9b6_logistic_logit {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    logistic (Real.log (q / (1-q))) = q := by
  have hd : 0 < 1-q := sub_pos.mpr hq1
  rw [logistic, Real.exp_log (div_pos hq hd)]
  apply (div_eq_iff (by positivity : (1 + q / (1-q)) ≠ 0)).2
  field_simp [hd.ne'] <;> ring

def t9b6_choice (q : ℝ) : ℝ :=
  if q ≤ 1/2 then 0 else if logistic 1 ≤ q then 1 else Real.log (q/(1-q))

lemma t9b6_logit_bounds {q : ℝ} (hl : (1/2 : ℝ) < q) (hu : q < logistic 1) :
    0 ≤ Real.log (q / (1-q)) ∧ Real.log (q / (1-q)) ≤ 1 := by
  have he := t9b6_logistic_logit (by linarith : 0 < q)
    (hu.trans (t9b6_logistic_lt_one 1))
  constructor
  · by_contra h
    have hh := t9b6_logistic_mono (le_of_lt (lt_of_not_ge h))
    rw [he, t9b6_logistic_zero] at hh
    linarith
  · by_contra h
    have hh := t9b6_logistic_mono (le_of_lt (lt_of_not_ge h))
    rw [he] at hh
    linarith

lemma t9b6_choice_bounds (q : ℝ) : 0 ≤ t9b6_choice q ∧ t9b6_choice q ≤ 1 := by
  unfold t9b6_choice
  split_ifs with hl hu
  · norm_num
  · norm_num
  · exact t9b6_logit_bounds (lt_of_not_ge hl) (lt_of_not_ge hu)

def t9b6_likelihood (n K t : ℝ) : ℝ := K*t - n*Real.log (1 + Real.exp t)

lemma t9b6_likelihood_deriv (n K t : ℝ) :
    HasDerivAt (t9b6_likelihood n K) (K - n*logistic t) t := by
  have he : HasDerivAt (fun x : ℝ => 1 + Real.exp x) (Real.exp t) t :=
    (Real.hasDerivAt_exp t).const_add 1
  have hl : HasDerivAt (fun x : ℝ => Real.log (1 + Real.exp x))
      (Real.exp t / (1 + Real.exp t)) t := he.log (by positivity)
  change HasDerivAt (fun y => K*y - n*Real.log (1 + Real.exp y)) _ t
  convert ((hasDerivAt_id' t).const_mul K).sub (hl.const_mul n) using 1
  rw [logistic, mul_one]

lemma t9b6_likelihood_mono (n K a b : ℝ)
    (hscore : ∀ t ∈ Set.Icc a b, 0 ≤ K - n*logistic t) :
    MonotoneOn (t9b6_likelihood n K) (Set.Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · intro t ht
    exact (t9b6_likelihood_deriv n K t).continuousAt.continuousWithinAt
  · intro t ht
    exact (t9b6_likelihood_deriv n K t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(t9b6_likelihood_deriv n K t).deriv]
    exact hscore t (interior_subset ht)

lemma t9b6_likelihood_antitone (n K a b : ℝ)
    (hscore : ∀ t ∈ Set.Icc a b, K - n*logistic t ≤ 0) :
    AntitoneOn (t9b6_likelihood n K) (Set.Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · intro t ht
    exact (t9b6_likelihood_deriv n K t).continuousAt.continuousWithinAt
  · intro t ht
    exact (t9b6_likelihood_deriv n K t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(t9b6_likelihood_deriv n K t).deriv]
    exact hscore t (interior_subset ht)

lemma t9b6_choice_max (n K θ : ℝ) (hn : 0 < n) (hθ : θ ∈ Set.Icc (0:ℝ) 1) :
    t9b6_likelihood n K θ ≤ t9b6_likelihood n K (t9b6_choice (K/n)) := by
  let q := K/n
  have hnq : n*q = K := by dsimp only [q]; field_simp [hn.ne'] <;> ring
  change t9b6_likelihood n K θ ≤ t9b6_likelihood n K (t9b6_choice q)
  unfold t9b6_choice
  split_ifs with hl hu
  · have ha : AntitoneOn (t9b6_likelihood n K) (Set.Icc (0:ℝ) 1) := by
      apply t9b6_likelihood_antitone
      intro t ht
      have hp : q ≤ logistic t := hl.trans (by
        rw [← t9b6_logistic_zero]
        exact t9b6_logistic_mono ht.1)
      have hm := mul_le_mul_of_nonneg_left hp hn.le
      rw [hnq] at hm
      linarith
    exact ha (by norm_num) hθ hθ.1
  · have hm : MonotoneOn (t9b6_likelihood n K) (Set.Icc (0:ℝ) 1) := by
      apply t9b6_likelihood_mono
      intro t ht
      have hp : logistic t ≤ q := (t9b6_logistic_mono ht.2).trans hu
      have hh := mul_le_mul_of_nonneg_left hp hn.le
      rw [hnq] at hh
      linarith
    exact hm hθ (by norm_num) hθ.2
  · have hlow : (1/2 : ℝ) < q := lt_of_not_ge hl
    have hupp : q < logistic 1 := lt_of_not_ge hu
    have hb := t9b6_logit_bounds hlow hupp
    have he := t9b6_logistic_logit (by linarith : 0 < q)
      (hupp.trans (t9b6_logistic_lt_one 1))
    by_cases ht : θ ≤ Real.log (q/(1-q))
    · have hm : MonotoneOn (t9b6_likelihood n K)
          (Set.Icc 0 (Real.log (q/(1-q)))) := by
        apply t9b6_likelihood_mono
        intro t ht
        have hp : logistic t ≤ q := by
          rw [← he]
          exact t9b6_logistic_mono ht.2
        have hh := mul_le_mul_of_nonneg_left hp hn.le
        rw [hnq] at hh
        linarith
      exact hm ⟨hθ.1, ht⟩ ⟨hb.1, le_rfl⟩ ht
    · have ht' : Real.log (q/(1-q)) ≤ θ := (lt_of_not_ge ht).le
      have ha : AntitoneOn (t9b6_likelihood n K)
          (Set.Icc (Real.log (q/(1-q))) 1) := by
        apply t9b6_likelihood_antitone
        intro t ht
        have hp : q ≤ logistic t := by
          rw [← he]
          exact t9b6_logistic_mono ht.1
        have hh := mul_le_mul_of_nonneg_left hp hn.le
        rw [hnq] at hh
        linarith
      exact ha ⟨le_rfl, hb.2⟩ ⟨ht', hθ.2⟩ ht'

lemma t9b6_count_eq {N : ℕ} (z : Assignment N) : armCount z true = ∑ i, bit (z i) := by
  apply Finset.sum_congr rfl
  intro i hi
  cases z i <;> norm_num [bit]

lemma t9b6_likelihood_sum {N : ℕ} (z : Assignment N) (t : ℝ) :
    (∑ i, (bit (z i)*t - Real.log (1 + Real.exp t))) =
      t9b6_likelihood N (armCount z true) t := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← t9b6_count_eq]
  simp [t9b6_likelihood, nsmul_eq_mul]

lemma t9b6_conditions :
    LogisticConditions (fun N (_ : Fin N) (_ : Fin 1) => 1)
      (fun _ => 0) {θ : Fin 1 → ℝ | 0 ≤ θ 0 ∧ θ 0 ≤ 1}
      (fun _ z _ => boundaryMLE z) := by
  have hc : IsCompact {θ : Fin 1 → ℝ | 0 ≤ θ 0 ∧ θ 0 ≤ 1} := by
    have he : {θ : Fin 1 → ℝ | 0 ≤ θ 0 ∧ θ 0 ≤ 1} =
        Set.pi Set.univ (fun _ : Fin 1 => Set.Icc (0:ℝ) 1) := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
      constructor
      · intro h i
        fin_cases i
        exact h
      · intro h
        exact h 0
    rw [he]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  refine ⟨hc, by norm_num, ⟨1, by intros; norm_num⟩, ?_, ?_⟩
  · refine ⟨1, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    intro v
    have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [dot, Fin.sum_univ_one, one_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel_left₀ _ hn]
  · intro N z
    refine ⟨t9b6_choice_bounds (armCount z true/N), ?_⟩
    intro θ hθ
    simp only [dot, Fin.sum_univ_one, one_mul]
    rw [t9b6_likelihood_sum, t9b6_likelihood_sum]
    by_cases hN : N = 0
    · subst N
      simp [t9b6_likelihood, armCount]
    · exact t9b6_choice_max N (armCount z true) (θ 0)
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)) hθ

def t9b6_signsum {N : ℕ} (z : Assignment N) : ℝ := ∑ i, (2*bit (z i)-1)

lemma t9b6_signsum_count {N : ℕ} (z : Assignment N) :
    t9b6_signsum z = 2*armCount z true - N := by
  simp [t9b6_signsum, t9b6_count_eq, Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma t9b6_signsum_cons_false {N : ℕ} (z : Assignment N) :
    t9b6_signsum (Fin.cons false z) = t9b6_signsum z - 1 := by
  simp [t9b6_signsum, Fin.sum_univ_succ, bit]
  <;> ring

lemma t9b6_signsum_cons_true {N : ℕ} (z : Assignment N) :
    t9b6_signsum (Fin.cons true z) = t9b6_signsum z + 1 := by
  simp [t9b6_signsum, Fin.sum_univ_succ, bit]
  <;> ring

lemma t9b6_weight_cons {N : ℕ} (b : Bool) (z : Assignment N) :
    designWeight (fun _ : Fin (N+1) => 1/2) (Fin.cons b z) =
      (1/2:ℝ)*designWeight (fun _ : Fin N => 1/2) z := by
  simp only [designWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  cases b <;> norm_num [coin]

/-- Conditioning on the first fair coin averages the two remaining polynomials. -/
lemma t9b6_expect_cons {N : ℕ} (F : Assignment (N+1) → ℝ) :
    expect (fun _ : Fin (N+1) => 1/2) F =
      expect (fun _ : Fin N => 1/2)
        (fun z => (F (Fin.cons false z) + F (Fin.cons true z))/2) := by
  unfold expect
  rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Bool)).sum_comp
    (fun z => designWeight (fun _ => 1/2) z * F z), Fintype.sum_prod_type]
  change (∑ b : Bool, ∑ z : Assignment N,
    designWeight (fun _ => 1/2) (Fin.cons b z)*F (Fin.cons b z)) = _
  simp_rw [t9b6_weight_cons]
  rw [Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- The exact even moments follow by adjoining one independent fair sign. -/
lemma t9b6_moments (N : ℕ) :
    expect (fun _ : Fin N => 1/2) (fun z => (t9b6_signsum z)^2) = N ∧
    expect (fun _ : Fin N => 1/2) (fun z => (t9b6_signsum z)^4) =
      3*(N:ℝ)^2 - 2*N := by
  induction N with
  | zero => simp [t9b6_signsum, expect]
  | succ N ih =>
    constructor
    · rw [t9b6_expect_cons]
      have he : (fun z : Assignment N =>
          ((t9b6_signsum (Fin.cons false z))^2 +
            (t9b6_signsum (Fin.cons true z))^2)/2) =
          (fun z => (t9b6_signsum z)^2 + 1) := by
        funext z
        rw [t9b6_signsum_cons_false, t9b6_signsum_cons_true]
        ring
      rw [he, expect_add, expect_const, ih.1]
      norm_num
    · rw [t9b6_expect_cons]
      have he : (fun z : Assignment N =>
          ((t9b6_signsum (Fin.cons false z))^4 +
            (t9b6_signsum (Fin.cons true z))^4)/2) =
          (fun z => (t9b6_signsum z)^4 + 6*(t9b6_signsum z)^2 + 1) := by
        funext z
        rw [t9b6_signsum_cons_false, t9b6_signsum_cons_true]
        ring
      rw [he, expect_add, expect_add, expect_mul, expect_const, ih.1, ih.2]
      push_cast
      ring

/-- Complementing every treatment is an involution of the full design. -/
def t9b6_flip (N : ℕ) : Assignment N ≃ Assignment N where
  toFun z i := !(z i)
  invFun z i := !(z i)
  left_inv z := by funext i; exact Bool.not_not (z i)
  right_inv z := by funext i; exact Bool.not_not (z i)

lemma t9b6_weight_flip {N : ℕ} (z : Assignment N) :
    designWeight (fun _ => 1/2) (t9b6_flip N z) =
      designWeight (fun _ => 1/2) z := by
  apply Finset.prod_congr rfl
  intro i hi
  cases z i <;> norm_num [coin, t9b6_flip]

lemma t9b6_signsum_flip {N : ℕ} (z : Assignment N) :
    t9b6_signsum (t9b6_flip N z) = -t9b6_signsum z := by
  unfold t9b6_signsum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases hzi : z i <;> norm_num [t9b6_flip, bit, hzi]

lemma t9b6_prob_flip {N : ℕ} (A : Assignment N → Prop) :
    prob (fun _ => 1/2) A = prob (fun _ => 1/2) (fun z => A (t9b6_flip N z)) := by
  unfold prob expect
  rw [← (t9b6_flip N).sum_comp
    (fun z => designWeight (fun _ => 1/2) z * (if A z then (1:ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro z hz
  rw [t9b6_weight_flip]

/-- A polynomial form of the second/fourth moment tail bound.  On the tail,
`(T²-4N)² ≥ 0`; off the tail, `T² ≤ N/4`. -/
lemma t9b6_two_sided_tail (N : ℕ) (hN : 0 < N) :
    (3/16:ℝ) ≤ prob (fun _ : Fin N => 1/2)
      (fun z => (N:ℝ)/4 < (t9b6_signsum z)^2) := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hpoint (z : Assignment N) :
      8*(N:ℝ)*(t9b6_signsum z)^2 ≤
        2*(N:ℝ)^2 + (t9b6_signsum z)^4 +
          16*(N:ℝ)^2*(if (N:ℝ)/4 < (t9b6_signsum z)^2 then 1 else 0) := by
    by_cases ht : (N:ℝ)/4 < (t9b6_signsum z)^2
    · rw [if_pos ht]
      nlinarith [sq_nonneg ((t9b6_signsum z)^2 - 4*(N:ℝ))]
    · rw [if_neg ht]
      have hm := mul_le_mul_of_nonneg_left (le_of_not_gt ht) (by positivity : 0 ≤ 8*(N:ℝ))
      nlinarith [sq_nonneg ((t9b6_signsum z)^2)]
  have hh := expect_mono (fun _ : Fin N => 1/2) (by intro i; constructor <;> norm_num)
    _ _ hpoint
  rw [expect_mul, expect_add, expect_add, expect_const, expect_mul,
    (t9b6_moments N).1, (t9b6_moments N).2] at hh
  change 8*(N:ℝ)*N ≤ 2*(N:ℝ)^2 + (3*(N:ℝ)^2 - 2*N) +
    16*(N:ℝ)^2*prob (fun _ => 1/2) (fun z => (N:ℝ)/4 < (t9b6_signsum z)^2) at hh
  by_contra hp
  have hm := mul_lt_mul_of_pos_left (lt_of_not_ge hp) (by positivity : 0 < 16*(N:ℝ)^2)
  nlinarith

/-- Symmetry divides the strict squared tail equally between the two signs. -/
lemma t9b6_negative_tail (N : ℕ) (hN : 0 < N) :
    (3/32:ℝ) ≤ prob (fun _ : Fin N => 1/2)
      (fun z => t9b6_signsum z < 0 ∧ (N:ℝ)/4 < (t9b6_signsum z)^2) := by
  have heq : prob (fun _ : Fin N => 1/2)
      (fun z => 0 < t9b6_signsum z ∧ (N:ℝ)/4 < (t9b6_signsum z)^2) =
      prob (fun _ : Fin N => 1/2)
        (fun z => t9b6_signsum z < 0 ∧ (N:ℝ)/4 < (t9b6_signsum z)^2) := by
    rw [t9b6_prob_flip]
    congr 1
    funext z
    apply propext
    rw [t9b6_signsum_flip]
    constructor <;> rintro ⟨hs, ht⟩ <;> constructor <;> nlinarith
  have hsplit : prob (fun _ : Fin N => 1/2)
      (fun z => (N:ℝ)/4 < (t9b6_signsum z)^2) =
      prob (fun _ : Fin N => 1/2)
        (fun z => t9b6_signsum z < 0 ∧ (N:ℝ)/4 < (t9b6_signsum z)^2) +
      prob (fun _ : Fin N => 1/2)
        (fun z => 0 < t9b6_signsum z ∧ (N:ℝ)/4 < (t9b6_signsum z)^2) := by
    unfold prob
    rw [← expect_add]
    congr 1
    funext z
    by_cases ht : (N:ℝ)/4 < (t9b6_signsum z)^2
    · have hz : t9b6_signsum z ≠ 0 := by
        intro hz
        rw [hz] at ht
        have := Nat.cast_nonneg (α := ℝ) N
        nlinarith
      rcases lt_or_gt_of_ne hz with hs | hs <;> simp [ht, hs, hs.not_gt]
    · simp [ht]
  have hh := t9b6_two_sided_tail N hN
  rw [hsplit, heq] at hh
  linarith

lemma t9b6_tail_inclusion {N : ℕ} (hN : 0 < N) (z : Assignment N)
    (ht : t9b6_signsum z < 0 ∧ (N:ℝ)/4 < (t9b6_signsum z)^2) :
    1 < Real.sqrt N * |boundaryMLE z - 4*(armCount z true/N-1/2)| := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hs2 := Real.sq_sqrt hn.le
  have hcount := t9b6_signsum_count z
  have hq : armCount z true/(N:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hn).2
    linarith [ht.1]
  have hmle : boundaryMLE z = 0 := by simp only [boundaryMLE, if_pos hq]
  rw [hmle]
  have ha : 0 ≤ (0:ℝ)-4*(armCount z true/(N:ℝ)-1/2) := by linarith
  have hroot : Real.sqrt (N:ℝ) < -2*t9b6_signsum z := by
    by_contra h
    have hh : -2*t9b6_signsum z ≤ Real.sqrt (N:ℝ) := le_of_not_gt h
    have hp := mul_nonneg (by linarith : 0 ≤ Real.sqrt (N:ℝ) + 2*t9b6_signsum z)
      (by linarith [ht.1] : 0 ≤ Real.sqrt (N:ℝ) - 2*t9b6_signsum z)
    nlinarith [ht.2]
  have hid : Real.sqrt N * |(0:ℝ)-4*(armCount z true/(N:ℝ)-1/2)| =
      (-2*t9b6_signsum z) / Real.sqrt N := by
    apply (eq_div_iff hs.ne').2
    calc
      Real.sqrt N * |(0:ℝ)-4*(armCount z true/(N:ℝ)-1/2)| * Real.sqrt N =
          (Real.sqrt N)^2 * |(0:ℝ)-4*(armCount z true/(N:ℝ)-1/2)| := by ring
      _ = (N:ℝ)*((0:ℝ)-4*(armCount z true/(N:ℝ)-1/2)) := by
        rw [hs2, abs_of_nonneg ha]
      _ = -2*t9b6_signsum z := by
        rw [hcount]
        field_simp [hn.ne'] <;> ring
  rw [hid]
  exact (lt_div_iff₀ hs).2 (by simpa using hroot)

lemma t9b6_remainder_tail (N : ℕ) (hN : 0 < N) :
    prob (fun _ : Fin N => 1/2)
      (fun z => 1 < Real.sqrt N * |boundaryMLE z - 4*(armCount z true/N-1/2)|) ≥ 3/32 := by
  apply (t9b6_negative_tail N hN).trans
  apply expect_mono (fun _ : Fin N => 1/2) (by intro i; constructor <;> norm_num)
  intro z
  by_cases ht : t9b6_signsum z < 0 ∧ (N:ℝ)/4 < (t9b6_signsum z)^2
  · simp only [if_pos ht, if_pos (t9b6_tail_inclusion hN z ht), le_refl]
  · simp only [if_neg ht]
    split_ifs <;> norm_num

lemma t9b6_not_littleOp :
    ¬ LittleOp (fun _ _ => 1/2) (fun N z => boundaryMLE z-4*(armCount z true/N-1/2))
      (fun N => (Real.sqrt N)⁻¹) := by
  intro h
  have hc := h 1 (by norm_num : (0:ℝ) < 1)
  have he : (fun N => prob (fun _ : Fin N => (1/2:ℝ))
      (fun z => 1 < |(boundaryMLE z-4*(armCount z true/N-1/2)) / (Real.sqrt N)⁻¹|)) =
      (fun N => prob (fun _ : Fin N => (1/2:ℝ))
        (fun z => 1 < Real.sqrt N * |boundaryMLE z-4*(armCount z true/N-1/2)|)) := by
    funext N
    congr 1
    funext z
    rw [div_inv_eq_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_comm]
  change Tendsto (fun N => prob (fun _ : Fin N => (1/2:ℝ))
    (fun z => 1 < |(boundaryMLE z-4*(armCount z true/N-1/2)) / (Real.sqrt N)⁻¹|))
      atTop (nhds 0) at hc
  rw [he] at hc
  have hlow : ∀ᶠ N : ℕ in atTop, (3/32:ℝ) ≤ prob (fun _ : Fin N => 1/2)
      (fun z => 1 < Real.sqrt N * |boundaryMLE z-4*(armCount z true/N-1/2)|) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    exact t9b6_remainder_tail N (by omega)
  have hbad : (3/32:ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hc hlow
  norm_num at hbad

theorem boundary_mle_counterexample_proof :
    LogisticConditions (fun N (_ : Fin N) (_ : Fin 1) => 1)
      (fun _ => 0) {θ : Fin 1 → ℝ | 0 ≤ θ 0 ∧ θ 0 ≤ 1}
      (fun _ z _ => boundaryMLE z) ∧
    (∀ N : ℕ, 0 < N → prob (fun _ : Fin N => 1/2)
      (fun z => 1 < Real.sqrt N * |boundaryMLE z - 4*(armCount z true/N-1/2)|) ≥ 3/32) ∧
    ¬ LittleOp (fun _ _ => 1/2) (fun N z => boundaryMLE z-4*(armCount z true/N-1/2))
      (fun N => (Real.sqrt N)⁻¹) := by
  exact ⟨t9b6_conditions, t9b6_remainder_tail, t9b6_not_littleOp⟩

end
end AronowAudit.P004.Wave1
