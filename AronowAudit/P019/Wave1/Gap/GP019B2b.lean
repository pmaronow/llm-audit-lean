import AronowAudit.P019.P019_Audit
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic

namespace AronowAudit.P019.Wave1

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

variable {Ω : Type*} [Fintype Ω]

lemma GP019B2b_t18_mean_mono (P : FiniteLaw Ω) {f g : Ω → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : P.mean f ≤ P.mean g := by
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω))

lemma GP019B2b_t18_mean_nonneg (P : FiniteLaw Ω) {f : Ω → ℝ}
    (h : ∀ ω, 0 ≤ f ω) : 0 ≤ P.mean f := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (P.nonneg ω) (h ω))

lemma GP019B2b_t18_mean_sq (P : FiniteLaw Ω) (f : Ω → ℝ) :
    (P.mean f)^2 ≤ P.mean (fun ω => (f ω)^2) := by
  have h := GP019B2b_t18_mean_nonneg P (f := fun ω => (f ω-P.mean f)^2)
    (fun _ => sq_nonneg _)
  have he : (fun ω => (f ω-P.mean f)^2) =
      (fun ω => (f ω)^2 - f ω*(2*P.mean f) + (P.mean f)^2) := by
    funext ω; ring
  rw [he, mean_add, mean_sub, mean_mul_const, mean_const] at h
  nlinarith

lemma GP019B2b_t18_cauchy (P : FiniteLaw Ω) (f g : Ω → ℝ) :
    (P.mean (fun ω => f ω*g ω))^2 ≤
      P.mean (fun ω => (f ω)^2)*P.mean (fun ω => (g ω)^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := fun ω => P.mass ω*(f ω)^2)
    (g := fun ω => P.mass ω*(g ω)^2)
  · intro ω _; exact mul_nonneg (P.nonneg ω) (sq_nonneg _)
  · intro ω _; exact mul_nonneg (P.nonneg ω) (sq_nonneg _)
  · intro ω _; exact le_of_eq (by ring)

def GP019B2b_t18_avg (f : Ω → ℝ) (n : ℕ) (s : Fin n → Ω) : ℝ :=
  (∑ i, f (s i))/(n : ℝ)

lemma GP019B2b_t18_avg_add (f g : Ω → ℝ) (n : ℕ) (s : Fin n → Ω) :
    GP019B2b_t18_avg (fun ω => f ω+g ω) n s =
      GP019B2b_t18_avg f n s+GP019B2b_t18_avg g n s := by
  simp only [GP019B2b_t18_avg, Finset.sum_add_distrib, add_div]

lemma GP019B2b_t18_avg_sub (f g : Ω → ℝ) (n : ℕ) (s : Fin n → Ω) :
    GP019B2b_t18_avg (fun ω => f ω-g ω) n s =
      GP019B2b_t18_avg f n s-GP019B2b_t18_avg g n s := by
  simp only [GP019B2b_t18_avg, Finset.sum_sub_distrib, sub_div]

lemma GP019B2b_t18_avg_const_mul (a : ℝ) (f : Ω → ℝ) (n : ℕ) (s : Fin n → Ω) :
    GP019B2b_t18_avg (fun ω => a*f ω) n s = a*GP019B2b_t18_avg f n s := by
  simp only [GP019B2b_t18_avg, ← Finset.mul_sum]
  ring

lemma GP019B2b_t18_avg_div (f : Ω → ℝ) (a : ℝ) (n : ℕ) (s : Fin n → Ω) :
    GP019B2b_t18_avg (fun ω => f ω/a) n s = GP019B2b_t18_avg f n s/a := by
  simp only [GP019B2b_t18_avg, ← Finset.sum_div]
  ring

lemma GP019B2b_t18_avg_center (f : Ω → ℝ) (a : ℝ) (n : ℕ) (hn : 0 < n)
    (s : Fin n → Ω) :
    GP019B2b_t18_avg (fun ω => f ω-a) n s = GP019B2b_t18_avg f n s-a := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [GP019B2b_t18_avg, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_div]
  field_simp [hn'] <;> ring

lemma GP019B2b_t18_iid_head_tail (P : FiniteLaw Ω) (n : ℕ)
    (f : Ω → ℝ) (g : (Fin n → Ω) → ℝ) :
    (P.iid (n+1)).mean (fun s => f (s 0)*g (fun i => s i.succ)) =
      P.mean f*(P.iid n).mean g := by
  unfold FiniteLaw.mean FiniteLaw.iid
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Ω)).sum_comp
    (fun s => (∏ i, P.mass (s i))*(f (s 0)*g (fun i => s i.succ)))]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, Fin.cons_zero,
    Fin.cons_succ, Fin.prod_univ_succ]
  calc
    _ = ∑ ω, ∑ s : Fin n → Ω,
        (P.mass ω*f ω)*((∏ i, P.mass (s i))*g s) := by
      apply Finset.sum_congr rfl
      intro ω _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      exact (Finset.mul_sum _ _ _).symm

lemma GP019B2b_t18_iid_tail (P : FiniteLaw Ω) (n : ℕ)
    (g : (Fin n → Ω) → ℝ) :
    (P.iid (n+1)).mean (fun s => g (fun i => s i.succ)) = (P.iid n).mean g := by
  simpa only [mean_const, one_mul] using GP019B2b_t18_iid_head_tail P n (fun _ => 1) g

lemma GP019B2b_t18_iid_head (P : FiniteLaw Ω) (n : ℕ) (f : Ω → ℝ) :
    (P.iid (n+1)).mean (fun s => f (s 0)) = P.mean f := by
  simpa only [mean_const, mul_one] using GP019B2b_t18_iid_head_tail P n f (fun _ => 1)

lemma GP019B2b_t18_sum_mean_zero (P : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : P.mean f = 0) (n : ℕ) :
    (P.iid n).mean (fun s => ∑ i, f (s i)) = 0 := by
  rw [mean_sum]
  simp only [iid_mean_coordinate, hf, Finset.sum_const_zero]

lemma GP019B2b_t18_iid_sum_fourth (P : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : P.mean f = 0) (n : ℕ) :
    (P.iid n).mean (fun s => (∑ i, f (s i))^2) =
        (n : ℝ)*P.mean (fun ω => (f ω)^2) ∧
    (P.iid n).mean (fun s => (∑ i, f (s i))^4) =
        (n : ℝ)*P.mean (fun ω => (f ω)^4) +
          3*(n : ℝ)*((n : ℝ)-1)*(P.mean (fun ω => (f ω)^2))^2 := by
  induction n with
  | zero => simp [FiniteLaw.mean]
  | succ n ih =>
    have hzero := GP019B2b_t18_sum_mean_zero P f hf n
    have he₂ : (fun s : Fin (n+1) → Ω => (∑ i, f (s i))^2) =
        (fun s => f (s 0)^2 +
          2*(f (s 0)*(∑ i : Fin n, f (s i.succ))) +
          (∑ i : Fin n, f (s i.succ))^2) := by
      funext s; rw [Fin.sum_univ_succ]; ring
    have he₄ : (fun s : Fin (n+1) → Ω => (∑ i, f (s i))^4) =
        (fun s => f (s 0)^4 +
          4*(f (s 0)^3*(∑ i : Fin n, f (s i.succ))) +
          6*(f (s 0)^2*(∑ i : Fin n, f (s i.succ))^2) +
          4*(f (s 0)*(∑ i : Fin n, f (s i.succ))^3) +
          (∑ i : Fin n, f (s i.succ))^4) := by
      funext s; rw [Fin.sum_univ_succ]; ring
    constructor
    · rw [he₂, mean_add, mean_add, mean_const_mul,
        GP019B2b_t18_iid_head P n (fun ω => f ω^2),
        GP019B2b_t18_iid_head_tail P n f (fun s => ∑ i, f (s i)),
        GP019B2b_t18_iid_tail P n (fun s => (∑ i, f (s i))^2),
        hf, ih.1]
      push_cast
      ring
    · rw [he₄, mean_add, mean_add, mean_add, mean_add,
        mean_const_mul, mean_const_mul, mean_const_mul,
        GP019B2b_t18_iid_head P n (fun ω => f ω^4),
        GP019B2b_t18_iid_head_tail P n (fun ω => f ω^3) (fun s => ∑ i, f (s i)),
        GP019B2b_t18_iid_head_tail P n (fun ω => f ω^2) (fun s => (∑ i, f (s i))^2),
        GP019B2b_t18_iid_head_tail P n f (fun s => (∑ i, f (s i))^3),
        GP019B2b_t18_iid_tail P n (fun s => (∑ i, f (s i))^4),
        hf, hzero, ih.1, ih.2]
      push_cast
      ring

/-- A bound of order n⁻², used with k=4 for averages and k=2 for remainders. -/
def GP019B2b_t18_MomentBound (P : FiniteLaw Ω) (k : ℕ)
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
    (P.iid n).mean (fun s => (T n s)^k) ≤ C/(n : ℝ)^2

lemma GP019B2b_t18_fourth_average (P : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : P.mean f = 0) : GP019B2b_t18_MomentBound P 4 (GP019B2b_t18_avg f) := by
  let m₂ := P.mean (fun ω => (f ω)^2)
  let m₄ := P.mean (fun ω => (f ω)^4)
  have hm₄ : 0 ≤ m₄ := GP019B2b_t18_mean_nonneg P (fun _ => by positivity)
  refine ⟨m₄+3*m₂^2, by positivity, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmoment := (GP019B2b_t18_iid_sum_fourth P f hf n).2
  have he : (P.iid n).mean (fun s => (GP019B2b_t18_avg f n s)^4) =
      ((n : ℝ)*m₄+3*(n : ℝ)*((n : ℝ)-1)*m₂^2)/(n : ℝ)^4 := by
    simpa only [GP019B2b_t18_avg, div_pow, mean_div_const] using
      congrArg (fun x : ℝ => x/(n : ℝ)^4) hmoment
  rw [he]
  apply (div_le_iff₀ (pow_pos hn0 4)).2
  have hcancel : (m₄+3*m₂^2)/(n : ℝ)^2*(n : ℝ)^4 =
      (m₄+3*m₂^2)*(n : ℝ)^2 := by field_simp [ne_of_gt hn0] <;> ring
  rw [hcancel]
  have hnsub : 0 ≤ (n : ℝ)-1 := sub_nonneg.2 hn1
  nlinarith [mul_nonneg (mul_nonneg hn0.le hnsub) hm₄,
    mul_nonneg hn0.le (sq_nonneg m₂)]

lemma GP019B2b_t18_square_add (a b : ℝ) : (a+b)^2 ≤ 2*(a^2+b^2) := by
  nlinarith [sq_nonneg (a-b)]

lemma GP019B2b_t18_fourth_add (a b : ℝ) : (a+b)^4 ≤ 8*(a^4+b^4) := by
  have h := GP019B2b_t18_square_add a b
  have hh := mul_self_le_mul_self (sq_nonneg (a+b)) h
  nlinarith [sq_nonneg (a^2-b^2)]

lemma GP019B2b_t18_bound_add (P : FiniteLaw Ω) (k : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hpoly : ∀ a b : ℝ, (a+b)^k ≤ K*(a^k+b^k))
    {T U : (n : ℕ) → (Fin n → Ω) → ℝ}
    (hT : GP019B2b_t18_MomentBound P k T) (hU : GP019B2b_t18_MomentBound P k U) :
    GP019B2b_t18_MomentBound P k (fun n s => T n s+U n s) := by
  obtain ⟨C,hC,hT⟩ := hT
  obtain ⟨D,hD,hU⟩ := hU
  refine ⟨K*(C+D), by positivity, ?_⟩
  intro n hn
  calc
    _ ≤ (P.iid n).mean (fun s => K*((T n s)^k+(U n s)^k)) :=
      GP019B2b_t18_mean_mono _ (fun s => hpoly _ _)
    _ = K*((P.iid n).mean (fun s => (T n s)^k)+
          (P.iid n).mean (fun s => (U n s)^k)) := by rw [mean_const_mul, mean_add]
    _ ≤ K*(C/(n : ℝ)^2+D/(n : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (add_le_add (hT n hn) (hU n hn)) hK
    _ = _ := by ring

/-- Uniform deterministic Taylor bounds, including a=0. The sole sampling
identity used here is a*e=u; e is bounded because it is a completed mean. -/
lemma GP019B2b_t18_ratio_polynomial_bound (p a u e B : ℝ)
    (hp : 0 < p) (ha : 0 ≤ a) (hB : 0 ≤ B) (he : e^2 ≤ B^2)
    (hu : a*e = u) :
    (e-u/p)^2 ≤ ((2+4*B^2)/p^4)*(u^4+(a-p)^4) ∧
    e^4 ≤ (32*(1+B^2)^2/p^4)*(u^4+(a-p)^4) := by
  have hp₄ : 0 < p^4 := pow_pos hp 4
  have hsum : 0 ≤ u^4+(a-p)^4 := by positivity
  have hid : p^4*(e-u/p)^2 = p^2*e^2*(a-p)^2 := by
    rw [← hu]
    field_simp [ne_of_gt hp] <;> ring
  have hpair : 4*u^2*(a-p)^2 ≤ 2*(u^4+(a-p)^4) := by
    nlinarith [sq_nonneg (u^2-(a-p)^2)]
  have hB₄ : e^4 ≤ B^4 := by
    have h := mul_self_le_mul_self (sq_nonneg e) he
    nlinarith
  have hconst : (1 : ℝ) ≤ (1+B^2)^2 := by nlinarith [sq_nonneg B, sq_nonneg (B^2)]
  by_cases hgood : p/2 ≤ a
  · have hp₂ : p^2 ≤ 4*a^2 := by
      have hh := mul_self_le_mul_self hp.le (show p ≤ 2*a by linarith)
      nlinarith only [hh]
    have he₂ : p^2*e^2 ≤ 4*u^2 := by
      have h := mul_le_mul_of_nonneg_right hp₂ (sq_nonneg e)
      rw [← hu]
      nlinarith only [h]
    have hr : p^4*(e-u/p)^2 ≤ 2*(u^4+(a-p)^4) := by
      rw [hid]
      exact (mul_le_mul_of_nonneg_right he₂ (sq_nonneg (a-p))).trans hpair
    have he₄ : p^4*e^4 ≤ 16*u^4 := by
      have h := mul_self_le_mul_self (by positivity : 0 ≤ p^2*e^2) he₂
      nlinarith only [h]
    constructor
    · rw [div_mul_eq_mul_div₀]
      apply (le_div_iff₀ hp₄).2
      have hc : 2*(u^4+(a-p)^4) ≤ (2+4*B^2)*(u^4+(a-p)^4) := by
        nlinarith [mul_nonneg (sq_nonneg B) hsum]
      have h := hr.trans hc
      nlinarith only [h]
    · have hc : 16*u^4 ≤ 32*(1+B^2)^2*(u^4+(a-p)^4) := by
        have hh := mul_le_mul_of_nonneg_right hconst hsum
        nlinarith [show 0 ≤ (a-p)^4 by positivity]
      have h := he₄.trans hc
      rw [div_mul_eq_mul_div₀]
      apply (le_div_iff₀ hp₄).2
      nlinarith only [h]
  · have hbad : a < p/2 := lt_of_not_ge hgood
    have hp₂ : p^2 ≤ 4*(a-p)^2 := by
      have hh := mul_self_le_mul_self hp.le (show p ≤ 2*(p-a) by linarith)
      nlinarith only [hh]
    have hp₄' : p^4 ≤ 16*(a-p)^4 := by
      have h := mul_self_le_mul_self (sq_nonneg p) hp₂
      nlinarith only [h]
    have hr : p^4*(e-u/p)^2 ≤ 4*B^2*(a-p)^4 := by
      rw [hid]
      have h₁ := mul_le_mul_of_nonneg_right hp₂ (mul_nonneg (sq_nonneg e) (sq_nonneg (a-p)))
      have h₂ := mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ 4*(a-p)^4)
      nlinarith only [h₁, h₂]
    have he₄ : p^4*e^4 ≤ 16*B^4*(a-p)^4 := by
      have h₁ := mul_le_mul_of_nonneg_right hp₄' (by positivity : 0 ≤ e^4)
      have h₂ := mul_le_mul_of_nonneg_right hB₄ (by positivity : 0 ≤ 16*(a-p)^4)
      nlinarith only [h₁, h₂]
    constructor
    · have hc : 4*B^2*(a-p)^4 ≤ (2+4*B^2)*(u^4+(a-p)^4) := by
        nlinarith [mul_nonneg (sq_nonneg B) (show 0 ≤ u^4 by positivity)]
      have h := hr.trans hc
      rw [div_mul_eq_mul_div₀]
      apply (le_div_iff₀ hp₄).2
      nlinarith only [h]
    · have hb : 16*B^4 ≤ 32*(1+B^2)^2 := by nlinarith [sq_nonneg B, sq_nonneg (B^2)]
      have hc : 16*B^4*(a-p)^4 ≤ 32*(1+B^2)^2*(u^4+(a-p)^4) := by
        have h₁ := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ (a-p)^4)
        have h₂ : 0 ≤ 32*(1+B^2)^2*u^4 := by positivity
        nlinarith
      have h := he₄.trans hc
      rw [div_mul_eq_mul_div₀]
      apply (le_div_iff₀ hp₄).2
      nlinarith only [h]

def GP019B2b_t18_count (D : Ω → Prop) (n : ℕ) (s : Fin n → Ω) : ℕ :=
  ∑ i, if D (s i) then 1 else 0

def GP019B2b_t18_ratio (f : Ω → ℝ) (D : Ω → Prop) (c : ℝ)
    (n : ℕ) (s : Fin n → Ω) : ℝ :=
  if GP019B2b_t18_count D n s = 0 then c else
    (∑ i, if D (s i) then f (s i) else 0)/(GP019B2b_t18_count D n s : ℝ)

lemma GP019B2b_t18_count_cast (D : Ω → Prop) (n : ℕ) (s : Fin n → Ω) :
    (GP019B2b_t18_count D n s : ℝ) = ∑ i, if D (s i) then (1 : ℝ) else 0 := by
  simp only [GP019B2b_t18_count, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma GP019B2b_t18_ratio_residual (f : Ω → ℝ) (D : Ω → Prop) (c m : ℝ)
    (n : ℕ) (s : Fin n → Ω) :
    (GP019B2b_t18_count D n s : ℝ)*(GP019B2b_t18_ratio f D c n s-m) =
      ∑ i, if D (s i) then f (s i)-m else 0 := by
  have hnum : (∑ i, if D (s i) then f (s i)-m else 0) =
      (∑ i, if D (s i) then f (s i) else 0)-(GP019B2b_t18_count D n s : ℝ)*m := by
    rw [GP019B2b_t18_count_cast, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; split_ifs <;> ring
  by_cases hc : GP019B2b_t18_count D n s = 0
  · have hd : ∀ i, ¬ D (s i) := by
      simpa [GP019B2b_t18_count, Finset.sum_eq_zero_iff] using hc
    simp only [hc, Nat.cast_zero, zero_mul]
    simp only [hd, if_false, Finset.sum_const_zero]
  · have hc' : (GP019B2b_t18_count D n s : ℝ) ≠ 0 := by exact_mod_cast hc
    rw [GP019B2b_t18_ratio, if_neg hc, hnum]
    field_simp [hc'] <;> ring

lemma GP019B2b_t18_ratio_bounded (f : Ω → ℝ) (D : Ω → Prop) (c m : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n s, (GP019B2b_t18_ratio f D c n s-m)^2 ≤ B^2 := by
  let B := (∑ ω, |f ω-m|)+|c-m|
  have hsum : 0 ≤ ∑ ω, |f ω-m| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB : 0 ≤ B := add_nonneg hsum (abs_nonneg _)
  have hf : ∀ ω, |f ω-m| ≤ B := by
    intro ω
    have h := Finset.single_le_sum (s := (Finset.univ : Finset Ω))
      (f := fun ω => |f ω-m|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ω)
    exact h.trans (le_add_of_nonneg_right (abs_nonneg _))
  refine ⟨B,hB,?_⟩
  intro n s
  suffices habs : |GP019B2b_t18_ratio f D c n s-m| ≤ B by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 habs
  by_cases hc : GP019B2b_t18_count D n s = 0
  · simp only [GP019B2b_t18_ratio, hc, if_true]
    exact le_add_of_nonneg_left hsum
  · have hcpos : (0 : ℝ) < GP019B2b_t18_count D n s := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    have h := GP019B2b_t18_ratio_residual f D c m n s
    have hb : |(GP019B2b_t18_count D n s : ℝ)*(GP019B2b_t18_ratio f D c n s-m)| ≤
        (GP019B2b_t18_count D n s : ℝ)*B := by
      rw [h, GP019B2b_t18_count_cast, Finset.sum_mul]
      calc
        _ ≤ ∑ i, |if D (s i) then f (s i)-m else 0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hi : D (s i)
          · simpa only [hi, if_true, one_mul] using hf (s i)
          · simp only [hi, if_false, abs_zero, zero_mul, le_refl]
    rw [abs_mul, abs_of_pos hcpos] at hb
    exact (mul_le_mul_iff_right₀ hcpos).mp (by simpa only [mul_comm] using hb)

lemma GP019B2b_t18_ratio_L2 (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop)
    (hp : 0 < P.prob D) (c : ℝ) :
    let m := P.ce f D
    let u := fun ω => if D ω then f ω-m else 0
    GP019B2b_t18_MomentBound P 2
      (fun n s => GP019B2b_t18_ratio f D c n s-m-GP019B2b_t18_avg u n s/P.prob D) ∧
    GP019B2b_t18_MomentBound P 4 (fun n s => GP019B2b_t18_ratio f D c n s-m) := by
  dsimp only
  let p := P.prob D
  let m := P.ce f D
  let u := fun ω => if D ω then f ω-m else 0
  let d := fun ω => (if D ω then (1 : ℝ) else 0)-p
  have hu : P.mean u = 0 := (masked_central_moments P f D (ne_of_gt hp)).1
  have hd : P.mean d = 0 := by
    dsimp [d, p]
    rw [mean_sub, mean_const]
    change P.prob D-P.prob D = 0
    ring
  obtain ⟨C,hC,hCu⟩ := GP019B2b_t18_fourth_average P u hu
  obtain ⟨E,hE,hEd⟩ := GP019B2b_t18_fourth_average P d hd
  obtain ⟨B,hB,hbounded⟩ := GP019B2b_t18_ratio_bounded f D c m
  have hpoint (n : ℕ) (hn : 0 < n) (s : Fin n → Ω) :
      (GP019B2b_t18_ratio f D c n s-m-GP019B2b_t18_avg u n s/p)^2 ≤
        ((2+4*B^2)/p^4)*((GP019B2b_t18_avg u n s)^4+(GP019B2b_t18_avg d n s)^4) ∧
      (GP019B2b_t18_ratio f D c n s-m)^4 ≤
        (32*(1+B^2)^2/p^4)*((GP019B2b_t18_avg u n s)^4+(GP019B2b_t18_avg d n s)^4) := by
    let a := (GP019B2b_t18_count D n s : ℝ)/(n : ℝ)
    have ha : 0 ≤ a := by positivity
    have hdelta : GP019B2b_t18_avg d n s = a-p := by
      rw [GP019B2b_t18_avg_center _ _ n hn s]
      simp only [a, GP019B2b_t18_avg, GP019B2b_t18_count_cast]
    have hres : a*(GP019B2b_t18_ratio f D c n s-m) = GP019B2b_t18_avg u n s := by
      dsimp only [a, GP019B2b_t18_avg, u]
      rw [div_mul_eq_mul_div₀, GP019B2b_t18_ratio_residual]
    simpa only [← hdelta] using GP019B2b_t18_ratio_polynomial_bound p a
      (GP019B2b_t18_avg u n s) (GP019B2b_t18_ratio f D c n s-m) B hp ha hB
      (hbounded n s) hres
  have htransfer (k : ℕ) (K : ℝ) (hK : 0 ≤ K)
      (T : (n : ℕ) → (Fin n → Ω) → ℝ)
      (hT : ∀ n, 0 < n → ∀ s, (T n s)^k ≤
        K*((GP019B2b_t18_avg u n s)^4+(GP019B2b_t18_avg d n s)^4)) :
      GP019B2b_t18_MomentBound P k T := by
    refine ⟨K*(C+E), by positivity, ?_⟩
    intro n hn
    calc
      _ ≤ (P.iid n).mean (fun s =>
          K*((GP019B2b_t18_avg u n s)^4+(GP019B2b_t18_avg d n s)^4)) :=
        GP019B2b_t18_mean_mono _ (hT n hn)
      _ = K*((P.iid n).mean (fun s => (GP019B2b_t18_avg u n s)^4)+
          (P.iid n).mean (fun s => (GP019B2b_t18_avg d n s)^4)) := by
        rw [mean_const_mul, mean_add]
      _ ≤ K*(C/(n : ℝ)^2+E/(n : ℝ)^2) :=
        mul_le_mul_of_nonneg_left (add_le_add (hCu n hn) (hEd n hn)) hK
      _ = _ := by ring
  constructor
  · exact htransfer 2 ((2+4*B^2)/p^4) (by positivity) _
      (fun n hn s => (hpoint n hn s).1)
  · exact htransfer 4 (32*(1+B^2)^2/p^4) (by positivity) _
      (fun n hn s => (hpoint n hn s).2)

lemma GP019B2b_t18_bound_scale (P : FiniteLaw Ω) (k : ℕ) (a : ℝ)
    (ha : 0 ≤ a^k) {T : (n : ℕ) → (Fin n → Ω) → ℝ}
    (hT : GP019B2b_t18_MomentBound P k T) :
    GP019B2b_t18_MomentBound P k (fun n s => a*T n s) := by
  obtain ⟨C,hC,hT⟩ := hT
  refine ⟨a^k*C, mul_nonneg ha hC, ?_⟩
  intro n hn
  simp only [mul_pow, mean_const_mul]
  calc
    _ ≤ a^k*(C/(n : ℝ)^2) := mul_le_mul_of_nonneg_left (hT n hn) ha
    _ = _ := by ring

lemma GP019B2b_t18_bound_sub₂ (P : FiniteLaw Ω)
    {T U : (n : ℕ) → (Fin n → Ω) → ℝ}
    (hT : GP019B2b_t18_MomentBound P 2 T) (hU : GP019B2b_t18_MomentBound P 2 U) :
    GP019B2b_t18_MomentBound P 2 (fun n s => T n s-U n s) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    GP019B2b_t18_bound_add P 2 2 (by norm_num) GP019B2b_t18_square_add hT
      (GP019B2b_t18_bound_scale P 2 (-1) (by norm_num) hU)

lemma GP019B2b_t18_bound_sub₄ (P : FiniteLaw Ω)
    {T U : (n : ℕ) → (Fin n → Ω) → ℝ}
    (hT : GP019B2b_t18_MomentBound P 4 T) (hU : GP019B2b_t18_MomentBound P 4 U) :
    GP019B2b_t18_MomentBound P 4 (fun n s => T n s-U n s) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    GP019B2b_t18_bound_add P 4 8 (by norm_num) GP019B2b_t18_fourth_add hT
      (GP019B2b_t18_bound_scale P 4 (-1) (by norm_num) hU)

lemma GP019B2b_t18_bound_product (P : FiniteLaw Ω)
    {T U : (n : ℕ) → (Fin n → Ω) → ℝ}
    (hT : GP019B2b_t18_MomentBound P 4 T) (hU : GP019B2b_t18_MomentBound P 4 U) :
    GP019B2b_t18_MomentBound P 2 (fun n s => T n s*U n s) := by
  obtain ⟨C,hC,hT⟩ := hT
  obtain ⟨D,hD,hU⟩ := hU
  refine ⟨C+D, add_nonneg hC hD, ?_⟩
  intro n hn
  calc
    _ ≤ (P.iid n).mean (fun s => (T n s)^4+(U n s)^4) := by
      apply GP019B2b_t18_mean_mono
      intro s
      nlinarith [sq_nonneg ((T n s)^2-(U n s)^2), sq_nonneg (T n s*U n s)]
    _ = _ := mean_add _ _ _
    _ ≤ C/(n : ℝ)^2+D/(n : ℝ)^2 := add_le_add (hT n hn) (hU n hn)
    _ = _ := by ring

lemma GP019B2b_t18_remainder_limit (P : FiniteLaw Ω)
    (R : (n : ℕ) → (Fin n → Ω) → ℝ)
    (hR : GP019B2b_t18_MomentBound P 2 R) :
    Tendsto (fun n : ℕ => (n : ℝ)*(P.iid n).mean (fun s => (R n s)^2))
      atTop (nhds 0) := by
  obtain ⟨C,hC,hR⟩ := hR
  apply squeeze_zero'
    (Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg _)
      (GP019B2b_t18_mean_nonneg _ (fun _ => sq_nonneg _))))
    (g := fun n : ℕ => C/(n : ℝ))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : 0 < n := by omega
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn'
    calc
      _ ≤ (n : ℝ)*(C/(n : ℝ)^2) :=
        mul_le_mul_of_nonneg_left (hR n hn') (Nat.cast_nonneg _)
      _ = _ := by field_simp [hnR] <;> ring
  · exact tendsto_const_div_atTop_nhds_zero_nat C

lemma GP019B2b_t18_variance_shift (P : FiniteLaw Ω) (f : Ω → ℝ) (θ : ℝ) :
    P.variance f = P.variance (fun ω => f ω-θ) := by
  have he : (fun ω => (f ω-θ)^2) =
      (fun ω => (f ω)^2-f ω*(2*θ)+θ^2) := by funext ω; ring
  simp only [FiniteLaw.variance, he, mean_add, mean_sub, mean_mul_const, mean_const]
  ring

lemma GP019B2b_t18_variance_add_centered (P : FiniteLaw Ω) (L R : Ω → ℝ)
    (hL : P.mean L = 0) :
    P.variance (fun ω => L ω+R ω) =
      P.mean (fun ω => (L ω)^2)+2*P.mean (fun ω => L ω*R ω)+
        P.mean (fun ω => (R ω)^2)-(P.mean R)^2 := by
  have he : (fun ω => (L ω+R ω)^2) =
      (fun ω => (L ω)^2+2*(L ω*R ω)+(R ω)^2) := by funext ω; ring
  rw [FiniteLaw.variance, he, mean_add, mean_add, mean_const_mul, mean_add, hL]
  ring

/-- Transfer actual sampling variances through a bounded L² remainder.
This lemma uses no distributional convergence or moment-convergence premise. -/
lemma GP019B2b_t18_variance_transfer (P : FiniteLaw Ω)
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) (θ : ℝ) (ψ : Ω → ℝ) (v : ℝ)
    (hψ : P.mean ψ = 0) (hv : P.variance ψ = v)
    (hR : GP019B2b_t18_MomentBound P 2
      (fun n s => T n s-θ-GP019B2b_t18_avg ψ n s)) :
    Tendsto (fun n : ℕ => (n : ℝ)*(P.iid n).variance (T n)) atTop (nhds v) := by
  let L := GP019B2b_t18_avg ψ
  let R := fun n s => T n s-θ-L n s
  let x := fun n : ℕ => (n : ℝ)*(P.iid n).mean (fun s => (R n s)^2)
  have hx : Tendsto x atTop (nhds 0) := GP019B2b_t18_remainder_limit P R hR
  have hxpos (n : ℕ) : 0 ≤ x n :=
    mul_nonneg (Nat.cast_nonneg _) (GP019B2b_t18_mean_nonneg _ (fun _ => sq_nonneg _))
  have hvpos : 0 ≤ v := by
    rw [FiniteLaw.variance, hψ] at hv
    have hh := GP019B2b_t18_mean_nonneg P (f := fun ω => (ψ ω)^2) (fun _ => sq_nonneg _)
    nlinarith
  have hL (n : ℕ) (hn : 0 < n) :
      (P.iid n).mean (L n) = 0 ∧
      (n : ℝ)*(P.iid n).mean (fun s => (L n s)^2) = v := by
    have hh := iid_average_moments P n hn ψ
    have hmean : (P.iid n).mean (L n) = 0 := hh.1.trans hψ
    have hhvar : (P.iid n).variance (L n) = v/(n : ℝ) := by
      change (P.iid n).variance (fun s => (∑ i, ψ (s i))/(n : ℝ)) = _
      rw [hh.2, hv]
    have hsecond : (P.iid n).mean (fun s => (L n s)^2) = v/(n : ℝ) := by
      simpa only [FiniteLaw.variance, hmean, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        sub_zero] using hhvar
    refine ⟨hmean, ?_⟩
    rw [hsecond]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hn']
  have hcross_bound : ∀ᶠ n : ℕ in atTop,
      |(n : ℝ)*(P.iid n).mean (fun s => L n s*R n s)| ≤ Real.sqrt (v*x n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : 0 < n := by omega
    have hh := GP019B2b_t18_cauchy (P.iid n) (L n) (R n)
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg (n : ℝ))
    have heq : (n : ℝ)^2*((P.iid n).mean (fun s => (L n s)^2)*
        (P.iid n).mean (fun s => (R n s)^2)) = v*x n := by
      calc
        _ = ((n : ℝ)*(P.iid n).mean (fun s => (L n s)^2))*x n := by dsimp [x]; ring
        _ = _ := by rw [(hL n hn').2]
    have hsquare : ((n : ℝ)*(P.iid n).mean (fun s => L n s*R n s))^2 ≤ v*x n := by
      nlinarith only [hh', heq]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).1
    rw [sq_abs, Real.sq_sqrt (mul_nonneg hvpos (hxpos n))]
    exact hsquare
  have hsqrt : Tendsto (fun n => Real.sqrt (v*x n)) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := v)).mul hx)
  have hcross : Tendsto (fun n : ℕ => (n : ℝ)*(P.iid n).mean
      (fun s => L n s*R n s)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hcross_bound hsqrt
  have hmeanR : Tendsto (fun n : ℕ => (n : ℝ)*((P.iid n).mean (R n))^2)
      atTop (nhds 0) := by
    apply squeeze_zero (fun n => by positivity) _ hx
    intro n
    exact mul_le_mul_of_nonneg_left (GP019B2b_t18_mean_sq (P.iid n) (R n)) (Nat.cast_nonneg _)
  have hevent : ∀ᶠ n : ℕ in atTop,
      (n : ℝ)*(P.iid n).variance (T n) =
        v+2*((n : ℝ)*(P.iid n).mean (fun s => L n s*R n s))+x n-
          (n : ℝ)*((P.iid n).mean (R n))^2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : 0 < n := by omega
    have hid : (fun s => T n s-θ) = (fun s => L n s+R n s) := by
      funext s; dsimp only [R]; ring
    rw [GP019B2b_t18_variance_shift _ _ θ, hid,
      GP019B2b_t18_variance_add_centered _ _ _ (hL n hn').1]
    dsimp only [x]
    nlinarith [(hL n hn').2]
  have hlim := ((tendsto_const_nhds (x := v)).add (hcross.const_mul 2)).add hx
  have hlim' := hlim.sub hmeanR
  simpa only [mul_zero, add_zero, sub_zero] using hlim'.congr' (hevent.mono (fun _ h => h.symm))

lemma GP019B2b_t18_combined_remainder (S : Study Ω) (hs : S.standing) (c1 c0 : ℝ) :
    GP019B2b_t18_MomentBound S.law 2
      (fun n s => S.muHat s c1 c0-S.mu-GP019B2b_t18_avg S.combinedPsi n s) := by
  let r := S.law.prob (fun ω => S.Y ω = true)
  let q := 1-r
  let m1 := S.listMean true false
  let m0 := S.listMean false false
  let d := m1-m0
  let p1 := S.law.prob (S.cell true false)
  let p0 := S.law.prob (S.cell false false)
  let u1 := fun ω => if S.cell true false ω then (S.V ω : ℝ)-m1 else 0
  let u0 := fun ω => if S.cell false false ω then (S.V ω : ℝ)-m0 else 0
  let fy := fun ω => bitVal (S.Y ω)-r
  let E1 := fun n (s : Fin n → Ω) => S.cellMean s true false c1-m1
  let E0 := fun n (s : Fin n → Ω) => S.cellMean s false false c0-m0
  let R1 := fun n s => E1 n s-GP019B2b_t18_avg u1 n s/p1
  let R0 := fun n s => E0 n s-GP019B2b_t18_avg u0 n s/p0
  let dy := fun n (s : Fin n → Ω) => S.ybar s-r
  have hrat1 := GP019B2b_t18_ratio_L2 S.law (fun ω => (S.V ω : ℝ))
    (S.cell true false) (hs.2.2.2.1 true false).1 c1
  have hrat0 := GP019B2b_t18_ratio_L2 S.law (fun ω => (S.V ω : ℝ))
    (S.cell false false) (hs.2.2.2.1 false false).1 c0
  have hR1 : GP019B2b_t18_MomentBound S.law 2 R1 := hrat1.1
  have hR0 : GP019B2b_t18_MomentBound S.law 2 R0 := hrat0.1
  have hE1 : GP019B2b_t18_MomentBound S.law 4 E1 := hrat1.2
  have hE0 : GP019B2b_t18_MomentBound S.law 4 E0 := hrat0.2
  have hfy : S.law.mean fy = 0 := by
    dsimp only [fy]
    rw [mean_sub, mean_const, mean_bit]
    change r-r = 0
    ring
  have hdy (n : ℕ) (hn : 0 < n) (s : Fin n → Ω) :
      GP019B2b_t18_avg fy n s = dy n s := by
    exact GP019B2b_t18_avg_center (fun ω => bitVal (S.Y ω)) r n hn s
  have hdy4 : GP019B2b_t18_MomentBound S.law 4 dy := by
    obtain ⟨C,hC,hCbound⟩ := GP019B2b_t18_fourth_average S.law fy hfy
    refine ⟨C,hC,?_⟩
    intro n hn
    simpa only [hdy n hn] using hCbound n hn
  have hcontrast4 := GP019B2b_t18_bound_sub₄ S.law hE1 hE0
  have hproduct2 := GP019B2b_t18_bound_product S.law hdy4 hcontrast4
  have hcontrast2 := GP019B2b_t18_bound_sub₂ S.law hR1 hR0
  have hscaled2 := GP019B2b_t18_bound_scale S.law 2 q (sq_nonneg q) hcontrast2
  have hwhole := GP019B2b_t18_bound_sub₂ S.law hscaled2 hproduct2
  have hp := regularity_probabilities S hs.2.2.2
  have hq : 0 < q := by
    have hh := hp.2 false
    rw [prob_false] at hh
    exact hh
  have hg : S.gamma ≠ 0 := ne_of_gt (hp.1 true)
  have hg0 : 1-S.gamma ≠ 0 := by
    have hh := hp.1 false
    rw [prob_false] at hh
    exact ne_of_gt hh
  have hp1 : p1 = S.gamma*q := by
    dsimp only [p1, q, r]
    rw [cell_probability S hs.2.2.1, prob_false] <;> rfl
  have hp0 : p0 = (1-S.gamma)*q := by
    dsimp only [p0, q, r]
    rw [cell_probability S hs.2.2.1, prob_false, prob_false] <;> rfl
  have hψ : S.combinedPsi =
      (fun ω => (1-d)*fy ω+q*(u1 ω/p1-u0 ω/p0)) := by
    funext ω
    change (1-d)*fy ω+u1 ω/S.gamma-u0 ω/(1-S.gamma) = _
    rw [hp1, hp0]
    field_simp [hg, hg0, ne_of_gt hq] <;> ring
  have hlinear (n : ℕ) (hn : 0 < n) (s : Fin n → Ω) :
      GP019B2b_t18_avg S.combinedPsi n s =
        (1-d)*dy n s+q*(GP019B2b_t18_avg u1 n s/p1-GP019B2b_t18_avg u0 n s/p0) := by
    rw [hψ, GP019B2b_t18_avg_add, GP019B2b_t18_avg_const_mul,
      GP019B2b_t18_avg_const_mul, hdy n hn,
      GP019B2b_t18_avg_sub (fun ω => u1 ω/p1) (fun ω => u0 ω/p0),
      GP019B2b_t18_avg_div, GP019B2b_t18_avg_div]
  have hid : S.mu = r+q*d := by
    rw [prevalence_identity S hs]
    unfold Study.combined
    rw [mean_sub, mean_const, mean_bit] <;> rfl
  obtain ⟨C,hC,hbound⟩ := hwhole
  refine ⟨C,hC,?_⟩
  intro n hn
  have herr (s : Fin n → Ω) : S.muHat s c1 c0-S.mu =
      (1-d)*dy n s+q*(E1 n s-E0 n s)-dy n s*(E1 n s-E0 n s) := by
    exact estimator_error_decomposition (S.ybar s)
      (S.cellMean s true false c1) (S.cellMean s false false c0)
      S.mu r m1 m0 hid
  have hfun (s : Fin n → Ω) : S.muHat s c1 c0-S.mu-
        GP019B2b_t18_avg S.combinedPsi n s =
      q*(R1 n s-R0 n s)-dy n s*(E1 n s-E0 n s) := by
    rw [herr s, hlinear n hn s]
    dsimp only [R1, R0]
    ring
  simp only [hfun]
  exact hbound n hn

theorem proposition_one_variance_limit_proof (S : Study Ω) (hs : S.standing) (c1 c0 : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (S.law.iid n).variance (fun s => S.muHat s c1 c0)) atTop (nhds S.sigmaSq) := by
  exact GP019B2b_t18_variance_transfer S.law (fun _ s => S.muHat s c1 c0) S.mu
    S.combinedPsi S.sigmaSq
    (combined_influence_moments S hs.2.2.1 hs.2.2.2).1
    (combined_influence_variance S hs)
    (GP019B2b_t18_combined_remainder S hs c1 c0)

/-! T20: apply the same ratio tools to the two treatment arms. -/

lemma GP019B2b_arm_ratio (S : Study Ω) (z : Bool) (c : ℝ) (n : ℕ) (s : Fin n → Ω) :
    GP019B2b_t18_ratio (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = z) c n s =
      S.armMean s z c := by
  have hc : GP019B2b_t18_count (fun ω => S.Z ω = z) n s = S.armCount s z := by
    unfold GP019B2b_t18_count Study.armCount
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : S.Z (s i) = z <;> simp only [h, ite_true, ite_false]
  unfold GP019B2b_t18_ratio Study.armMean
  rw [hc]
  by_cases h : S.armCount s z = 0
  · simp only [h, ite_true]
  · simp only [h, ite_false]

lemma GP019B2b_t20_standard_remainder (S : Study Ω) (hs : S.standing) (d1 d0 : ℝ) :
    let f := fun ω => (S.V ω : ℝ)
    let D1 := fun ω => S.Z ω = true
    let D0 := fun ω => S.Z ω = false
    let ψ := S.law.contrastInfluence f D1 D0
    let θ := S.law.ce f D1-S.law.ce f D0
    GP019B2b_t18_MomentBound S.law 2
      (fun n s => S.standardHat s d1 d0-θ-GP019B2b_t18_avg ψ n s) := by
  dsimp only
  let f := fun ω => (S.V ω : ℝ)
  let D1 := fun ω => S.Z ω = true
  let D0 := fun ω => S.Z ω = false
  let m1 := S.law.ce f D1
  let m0 := S.law.ce f D0
  let u1 := fun ω => if D1 ω then f ω-m1 else 0
  let u0 := fun ω => if D0 ω then f ω-m0 else 0
  let p1 := S.law.prob D1
  let p0 := S.law.prob D0
  let R1 := fun n (s : Fin n → Ω) =>
    S.armMean s true d1-m1-GP019B2b_t18_avg u1 n s/p1
  let R0 := fun n (s : Fin n → Ω) =>
    S.armMean s false d0-m0-GP019B2b_t18_avg u0 n s/p0
  have hp := (regularity_probabilities S hs.2.2.2).1
  have hp1 : 0 < @FiniteLaw.prob Ω _ S.law D1
      (fun ω => Classical.propDecidable (D1 ω)) := by
    convert hp true using 1 <;> simp only [FiniteLaw.prob, D1] <;> congr! (etaExpand := true)
  have hp0 : 0 < @FiniteLaw.prob Ω _ S.law D0
      (fun ω => Classical.propDecidable (D0 ω)) := by
    convert hp false using 1 <;> simp only [FiniteLaw.prob, D0] <;> congr! (etaExpand := true)
  have hR1 : GP019B2b_t18_MomentBound S.law 2 R1 := by
    convert (GP019B2b_t18_ratio_L2 S.law f D1 hp1 d1).1 using 1 <;>
      simp only [R1, f, D1, GP019B2b_arm_ratio S true d1,
        m1, p1, u1, FiniteLaw.ce, FiniteLaw.prob] <;> congr! (etaExpand := true)
  have hR0 : GP019B2b_t18_MomentBound S.law 2 R0 := by
    convert (GP019B2b_t18_ratio_L2 S.law f D0 hp0 d0).1 using 1 <;>
      simp only [R0, f, D0, GP019B2b_arm_ratio S false d0,
        m0, p0, u0, FiniteLaw.ce, FiniteLaw.prob] <;> congr! (etaExpand := true)
  have hh := GP019B2b_t18_bound_sub₂ S.law hR1 hR0
  have hlinear (n : ℕ) (s : Fin n → Ω) :
      GP019B2b_t18_avg (S.law.contrastInfluence f D1 D0) n s =
        GP019B2b_t18_avg u1 n s/p1-GP019B2b_t18_avg u0 n s/p0 := by
    change GP019B2b_t18_avg (fun ω => u1 ω/p1-u0 ω/p0) n s = _
    rw [GP019B2b_t18_avg_sub, GP019B2b_t18_avg_div, GP019B2b_t18_avg_div]
  obtain ⟨C,hC,hbound⟩ := hh
  refine ⟨C,hC,?_⟩
  intro n hn
  have he (s : Fin n → Ω) : S.standardHat s d1 d0-(m1-m0)-
        GP019B2b_t18_avg (S.law.contrastInfluence f D1 D0) n s =
      R1 n s-R0 n s := by
    rw [hlinear]
    dsimp only [Study.standardHat, R1, R0]
    ring
  convert hbound n hn using 1
  congr 1
  funext s
  congr 1
  convert he s using 1 <;>
    simp only [m1, m0, D1, D0, f, FiniteLaw.ce, FiniteLaw.prob,
      FiniteLaw.contrastInfluence, GP019B2b_t18_avg]


lemma GP019B2b_t20_standard_variance_limit (S : Study Ω) (hs : S.standing) (d1 d0 : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)*(S.law.iid n).variance
      (fun s => S.standardHat s d1 d0)) atTop (nhds S.standardSigmaSq) := by
  let f := fun ω => (S.V ω : ℝ)
  let D1 := fun ω => S.Z ω = true
  let D0 := fun ω => S.Z ω = false
  let ψ := S.law.contrastInfluence f D1 D0
  let θ := S.law.ce f D1-S.law.ce f D0
  have hp := (regularity_probabilities S hs.2.2.2).1
  have hm := contrast_influence_moments S.law f D1 D0
    (ne_of_gt (hp true)) (ne_of_gt (hp false)) (by
      intro ω h1 h0
      exact Bool.noConfusion (h1.symm.trans h0))
  have hv : S.law.variance ψ = S.standardSigmaSq := by
    rw [hm.2]
    change S.law.cv f D1/S.gamma+S.law.cv f D0/S.law.prob D0 = _
    rw [prob_false S.law S.Z] <;> rfl
  exact GP019B2b_t18_variance_transfer S.law (fun _ s => S.standardHat s d1 d0)
    θ ψ S.standardSigmaSq hm.1 hv (GP019B2b_t20_standard_remainder S hs d1 d0)

theorem proposition_two_efficiency_proof (S : Study Ω) (hs : S.standing)
    (c1 c0 d1 d0 : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)*(S.law.iid n).variance
      (fun s => S.muHat s c1 c0)) atTop (nhds S.sigmaSq) ∧
    Tendsto (fun n : ℕ => (n : ℝ)*(S.law.iid n).variance
      (fun s => S.standardHat s d1 d0)) atTop (nhds S.standardSigmaSq) ∧
    S.sigmaSq < S.standardSigmaSq := by
  exact ⟨proposition_one_variance_limit_proof S hs c1 c0,
    GP019B2b_t20_standard_variance_limit S hs d1 d0,
    (population_efficiency_gap S hs).2⟩

end
end AronowAudit.P019.Wave1
