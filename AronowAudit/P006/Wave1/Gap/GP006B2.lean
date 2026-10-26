import AronowAudit.P006.P006_CounterfactualMetrics
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Independence.Basic


namespace AronowAudit.P006.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section
local instance instDecidableGP006B2 (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## P006-T29 -/

/-- Finite product integration, with a possibly different mass at each coordinate.
No division and no positivity assumptions are needed in this algebraic lemma. -/
lemma T29_weighted_sum {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (w f : I → A → ℝ) (r : I → ℝ)
    (hr : ∀ i, (∑ a, w i a * f i a) = (∑ a, w i a) * r i) :
    (∑ x : I → A, (∏ i, w i (x i)) * ∑ i, f i (x i)) =
      (∏ i, ∑ a, w i a) * ∑ i, r i := by
  have marginal (i : I) :
      (∑ x : I → A, (∏ j, w j (x j)) * f i (x i)) =
        (∏ j, ∑ a, w j a) * r i := by
    have factor (x : I → A) :
        (∏ j, w j (x j)) * f i (x i) =
          ∏ j, w j (x j) * (if j = i then f i (x j) else 1) := by
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    simp_rw [factor]
    rw [← Fintype.prod_sum (fun j a => w j a * (if j = i then f i a else 1))]
    have each (j : I) :
        (∑ a, w j a * (if j = i then f i a else 1)) =
          (∑ a, w j a) * (if j = i then r i else 1) := by
      by_cases hj : j = i
      · subst j
        simpa using hr i
      · simp [hj]
    simp_rw [each]
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  calc
    _ = ∑ x : I → A, ∑ i, (∏ j, w j (x j)) * f i (x i) := by
      simp only [Finset.mul_sum]
    _ = ∑ i, ∑ x : I → A, (∏ j, w j (x j)) * f i (x i) := Finset.sum_comm
    _ = ∑ i, (∏ j, ∑ a, w j a) * r i := by
      exact Finset.sum_congr rfl (fun i _ => marginal i)
    _ = _ := by rw [Finset.mul_sum]

lemma T29_count_nonneg {n : ℕ} (T : Fin n → Bool) : 0 ≤ treatedCount T := by
  unfold treatedCount
  exact Finset.sum_nonneg fun i _ => by cases T i <;> norm_num [bit]

lemma T29_count_zero_iff {n : ℕ} (T : Fin n → Bool) :
    treatedCount T = 0 ↔ T = fun _ => false := by
  constructor
  · intro h
    funext i
    have hi : bit (T i) ≤ treatedCount T := by
      unfold treatedCount
      exact Finset.single_le_sum (f := fun j => bit (T j))
        (fun j _ => by cases T j <;> norm_num [bit]) (Finset.mem_univ i)
    cases ht : T i
    · rfl
    · norm_num [ht, bit, h] at hi
  · rintro rfl
    simp [treatedCount, bit]

lemma T29_nonempty_mass (n : ℕ) (q : ℝ) :
    (∑ T : Fin n → Bool,
      if 0 < treatedCount T then ∏ i, coinMass q (T i) else 0) =
      1 - (1-q)^n := by
  have total : (∑ T : Fin n → Bool, ∏ i, coinMass q (T i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [coinMass, Fintype.sum_bool]
  have pos (T : Fin n → Bool) :
      0 < treatedCount T ↔ T ≠ (fun _ => false) := by
    constructor
    · intro hp he
      have hz := (T29_count_zero_iff T).mpr he
      linarith
    · intro hne
      have hz : treatedCount T ≠ 0 := fun hz => hne ((T29_count_zero_iff T).mp hz)
      exact lt_of_le_of_ne (T29_count_nonneg T) (Ne.symm hz)
  have split :
      (∑ T : Fin n → Bool, ∏ i, coinMass q (T i)) =
        (∑ T : Fin n → Bool,
          if 0 < treatedCount T then ∏ i, coinMass q (T i) else 0) +
        (1-q)^n := by
    have each (T : Fin n → Bool) :
        (∏ i, coinMass q (T i)) =
          (if T ≠ (fun _ => false) then ∏ i, coinMass q (T i) else 0) +
          (if T = (fun _ => false) then (1-q)^n else 0) := by
      by_cases hT : T = (fun _ => false)
      · subst T
        simp [coinMass]
      · simp [hT]
    calc
      _ = ∑ T : Fin n → Bool,
          ((if T ≠ (fun _ => false) then ∏ i, coinMass q (T i) else 0) +
          (if T = (fun _ => false) then (1-q)^n else 0)) := by
        exact Finset.sum_congr rfl (fun T _ => each T)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp_rw [pos]
        simp
  linarith

lemma T29_geometric (n : ℕ) (q : ℝ) :
    q * emptyFactor n q = 1 - (1-q)^n := by
  induction n with
  | zero => simp [emptyFactor]
  | succ n ih =>
      rw [emptyFactor, Finset.sum_range_succ, mul_add]
      change q * emptyFactor n q + q * (1-q)^n = _
      rw [ih, pow_succ]
      ring

/-- Sum the actual double enumeration in the definition, rather than replacing
that definition by an asserted population objective. The zero-mass case is
handled before the only cancellation by q. -/
lemma T29_finite_iid_formula (n : ℕ) (p : ℝ) (hp : 0 < p ∧ p < 1)
    (π : BinaryPolicy) (hπ : binaryFeasible π) :
    finiteIIDAverage n p outcomeP1 π =
      emptyFactor n ((1-p)*π.1+p*π.2) * (p*π.2) := by
  let q : ℝ := (1-p)*π.1+p*π.2
  let A : ℝ := p*π.2
  let r : ℝ := A/q
  have hA : 0 ≤ A := mul_nonneg hp.1.le hπ.2.2.1
  have hother : 0 ≤ (1-p)*π.1 := mul_nonneg (by linarith) hπ.1
  have hq : 0 ≤ q := add_nonneg hother hA
  have hzero : q = 0 → A = 0 := by
    intro h
    dsimp [q] at h
    dsimp [A] at hA ⊢
    linarith
  have hrq : q*r = A := by
    by_cases h : q = 0
    · simp [r, h, hzero h]
    · dsimp [r]
      field_simp [h]
  have fixed (T : Fin n → Bool) :
      (∑ X : Fin n → Bool,
        (∏ i, coinMass p (X i)) *
        (∏ i, coinMass (binaryRule π (X i)) (T i)) *
          wATO T (fun i => outcomeP1 (X i))) =
        (if 0 < treatedCount T then r else 0) *
          ∏ i, coinMass q (T i) := by
    let w : Fin n → Bool → ℝ :=
      fun i x => coinMass p x * coinMass (binaryRule π x) (T i)
    have wm (i : Fin n) : (∑ x : Bool, w i x) = coinMass q (T i) := by
      cases ht : T i <;>
        simp [w, ht, coinMass, binaryRule, Fintype.sum_bool, q] <;> ring
    have fm (i : Fin n) :
        (∑ x : Bool, w i x * (outcomeP1 x * bit (T i))) =
          (∑ x : Bool, w i x) * (r * bit (T i)) := by
      rw [wm]
      cases ht : T i
      · simp [w, ht, coinMass, bit]
      · simp [w, ht, coinMass, bit, outcomeP1, binaryRule, Fintype.sum_bool]
        change A = q*r
        exact hrq.symm
    have numerator := T29_weighted_sum w
      (fun i x => outcomeP1 x * bit (T i)) (fun i => r*bit (T i)) fm
    have products (X : Fin n → Bool) :
        (∏ i, coinMass p (X i)) *
          (∏ i, coinMass (binaryRule π (X i)) (T i)) = ∏ i, w i (X i) := by
      rw [← Finset.prod_mul_distrib]
    simp_rw [products]
    by_cases hT : 0 < treatedCount T
    · simp only [wATO, if_pos hT]
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div, numerator]
      simp_rw [wm]
      rw [← Finset.mul_sum]
      change ((∏ i, coinMass q (T i)) * (r*treatedCount T)) / treatedCount T = _
      field_simp [ne_of_gt hT] <;> ring
    · simp [wATO, hT]
  have enumeration : finiteIIDAverage n p outcomeP1 π = r*(1-(1-q)^n) := by
    unfold finiteIIDAverage
    rw [Finset.sum_comm]
    simp_rw [fixed]
    have term (T : Fin n → Bool) :
        (if 0 < treatedCount T then r else 0) * (∏ i, coinMass q (T i)) =
        r * (if 0 < treatedCount T then ∏ i, coinMass q (T i) else 0) := by
      split_ifs <;> ring
    simp_rw [term]
    rw [← Finset.mul_sum, T29_nonempty_mass]
  change finiteIIDAverage n p outcomeP1 π = emptyFactor n q * A
  rw [enumeration, ← T29_geometric, ← hrq]
  ring

lemma T29_factor_antitone (n : ℕ) {q₁ q₂ : ℝ}
    (h₁ : 0 ≤ q₁) (h₂ : q₂ ≤ 1) (h : q₁ ≤ q₂) :
    emptyFactor n q₂ ≤ emptyFactor n q₁ := by
  apply Finset.sum_le_sum
  intro j hj
  exact pow_le_pow_left₀ (by linarith : 0 ≤ 1-q₂) (by linarith) j

lemma T29_factor_strict (n : ℕ) (hn : 2 ≤ n) {q₁ q₂ : ℝ}
    (h₁ : 0 ≤ q₁) (h₂ : q₂ ≤ 1) (h : q₁ < q₂) :
    emptyFactor n q₂ < emptyFactor n q₁ := by
  apply Finset.sum_lt_sum
  · intro j hj
    exact pow_le_pow_left₀ (by linarith : 0 ≤ 1-q₂) (by linarith) j
  · exact ⟨1, Finset.mem_range.mpr (by omega), by simpa using sub_lt_sub_left h 1⟩

lemma T29_mass_bounds (p : ℝ) (hp : 0 < p ∧ p < 1)
    (π : BinaryPolicy) (hπ : binaryFeasible π) :
    0 ≤ (1-p)*π.1+p*π.2 ∧ (1-p)*π.1+p*π.2 ≤ 1 ∧
      0 ≤ p*π.2 ∧ p*π.2 ≤ (1-p)*π.1+p*π.2 := by
  rcases hπ with ⟨ha, hau, hb, hbu⟩
  have h0 : 0 ≤ (1-p)*π.1 := mul_nonneg (by linarith) ha
  have h1 : 0 ≤ p*π.2 := mul_nonneg hp.1.le hb
  have h0u := mul_le_mul_of_nonneg_left hau (by linarith : 0 ≤ 1-p)
  have h1u := mul_le_mul_of_nonneg_left hbu hp.1.le
  exact ⟨by linarith, by linarith, h1, by linarith⟩

lemma T29_upper (n : ℕ) (p : ℝ) (hp : 0 < p ∧ p < 1)
    (π : BinaryPolicy) (hπ : binaryFeasible π) :
    finiteIIDAverage n p outcomeP1 π ≤ 1-(1-p*π.2)^n ∧
      1-(1-p*π.2)^n ≤ 1-(1-p)^n := by
  obtain ⟨hq0,hq1,hA0,hAq⟩ := T29_mass_bounds p hp π hπ
  have hfac := T29_factor_antitone n hA0 hq1 hAq
  have hAb := mul_le_mul_of_nonneg_left hπ.2.2.2 hp.1.le
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1-p)
    (by linarith : 1-p ≤ 1-p*π.2) n
  constructor
  · rw [T29_finite_iid_formula n p hp π hπ]
    calc
      _ ≤ emptyFactor n (p*π.2)*(p*π.2) := mul_le_mul_of_nonneg_right hfac hA0
      _ = 1-(1-p*π.2)^n := by
        simpa only [mul_comm] using T29_geometric n (p*π.2)
  · linarith

lemma T29_corner_value (n : ℕ) (p : ℝ) (hp : 0 < p ∧ p < 1) :
    finiteIIDAverage n p outcomeP1 (0,1) = 1-(1-p)^n := by
  rw [T29_finite_iid_formula n p hp (0,1) (by norm_num [binaryFeasible])]
  simp only [mul_zero, zero_add, mul_one]
  simpa only [mul_comm] using T29_geometric n p

lemma T29_best_corner (n : ℕ) (p : ℝ) (hp : 0 < p ∧ p < 1) :
    IsBest binaryPolicies (finiteIIDAverage n p outcomeP1) (0,1) := by
  refine ⟨by norm_num [binaryPolicies,binaryFeasible], ?_⟩
  intro π hπ
  rw [T29_corner_value n p hp]
  exact le_trans (T29_upper n p hp π hπ).1 (T29_upper n p hp π hπ).2

lemma T29_unique (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : 0 < p ∧ p < 1)
    (π : BinaryPolicy) :
    IsBest binaryPolicies (finiteIIDAverage n p outcomeP1) π ↔ π = (0,1) := by
  constructor
  · intro hb
    have hπ : binaryFeasible π := hb.1
    have equal : finiteIIDAverage n p outcomeP1 π = 1-(1-p)^n := by
      apply le_antisymm ((T29_upper n p hp π hπ).1.trans (T29_upper n p hp π hπ).2)
      simpa [T29_corner_value n p hp] using
        hb.2 (0,1) (by norm_num [binaryPolicies,binaryFeasible])
    have hb1 : π.2 = 1 := by
      by_contra hne
      have hlt : π.2 < 1 := lt_of_le_of_ne hπ.2.2.2 hne
      have hprod := mul_pos hp.1 (sub_pos.mpr hlt)
      have hh : (1-p)^n < (1-p*π.2)^n :=
        pow_lt_pow_left₀ (by nlinarith) (by linarith) (by omega)
      have hu := (T29_upper n p hp π hπ).1
      rw [equal] at hu
      linarith
    have ha0 : π.1 = 0 := by
      by_contra hne
      have hapos : 0 < π.1 := lt_of_le_of_ne hπ.1 (Ne.symm hne)
      have hq := (T29_mass_bounds p hp π hπ).2.1
      have hprod := mul_pos (sub_pos.mpr hp.2) hapos
      have hf := T29_factor_strict n hn hp.1.le hq
        (show p < (1-p)*π.1+p*π.2 by rw [hb1]; nlinarith)
      have hs : finiteIIDAverage n p outcomeP1 π <
          finiteIIDAverage n p outcomeP1 (0,1) := by
        rw [T29_finite_iid_formula n p hp π hπ,
          T29_finite_iid_formula n p hp (0,1) (by norm_num [binaryFeasible])]
        simp only [hb1, mul_one, mul_zero, zero_add] at hf ⊢
        exact mul_lt_mul_of_pos_right hf hp.1
      rw [equal, T29_corner_value n p hp] at hs
      exact (lt_irrefl _ hs)
    exact Prod.ext ha0 hb1
  · rintro rfl
    exact T29_best_corner n p hp

lemma T29_one (p : ℝ) (hp : 0 < p ∧ p < 1) (π : BinaryPolicy) :
    IsBest binaryPolicies (finiteIIDAverage 1 p outcomeP1) π ↔
      binaryFeasible π ∧ π.2 = 1 := by
  have formula (ρ : BinaryPolicy) (hρ : binaryFeasible ρ) :
      finiteIIDAverage 1 p outcomeP1 ρ = p*ρ.2 := by
    rw [T29_finite_iid_formula 1 p hp ρ hρ]
    simp [emptyFactor]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have hc := h.2 (0,1) (by norm_num [binaryPolicies,binaryFeasible])
    rw [formula _ (by norm_num [binaryFeasible]), formula π h.1] at hc
    have hge : 1 ≤ π.2 := (mul_le_mul_iff_right₀ hp.1).mp (by simpa using hc)
    exact le_antisymm h.1.2.2.2 hge
  · rintro ⟨hπ,hb⟩
    refine ⟨hπ, ?_⟩
    intro ρ hρ
    rw [formula ρ hρ, formula π hπ, hb]
    exact mul_le_mul_of_nonneg_left hρ.2.2.2 hp.1.le

theorem T29_family_all_sizes_proof (n : ℕ) (hn : 0 < n) (p α : ℝ)
    (hp : 0 < p ∧ p < 1) (hα : α < 0) :
    (∀ π ∈ binaryPolicies, finiteIIDAverage n p outcomeP1 π =
      emptyFactor n ((1-p)*π.1+p*π.2)*(p*π.2)) ∧
    (2 ≤ n → ∀ π, IsBest binaryPolicies (finiteIIDAverage n p outcomeP1) π ↔
      π = (0,1)) ∧
    (n = 1 → ∀ π, IsBest binaryPolicies (finiteIIDAverage n p outcomeP1) π ↔
      binaryFeasible π ∧ π.2 = 1) ∧
    IsBest binaryPolicies
      (binaryWelfare p (fun x => if x then 1 else -α)) (1,1) ∧
    bestValue binaryPolicies (binaryWelfare p (fun x => if x then 1 else -α)) =
      -α*(1-p)+p ∧
    regret binaryPolicies (binaryWelfare p (fun x => if x then 1 else -α)) (0,1) =
      -α*(1-p) := by
  refine ⟨fun π hπ => T29_finite_iid_formula n p hp π hπ,
    fun hn₂ π => T29_unique n hn₂ p hp π, ?_, T29_first_mode_welfare p α hp hα⟩
  intro hn₁ π
  subst n
  exact T29_one p hp π







end
end AronowAudit.P006.Wave1
