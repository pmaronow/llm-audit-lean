import AronowAudit.P006.P006_CounterfactualMetrics
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Independence.Basic

/-!
Drafter dd-GP006B2. No Lean process has been run on this file.
The preamble deliberately agrees with P006_CounterfactualMetrics.
The held declarations are used only in the requested type checks.
-/
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

example : type_of% @AronowAudit.P006.T29_family_all_sizes := T29_family_all_sizes_proof

/-! ## P006-T3

The analytic prerequisites are the fixed-policy ATT identity and the actual-welfare identity
assigned to the mapper's shared machinery. Neither proof is
in this checkout. The following is the complete decision-theoretic assembly;
its two hypotheses record those intermediate propositions, not additional
hypotheses proposed for the frozen node. See the run report.
-/

lemma T3_assemble_from_policywise_identities {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C] {n : ℕ}
    (E : Experiment Ω C n) (hS : Standing E) (PiSet : Set (C → ℝ))
    (hPiSet : ∀ π ∈ PiSet, Admissible π) (hz : (fun _ => 0) ∈ PiSet)
    (b s : C → ℝ)
    (hb : IsBest PiSet E.expectedATT b) (hs : IsBest PiSet E.V s)
    (haverage : ∀ π ∈ PiSet,
      E.expectedATT π = emptyFactor n (E.q π) * E.A E.τ π)
    (hwelfare : ∀ π ∈ PiSet, E.V π = E.A E.τ π) :
    (∀ π ∈ PiSet, E.V π = E.A E.τ π ∧
      E.expectedATT π = emptyFactor n (E.q π)*E.V π ∧
      1 ≤ emptyFactor n (E.q π)) ∧
    E.expectedATT (fun _ => 0) = 0 ∧ E.V (fun _ => 0) = 0 ∧
    0 ≤ E.expectedATT b ∧ 0 ≤ E.V b ∧ regret PiSet E.V b ≤ bestValue PiSet E.V := by
  letI : IsProbabilityMeasure E.PX := hS.px_probability
  have policywise (π : C → ℝ) (hπ : π ∈ PiSet) :
      E.V π = E.A E.τ π ∧
      E.expectedATT π = emptyFactor n (E.q π)*E.V π ∧
      1 ≤ emptyFactor n (E.q π) := by
    have ha := hPiSet π hπ
    have hπint : Integrable π E.PX :=
      (integrable_const (1 : ℝ)).mono' ha.1.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (ha.2 x).1]
          exact (ha.2 x).2)
    have hq : 0 ≤ E.q π ∧ E.q π ≤ 1 := by
      constructor
      · exact integral_nonneg fun x => (ha.2 x).1
      · have hh := integral_mono hπint (integrable_const (1 : ℝ))
          (fun x => (ha.2 x).2)
        simpa [Experiment.q] using hh
    refine ⟨hwelfare π hπ, ?_, emptyFactor_ge_one n E.hn (E.q π) hq⟩
    rw [haverage π hπ, hwelfare π hπ]
  have hVz : E.V (fun _ => 0) = 0 := by
    rw [hwelfare _ hz]
    simp [Experiment.A]
  have hRz : E.expectedATT (fun _ => 0) = 0 := by
    rw [(policywise _ hz).2.1, hVz, mul_zero]
  have hRb : 0 ≤ E.expectedATT b := by
    have hh := hb.2 (fun _ => 0) hz
    rwa [hRz] at hh
  have hbest : IsBest PiSet (fun π => emptyFactor n (E.q π)*E.V π) b := by
    refine ⟨hb.1, ?_⟩
    intro π hπ
    dsimp only
    rw [← (policywise π hπ).2.1, ← (policywise b hb.1).2.1]
    exact hb.2 π hπ
  have hfinish := positive_factor_regret PiSet E.V
    (fun π => emptyFactor n (E.q π)) (fun _ => 0) b s hz hVz
    (fun π hπ => (policywise π hπ).2.2) hbest hs
  exact ⟨policywise, hRz, hVz, hRb, hfinish.1, hfinish.2⟩

/-! ## P006-T6 independent estimation -/

/-- Conditional integration with respect to an independent auxiliary draw.
This is a direct set-integral uniqueness proof; the measurable spaces A and D
are arbitrary. In particular, no regular conditional distribution is used. -/
lemma T6_auxiliary_condExp {Ω A D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace D]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → A) (V : Ω → D) (hZ : Measurable Z) (hV : Measurable V)
    (hI : IndepFun Z V μ) (F : A × D → ℝ) (g : D → ℝ)
    (hF : Measurable F) (hg : Measurable g)
    (hFi : Integrable (fun ω => F (Z ω, V ω)) μ)
    (hgi : Integrable (fun ω => g (V ω)) μ)
    (hmean : ∀ d, (∫ z, F (z,d) ∂μ.map Z) = g d) :
    μ[(fun ω => F (Z ω,V ω)) | MeasurableSpace.comap V inferInstance]
      =ᵐ[μ] (fun ω => g (V ω)) := by
  let ν : Measure A := μ.map Z
  let η : Measure D := μ.map V
  let P : Ω → A × D := fun ω => (Z ω,V ω)
  have hP : Measurable P := hZ.prodMk hV
  have hmap : μ.map P = ν.prod η :=
    hI.map_prod_eq_prod_map_map hZ.aemeasurable hV.aemeasurable
  letI : IsProbabilityMeasure ν := inferInstance
  letI : IsProbabilityMeasure η := inferInstance
  have hFP : Integrable F (ν.prod η) := by
    rw [← hmap]
    exact (integrable_map_measure hF.aestronglyMeasurable hP.aemeasurable).mpr hFi
  have hcomap : MeasurableSpace.comap V (inferInstance : MeasurableSpace D) ≤ (inferInstance : MeasurableSpace Ω) := hV.comap_le
  have hgm : Measurable[MeasurableSpace.comap V inferInstance] (fun ω => g (V ω)) :=
    hg.comp (comap_measurable V)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hcomap hFi
    (fun s _ _ => hgi.integrableOn) ?_ hgm.stronglyMeasurable.aestronglyMeasurable).symm
  intro s hs hfinite
  rcases hs with ⟨t, ht, rfl⟩
  let J : A × D → ℝ := (Prod.snd ⁻¹' t).indicator F
  have hJ : Measurable J := hF.indicator (ht.preimage measurable_snd)
  have hJi : Integrable J (ν.prod η) := hFP.indicator (ht.preimage measurable_snd)
  have hslice (d : D) : (∫ z, J (z,d) ∂ν) = t.indicator g d := by
    by_cases hd : d ∈ t
    · simpa [J, hd, ν, Set.indicator_of_mem] using hmean d
    · simp [J, hd]
  have hJmap :
      (∫ z, J z ∂ν.prod η) =
        ∫ ω, (V ⁻¹' t).indicator (fun ω => F (Z ω,V ω)) ω ∂μ := by
    rw [← hmap]
    exact integral_map_of_stronglyMeasurable hP hJ.stronglyMeasurable
  have hgmap :
      (∫ d, t.indicator g d ∂η) =
        ∫ ω, (V ⁻¹' t).indicator (fun ω => g (V ω)) ω ∂μ := by
    exact integral_map_of_stronglyMeasurable hV (hg.indicator ht).stronglyMeasurable
  calc
    (∫ ω in V ⁻¹' t, g (V ω) ∂μ) = ∫ d, t.indicator g d ∂η := by
      rw [hgmap, integral_indicator (ht.preimage hV)]
    _ = ∫ z, J z ∂ν.prod η := by
      rw [integral_prod_symm J hJi]
      simp_rw [hslice]
    _ = ∫ ω in V ⁻¹' t, F (Z ω,V ω) ∂μ := by
      rw [hJmap, integral_indicator (ht.preimage hV)]

/-- Derive full-design conditional unbiasedness from the frozen hypotheses.
The stronger intermediate conclusion is proved here, not assumed. -/
lemma T6_independent_vector {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n)
    (hS : Standing E) (PiSet : Set (C → ℝ)) (hPiSet : ∀ π ∈ PiSet, Admissible π)
    (hU : PointwiseUnbiased E PiSet) (hI : IndependentEstimator E PiSet) :
    VectorUnbiased E PiSet := by
  obtain ⟨A, mA, Z, f, hZ, hf⟩ := hI
  letI : MeasurableSpace A := mA
  intro π hπ i
  have ha : Admissible π := hPiSet π hπ
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability π ha
  let D := (Fin n → C) × (Fin n → Bool)
  let V : Ω → D := fun ω => ((fun j => E.X j ω),(fun j => E.T π j ω))
  let F : A × D → ℝ := fun z => f π z.1 (z.2.1 i)
  let g : D → ℝ := fun d => E.μ0 (d.1 i)
  obtain ⟨hfm,hrep,hi⟩ := hf π hπ
  have hV : Measurable V :=
    (measurable_pi_iff.mpr (fun j => (hS.measurable_units π ha j).1)).prodMk
      (measurable_pi_iff.mpr (fun j => (hS.measurable_units π ha j).2.2.2))
  have hF : Measurable F :=
    hfm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp
      (measurable_fst.comp measurable_snd)))
  have hg : Measurable g :=
    hS.means_measurable.1.comp ((measurable_pi_apply i).comp measurable_fst)
  have hFi : Integrable (fun ω => F (Z ω,V ω)) (E.law π) := by
    have heq : (fun ω => F (Z ω,V ω)) = (fun ω => E.μhat π ω (E.X i ω)) := by
      funext ω
      exact (hrep ω (E.X i ω)).symm
    rw [heq]
    exact (hS.integrable_units π ha i).2.2
  have hgi : Integrable (fun ω => g (V ω)) (E.law π) := by
    exact ((hS.covariate_law π ha i).comp hS.means_measurable.1).integrable_iff.mpr
      hS.means_integrable.1
  have hmean (d : D) :
      (∫ z, F (z,d) ∂(E.law π).map Z) = g d := by
    have hslice : Measurable (fun z : A => f π z (d.1 i)) :=
      hfm.comp (measurable_id.prodMk measurable_const)
    rw [integral_map_of_stronglyMeasurable hZ hslice.stronglyMeasurable]
    calc
      (∫ ω, f π (Z ω) (d.1 i) ∂E.law π) =
          ∫ ω, E.μhat π ω (d.1 i) ∂E.law π := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => (hrep ω (d.1 i)).symm
      _ = E.μ0 (d.1 i) := (hU π hπ (d.1 i)).2
  have hce := T6_auxiliary_condExp (E.law π) Z V hZ hV hi F g hF hg hFi hgi hmean
  have heq : (fun ω => F (Z ω,V ω)) = (fun ω => E.μhat π ω (E.X i ω)) := by
    funext ω
    exact (hrep ω (E.X i ω)).symm
  rw [heq] at hce
  exact hce

lemma T6_vector_to_treated {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n)
    (hS : Standing E) (PiSet : Set (C → ℝ)) (hPiSet : ∀ π ∈ PiSet, Admissible π)
    (hU : VectorUnbiased E PiSet) : TreatedUnbiased E E.μ0 PiSet := by
  intro π hπ i
  have ha := hPiSet π hπ
  let μ : Measure Ω := E.law π
  let V : Ω → (Fin n → C) × (Fin n → Bool) :=
    fun ω => ((fun j => E.X j ω),(fun j => E.T π j ω))
  let B : Ω → ℝ := fun ω => bit (E.T π i ω)
  let H : Ω → ℝ := fun ω => E.μhat π ω (E.X i ω)
  let G : Ω → ℝ := fun ω => E.μ0 (E.X i ω)
  let R : Ω → ℝ := fun ω => B ω * (H ω-G ω)
  letI : IsProbabilityMeasure μ := hS.law_probability π ha
  have hV : Measurable V :=
    (measurable_pi_iff.mpr (fun j => (hS.measurable_units π ha j).1)).prodMk
      (measurable_pi_iff.mpr (fun j => (hS.measurable_units π ha j).2.2.2))
  have hvle : E.vectorSigma π ≤ (inferInstance : MeasurableSpace Ω) := hV.comap_le
  have hXv : Measurable[E.vectorSigma π] (E.X i) :=
    ((measurable_pi_apply i).comp measurable_fst).comp (comap_measurable V)
  have hTv : Measurable[E.vectorSigma π] (E.T π i) :=
    ((measurable_pi_apply i).comp measurable_snd).comp (comap_measurable V)
  have hBv : Measurable[E.vectorSigma π] B :=
    (measurable_of_finite bit).comp hTv
  have hGv : Measurable[E.vectorSigma π] G := hS.means_measurable.1.comp hXv
  have hB : Measurable B := (measurable_of_finite bit).comp
    (hS.measurable_units π ha i).2.2.2
  have hHi : Integrable H μ := (hS.integrable_units π ha i).2.2
  have hGi : Integrable G μ :=
    ((hS.covariate_law π ha i).comp hS.means_measurable.1).integrable_iff.mpr
      hS.means_integrable.1
  have hres : Integrable (H-G) μ := hHi.sub hGi
  have hRi : Integrable R μ := hres.bdd_mul (c := 1) hB.aestronglyMeasurable
    (Eventually.of_forall fun ω => by dsimp [B]; cases E.T π i ω <;> norm_num [bit])
  have hGce : μ[G | E.vectorSigma π] =ᵐ[μ] G := by
    exact condExp_of_aestronglyMeasurable' hvle hGv.stronglyMeasurable.aestronglyMeasurable hGi
  have hresce : μ[H-G | E.vectorSigma π] =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    filter_upwards [condExp_sub hHi hGi (E.vectorSigma π), hU π hπ i, hGce]
      with ω hsub hH hG
    change μ[H-G | E.vectorSigma π] ω = 0
    change μ[H | E.vectorSigma π] ω = G ω at hH
    change μ[H-G | E.vectorSigma π] ω = μ[H | E.vectorSigma π] ω -
      μ[G | E.vectorSigma π] ω at hsub
    rw [hsub, hH, hG]
    simp [G]
  have hRce : μ[R | E.vectorSigma π] =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    have hpull := condExp_mul_of_stronglyMeasurable_left
      hBv.stronglyMeasurable hRi hres
    filter_upwards [hpull, hresce] with ω h1 h2
    change μ[R | E.vectorSigma π] ω = 0
    change μ[R | E.vectorSigma π] ω = B ω * μ[H-G | E.vectorSigma π] ω at h1
    rw [h1, h2, mul_zero]
  have hsmall : E.covariateSigma i ≤ E.vectorSigma π := hXv.comap_le
  have htower : μ[μ[R | E.vectorSigma π] | E.covariateSigma i]
      =ᵐ[μ] μ[R | E.covariateSigma i] := condExp_condExp_of_le hsmall hvle
  have hzero : μ[μ[R | E.vectorSigma π] | E.covariateSigma i]
      =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    exact (condExp_congr_ae hRce).trans (by simp)
  exact htower.symm.trans hzero

theorem T6_independent_estimation_proof {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n)
    (hS : Standing E) (PiSet : Set (C → ℝ)) (hPiSet : ∀ π ∈ PiSet, Admissible π)
    (hU : PointwiseUnbiased E PiSet) (hI : IndependentEstimator E PiSet) :
    TreatedUnbiased E E.μ0 PiSet := by
  exact T6_vector_to_treated E hS PiSet hPiSet
    (T6_independent_vector E hS PiSet hPiSet hU hI)

example : type_of% @AronowAudit.P006.T6_independent_estimation := T6_independent_estimation_proof

end
end AronowAudit.P006.Wave1
