import AronowAudit.P003.P003_Audit
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Intervals

/-! P003-T7 and P003-T8: adaptive test budgets and the corrected Wald bound. -/

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-! ## P003-T7: pathwise adaptive test budget -/

/-- The chronological counter advances by the number of actual tests. -/
lemma T7_runTests_cost (reject : Counts → ℕ → Bool) (xs : List Counts) (idx : ℕ) :
    (runTests reject idx xs).idx = idx + (runTests reject idx xs).trace.length ∧
    (runTests reject idx xs).trace.length ≤ xs.length := by
  induction xs generalizing idx with
  | nil => simp [runTests]
  | cons v vs ih =>
    by_cases hv : reject v idx = true
    · have hi := ih (idx+1)
      simpa [runTests, hv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        And.intro hi.1 (Nat.succ_le_succ hi.2)
    · simp [runTests, hv]

/-- A uniform flat-map length bound. -/
lemma T7_flatMap_length {α β : Type*} (xs : List α) (f : α → List β) (B : ℕ)
    (hf : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

/-- Only a zero effect can contribute two candidates at one value of j. -/
lemma T7_candidates_length (o : Counts) (x : ℤ) :
    (candidates o x).length ≤ (o.total+1) * (if x = 0 then 2 else 1) := by
  unfold candidates
  generalize hjs : List.range (o.total+1) = js
  have hjlen : js.length = o.total+1 := by rw [← hjs, List.length_range]
  rw [← hjlen]
  apply T7_flatMap_length
  intro j hj
  cases hv : firstOnLine o x j with
  | none => simp
  | some v =>
    have he : v.effect = x := (first_on_line_spec o x j v hv).2.1
    by_cases hx : x = 0
    · simp only [if_pos hx]
      split <;> simp
    · have hn : ¬ (v.b = 0 ∧ v.c = 0 ∧ 1 ≤ v.a ∧ 1 ≤ v.d ∧
          Possible o ⟨v.a-1,1,1,v.d-1⟩) := by
        intro h
        apply hx
        simpa only [Counts.effect, h.1, h.2.1, Nat.cast_zero, sub_self] using he.symm
      simp [hx, hn]

/-- One extra block is reserved precisely while zero is strictly between sentinels. -/
def T7_zeroCredit (a b : ℤ) : ℕ := if a < 0 ∧ 0 < b then 1 else 0

lemma T7_zeroCredit_le (a b : ℤ) : T7_zeroCredit a b ≤ 1 := by
  unfold T7_zeroCredit
  split <;> omega

lemma T7_zeroCredit_left (a c b : ℤ) (hac : a < c) (hcb : c < b) :
    (if c = 0 then 1 else 0) + T7_zeroCredit a c ≤ T7_zeroCredit a b := by
  unfold T7_zeroCredit
  split_ifs <;> omega

lemma T7_zeroCredit_right (a c b : ℤ) (hac : a < c) (hcb : c < b) :
    (if c = 0 then 1 else 0) + T7_zeroCredit c b ≤ T7_zeroCredit a b := by
  unfold T7_zeroCredit
  split_ifs <;> omega

/-- Expose the corrected branch of the recursion. -/
lemma T7_search_succ (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) :
    adaptiveSearch (fuel+1) true o k₁ k₂ reject a b idx =
      if b ≤ a+1 then ⟨some a, []⟩ else
        let c := (a+b)/2
        let q := runTests reject idx (candidates o c)
        let r := if q.compatible then
          adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
        else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx
        ⟨r.value, q.trace ++ r.trace⟩ := by
  conv_lhs => unfold adaptiveSearch
  simp only [eq_self, true_and, not_true_eq_false, false_and, ite_false]
  by_cases hs : b ≤ a+1
  · simp only [if_pos hs]
  · simp only [if_neg hs]
    cases hq : (runTests reject idx (candidates o ((a+b)/2))).compatible <;>
      simp [hq]

/-- Strict narrowing makes the supplied linear fuel sufficient, for every start index. -/
lemma T7_search_terminates (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ)
    (hab : a < b) (hw : (b-a).toNat ≤ fuel+1) :
    (adaptiveSearch fuel true o k₁ k₂ reject a b idx).value.isSome := by
  induction fuel generalizing a b idx with
  | zero =>
    have hs : b ≤ a+1 := by omega
    simp [adaptiveSearch, hs]
  | succ fuel ih =>
    rw [T7_search_succ]
    by_cases hs : b ≤ a+1
    · simp [hs]
    · simp only [if_neg hs]
      let c : ℤ := (a+b)/2
      let q := runTests reject idx (candidates o c)
      have hac : a < c := by dsimp [c]; omega
      have hcb : c < b := by dsimp [c]; omega
      change (if q.compatible then
        adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
        else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).value.isSome
      by_cases hq : q.compatible = true
      · simp only [if_pos hq]
        exact ih c b q.idx hcb (by omega)
      · simp only [if_neg hq]
        exact ih a c q.idx hac (by omega)

/-- Stateful sentinel-search bound, measured in table tests.
The reserve pays for the exceptional candidate block at zero at most once.
No property of `reject`, or of the chronological start index, is assumed. -/
lemma T7_search_cost (q fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ)
    (hw : b-a ≤ (2 : ℤ)^q) :
    (adaptiveSearch fuel true o k₁ k₂ reject a b idx).trace.length ≤
      (o.total+1) * (q + T7_zeroCredit a b) := by
  induction q generalizing fuel a b idx with
  | zero =>
    have hs : b ≤ a+1 := by simp only [pow_zero] at hw; omega
    cases fuel <;> simp [adaptiveSearch, hs]
  | succ q ih =>
    cases fuel with
    | zero =>
      by_cases hs : b ≤ a+1 <;> simp [adaptiveSearch, hs]
    | succ fuel =>
      rw [T7_search_succ]
      by_cases hs : b ≤ a+1
      · simp [hs]
      · simp only [if_neg hs]
        let c : ℤ := (a+b)/2
        let r := runTests reject idx (candidates o c)
        have hac : a < c := by dsimp [c]; omega
        have hcb : c < b := by dsimp [c]; omega
        have hp : (2 : ℤ)^(q+1) = 2*(2 : ℤ)^q := by ring
        rw [hp] at hw
        have hl : c-a ≤ (2 : ℤ)^q := by dsimp [c]; omega
        have hr : b-c ≤ (2 : ℤ)^q := by dsimp [c]; omega
        have hquery : r.trace.length ≤
            (o.total+1) * (1 + if c = 0 then 1 else 0) := by
          have h₁ := (T7_runTests_cost reject (candidates o c) idx).2
          have h₂ := T7_candidates_length o c
          have hh := le_trans h₁ h₂
          show (runTests reject idx (candidates o c)).trace.length ≤ _
          split_ifs at hh ⊢ <;> omega
        change (r.trace ++ (if r.compatible then
          adaptiveSearch fuel true o k₁ k₂ reject c b r.idx
          else adaptiveSearch fuel true o k₁ k₂ reject a c r.idx).trace).length ≤ _
        by_cases hrc : r.compatible = true
        · simp only [if_pos hrc, List.length_append]
          have hi := ih fuel c b r.idx hr
          have hc := T7_zeroCredit_right a c b hac hcb
          have hm := Nat.mul_le_mul_left (o.total+1) hc
          nlinarith
        · simp only [if_neg hrc, List.length_append]
          have hi := ih fuel a c r.idx hl
          have hc := T7_zeroCredit_left a c b hac hcb
          have hm := Nat.mul_le_mul_left (o.total+1) hc
          nlinarith

/-- Arbitrary-start version with one additional candidate block in the budget. -/
lemma T7_upperRun_budget (o : Counts) (reject : Counts → ℕ → Bool) (idx : ℕ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) :
    (upperRun true o reject idx).value.isSome ∧
    (upperRun true o reject idx).trace.length ≤
      (o.total+1)*(Nat.log2 (o.total+1)+2) := by
  let k₁ : ℤ := 2*((o.a : ℤ)-o.c)
  let k₂ : ℤ := (o.a : ℤ)-o.c+(o.a+o.b)
  have hk : k₁ ≤ k₂ := by dsimp [k₁, k₂]; omega
  have hw : k₂+1-(k₁-1) ≤ (o.total : ℤ)+2 := by
    dsimp [k₁, k₂, Counts.total]
    omega
  have hterm := T7_search_terminates (o.total+3) o k₁ k₂ reject
    (k₁-1) (k₂+1) idx (by omega) (by omega)
  have hpN := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (o.total+1)
  have hp : (o.total : ℤ)+1 < (2 : ℤ)^(Nat.log2 (o.total+1)+1) := by
    rw [Nat.log2_eq_log_two]
    exact_mod_cast hpN
  have hcost := T7_search_cost (Nat.log2 (o.total+1)+1) (o.total+3)
    o k₁ k₂ reject (k₁-1) (k₂+1) idx (by omega)
  have hcredit := T7_zeroCredit_le (k₁-1) (k₂+1)
  have hm := Nat.mul_le_mul_left (o.total+1)
    (show Nat.log2 (o.total+1)+1+T7_zeroCredit (k₁-1) (k₂+1) ≤
      Nat.log2 (o.total+1)+2 by omega)
  have hu : upperRun true o reject idx =
      adaptiveSearch (o.total+3) true o k₁ k₂ reject (k₁-1) (k₂+1) idx := rfl
  rw [hu]
  exact ⟨hterm, le_trans hcost hm⟩

theorem adaptive_test_budget_proof (o : Counts) (reject : Counts → ℕ → Bool)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) :
    (upperRun true o reject).value.isSome ∧
    (upperRun true o reject).trace.length ≤ testBudget o.total := by
  have h := T7_upperRun_budget o reject 0 ho
  refine ⟨h.1, le_trans h.2 ?_⟩
  unfold testBudget
  exact Nat.mul_le_mul_left _ (by omega)

/-! ## P003-T8: corrected Wald row -/

/-- A rank whose terminal segment is shorter than the number of entries ≥ B
must itself be ≥ B in a nondecreasing list. -/
lemma T8_sorted_rank_ge (B : ℝ) (xs : List ℝ) (i : ℕ)
    (hs : xs.Pairwise (· ≤ ·)) (hi : i < xs.length)
    (hc : xs.length ≤ (xs.filter fun x => B ≤ x).length + i) :
    B ≤ xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hs' := List.pairwise_cons.mp hs
    by_cases hx : B ≤ x
    · cases i with
      | zero => simpa only [List.getElem_cons_zero] using hx
      | succ i =>
        have hi' : i < xs.length := by simp only [List.length_cons] at hi; omega
        have hxi : x ≤ xs[i] := hs'.1 _ (List.getElem_mem hi')
        simpa only [List.getElem_cons_succ] using le_trans hx hxi
    · have hf : ((x::xs).filter fun y => B ≤ y).length =
          (xs.filter fun y => B ≤ y).length := by simp [hx]
      rw [hf] at hc
      have hle := List.length_filter_le (fun y : ℝ => decide (B ≤ y)) xs
      cases i with
      | zero => simp only [List.length_cons] at hc; omega
      | succ i =>
        have hi' : i < xs.length := by simp only [List.length_cons] at hi; omega
        have hc' : xs.length ≤ (xs.filter fun y => B ≤ y).length + i := by
          simp only [List.length_cons] at hc
          omega
        simpa only [List.getElem_cons_succ] using ih i hs'.2 hi' hc'

/-- Strict-majority lower bound for the actual average-of-middle-values median.
Repeated entries and both parities of the list length are included. -/
lemma T8_median_of_strict_majority_ge (B : ℝ) (xs : List ℝ) (hne : xs ≠ [])
    (hmajor : xs.length < 2*(xs.filter fun x => B ≤ x).length) :
    B ≤ median xs := by
  let ys := xs.mergeSort (fun x y => x ≤ y)
  have hperm : ys.Perm xs := List.mergeSort_perm xs _
  have hlen : ys.length = xs.length := hperm.length_eq
  have hf : (ys.filter fun x => B ≤ x).length =
      (xs.filter fun x => B ≤ x).length :=
    (hperm.filter (fun x : ℝ => decide (B ≤ x))).length_eq
  have hn : 0 < ys.length := by
    rw [hlen]
    exact List.length_pos_iff.mpr hne
  have hys : ys ≠ [] := by intro h; simp [h] at hn
  have hs : ys.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) xs
  have ha : (ys.length-1)/2 < ys.length := by omega
  have hb : ys.length/2 < ys.length := by omega
  have hmaj : ys.length < 2*(ys.filter fun x => B ≤ x).length := by
    simpa only [hlen, hf] using hmajor
  have hca : ys.length ≤ (ys.filter fun x => B ≤ x).length + (ys.length-1)/2 := by
    omega
  have hcb : ys.length ≤ (ys.filter fun x => B ≤ x).length + ys.length/2 := by
    omega
  have hva := T8_sorted_rank_ge B ys _ hs ha hca
  have hvb := T8_sorted_rank_ge B ys _ hs hb hcb
  change B ≤ if ys = [] then 0 else (ys[(ys.length-1)/2]! + ys[ys.length/2]!)/2
  rw [if_neg hys, getElem!_pos ys _ ha, getElem!_pos ys _ hb]
  linarith

/-- Turn zero-coverage into a square inequality without dividing by a standard error. -/
lemma T8_interval_mem_iff_sq (z : ℝ) (m k : ℕ) (hz : 0 ≤ z)
    (hv : 0 ≤ (waldVarianceQ m k : ℝ)) :
    0 ∈ waldInterval z m k ↔
      (waldEstimateQ m k : ℝ)^2 ≤ z^2*(waldVarianceQ m k : ℝ) := by
  have hr : 0 ≤ z*Real.sqrt (waldVarianceQ m k) :=
    mul_nonneg hz (Real.sqrt_nonneg _)
  have hmem : 0 ∈ waldInterval z m k ↔
      |(waldEstimateQ m k : ℝ)| ≤ z*Real.sqrt (waldVarianceQ m k) := by
    rw [abs_le]
    change ((waldEstimateQ m k : ℝ) - z*Real.sqrt (waldVarianceQ m k) ≤ 0 ∧
      0 ≤ (waldEstimateQ m k : ℝ) + z*Real.sqrt (waldVarianceQ m k)) ↔
      (- (z*Real.sqrt (waldVarianceQ m k)) ≤ (waldEstimateQ m k : ℝ) ∧
        (waldEstimateQ m k : ℝ) ≤ z*Real.sqrt (waldVarianceQ m k))
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [hmem, ← sq_le_sq₀ (abs_nonneg _) hr, sq_abs, mul_pow, Real.sq_sqrt hv]

lemma T8_variance25_nonneg (k : ℕ) (hk : k ≤ 25) :
    0 ≤ (waldVarianceQ 25 k : ℝ) := by
  interval_cases k <;> norm_num [waldVarianceQ]

/-- These 26 comparisons are entirely rational after treating z² as one variable. -/
lemma T8_square_certificate (s : ℝ)
    (hs : (1.95996398454005 : ℝ)^2 < s ∧ s < (1.95996398454006 : ℝ)^2)
    (k : ℕ) (hk : k ≤ 25) :
    ((waldEstimateQ 25 k : ℝ)^2 ≤ s*(waldVarianceQ 25 k : ℝ) ↔
      10 ≤ k ∧ k ≤ 15) := by
  interval_cases k <;> norm_num [waldEstimateQ, waldVarianceQ] <;>
    nlinarith only [hs.1, hs.2]

lemma T8_coverage25 (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006)
    (k : ℕ) (hk : k ≤ 25) :
    0 ∈ waldInterval z 25 k ↔ 10 ≤ k ∧ k ≤ 15 := by
  have hp : 0 < z := by linarith [hz.1]
  have hs : (1.95996398454005 : ℝ)^2 < z^2 ∧
      z^2 < (1.95996398454006 : ℝ)^2 := by
    exact ⟨(sq_lt_sq₀ (by norm_num) hp.le).mpr hz.1,
      (sq_lt_sq₀ hp.le (by norm_num)).mpr hz.2⟩
  rw [T8_interval_mem_iff_sq z 25 k hp.le (T8_variance25_nonneg k hk)]
  exact T8_square_certificate (z^2) hs k hk

/-- Sharp common lower bound on the widths of all covering observations. -/
lemma T8_covering_width_lower (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006)
    (k : ℕ) (hk : k ≤ 25) (hcov : 0 ∈ waldInterval z 25 k) :
    2*z*Real.sqrt (1/50) ≤ waldWidth z 25 k := by
  have hp : 0 < z := by linarith [hz.1]
  have hr := (T8_coverage25 z hz k hk).mp hcov
  have hv : (1/50 : ℝ) ≤ (waldVarianceQ 25 k : ℝ) := by
    rcases hr with ⟨hlo,hhi⟩
    interval_cases k <;> norm_num [waldVarianceQ]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv) (by positivity : 0 ≤ 2*z)

lemma T8_common_width_gt (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006) :
    0.55 < 2*z*Real.sqrt (1/50) := by
  have hp : 0 < z := by linarith [hz.1]
  have hs : (11/78 : ℝ) < Real.sqrt (1/50) :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hm := mul_lt_mul_of_pos_left hs hp
  nlinarith only [hm, hz.1]

/-- Monotonicity of finite event counts, with no distinctness assumption. -/
lemma T8_filter_length_mono {α : Type*} (xs : List α) (p q : α → Bool)
    (hpq : ∀ x ∈ xs, p x = true → q x = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ht := ih (fun y hy => hpq y (by simp [hy]))
    by_cases hp : p x = true
    · have hq := hpq x (by simp) hp
      simpa [hp, hq] using Nat.succ_le_succ ht
    · by_cases hq : q x = true
      · simp only [List.filter_cons, hp, hq, ite_false, ite_true, Bool.false_eq_true,
          ↓reduceIte, List.length_cons]
        omega
      · simpa [hp, hq] using ht

/-- The coverage-fraction premise gives a strict majority of widths above the
common lower bound. -/
lemma T8_run_median_lower (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006)
    (runs : List (Fin 26)) (hne : runs ≠ [])
    (hc : ((runs.filter fun k => 0 ∈ waldInterval z 25 k.val).length : ℝ) /
      runs.length ≥ 0.925) :
    2*z*Real.sqrt (1/50) ≤ median (runs.map fun k => waldWidth z 25 k.val) := by
  let B : ℝ := 2*z*Real.sqrt (1/50)
  have hn : 0 < runs.length := List.length_pos_iff.mpr hne
  have hnR : (0 : ℝ) < runs.length := by exact_mod_cast hn
  have hcR : (0.925 : ℝ)*runs.length ≤
      (runs.filter fun k => 0 ∈ waldInterval z 25 k.val).length :=
    (le_div_iff₀ hnR).mp hc
  have hmajor : runs.length <
      2*(runs.filter fun k => 0 ∈ waldInterval z 25 k.val).length := by
    have hr : (runs.length : ℝ) <
        2*(runs.filter fun k => 0 ∈ waldInterval z 25 k.val).length := by
      linarith
    exact_mod_cast hr
  have hcounts := T8_filter_length_mono runs
    (fun k => decide (0 ∈ waldInterval z 25 k.val))
    (fun k => decide (B ≤ waldWidth z 25 k.val)) (by
      intro k hk hcov
      have hcov' : 0 ∈ waldInterval z 25 k.val := of_decide_eq_true hcov
      have hwidth := T8_covering_width_lower z hz k.val (Nat.le_of_lt_succ k.isLt) hcov'
      exact decide_eq_true hwidth)
  have hcounts' : (runs.filter fun k => 0 ∈ waldInterval z 25 k.val).length ≤
      ((runs.map fun k => waldWidth z 25 k.val).filter fun w => B ≤ w).length := by
    simpa only [List.filter_map, List.length_map, Function.comp_def] using hcounts
  apply T8_median_of_strict_majority_ge B
  · intro h
    exact hne (List.map_eq_nil_iff.mp h)
  · simp only [List.length_map]
    omega

lemma T8_central_mass_small :
    ((∑ k ∈ Finset.Icc 12 13, ((25 : ℕ).choose k : ℝ)^2) /
      ((50 : ℕ).choose 25 : ℝ) < 1/2) := by
  norm_num [Finset.sum_Icc_succ_top, Nat.choose_eq_fast_choose, Nat.fast_choose]

lemma T8_central_mass_large :
    (1/2 < (∑ k ∈ Finset.Icc 11 14, ((25 : ℕ).choose k : ℝ)^2) /
      ((50 : ℕ).choose 25 : ℝ)) := by
  norm_num [Finset.sum_Icc_succ_top, Nat.choose_eq_fast_choose, Nat.fast_choose]

theorem corrected_wald_row_proof (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006) :
    (∀ k ≤ 25, 0 ∈ waldInterval z 25 k ↔ 10 ≤ k ∧ k ≤ 15) ∧
    (∀ k ≤ 25, 0 ∈ waldInterval z 25 k → 0.55 < waldWidth z 25 k) ∧
    (∀ runs : List (Fin 26), runs ≠ [] →
      ((runs.filter fun k => 0 ∈ waldInterval z 25 k.val).length : ℝ) /
        runs.length ≥ 0.925 →
      0.55 < median (runs.map fun k => waldWidth z 25 k.val)) ∧
    waldCoverageQ 25 10 15 = 14399081696900/15801325804719 ∧
    (waldWidth z 25 11 = 2*z*Real.sqrt (77/3750)) ∧
    ((∑ k ∈ Finset.Icc 12 13, ((25 : ℕ).choose k : ℝ)^2) /
      ((50 : ℕ).choose 25 : ℝ) < 1/2) ∧
    (1/2 < (∑ k ∈ Finset.Icc 11 14, ((25 : ℕ).choose k : ℝ)^2) /
      ((50 : ℕ).choose 25 : ℝ)) ∧
    waldCoverageQ 50 21 29 = 3816125510529753382833452/4109292299835622081085553 ∧
    waldWidth z 50 23 = 2*z*Real.sqrt (621/61250) := by
  refine ⟨T8_coverage25 z hz, ?_, ?_, wald_exact_arithmetic.1, ?_,
    T8_central_mass_small, T8_central_mass_large, wald_exact_arithmetic.2.2.2.1, ?_⟩
  · intro k hk hcov
    exact lt_of_lt_of_le (T8_common_width_gt z hz)
      (T8_covering_width_lower z hz k hk hcov)
  · intro runs hne hc
    exact lt_of_lt_of_le (T8_common_width_gt z hz) (T8_run_median_lower z hz runs hne hc)
  · unfold waldWidth
    rw [wald_exact_arithmetic.2.1]
    norm_num
  · unfold waldWidth
    rw [wald_exact_arithmetic.2.2.2.2]
    norm_num

end AronowAudit.P003.Wave1
