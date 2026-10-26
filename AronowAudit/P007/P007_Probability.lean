import Mathlib

namespace AronowAudit.P007
open Filter Topology
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
attribute [local instance] Classical.propDecidable

/-- Section 2, p. 150: "a random indicator variable for whether or not ... is missing".
A row is a vector of h Boolean indicators: false=observed (M=0), true=missing (M=1).
For Supporting Information B, pp. 3-4, h is the number g of groups, with one indicator
per group. Singleton groups recover the variable setting. -/
abbrev IndicatorRow (h : ℕ) := Fin h → Bool

/-- Section 2, p. 150: "All rows of the data" have n rows and h columns (h=k variables or h=g groups).
The finite state space contains every binary missingness array. An arbitrary distribution
of these indicators on any probability space has such a finite joint law. -/
abbrev IndicatorArray (n h : ℕ) := Fin n → IndicatorRow h

/-- Section 2, p. 150: the probabilities of the "random indicator variable" are represented by normalized nonnegative finite weights.
This models the joint distribution, and permits arbitrary within-row dependence. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

/-- Section 2, p. 150: Pr denotes probability of an event under the indicator law, represented here by a weighted finite sum. -/
noncomputable def eventProbability {α : Type*} [Fintype α] (L : FiniteLaw α) (P : α → Prop) : ℝ := by
  classical
  exact ∑ a, if P a then L.weight a else 0

/-- Corrected Figure 5, Supplement pp. 2-3 (P007-T10): the "expected proportion" uses expectation over the missingness law, a weighted finite sum. -/
noncomputable def finiteExpectation {α : Type*} [Fintype α] (L : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ a, L.weight a * f a

/-- Basic finite probability identity: the sure event has probability one. 
Supporting finite lemma for printed Lemma 3 (p. 150), its corrected proof (p. 154), and Lemma 8 (Supplement p. 4). -/
theorem probability_true {α : Type*} [Fintype α] (L : FiniteLaw α) :
    eventProbability L (fun _ => True) = 1 := by simp [eventProbability, L.total]

/-- Basic finite probability property: event probabilities are nonnegative. 
Supporting finite lemma for Lemma 3/8 and their corrected prefix proofs (p. 154; Supplement p. 4). -/
theorem probability_nonneg {α : Type*} [Fintype α] (L : FiniteLaw α) (P : α → Prop) :
    0 ≤ eventProbability L P := by
  classical
  exact Finset.sum_nonneg (fun a _ => by split_ifs <;> simp [L.nonneg])

/-- Event inclusion gives monotonicity, used for null all-observed prefixes. 
Supporting finite lemma for the null-prefix repair of Lemma 3/8 (p. 154; Supplement p. 4). -/
theorem probability_mono {α : Type*} [Fintype α] (L : FiniteLaw α)
    {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    eventProbability L P ≤ eventProbability L Q := by
  classical
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a
  · simp [hp, h a hp]
  · simp [hp]
    split_ifs <;> simp [L.nonneg]

/-- Basic finite probability property: event probabilities are at most one. 
Supporting finite lemma for the proposition sandwich (p. 154; Supplement pp. 4-5). -/
theorem probability_le_one {α : Type*} [Fintype α] (L : FiniteLaw α) (P : α → Prop) :
    eventProbability L P ≤ 1 := by
  simpa [probability_true] using probability_mono L (P:=P) (Q:=fun _ => True) (fun _ _ => True.intro)

/-- Complement identity for finite probability, used for deleted rows. 
Supporting finite lemma for the row deletion factors in Lemma 3/8 (p. 154; Supplement p. 4). -/
theorem probability_compl {α : Type*} [Fintype α] (L : FiniteLaw α) (P : α → Prop) :
    eventProbability L (fun a => ¬ P a) = 1 - eventProbability L P := by
  classical
  have h : eventProbability L (fun a => ¬ P a) + eventProbability L P = 1 := by
    rw [eventProbability, eventProbability, ← Finset.sum_add_distrib]
    convert L.total using 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases hp : P a <;> simp [hp]
  linarith

/-- Equal events have equal finite probabilities. 
Supporting finite lemma for the event definitions in Section 2 (p. 150) and corrected Lemma 3/8 proofs. -/
theorem probability_congr {α : Type*} [Fintype α] (L : FiniteLaw α)
    {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) :
    eventProbability L P = eventProbability L Q := by
  classical
  simp only [eventProbability]
  apply Finset.sum_congr rfl
  intro a _
  rw [h a]

/-- Finite union bound, needed to dispatch q_*=0 without row independence. 
Supporting finite lemma for the corrected zero-bound endpoint of Lemma 3/8 (p. 154; Supplement p. 4). -/
theorem probability_exists_le_sum {α I : Type*} [Fintype α] [Fintype I]
    (L : FiniteLaw α) (P : I → α → Prop) :
    eventProbability L (fun a => ∃ i, P i a) ≤ ∑ i, eventProbability L (P i) := by
  classical
  simp only [eventProbability]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : ∃ i, P i a
  · obtain ⟨i, hi⟩ := hp
    simp only [if_pos (show ∃ i, P i a from ⟨i, hi⟩)]
    calc
      L.weight a = if P i a then L.weight a else 0 := by simp [hi]
      _ ≤ ∑ j, if P j a then L.weight a else 0 :=
        Finset.single_le_sum (f:=fun j => if P j a then L.weight a else 0) (fun j _ => by split_ifs <;> simp [L.nonneg]) (Finset.mem_univ i)
  · simp only [if_neg hp]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [L.nonneg])

/-- Assumption 1 (p. 150), respectively Assumption 6 (Supplement p. 4): "All rows ...
are mutually independent". This is full independence for every choice of row events,
not merely independence of the complete-row events, and does not require identical laws. -/
noncomputable def RowsIndependent {n h : ℕ} (L : FiniteLaw (IndicatorArray n h)) : Prop :=
  ∀ E : Fin n → IndicatorRow h → Prop,
    eventProbability L (fun x => ∀ i, E i (x i)) =
      ∏ i, eventProbability L (fun x => E i (x i))

/-- Section 2, p. 150: the event "M_ij = 0" in bold denotes all first j indicators
being observed. Write this event as C_ij; C_i0 is sure. -/
noncomputable def observedPrefix {h : ℕ} (r : IndicatorRow h) (j : ℕ) : Prop :=
  ∀ t : Fin h, t.val < j → r t = false

/-- P007-T5 notation for the proof of Lemma 3 (p. 154) and Lemma 8 (Supplement p. 4): s_ij=Pr(C_ij), where C_ij is the printed bold-M_ij=0 event. -/
noncomputable def prefixSurvival {n h : ℕ} (L : FiniteLaw (IndicatorArray n h))
    (i : Fin n) (j : ℕ) : ℝ := eventProbability L (fun x => observedPrefix (x i) j)

/-- Lemma 3 (p. 150): "the probability that listwise deletion removes all rows".
Every row has at least one missing entry iff no row's full prefix is all observed. -/
noncomputable def pAll {n h : ℕ} (L : FiniteLaw (IndicatorArray n h)) : ℝ :=
  eventProbability L (fun x => ∀ i, ¬ observedPrefix (x i) h)

/-- Assumption 2 (p. 150), respectively 7 (Supplement p. 4), with its positive-prefix
proviso intact: "such that Pr(bold M_i,j-1=0)>0". q_* is an upper bound on being observed, not necessarily the least bound.
The first clause handles variable one; later conditionals use s_(j+1)/s_j only if s_j>0. -/
noncomputable def ConditionalObservationBound {n h : ℕ} (L : FiniteLaw (IndicatorArray n h)) (q : ℝ) : Prop :=
  0 ≤ q ∧ q < 1 ∧ ∀ i,
    (0 < h → prefixSurvival L i 1 ≤ q) ∧
    ∀ j, 1 ≤ j → j < h → 0 < prefixSurvival L i j →
      prefixSurvival L i (j + 1) / prefixSurvival L i j ≤ q

/-- Empty all-observed prefixes are sure events. 
Supporting finite lemma for the corrected Lemma 3/8 proof (p. 154; Supplement p. 4). -/
theorem prefix_zero {n h : ℕ} (L : FiniteLaw (IndicatorArray n h)) (i : Fin n) :
    prefixSurvival L i 0 = 1 := by simp [prefixSurvival, observedPrefix, eventProbability, L.total]

/-- An all-observed prefix is contained in every shorter prefix. 
Supporting finite lemma for the corrected null-prefix recursion in Lemma 3/8 (p. 154; Supplement p. 4). -/
theorem prefix_antitone {n h : ℕ} (L : FiniteLaw (IndicatorArray n h)) (i : Fin n)
    {a b : ℕ} (hab : a ≤ b) : prefixSurvival L i b ≤ prefixSurvival L i a := by
  apply probability_mono L
  intro x hx t ht
  exact hx t (lt_of_lt_of_le ht hab)

/-- P007-T5(b): the corrected recursion s_(j+1)≤q_* s_j handles both positive and
null prefixes under the printed Assumption 2/7, with no added nonzero assumption. -/
theorem prefix_step {n h : ℕ} (L : FiniteLaw (IndicatorArray n h)) {q : ℝ}
    (hq : ConditionalObservationBound L q) (i : Fin n) {j : ℕ} (hj : j < h) :
    prefixSurvival L i (j + 1) ≤ prefixSurvival L i j * q := by
  by_cases hj0 : j = 0
  · subst j
    simpa [prefix_zero] using (hq.2.2 i).1 hj
  · have hs0 := probability_nonneg L (fun x => observedPrefix (x i) j)
    by_cases hs : 0 < prefixSurvival L i j
    · simpa [mul_comm] using (div_le_iff₀ hs).mp ((hq.2.2 i).2 j (by omega) hj hs)
    · have hz : prefixSurvival L i j = 0 := le_antisymm (not_lt.mp hs) hs0
      have hm := prefix_antitone L i (Nat.le_succ j)
      simp only [hz, zero_mul]
      exact hm.trans (le_of_eq hz)

/-- P007-T5(d): induction gives each row's full observed-prefix probability at most
q_*^h. This finite lemma uses no independence across rows or columns. -/
theorem prefix_survival_bound {n h : ℕ} (L : FiniteLaw (IndicatorArray n h)) {q : ℝ}
    (hq : ConditionalObservationBound L q) (i : Fin n) {j : ℕ} (hj : j ≤ h) :
    prefixSurvival L i j ≤ q ^ j := by
  induction j with
  | zero => simp [prefix_zero]
  | succ j ih =>
      calc
        prefixSurvival L i (j + 1) ≤ prefixSurvival L i j * q := prefix_step L hq i (by omega)
        _ ≤ q ^ j * q := mul_le_mul_of_nonneg_right (ih (by omega)) hq.1
        _ = q ^ (j + 1) := (pow_succ q j).symm

/-- P007-T5(e) and T11(iii): full row independence implies the product of the
row-specific deletion probabilities. Identical distribution plays no role. -/
theorem independent_rows_product {n h : ℕ} (L : FiniteLaw (IndicatorArray n h))
    (hi : RowsIndependent L) :
    pAll L = ∏ i, (1 - prefixSurvival L i h) := by
  rw [pAll, hi (fun _ r => ¬ observedPrefix r h)]
  apply Finset.prod_congr rfl
  intro i _
  exact probability_compl L (fun x => observedPrefix (x i) h)

/-- P007-T14, printed Lemma 3 (p. 150): under mutual row independence and the
conditional observation bound, p_all≥(1-q_*^k)^n, including q_*=0 and null prefixes. -/
theorem lemma3 {n k : ℕ} (L : FiniteLaw (IndicatorArray n k))
    (_hn : 0 < n) (_hk : 0 < k) {q : ℝ}
    (hi : RowsIndependent L) (hq : ConditionalObservationBound L q) :
    (1 - q ^ k) ^ n ≤ pAll L := by
  rw [independent_rows_product L hi]
  calc
    (1 - q ^ k) ^ n = ∏ _i : Fin n, (1 - q ^ k) := by simp
    _ ≤ ∏ i : Fin n, (1 - prefixSurvival L i k) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact sub_nonneg.mpr (pow_le_one₀ hq.1 hq.2.1.le)
      · intro i _
        exact sub_le_sub_left (prefix_survival_bound L hq i le_rfl) 1

/-- P007-T15, printed Lemma 8 (Supplement p. 4): the same statement with one
indicator per group and g in place of k. Groups need not be independent of one another. -/
theorem lemma8 {n g : ℕ} (L : FiniteLaw (IndicatorArray n g))
    (hn : 0 < n) (hg : 0 < g) {q : ℝ}
    (hi : RowsIndependent L) (hq : ConditionalObservationBound L q) :
    (1 - q ^ g) ^ n ≤ pAll L := lemma3 L hn hg hi hq

/-- P007-T5(a): at zero observation bound all rows are removed almost surely,
without row independence. Later variables may still be observed. -/
theorem zero_bound_all_deleted {n h : ℕ} (L : FiniteLaw (IndicatorArray n h))
    (hh : 0 < h) (hq : ConditionalObservationBound L 0) :
    pAll L = 1 ∧ (1 - (0 : ℝ)^h)^n = 1 := by
  have hz : ∀ i, prefixSurvival L i h = 0 := by
    intro i
    have hu := prefix_survival_bound L hq i le_rfl
    simp only [zero_pow (Nat.ne_of_gt hh)] at hu
    exact le_antisymm hu (probability_nonneg L _)
  have hb := probability_exists_le_sum L (fun i x => observedPrefix (x i) h)
  have he : eventProbability L (fun x => ∃ i, observedPrefix (x i) h) = 0 := by
    change eventProbability L (fun a => ∃ i, observedPrefix (a i) h) ≤ ∑ i, prefixSurvival L i h at hb
    simp only [hz, Finset.sum_const_zero] at hb
    exact le_antisymm hb (probability_nonneg L _)
  have hp := probability_compl L (fun x => ∃ i, observedPrefix (x i) h)
  have hsame : pAll L = eventProbability L (fun x => ¬ ∃ i, observedPrefix (x i) h) := by
    apply probability_congr L
    intro x
    simp
  constructor
  · rw [hsame,hp,he]; norm_num
  · simp [zero_pow (Nat.ne_of_gt hh)]

/-- The first observed-prefix event is exactly observation of the first variable/group. 
Supporting finite lemma for the corrected zero-bound sentence of Lemma 3/8 (p. 154; Supplement p. 4). -/
theorem first_prefix_event {h : ℕ} (hh : 0 < h) (r : IndicatorRow h) :
    observedPrefix r 1 ↔ r ⟨0, hh⟩ = false := by
  constructor
  · intro he
    exact he ⟨0, hh⟩ (by simp)
  · intro he t ht
    have ht0 : t = ⟨0, hh⟩ := Fin.ext (by change t.val=0; omega)
    simpa [ht0] using he

/-- P007-T5(a): q_*=0 forces the first variable/group, specifically, to be missing
with probability one. No assertion is made about later variables/groups. -/
theorem zero_bound_first_missing {n h : ℕ} (L : FiniteLaw (IndicatorArray n h))
    (hh : 0 < h) (hq : ConditionalObservationBound L 0) (i : Fin n) :
    eventProbability L (fun x => x i ⟨0, hh⟩ = true) = 1 := by
  have hz : prefixSurvival L i 1 = 0 :=
    le_antisymm ((hq.2.2 i).1 hh) (probability_nonneg L _)
  have hp := probability_compl L (fun x => observedPrefix (x i) 1)
  have he := probability_congr L (P := fun x => x i ⟨0, hh⟩ = true)
    (Q := fun x => ¬ observedPrefix (x i) 1) (by intro x; rw [first_prefix_event hh]; simp)
  rw [he, hp]
  change 1 - prefixSurvival L i 1 = 1
  rw [hz]; norm_num

/-- P007-T5(c), corrected proof of Lemma 3 (p. 154) and Lemma 8 (Supplement p. 4): the repaired q_ij uses zero on a null prefix and the ordinary ratio
on a positive prefix. Index j here is zero-based: j=0 is the first variable/group. -/
noncomputable def repairedConditional {n h : ℕ} (L : FiniteLaw (IndicatorArray n h))
    (i : Fin n) (j : ℕ) : ℝ :=
  if 0 < prefixSurvival L i j then prefixSurvival L i (j+1) / prefixSurvival L i j else 0

/-- P007-T5(c): the zero convention restores the chain-rule relation in every case. -/
theorem repaired_chain_step {n h : ℕ} (L : FiniteLaw (IndicatorArray n h))
    (i : Fin n) (j : ℕ) :
    prefixSurvival L i (j+1) = prefixSurvival L i j * repairedConditional L i j := by
  unfold repairedConditional
  split_ifs with hs
  · field_simp [ne_of_gt hs]
  · have hz : prefixSurvival L i j = 0 :=
      le_antisymm (not_lt.mp hs) (probability_nonneg L _)
    have hm := prefix_antitone L i (Nat.le_succ j)
    have hz' : prefixSurvival L i (j+1) = 0 :=
      le_antisymm (hm.trans (le_of_eq hz)) (probability_nonneg L _)
    simp [hz, hz']

/-- P007-T5(c): the repaired conditionals are nonnegative and at most q_* even
when an earlier prefix has probability zero. -/
theorem repairedConditional_bounds {n h : ℕ} (L : FiniteLaw (IndicatorArray n h))
    {q : ℝ} (hq : ConditionalObservationBound L q) (i : Fin n) {j : ℕ} (hj : j < h) :
    0 ≤ repairedConditional L i j ∧ repairedConditional L i j ≤ q := by
  classical
  unfold repairedConditional
  split_ifs with hs
  · constructor
    · exact div_nonneg (probability_nonneg L _) hs.le
    · by_cases hj0 : j=0
      · subst j
        simpa [prefix_zero] using (hq.2.2 i).1 hj
      · exact (hq.2.2 i).2 j (by omega) hj hs
  · exact ⟨le_rfl, hq.1⟩

/-- P007-T5(c): the full-prefix survival probability is the product of the repaired
q_i1,...,q_ih, the product intended by the printed comma lists on p. 154. -/
theorem repaired_chain_product {n h : ℕ} (L : FiniteLaw (IndicatorArray n h))
    (i : Fin n) (j : ℕ) :
    prefixSurvival L i j = ∏ t ∈ Finset.range j, repairedConditional L i t := by
  induction j with
  | zero => simp [prefix_zero]
  | succ j ih => rw [repaired_chain_step, Finset.prod_range_succ, ih]

/-- P007-T6(a): the corrected Bernoulli sandwich, with ordinary inequalities and
balanced exponents. The strict -q^h>-1 includes q=0 and requires h≥1. -/
theorem bernoulli_sandwich {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {n h : ℕ} (hh : 0 < h) :
    -1 < -(q^h) ∧ 1-q^h ≤ 1 ∧
    1 + (n : ℝ)*(-(q^h)) = 1-(n : ℝ)*q^h ∧
    1-(n : ℝ)*q^h ≤ (1-q^h)^n ∧ (1-q^h)^n ≤ 1 := by
  have hp0 : 0 ≤ q^h := pow_nonneg hq0 h
  have hp1 : q^h < 1 := pow_lt_one₀ hq0 hq1 (Nat.ne_of_gt hh)
  have hb := one_add_mul_le_pow (a := -(q^h)) (by linarith : -2 ≤ -(q^h)) n
  refine ⟨by linarith, by linarith, by ring, ?_, ?_⟩
  · simpa [sub_eq_add_neg, mul_neg] using hb
  · exact pow_le_one₀ (by linarith) (by linarith)

/-- P007-T6(b): for each fixed population, 0≤1-p_all≤n q_*^h, the finite bound
on which the asymptotic result rests. -/
theorem deletion_probability_sandwich {n h : ℕ} (L : FiniteLaw (IndicatorArray n h))
    (hn : 0 < n) (hh : 0 < h) {q : ℝ}
    (hi : RowsIndependent L) (hq : ConditionalObservationBound L q) :
    1-(n : ℝ)*q^h ≤ (1-q^h)^n ∧ (1-q^h)^n ≤ pAll L ∧ pAll L ≤ 1 ∧
    0 ≤ 1-pAll L ∧ 1-pAll L ≤ (n : ℝ)*q^h := by
  have hb := bernoulli_sandwich (n:=n) hq.1 hq.2.1 hh
  have hl := lemma3 L hn hh hi hq
  have hu := probability_le_one L (fun x => ∀ i, ¬ observedPrefix (x i) h)
  change pAll L ≤ 1 at hu
  exact ⟨hb.2.2.2.1, hl, hu, by linarith, by linarith [hb.2.2.2.1]⟩

/-- P007-T6(c), finite analytic identity used by Propositions 5 and 10 only for
q>0 and n≥1. The zero endpoint is handled by zero_bound_all_deleted. -/
theorem logarithm_decay_identity {q : ℝ} (hq : 0 < q) {n : ℕ} (hn : 0 < n) (h : ℕ) :
    (n : ℝ)*q^h = Real.exp (Real.log (n : ℝ) + (h : ℝ)*Real.log q) := by
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hq,
    Real.exp_log (by exact_mod_cast hn)]

/-- P007-T6(d): two variables per group give g_n=n and k_n=2n≠l(n)=n for n≥1;
the exponent in the grouped proof is the number of groups. -/
theorem groups_are_not_variables {n : ℕ} (hn : 0 < n) : n ≤ 2*n ∧ 2*n ≠ n := by omega

/-- Assumption 4 (p. 151), respectively Assumption 9 (Supplement p. 4): "grows
superlogarithmically in n", namely h_n/log n tends to +infinity. Values at n=0,1
use Mathlib's total log convention and cannot affect the atTop limit. -/
noncomputable def Superlogarithmic (h : ℕ → ℕ) : Prop :=
  Tendsto (fun n : ℕ => (h n : ℝ) / Real.log (n : ℝ)) atTop atTop

/-- Finite-sequence analytic lemma underlying Propositions 5 and 10: with one
fixed q∈[0,1), n q^(h_n)→0 for superlogarithmic h_n.
This includes the endpoint q=0 instead of evaluating a logarithm there. -/
theorem uniform_decay {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {k : ℕ → ℕ} (hk : Superlogarithmic k) :
    Tendsto (fun n : ℕ => (n : ℝ) * q ^ k n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hn2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  have hlogpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) := by
    filter_upwards [hn2] with n hn
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  by_cases hq : q = 0
  · have hkpos : ∀ᶠ n : ℕ in atTop, 0 < k n := by
      filter_upwards [hlogpos, hk.eventually_ge_atTop 1] with n hl hr
      have h := (le_div_iff₀ hl).mp hr
      have hkp : (0 : ℝ) < k n := by nlinarith
      exact_mod_cast hkp
    have heq : (fun n : ℕ => (n : ℝ) * q ^ k n) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [hkpos] with n hn
      simp [hq, Nat.ne_of_gt hn]
    exact tendsto_const_nhds.congr' heq.symm
  · have hqp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have hneg : Real.log q < 0 := Real.log_neg hqp hq1
    have hc : Tendsto
        (fun n : ℕ => 1 + (k n : ℝ) / Real.log (n : ℝ) * Real.log q) atTop atBot := by
      simpa [mul_comm] using
        (tendsto_const_nhds.add_atBot (hk.const_mul_atTop_of_neg hneg))
    have he : Tendsto
        (fun n : ℕ => Real.log (n : ℝ) *
          (1 + (k n : ℝ) / Real.log (n : ℝ) * Real.log q)) atTop atBot :=
      hlog.atTop_mul_atBot₀ hc
    have hz := Real.tendsto_exp_atBot.comp he
    apply hz.congr'
    filter_upwards [hlogpos] with n hl
    have hlne : Real.log (n : ℝ) ≠ 0 := ne_of_gt hl
    have hnpos : (0 : ℝ) < n := by
      by_contra hn
      have hn0 : (n : ℝ) = 0 := le_antisymm (not_lt.mp hn) (Nat.cast_nonneg n)
      simp [hn0] at hl
    have heq : Real.log (n : ℝ) *
        (1 + (k n : ℝ) / Real.log (n : ℝ) * Real.log q) =
        Real.log (n : ℝ) + (k n : ℝ) * Real.log q := by field_simp
    dsimp only [Function.comp_def]
    rw [heq, Real.exp_add, Real.exp_log hnpos, Real.exp_nat_mul, Real.exp_log hqp]

/-- Analytic squeeze step for Proposition 5/10; the probability interpretation is
proved separately in lemma3 and lemma8, rather than assumed as a named axiom. -/
theorem limit_from_finite_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {k : ℕ → ℕ} {p : ℕ → ℝ} (hk : Superlogarithmic k)
    (hlower : ∀ᶠ n in atTop, (1-q^k n)^n ≤ p n) (hupper : ∀ n, p n ≤ 1) :
    Tendsto p atTop (𝓝 1) := by
  have hz := uniform_decay hq0 hq1 hk
  have hl : Tendsto (fun n : ℕ => 1-(n : ℝ)*q^k n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [hlower] with n hn
    have hp : q^k n ≤ 1 := pow_le_one₀ hq0 hq1.le
    have hb := one_add_mul_le_pow (a := -(q^k n)) (by linarith : -2 ≤ -(q^k n)) n
    have hb' : 1-(n : ℝ)*q^k n ≤ (1-q^k n)^n := by
      simpa [sub_eq_add_neg, mul_neg] using hb
    exact hb'.trans hn
  · exact Eventually.of_forall hupper

/-- P007-T16, printed Proposition 5 (p. 151): for arbitrary changing laws of n rows
and k_n=f(n) variables, mutual independence at every n, one fixed conditional bound
q_*∈[0,1), and f(n)/log n→infinity imply p_all,n→1. Laws may depend on n; no identical
row distributions or cross-population coupling is required. -/
theorem proposition5 {k : ℕ → ℕ} (L : ∀ n, FiniteLaw (IndicatorArray n (k n)))
    (hkpos : ∀ n, 0<n → 0<k n) {q : ℝ} (hq0 : 0≤q) (hq1 : q<1)
    (hi : ∀ n, 0<n → RowsIndependent (L n))
    (hb : ∀ n, 0<n → ConditionalObservationBound (L n) q)
    (hk : Superlogarithmic k) :
    Tendsto (fun n => pAll (L n)) atTop (𝓝 1) := by
  apply limit_from_finite_bound hq0 hq1 hk
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact lemma3 (L n) hn (hkpos n hn) (hi n hn) (hb n hn)
  · intro n
    exact probability_le_one (L n) _

/-- P007-T17, printed Proposition 10 (Supplement p. 4): with h_n=g_n=l(n) group
indicators and the same fixed-bound assumptions, superlogarithmic group count implies
p_all,n→1. One indicator per group represents shared within-group missingness. -/
theorem proposition10 {g : ℕ → ℕ} (L : ∀ n, FiniteLaw (IndicatorArray n (g n)))
    (hgpos : ∀ n, 0<n → 0<g n) {q : ℝ} (hq0 : 0≤q) (hq1 : q<1)
    (hi : ∀ n, 0<n → RowsIndependent (L n))
    (hb : ∀ n, 0<n → ConditionalObservationBound (L n) q)
    (hg : Superlogarithmic g) :
    Tendsto (fun n => pAll (L n)) atTop (𝓝 1) :=
  proposition5 L hgpos hq0 hq1 hi hb hg

/-- Assumption 1 (p. 150) and 6 (Supplement p. 4): "mutually independent" coordinates are modeled by a finite product law with possibly different distributions.
This supplies concrete row-independent and cell-independent witnesses. -/
noncomputable def independentProduct {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    (L : I → FiniteLaw α) : FiniteLaw (I → α) where
  weight x := ∏ i, (L i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (L i).nonneg (x i))
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp [fun i => (L i).total]

/-- The product law multiplies probabilities of arbitrary coordinate events. 
Supporting finite lemma for Assumptions 1/6 and the sharpness model (p. 150; Supplement pp. 1,4). -/
theorem independentProduct_events {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    (L : I → FiniteLaw α) (E : I → α → Prop) :
    eventProbability (independentProduct L) (fun x => ∀ i, E i (x i)) =
      ∏ i, eventProbability (L i) (E i) := by
  classical
  simp only [eventProbability, independentProduct]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ i, E i (x i)
  · rw [if_pos hx]
    symm
    apply Finset.prod_congr rfl
    intro i _
    exact if_pos (hx i)
  · rw [if_neg hx]
    symm
    obtain ⟨i,hi⟩ := not_forall.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Each coordinate of a product law has exactly its prescribed marginal law. 
Supporting finite lemma for the concrete normalized laws used in P007-T3,T4,T7,T9,T11. -/
theorem independentProduct_marginal {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    (L : I → FiniteLaw α) (i : I) (E : α → Prop) :
    eventProbability (independentProduct L) (fun x => E (x i)) = eventProbability (L i) E := by
  classical
  have he := independentProduct_events L (fun j a => if j=i then E a else True)
  have hleft : eventProbability (independentProduct L) (fun x => ∀ j, if j=i then E (x j) else True) =
      eventProbability (independentProduct L) (fun x => E (x i)) := by
    apply probability_congr
    intro x
    constructor
    · intro hx; simpa using hx i
    · intro hx j; by_cases hj : j=i <;> simp [hj, hx]
  rw [hleft] at he
  rw [he]
  have hright : (fun j => eventProbability (L j) (fun a => if j=i then E a else True)) =
      (fun j => if j=i then eventProbability (L j) E else 1) := by
    funext j
    by_cases hj : j=i <;> simp [hj, probability_true]
  rw [hright, Fintype.prod_ite_eq']

/-- Prefix events under a product of row laws have exactly the row's marginal probability. 
Supporting finite lemma for the Lemma 3/8 proof witnesses (p. 154; Supplement p. 4). -/
theorem product_row_prefix {n h : ℕ} (L : Fin n → FiniteLaw (IndicatorRow h))
    (i : Fin n) (j : ℕ) :
    prefixSurvival (independentProduct L) i j = eventProbability (L i) (fun r => observedPrefix r j) :=
  independentProduct_marginal L i (fun r => observedPrefix r j)

/-- A specified entry under a product of row laws has its specified marginal probability. 
Supporting finite lemma for the Lemma 3/8 proof witnesses (p. 154; Supplement p. 4). -/
theorem product_row_entry {n h : ℕ} (L : Fin n → FiniteLaw (IndicatorRow h))
    (i : Fin n) (j : Fin h) (b : Bool) :
    eventProbability (independentProduct L) (fun x => x i j=b) = eventProbability (L i) (fun r => r j=b) :=
  independentProduct_marginal L i (fun r => r j=b)

/-- Product laws satisfy the full, eventwise mutual-independence definition. 
Supporting finite lemma for Assumptions 1/6 and the supplement sharpness model (p. 150; Supplement pp. 1,4). -/
theorem independentProduct_rowsIndependent {n h : ℕ}
    (L : Fin n → FiniteLaw (IndicatorRow h)) : RowsIndependent (independentProduct L) := by
  intro E
  rw [independentProduct_events]
  apply Finset.prod_congr rfl
  intro i _
  exact (independentProduct_marginal L i (E i)).symm

/-- P007-E003 witnesses A, B, D in P007-T3,T4 (proof of Lemma 3, p. 154; Lemma 8, Supplement p. 4): a one-atom law with explicitly unit mass. -/
noncomputable def pointMass {α : Type*} [Fintype α] (a : α) : FiniteLaw α where
  weight b := by classical exact if b=a then 1 else 0
  nonneg b := by classical split_ifs <;> norm_num
  total := by classical simp

/-- Point-mass event probabilities are the exact indicators of the specified atom. 
Supporting finite lemma for the explicit witnesses against the proof sentences of Lemma 3/8 (p. 154; Supplement p. 4). -/
theorem pointMass_probability {α : Type*} [Fintype α] (a : α) (P : α → Prop) :
    eventProbability (pointMass a) P = if P a then 1 else 0 := by
  classical
  unfold eventProbability pointMass
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba; simp [hba]
  · simp

/-- P007-E003 witness C in P007-T4 (proof of Lemma 3, p. 154; Lemma 8, Supplement p. 4): a convex mixture of two finite laws. -/
noncomputable def mixtureLaw {α : Type*} [Fintype α] (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (A B : FiniteLaw α) : FiniteLaw α where
  weight a := p*A.weight a + (1-p)*B.weight a
  nonneg a := add_nonneg (mul_nonneg hp0 (A.nonneg a)) (mul_nonneg (by linarith) (B.nonneg a))
  total := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, A.total, B.total]

/-- Event probabilities of a mixture are the same convex combination. 
Supporting finite lemma for witness C against the null-prefix step of Lemma 3/8 (p. 154; Supplement p. 4). -/
theorem mixtureLaw_probability {α : Type*} [Fintype α] (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (A B : FiniteLaw α) (P : α → Prop) :
    eventProbability (mixtureLaw p hp0 hp1 A B) P =
      p*eventProbability A P + (1-p)*eventProbability B P := by
  classical
  simp only [eventProbability, mixtureLaw]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

/-- P007-T3 and T4, P007-E003 witness A/B: one row (M_11,M_12)=(1,0) surely.
Read as two singleton groups, it is the same law in the grouped setting. -/
noncomputable def nullFirstLaw : FiniteLaw (IndicatorArray 1 2) :=
  independentProduct (fun _ => pointMass (fun j : Fin 2 => decide (j.val = 0)))

/-- Prefix probabilities of the explicit one-row null-first witness. Supporting finite calculation for P007-E003 witnesses A/B against Lemma 3/8 proof sentences (p. 154; Supplement p. 4). -/
theorem nullFirst_prefixes :
    prefixSurvival nullFirstLaw 0 1 = 0 ∧ prefixSurvival nullFirstLaw 0 2 = 0 ∧
    eventProbability nullFirstLaw (fun x => x 0 1 = false) = 1 ∧
    eventProbability nullFirstLaw (fun x => x 0 1 = true) = 0 := by
  simp only [nullFirstLaw, product_row_prefix, product_row_entry]
  simp [pointMass_probability, observedPrefix, Fin.forall_fin_succ]

/-- P007-T3(i)-(iv),(vi): q_*=0 and both assumptions hold in an actual normalized
law, yet variable/group two is observed surely. The all-deletion consequence stays true. -/
theorem zero_bound_counterexample :
    RowsIndependent nullFirstLaw ∧ ConditionalObservationBound nullFirstLaw 0 ∧
    eventProbability nullFirstLaw (fun x => x 0 1 = false) = 1 ∧
    eventProbability nullFirstLaw (fun x => x 0 1 = true) = 0 ∧
    pAll nullFirstLaw = 1 ∧ (1-(0 : ℝ)^2)^1 = 1 := by
  have hi : RowsIndependent nullFirstLaw := independentProduct_rowsIndependent _
  have hb : ConditionalObservationBound nullFirstLaw 0 := by
    refine ⟨le_rfl, by norm_num, ?_⟩
    intro i
    have hi0 : i=0 := Subsingleton.elim _ _
    subst i
    refine ⟨by intro _; exact nullFirst_prefixes.1.le, ?_⟩
    intro j hj1 hj2 hs
    have hj : j=1 := by omega
    subst j
    rw [nullFirst_prefixes.1] at hs
    norm_num at hs
  have hp := zero_bound_all_deleted nullFirstLaw (by norm_num) hb
  exact ⟨hi, hb, nullFirst_prefixes.2.2.1, nullFirst_prefixes.2.2.2, hp.1, hp.2⟩

/-- P007-T3(v), P007-E003 witness D: one all-missing row; q_* is still allowed to be 1/2. -/
noncomputable def fullyMissingLaw : FiniteLaw (IndicatorArray 1 2) :=
  independentProduct (fun _ => pointMass (fun _ : Fin 2 => true))

/-- P007-T3(v): full missingness satisfies Assumption 2 with every q∈[0,1),
so full missingness does not force the selected upper bound q_* to equal zero. -/
theorem fully_missing_all_bounds {q : ℝ} (hq0 : 0≤q) (hq1 : q<1) :
    RowsIndependent fullyMissingLaw ∧ ConditionalObservationBound fullyMissingLaw q ∧
    (∀ j : Fin 2, eventProbability fullyMissingLaw (fun x => x 0 j = true) = 1) := by
  refine ⟨independentProduct_rowsIndependent _, ⟨hq0,hq1,?_⟩, ?_⟩
  · intro i
    have hi0 : i=0 := Subsingleton.elim _ _
    subst i
    have hs : prefixSurvival fullyMissingLaw 0 1 = 0 := by
      simp only [fullyMissingLaw, product_row_prefix]
      simp [pointMass_probability, observedPrefix, Fin.forall_fin_succ]
    refine ⟨by intro _; simpa [hs] using hq0, ?_⟩
    intro j hj1 hj2 hp
    have hj : j=1 := by omega
    subst j
    rw [hs] at hp
    norm_num at hp
  · intro j
    simp only [fullyMissingLaw, product_row_entry]
    simp [pointMass_probability]

/-- P007-T4 witness B: at q_*=1/2, null conditional probabilities are not determined
by the law. All v∈[0,1] solve s_12=v s_11; v=1 violates the alleged bound, while v=0
preserves it. This relation is retained rather than Mathlib's totalized 0/0 convention. -/
theorem null_prefix_counterexample :
    RowsIndependent nullFirstLaw ∧ ConditionalObservationBound nullFirstLaw (1/2) ∧
    prefixSurvival nullFirstLaw 0 1 = 0 ∧ prefixSurvival nullFirstLaw 0 2 = 0 ∧
    (∀ v : ℝ, 0≤v → v≤1 → prefixSurvival nullFirstLaw 0 2 = v*prefixSurvival nullFirstLaw 0 1) ∧
    (1/2 : ℝ) < 1 ∧
    prefixSurvival nullFirstLaw 0 2 ≤ (1/2 : ℝ)^2 ∧
    (3/4 : ℝ) ≤ pAll nullFirstLaw := by
  have hz := zero_bound_counterexample
  have hb : ConditionalObservationBound nullFirstLaw (1/2) := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro i
    have hi0 : i=0 := Subsingleton.elim _ _
    subst i
    refine ⟨by intro _; rw [nullFirst_prefixes.1]; norm_num, ?_⟩
    intro j hj1 hj2 hs
    have hj : j=1 := by omega
    subst j
    rw [nullFirst_prefixes.1] at hs
    norm_num at hs
  refine ⟨hz.1, hb, nullFirst_prefixes.1, nullFirst_prefixes.2.1, ?_, by norm_num, ?_, ?_⟩
  · intro v _ _; simp [nullFirst_prefixes.1, nullFirst_prefixes.2.1]
  · rw [nullFirst_prefixes.2.1]; norm_num
  · rw [hz.2.2.2.2.1]; norm_num

/-- P007-T4 witness C: two independent rows, each equally likely to be (1,0,0)
or (0,1,0). The first prefix is positive but the next prefix is null. -/
noncomputable def laterNullLaw : FiniteLaw (IndicatorArray 2 3) :=
  independentProduct (fun _ => mixtureLaw (1/2) (by norm_num) (by norm_num)
    (pointMass (fun j : Fin 3 => decide (j.val = 0)))
    (pointMass (fun j : Fin 3 => decide (j.val = 1))))

/-- P007-T4(v)-(viii): every hypothesis holds while the conditioning event for the
third variable/group is null. Prefixes and the unchanged lemma conclusion are exact. -/
theorem later_null_counterexample :
    RowsIndependent laterNullLaw ∧ ConditionalObservationBound laterNullLaw (1/2) ∧
    (∀ i, prefixSurvival laterNullLaw i 1 = 1/2 ∧
      prefixSurvival laterNullLaw i 2 = 0 ∧ prefixSurvival laterNullLaw i 3 = 0) ∧
    pAll laterNullLaw = 1 ∧ (49/64 : ℝ) ≤ pAll laterNullLaw := by
  have hs : ∀ i, prefixSurvival laterNullLaw i 1 = 1/2 ∧
      prefixSurvival laterNullLaw i 2 = 0 ∧ prefixSurvival laterNullLaw i 3 = 0 := by
    intro i
    simp only [laterNullLaw, product_row_prefix]
    norm_num [mixtureLaw_probability, pointMass_probability, observedPrefix, Fin.forall_fin_succ]
  have hi : RowsIndependent laterNullLaw := independentProduct_rowsIndependent _
  have hb : ConditionalObservationBound laterNullLaw (1/2) := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro i
    refine ⟨by intro _; rw [(hs i).1], ?_⟩
    intro j hj1 hj3 hp
    interval_cases j
    · rw [(hs i).2.1, (hs i).1]; norm_num
    · rw [(hs i).2.1] at hp; norm_num at hp
  have hp : pAll laterNullLaw = 1 := by rw [independent_rows_product laterNullLaw hi]; simp [hs]
  exact ⟨hi, hb, hs, hp, by rw [hp]; norm_num⟩

/-- P007-T8(iv), equality witness for the "sharp lower bound" of Supplement p. 1: Pr(M_ij=0)=q_*. A Bernoulli observation law has M=0 with probability q, M=1 with probability 1-q. -/
noncomputable def observationBernoulli (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) : FiniteLaw Bool where
  weight b := if b then 1-q else q
  nonneg b := by cases b <;> simp <;> linarith
  total := by simp [Fintype.sum_bool]

/-- The prescribed observed probability in the Bernoulli cell law. 
Supporting finite lemma for the supplement equality model and the Figure 4/5 witnesses (Supplement pp. 1-3). -/
theorem observationBernoulli_false (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) :
    eventProbability (observationBernoulli q hq0 hq1) (fun b => b=false) = q := by
  simp [eventProbability, observationBernoulli, Fintype.sum_bool]

/-- P007-T8(iv), equality witness for the sharp lower bound of Supplement p. 1: "all n*k indicators independent", generalized to observation probabilities a_ij. The two nested product
laws mean independence of every cell, and automatically independence of entire row vectors. -/
noncomputable def independentCells {n h : ℕ} (a : Fin n → Fin h → ℝ)
    (ha0 : ∀ i j, 0≤a i j) (ha1 : ∀ i j, a i j≤1) : FiniteLaw (IndicatorArray n h) :=
  independentProduct (fun i => independentProduct
    (fun j => observationBernoulli (a i j) (ha0 i j) (ha1 i j)))

/-- Independent-cell models have independent row vectors. 
Supporting finite lemma for the supplement equality model and Figure 4/5 witnesses (Supplement pp. 1-3). -/
theorem independentCells_rows {n h : ℕ} (a : Fin n → Fin h → ℝ)
    (ha0 : ∀ i j, 0≤a i j) (ha1 : ∀ i j, a i j≤1) :
    RowsIndependent (independentCells a ha0 ha1) := independentProduct_rowsIndependent _

/-- Exact prefix probabilities under independent cells: multiply the observed chances
in the prefix, with factor one for unused columns. 
Supporting finite lemma for the supplement equality model and Figure 4/5 witnesses (Supplement pp. 1-3). -/
theorem independentCells_prefix {n h : ℕ} (a : Fin n → Fin h → ℝ)
    (ha0 : ∀ i j, 0≤a i j) (ha1 : ∀ i j, a i j≤1) (i : Fin n) (j : ℕ) :
    prefixSurvival (independentCells a ha0 ha1) i j =
      ∏ t : Fin h, if t.val < j then a i t else 1 := by
  unfold independentCells
  rw [product_row_prefix]
  have he : eventProbability
      (independentProduct (fun t => observationBernoulli (a i t) (ha0 i t) (ha1 i t)))
      (fun r => observedPrefix r j) =
      eventProbability
      (independentProduct (fun t => observationBernoulli (a i t) (ha0 i t) (ha1 i t)))
      (fun r => ∀ t, if t.val<j then r t=false else True) := by
    apply probability_congr
    intro r
    simp [observedPrefix]
  rw [he]
  rw [independentProduct_events
    (fun t => observationBernoulli (a i t) (ha0 i t) (ha1 i t))
    (fun t b => if t.val<j then b=false else True)]
  apply Finset.prod_congr rfl
  intro t _
  by_cases ht : t.val<j <;> simp [ht, observationBernoulli_false, probability_true]

/-- Supplement p. 1: the sharp lower bound underline(p_all)=(1-q_*^k)^n. -/
noncomputable def bestCaseBound (n : ℕ) (q : ℝ) (k : ℕ) : ℝ := (1-q^k)^n

/-- Supplement p. 2, corrected Figure 5: b_k=1-q_*^k, independent of n. -/
noncomputable def deletedFractionBound (q : ℝ) (k : ℕ) : ℝ := 1-q^k

/-- P007-T8(iv), equality witness for the "sharp lower bound" printed in Supplement p. 1: all n k indicators independent with
Pr(M_ij=0)=q_*, represented as an actual normalized law. -/
noncomputable def equalProbabilityLaw (n h : ℕ) (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) :
    FiniteLaw (IndicatorArray n h) :=
  independentCells (fun _ _ => q) (fun _ _ => hq0) (fun _ _ => hq1)

/-- Equal-probability model: every prefix of j≤h variables survives with chance q^j. 
Supporting finite lemma for attainment of the supplement sharp lower bound (Supplement p. 1). -/
theorem equalProbability_prefix (n h : ℕ) (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
    (i : Fin n) {j : ℕ} (hj : j≤h) :
    prefixSurvival (equalProbabilityLaw n h q hq0 hq1) i j = q^j := by
  rw [equalProbabilityLaw, independentCells_prefix, Finset.prod_ite]
  simp [Fin.card_filter_val_lt, Nat.min_eq_right hj]

/-- The equality model satisfies the paper's Assumption 2/7, including q=0. 
Supporting finite lemma for attainment of the supplement sharp lower bound (Supplement p. 1). -/
theorem equalProbability_assumption (n h : ℕ) (q : ℝ) (hq0 : 0≤q) (hq1 : q<1) :
    ConditionalObservationBound (equalProbabilityLaw n h q hq0 hq1.le) q := by
  refine ⟨hq0, hq1, ?_⟩
  intro i
  refine ⟨?_, ?_⟩
  · intro hh
    rw [equalProbability_prefix n h q hq0 hq1.le i (show 1≤h by omega), pow_one]
  · intro j hj1 hjh hs
    rw [equalProbability_prefix n h q hq0 hq1.le i (show j+1≤h by omega),
      equalProbability_prefix n h q hq0 hq1.le i hjh.le, pow_succ]
    rw [equalProbability_prefix n h q hq0 hq1.le i hjh.le] at hs
    rw [mul_div_cancel_left₀ q (ne_of_gt hs)]

/-- P007-T8(iv): the sharp lower bound is attained by the explicit equality law. -/
theorem bestCase_attained (n h : ℕ) (q : ℝ) (hq0 : 0≤q) (hq1 : q<1) :
    RowsIndependent (equalProbabilityLaw n h q hq0 hq1.le) ∧
    ConditionalObservationBound (equalProbabilityLaw n h q hq0 hq1.le) q ∧
    pAll (equalProbabilityLaw n h q hq0 hq1.le) = bestCaseBound n q h := by
  have hi : RowsIndependent (equalProbabilityLaw n h q hq0 hq1.le) := independentCells_rows _ _ _
  refine ⟨hi, equalProbability_assumption n h q hq0 hq1, ?_⟩
  rw [independent_rows_product _ hi]
  simp [equalProbability_prefix n h q hq0 hq1.le, bestCaseBound]

/-- P007-T10, corrected Figure 5 (Supporting Information A, pp. 2-3): D_i is "1 if row i has at least one missing entry" and zero otherwise. -/
noncomputable def removedRowIndicator {n h : ℕ} (x : IndicatorArray n h) (i : Fin n) : ℝ := by
  classical exact if observedPrefix (x i) h then 0 else 1

/-- P007-T10, corrected Figure 5 (Supporting Information A, pp. 2-3): "the proportion of rows removed" is F_n=(1/n)sum_i D_i, the fraction of removed
rows, not the fraction of missing cells. -/
noncomputable def removedFraction {n h : ℕ} (x : IndicatorArray n h) : ℝ :=
  (∑ i, removedRowIndicator x i) / n

/-- P007-T10(i): E[D_i]=1-s_ih, with no row independence assumption. -/
theorem expected_removed_row {n h : ℕ} (L : FiniteLaw (IndicatorArray n h)) (i : Fin n) :
    finiteExpectation L (fun x => removedRowIndicator x i) = 1-prefixSurvival L i h := by
  change finiteExpectation L (fun x => removedRowIndicator x i) =
    1-eventProbability L (fun x => observedPrefix (x i) h)
  rw [← probability_compl]
  unfold finiteExpectation removedRowIndicator eventProbability
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : observedPrefix (x i) h <;> simp [hx]

/-- P007-T10(ii): E[F_n]=(1/n)sum_i(1-s_ih), by finite linearity of expectation. -/
theorem expected_removed_fraction {n h : ℕ} (L : FiniteLaw (IndicatorArray n h)) :
    finiteExpectation L removedFraction = (∑ i, (1-prefixSurvival L i h)) / n := by
  change (∑ x, L.weight x * ((∑ i, removedRowIndicator x i) / (n : ℝ))) = _
  have hmul : ∀ x, L.weight x * ((∑ i, removedRowIndicator x i) / (n : ℝ)) =
      (∑ i, L.weight x * removedRowIndicator x i) / n := by
    intro x
    rw [← Finset.mul_sum]
    ring
  simp_rw [hmul]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact expected_removed_row L i

/-- P007-T10(i)-(ii): b_k is a lower bound on E[D_i] and E[F_n], without
Assumption 1. This corrects the word "upper" in Supplement p. 2. -/
theorem expected_deletion_lower_bound {n h : ℕ} (L : FiniteLaw (IndicatorArray n h))
    (hn : 0<n) {q : ℝ} (hq : ConditionalObservationBound L q) :
    (∀ i, deletedFractionBound q h ≤ finiteExpectation L (fun x => removedRowIndicator x i)) ∧
    deletedFractionBound q h ≤ finiteExpectation L removedFraction := by
  have hi : ∀ i, deletedFractionBound q h ≤ 1-prefixSurvival L i h := by
    intro i
    exact sub_le_sub_left (prefix_survival_bound L hq i le_rfl) 1
  constructor
  · intro i; rw [expected_removed_row]; exact hi i
  · rw [expected_removed_fraction]
    apply (le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ)<n)).mpr
    calc
      deletedFractionBound q h * (n : ℝ) = ∑ _i : Fin n, deletedFractionBound q h := by simp [mul_comm]
      _ ≤ ∑ i : Fin n, (1-prefixSurvival L i h) := Finset.sum_le_sum (fun i _ => hi i)

/-- P007-T10(iii): independent equal-observation cells attain the lower bound on
expected removed fraction. The finite law also satisfies both paper assumptions. -/
theorem expected_deletion_bound_attained {n h : ℕ} (hn : 0<n)
    (q : ℝ) (hq0 : 0≤q) (hq1 : q<1) :
    finiteExpectation (equalProbabilityLaw n h q hq0 hq1.le) removedFraction = deletedFractionBound q h := by
  rw [expected_removed_fraction]
  simp only [equalProbability_prefix n h q hq0 hq1.le _ le_rfl,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold deletedFractionBound
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

/-- P007-T10(iv): the Figure 5 quantity is b_k, whereas underline(p_all)=b_k^n.
For n≥2 and 0<q<1, h≥1, the latter is strictly smaller. -/
theorem fraction_bound_vs_all_bound {n h : ℕ} {q : ℝ}
    (hn : 2≤n) (hh : 0<h) (hq0 : 0<q) (hq1 : q<1) :
    bestCaseBound n q h = (deletedFractionBound q h)^n ∧
    bestCaseBound 1 q h = deletedFractionBound q h ∧
    0 < deletedFractionBound q h ∧ deletedFractionBound q h < 1 ∧
    bestCaseBound n q h < deletedFractionBound q h := by
  have hpow0 : 0<q^h := pow_pos hq0 h
  have hpow1 : q^h<1 := pow_lt_one₀ hq0.le hq1 (Nat.ne_of_gt hh)
  have hb0 : 0<deletedFractionBound q h := by unfold deletedFractionBound; linarith
  have hb1 : deletedFractionBound q h<1 := by unfold deletedFractionBound; linarith
  refine ⟨rfl, by simp [bestCaseBound, deletedFractionBound], hb0, hb1, ?_⟩
  change (deletedFractionBound q h)^n < deletedFractionBound q h
  simpa using pow_right_strictAnti₀ hb0 hb1 (show 1<n by omega)

/-- Prefix multiplication in an independent-cell model; j is the new zero-based column. 
Supporting finite lemma for the supplement equality model and Figure 4/5 witnesses (Supplement pp. 1-3). -/
theorem independentCells_prefix_step {n h : ℕ} (a : Fin n → Fin h → ℝ)
    (ha0 : ∀ i j, 0≤a i j) (ha1 : ∀ i j, a i j≤1) (i : Fin n)
    {j : ℕ} (hj : j<h) :
    prefixSurvival (independentCells a ha0 ha1) i (j+1) =
      prefixSurvival (independentCells a ha0 ha1) i j * a i ⟨j,hj⟩ := by
  classical
  rw [independentCells_prefix, independentCells_prefix]
  have he : (fun t : Fin h => if t.val<j+1 then a i t else 1) =
      (fun t : Fin h => (if t.val<j then a i t else 1) *
        (if t=⟨j,hj⟩ then a i t else 1)) := by
    funext t
    by_cases ht : t.val<j
    · have hne : t ≠ ⟨j,hj⟩ := by intro e; have := congrArg Fin.val e; simp at this; omega
      simp [ht, show t.val<j+1 by omega, hne]
    · by_cases he : t=⟨j,hj⟩
      · subst t; simp
      · have hge : ¬ t.val<j+1 := by
          intro hl
          have : t.val=j := by omega
          exact he (Fin.ext this)
        simp [ht, he, hge]
  rw [he, Finset.prod_mul_distrib, Fintype.prod_ite_eq']

/-- Independent-cell laws with every observation chance ≤q obey the printed
conditional bound, even when an earlier prefix is null. 
Supporting finite lemma for Assumption 2 in the explicit equality and Figure 4/5 models (p. 150; Supplement pp. 1-3). -/
theorem independentCells_assumption {n h : ℕ} (a : Fin n → Fin h → ℝ)
    (ha0 : ∀ i j, 0≤a i j) (ha1 : ∀ i j, a i j≤1) {q : ℝ}
    (hq0 : 0≤q) (hq1 : q<1) (haq : ∀ i j, a i j≤q) :
    ConditionalObservationBound (independentCells a ha0 ha1) q := by
  refine ⟨hq0,hq1,?_⟩
  intro i
  refine ⟨?_,?_⟩
  · intro hh
    have he := independentCells_prefix_step a ha0 ha1 i (j:=0) hh
    simpa [prefix_zero] using he.le.trans (by simpa [prefix_zero] using haq i ⟨0,hh⟩)
  · intro j _ hj hs
    rw [independentCells_prefix_step a ha0 ha1 i hj, mul_div_cancel_left₀ _ (ne_of_gt hs)]
    exact haq i ⟨j,hj⟩

/-- P007-T9, P007-E006 witness: two rows, two columns; observation chances 3/4 and 1/2.
All four indicators are independent and the chosen q_*=3/4 is the least allowed bound. -/
noncomputable def figure5Witness : FiniteLaw (IndicatorArray 2 2) :=
  independentCells (fun _ => ![(3/4 : ℝ),1/2])
    (by intro i j; fin_cases j <;> norm_num)
    (by intro i j; fin_cases j <;> norm_num)

/-- Exact complete-prefix probabilities for the Figure 5 witness (Supplement pp. 2-3; P007-T9). -/
theorem figure5Witness_prefixes (i : Fin 2) :
    prefixSurvival figure5Witness i 1 = 3/4 ∧ prefixSurvival figure5Witness i 2 = 3/8 := by
  unfold figure5Witness
  rw [independentCells_prefix, independentCells_prefix]
  norm_num [Fin.prod_univ_succ]

/-- P007-T9(i)-(v): an actual law satisfying every hypothesis has E[F_2]=5/8,
strictly above 1-q_*^2=7/16. Its p_all=25/64 and lower bound 49/256 are different
from the Figure 5 curve. The least-bound assertion is included. -/
theorem figure5_upper_bound_counterexample :
    RowsIndependent figure5Witness ∧ ConditionalObservationBound figure5Witness (3/4) ∧
    (∀ q : ℝ, ConditionalObservationBound figure5Witness q → (3/4 : ℝ)≤q) ∧
    (∀ i, finiteExpectation figure5Witness (fun x => removedRowIndicator x i) = 5/8) ∧
    finiteExpectation figure5Witness removedFraction = 5/8 ∧
    deletedFractionBound (3/4) 2 = 7/16 ∧
    deletedFractionBound (3/4) 2 < finiteExpectation figure5Witness removedFraction ∧
    bestCaseBound 2 (3/4) 2 = 49/256 ∧ bestCaseBound 2 (3/4) 2 ≠ deletedFractionBound (3/4) 2 ∧
    pAll figure5Witness = 25/64 := by
  have hi : RowsIndependent figure5Witness := independentCells_rows _ _ _
  have hb : ConditionalObservationBound figure5Witness (3/4) := by
    apply independentCells_assumption
    · norm_num
    · norm_num
    · intro i j; fin_cases j <;> norm_num
  have hd : ∀ i, finiteExpectation figure5Witness (fun x => removedRowIndicator x i) = 5/8 := by
    intro i; rw [expected_removed_row, (figure5Witness_prefixes i).2]; norm_num
  have hf : finiteExpectation figure5Witness removedFraction = 5/8 := by
    rw [expected_removed_fraction]
    norm_num [Fin.sum_univ_succ, figure5Witness_prefixes]
  refine ⟨hi,hb,?_,hd,hf,by norm_num [deletedFractionBound],?_,
    by norm_num [bestCaseBound],by norm_num [bestCaseBound,deletedFractionBound],?_⟩
  · intro q hq
    have he := (hq.2.2 (0 : Fin 2)).1 (by norm_num)
    rwa [(figure5Witness_prefixes 0).1] at he
  · rw [hf]; norm_num [deletedFractionBound]
  · rw [independent_rows_product _ hi]
    norm_num [Fin.prod_univ_succ, figure5Witness_prefixes]

/-- "i.i.d." in Section 3.1 (p. 152), for comparison with Assumption 1: equality
of the distributions of all row vectors, tested by all row events. -/
noncomputable def RowsIdenticallyDistributed {n h : ℕ} (L : FiniteLaw (IndicatorArray n h)) : Prop :=
  ∀ (i j : Fin n) (E : IndicatorRow h → Prop),
    eventProbability L (fun x => E (x i)) = eventProbability L (fun x => E (x j))

/-- P007-T11(ii), P007-E004 witness: independent one-column rows with observed chances
1/4 and 1/2. The row laws differ. -/
noncomputable def nonidenticalRowsWitness : FiniteLaw (IndicatorArray 2 1) :=
  independentCells (fun i _ => ![(1/4 : ℝ),1/2] i)
    (by intro i j; fin_cases i <;> norm_num)
    (by intro i j; fin_cases i <;> norm_num)

/-- P007-T11(i)-(ii): Assumptions 1 and 2 do not entail identical row distribution.
The two-row witness still satisfies the lower bound of Lemma 3. -/
theorem mutually_independent_need_not_be_iid :
    RowsIndependent nonidenticalRowsWitness ∧
    ConditionalObservationBound nonidenticalRowsWitness (1/2) ∧
    ¬ RowsIdenticallyDistributed nonidenticalRowsWitness ∧
    prefixSurvival nonidenticalRowsWitness 0 1 = 1/4 ∧
    prefixSurvival nonidenticalRowsWitness 1 1 = 1/2 ∧
    pAll nonidenticalRowsWitness = 3/8 ∧ bestCaseBound 2 (1/2) 1 = 1/4 ∧
    bestCaseBound 2 (1/2) 1 ≤ pAll nonidenticalRowsWitness := by
  have hs : ∀ i, prefixSurvival nonidenticalRowsWitness i 1 = ![(1/4 : ℝ),1/2] i := by
    intro i
    unfold nonidenticalRowsWitness
    rw [independentCells_prefix]
    simp [Fin.prod_univ_succ]
  have hi : RowsIndependent nonidenticalRowsWitness := independentCells_rows _ _ _
  have hb : ConditionalObservationBound nonidenticalRowsWitness (1/2) := by
    apply independentCells_assumption
    · norm_num
    · norm_num
    · intro i j; fin_cases i <;> norm_num
  have hp : pAll nonidenticalRowsWitness = 3/8 := by
    rw [independent_rows_product _ hi]
    norm_num [Fin.prod_univ_succ, hs]
  refine ⟨hi,hb,?_,by simpa using hs 0,by simpa using hs 1,hp,by norm_num [bestCaseBound],?_⟩
  · intro hid
    have he := hid 0 1 (fun r => observedPrefix r 1)
    change prefixSurvival nonidenticalRowsWitness 0 1 = prefixSurvival nonidenticalRowsWitness 1 1 at he
    rw [hs,hs] at he
    norm_num at he
  · rw [hp]; norm_num [bestCaseBound]

/-- P007-T7(c): all cells independent, first-column observation chance 3/4 and
later-column chance 1/4. This respects q_*=3/4 while actual deletion exceeds the bound. -/
noncomputable def unequalProbabilityLaw (n h : ℕ) : FiniteLaw (IndicatorArray n h) :=
  independentCells (fun _ t => if t.val=0 then (3/4 : ℝ) else 1/4)
    (by intro i t; split_ifs <;> norm_num) (by intro i t; split_ifs <;> norm_num)

/-- All the hypotheses of the paper hold for the unequal-probability witnesses. 
Supporting finite lemma for the literal upper-guarantee counterexamples to Figure 4 (Supplement p. 2). -/
theorem unequalProbability_assumptions (n h : ℕ) :
    RowsIndependent (unequalProbabilityLaw n h) ∧
    ConditionalObservationBound (unequalProbabilityLaw n h) (3/4) := by
  refine ⟨independentCells_rows _ _ _,?_⟩
  apply independentCells_assumption
  · norm_num
  · norm_num
  · intro i t; split_ifs <;> norm_num

/-- Complete-row probability of the unequal-probability law is 3/4^h for h≥1. 
Supporting finite lemma for the literal upper-guarantee counterexamples to Figure 4 (Supplement p. 2). -/
theorem unequalProbability_full_prefix (n h : ℕ) (hh : 0<h) (i : Fin n) :
    prefixSurvival (unequalProbabilityLaw n h) i h = (3 : ℝ)/4^h := by
  unfold unequalProbabilityLaw
  rw [independentCells_prefix]
  cases h with
  | zero => omega
  | succ h =>
      simp [Fin.prod_univ_succ, pow_succ, Fin.is_lt]
      ring

/-- Actual all-deletion probability of the unequal-probability law. 
Supporting finite lemma for the literal upper-guarantee counterexamples to Figure 4 (Supplement p. 2). -/
theorem unequalProbability_all (n h : ℕ) (hh : 0<h) :
    pAll (unequalProbabilityLaw n h) = (1-(3 : ℝ)/4^h)^n := by
  rw [independent_rows_product _ (unequalProbability_assumptions n h).1]
  simp [unequalProbability_full_prefix n h hh]

/-- P007-T7(c1)-(c2): the lower bound being below 0.5 or 0.99 does not ensure
that actual p_all is below that value. These explicit independent-cell laws meet both assumptions. -/
theorem lower_bound_is_not_upper_guarantee :
    RowsIndependent (unequalProbabilityLaw 1 2) ∧
    ConditionalObservationBound (unequalProbabilityLaw 1 2) (3/4) ∧
    bestCaseBound 1 (3/4) 2 = 7/16 ∧ bestCaseBound 1 (3/4) 2 ≤ 1/2 ∧
    pAll (unequalProbabilityLaw 1 2) = 13/16 ∧ (1/2 : ℝ)<pAll (unequalProbabilityLaw 1 2) ∧
    RowsIndependent (unequalProbabilityLaw 1 16) ∧
    ConditionalObservationBound (unequalProbabilityLaw 1 16) (3/4) ∧
    bestCaseBound 1 (3/4) 16 = 4251920575/4294967296 ∧
    bestCaseBound 1 (3/4) 16 < 99/100 ∧ (99/100 : ℝ)<bestCaseBound 1 (3/4) 17 ∧
    pAll (unequalProbabilityLaw 1 16) = 4294967293/4294967296 ∧
    (99/100 : ℝ)<pAll (unequalProbabilityLaw 1 16) := by
  have h2 := unequalProbability_assumptions 1 2
  have h16 := unequalProbability_assumptions 1 16
  rw [unequalProbability_all 1 2 (by norm_num), unequalProbability_all 1 16 (by norm_num)]
  norm_num [bestCaseBound]
  exact ⟨h2.1,h2.2,h16.1,h16.2⟩

/-- P007-T7(c3): at the printed n=10000,k=33,q_*=3/4 an admissible law has
p_all≥1-30000/4^33>0.99, despite the sharp lower bound being below 0.5. -/
theorem printed_parameters_actual_deletion_high :
    RowsIndependent (unequalProbabilityLaw 10000 33) ∧
    ConditionalObservationBound (unequalProbabilityLaw 10000 33) (3/4) ∧
    1-(30000 : ℝ)/4^33 ≤ pAll (unequalProbabilityLaw 10000 33) ∧
    (99/100 : ℝ)<pAll (unequalProbabilityLaw 10000 33) := by
  have hs := unequalProbability_assumptions 10000 33
  have hb := one_add_mul_le_pow (a := -((3 : ℝ)/4^33)) (by norm_num : -2 ≤ -((3 : ℝ)/4^33)) 10000
  have hl : 1-(30000 : ℝ)/4^33 ≤ pAll (unequalProbabilityLaw 10000 33) := by
    rw [unequalProbability_all 10000 33 (by norm_num)]
    have hb' : 1-(10000 : ℝ)*((3 : ℝ)/4^33) ≤ (1-(3 : ℝ)/4^33)^10000 := by
      simpa only [sub_eq_add_neg, mul_neg, Nat.cast_ofNat] using hb
    have he : 1-(10000 : ℝ)*((3 : ℝ)/4^33) = 1-(30000 : ℝ)/4^33 := by ring
    rw [he] at hb'
    exact hb' 
  refine ⟨hs.1,hs.2,hl,?_⟩
  exact lt_of_lt_of_le (by norm_num : (99/100 : ℝ)<1-30000/4^33) hl

/-- Supplement p. 2, corrected Figure 4: the real solution of B(r)=a is
r=log(1-a^(1/n))/log(q_*), on n≥1,0<q_*<1,0<a<1. -/
noncomputable def thresholdReal (n : ℕ) (q a : ℝ) : ℝ :=
  Real.log (1-a^((n : ℝ)⁻¹)) / Real.log q

/-- Corrected Figure 4, Supplement p. 2 (P007-T8): the real extension B(x)=(1-q_*^x)^n distinguishes solving the equality from rounding its solution. -/
noncomputable def realBestCaseBound (n : ℕ) (q x : ℝ) : ℝ := (1-q^x)^n

/-- P007-T8(i): the integer lower bound starts at zero, stays below one, and is
strictly increasing in the number of variables. -/
theorem bestCase_increasing {n : ℕ} (hn : 0<n) {q : ℝ} (hq0 : 0<q) (hq1 : q<1) :
    bestCaseBound n q 0 = 0 ∧
    (∀ k, 0≤bestCaseBound n q k ∧ bestCaseBound n q k<1) ∧
    StrictMono (bestCaseBound n q) := by
  have hp : ∀ k, 0≤1-q^k := fun k => sub_nonneg.mpr (pow_le_one₀ hq0.le hq1.le)
  refine ⟨by simp [bestCaseBound, Nat.ne_of_gt hn],?_,?_⟩
  · intro k
    constructor
    · exact pow_nonneg (hp k) n
    · exact pow_lt_one₀ (hp k) (by have := pow_pos hq0 k; linarith) (Nat.ne_of_gt hn)
  · intro k l hkl
    exact pow_lt_pow_left₀ (by have := pow_right_strictAnti₀ hq0 hq1 hkl; linarith)
      (hp k) (Nat.ne_of_gt hn)

/-- Root and logarithm facts for the corrected Figure 4 inverse: the real threshold
is positive and q_*^r=1-a^(1/n). -/
theorem threshold_root {n : ℕ} (hn : 0<n) {q a : ℝ}
    (hq0 : 0<q) (hq1 : q<1) (ha0 : 0<a) (ha1 : a<1) :
    0<thresholdReal n q a ∧ q^(thresholdReal n q a) = 1-a^((n : ℝ)⁻¹) := by
  have hnr : (0 : ℝ)<n := by exact_mod_cast hn
  have ht0 : 0<a^((n : ℝ)⁻¹) := Real.rpow_pos_of_pos ha0 _
  have ht1 : a^((n : ℝ)⁻¹)<1 := Real.rpow_lt_one ha0.le ha1 (inv_pos.mpr hnr)
  have hu0 : 0<1-a^((n : ℝ)⁻¹) := by linarith
  have hu1 : 1-a^((n : ℝ)⁻¹)<1 := by linarith
  have hqlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have hulog : Real.log (1-a^((n : ℝ)⁻¹)) < 0 := Real.log_neg hu0 hu1
  constructor
  · exact div_pos_of_neg_of_neg hulog hqlog
  · rw [Real.rpow_def_of_pos hq0]
    have he : Real.log q * thresholdReal n q a = Real.log (1-a^((n : ℝ)⁻¹)) := by
      unfold thresholdReal
      field_simp [ne_of_lt hqlog]
    rw [he, Real.exp_log hu0]

/-- P007-T8(ii): for every real x≥0, the corrected threshold r uniquely inverts
the lower bound: B(x)≤a iff x≤r, and B(x)≥a iff x≥r. -/
theorem threshold_real_inversion {n : ℕ} (hn : 0<n) {q a : ℝ}
    (hq0 : 0<q) (hq1 : q<1) (ha0 : 0<a) (ha1 : a<1) {x : ℝ} (hx : 0≤x) :
    (realBestCaseBound n q x ≤ a ↔ x≤thresholdReal n q a) ∧
    (a ≤ realBestCaseBound n q x ↔ thresholdReal n q a≤x) ∧
    (realBestCaseBound n q x = a ↔ x=thresholdReal n q a) := by
  have hnr : (0 : ℝ)<n := by exact_mod_cast hn
  have hb0 : 0≤1-q^x := sub_nonneg.mpr (Real.rpow_le_one hq0.le hq1.le hx)
  have he := (threshold_root hn hq0 hq1 ha0 ha1).2
  have hl : realBestCaseBound n q x ≤ a ↔ x≤thresholdReal n q a := by
    calc
      realBestCaseBound n q x ≤ a ↔ 1-q^x ≤ a^((n : ℝ)⁻¹) := by
        simpa [realBestCaseBound, Real.rpow_natCast] using
          (Real.le_rpow_inv_iff_of_pos hb0 ha0.le hnr).symm
      _ ↔ q^(thresholdReal n q a) ≤ q^x := by rw [he]; constructor <;> intro h <;> linarith
      _ ↔ x≤thresholdReal n q a := Real.rpow_le_rpow_left_iff_of_base_lt_one hq0 hq1
  have hu : a ≤ realBestCaseBound n q x ↔ thresholdReal n q a≤x := by
    calc
      a ≤ realBestCaseBound n q x ↔ a^((n : ℝ)⁻¹) ≤ 1-q^x := by
        simpa [realBestCaseBound, Real.rpow_natCast] using
          (Real.rpow_inv_le_iff_of_pos ha0.le hb0 hnr).symm
      _ ↔ q^x ≤ q^(thresholdReal n q a) := by rw [he]; constructor <;> intro h <;> linarith
      _ ↔ thresholdReal n q a≤x := Real.rpow_le_rpow_left_iff_of_base_lt_one hq0 hq1
  refine ⟨hl,hu,?_⟩
  constructor
  · intro h; exact le_antisymm (hl.mp h.le) (hu.mp h.ge)
  · intro h; exact le_antisymm (hl.mpr h.le) (hu.mpr h.ge)

/-- P007-T8(ii): r is the unique nonnegative real solution of the equality.
The printed floor is a separate integer operation, not that real solution. -/
theorem threshold_unique_solution {n : ℕ} (hn : 0<n) {q a : ℝ}
    (hq0 : 0<q) (hq1 : q<1) (ha0 : 0<a) (ha1 : a<1) :
    0<thresholdReal n q a ∧
    realBestCaseBound n q (thresholdReal n q a) = a ∧
    (∀ x : ℝ, 0≤x → realBestCaseBound n q x=a → x=thresholdReal n q a) := by
  have hr := (threshold_root hn hq0 hq1 ha0 ha1).1
  refine ⟨hr,?_,?_⟩
  · exact (threshold_real_inversion hn hq0 hq1 ha0 ha1 hr.le).2.2.mpr rfl
  · intro x hx he
    exact (threshold_real_inversion hn hq0 hq1 ha0 ha1 hx).2.2.mp he

/-- P007-T8(ii), integer specialization retaining every k≥0. -/
theorem threshold_integer_inversion {n : ℕ} (hn : 0<n) {q a : ℝ}
    (hq0 : 0<q) (hq1 : q<1) (ha0 : 0<a) (ha1 : a<1) (k : ℕ) :
    (bestCaseBound n q k ≤ a ↔ (k : ℝ)≤thresholdReal n q a) ∧
    (a ≤ bestCaseBound n q k ↔ thresholdReal n q a≤(k : ℝ)) ∧
    (bestCaseBound n q k = a ↔ (k : ℝ)=thresholdReal n q a) := by
  simpa [realBestCaseBound, bestCaseBound, Real.rpow_natCast] using
    threshold_real_inversion hn hq0 hq1 ha0 ha1 (Nat.cast_nonneg k)

/-- P007-T8(iii): floor(r) is the largest nonnegative integer with B(k)≤a;
ceil(r) is the smallest with B(k)≥a. These equivalences express the exact max/min. -/
theorem threshold_floor_ceiling {n : ℕ} (hn : 0<n) {q a : ℝ}
    (hq0 : 0<q) (hq1 : q<1) (ha0 : 0<a) (ha1 : a<1) :
    (∀ k : ℕ, bestCaseBound n q k ≤ a ↔ k≤⌊thresholdReal n q a⌋₊) ∧
    (∀ k : ℕ, a ≤ bestCaseBound n q k ↔ ⌈thresholdReal n q a⌉₊≤k) ∧
    bestCaseBound n q ⌊thresholdReal n q a⌋₊ ≤ a ∧
    a ≤ bestCaseBound n q ⌈thresholdReal n q a⌉₊ := by
  have hr := (threshold_root hn hq0 hq1 ha0 ha1).1.le
  have hl : ∀ k : ℕ, bestCaseBound n q k ≤ a ↔ k≤⌊thresholdReal n q a⌋₊ := by
    intro k
    rw [(threshold_integer_inversion hn hq0 hq1 ha0 ha1 k).1, Nat.le_floor_iff hr]
  have hu : ∀ k : ℕ, a ≤ bestCaseBound n q k ↔ ⌈thresholdReal n q a⌉₊≤k := by
    intro k
    rw [(threshold_integer_inversion hn hq0 hq1 ha0 ha1 k).2.1, Nat.ceil_le]
  exact ⟨hl,hu,(hl _).mpr le_rfl,(hu _).mpr le_rfl⟩

/-- P007-T8(iii): floor and ceiling coincide exactly at integer solutions; otherwise
ceiling=floor+1 and the integer lower bounds strictly bracket the target. -/
theorem threshold_rounding_gap {n : ℕ} (hn : 0<n) {q a : ℝ}
    (hq0 : 0<q) (hq1 : q<1) (ha0 : 0<a) (ha1 : a<1) :
    (⌈thresholdReal n q a⌉₊=⌊thresholdReal n q a⌋₊ ↔
      ∃ m : ℕ, (m : ℝ)=thresholdReal n q a) ∧
    ((¬∃ m : ℕ, (m : ℝ)=thresholdReal n q a) →
      ⌈thresholdReal n q a⌉₊=⌊thresholdReal n q a⌋₊+1 ∧
      bestCaseBound n q ⌊thresholdReal n q a⌋₊<a ∧
      a<bestCaseBound n q ⌈thresholdReal n q a⌉₊) := by
  have hr := (threshold_root hn hq0 hq1 ha0 ha1).1.le
  have heq : ⌈thresholdReal n q a⌉₊=⌊thresholdReal n q a⌋₊ ↔
      ∃ m : ℕ, (m : ℝ)=thresholdReal n q a := by
    constructor
    · intro he
      refine ⟨⌊thresholdReal n q a⌋₊,?_⟩
      have hlow := Nat.floor_le hr
      have hhigh := Nat.le_ceil (thresholdReal n q a)
      rw [he] at hhigh
      exact le_antisymm hlow hhigh
    · rintro ⟨m,hm⟩
      rw [← hm, Nat.ceil_natCast, Nat.floor_natCast]
  refine ⟨heq,?_⟩
  intro hint
  have hne := mt heq.mp hint
  have hle := Nat.floor_le_ceil (thresholdReal n q a)
  have hup := Nat.ceil_le_floor_add_one (thresholdReal n q a)
  have hgap : ⌈thresholdReal n q a⌉₊=⌊thresholdReal n q a⌋₊+1 := by omega
  have hb := threshold_floor_ceiling hn hq0 hq1 ha0 ha1
  refine ⟨hgap,lt_of_le_of_ne hb.2.2.1 ?_,lt_of_le_of_ne hb.2.2.2 ?_⟩
  · intro he
    exact hint ⟨_,(threshold_integer_inversion hn hq0 hq1 ha0 ha1 _).2.2.mp he⟩
  · intro he
    exact hint ⟨_,(threshold_integer_inversion hn hq0 hq1 ha0 ha1 _).2.2.mp he.symm⟩

/-- P007-T8(iv): the ceiling guarantees p_all≥a under the paper assumptions.
For any positive integer k<r, the explicit equal-probability law meets both assumptions
and has p_all=B(k)<a. Thus the guarantee and its sharpness concern a lower bound. -/
theorem threshold_probability_guarantee {n : ℕ} (hn : 0<n) {q a : ℝ}
    (hq0 : 0<q) (hq1 : q<1) (ha0 : 0<a) (ha1 : a<1) :
    (∀ k : ℕ, 0<k → ⌈thresholdReal n q a⌉₊≤k →
      ∀ L : FiniteLaw (IndicatorArray n k), RowsIndependent L → ConditionalObservationBound L q →
        a≤pAll L) ∧
    (∀ k : ℕ, 0<k → (k : ℝ)<thresholdReal n q a →
      RowsIndependent (equalProbabilityLaw n k q hq0.le hq1.le) ∧
      ConditionalObservationBound (equalProbabilityLaw n k q hq0.le hq1.le) q ∧
      pAll (equalProbabilityLaw n k q hq0.le hq1.le)=bestCaseBound n q k ∧
      pAll (equalProbabilityLaw n k q hq0.le hq1.le)<a) := by
  have hf := threshold_floor_ceiling hn hq0 hq1 ha0 ha1
  constructor
  · intro k hk hceil L hi hb
    exact ((hf.2.1 k).mpr hceil).trans (lemma3 L hn hk hi hb)
  · intro k hk hkr
    have he := bestCase_attained n k q hq0.le hq1
    refine ⟨he.1,he.2.1,he.2.2,?_⟩
    rw [he.2.2]
    have hu := (threshold_integer_inversion hn hq0 hq1 ha0 ha1 k).2.1
    exact lt_of_not_ge (by intro hge; exact (not_le_of_gt hkr) (hu.mp hge))

/-- P007-T7(a): n=1,q_*=3/4,a=1/2 gives B(2)=7/16<1/2<B(3)=37/64,
r strictly between 2 and 3, floor=2, ceiling=3, and no integer equality solution.
The equal-probability law at k=2 satisfies the paper assumptions and has p_all=7/16. -/
theorem floor_is_not_first_crossing :
    bestCaseBound 1 (3/4) 2 = 7/16 ∧ bestCaseBound 1 (3/4) 3 = 37/64 ∧
    bestCaseBound 1 (3/4) 2 < 1/2 ∧ (1/2 : ℝ)<bestCaseBound 1 (3/4) 3 ∧
    (2 : ℝ)<thresholdReal 1 (3/4) (1/2) ∧ thresholdReal 1 (3/4) (1/2)<3 ∧
    ⌊thresholdReal 1 (3/4) (1/2)⌋₊=2 ∧ ⌈thresholdReal 1 (3/4) (1/2)⌉₊=3 ∧
    (∀ k : ℕ, bestCaseBound 1 (3/4) k ≠ 1/2) ∧
    RowsIndependent (equalProbabilityLaw 1 2 (3/4) (by norm_num) (by norm_num)) ∧
    ConditionalObservationBound (equalProbabilityLaw 1 2 (3/4) (by norm_num) (by norm_num)) (3/4) ∧
    pAll (equalProbabilityLaw 1 2 (3/4) (by norm_num) (by norm_num))=7/16 := by
  have h2 : bestCaseBound 1 (3/4) 2 < 1/2 := by norm_num [bestCaseBound]
  have h3 : (1/2 : ℝ)<bestCaseBound 1 (3/4) 3 := by norm_num [bestCaseBound]
  have hinv (k : ℕ) := threshold_integer_inversion (n:=1) (by norm_num)
    (q:=3/4) (a:=1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) k
  have hr2 : (2 : ℝ)<thresholdReal 1 (3/4) (1/2) :=
    lt_of_not_ge (by intro h; exact (not_le_of_gt h2) ((hinv 2).2.1.mpr h))
  have hr3 : thresholdReal 1 (3/4) (1/2)<3 :=
    lt_of_not_ge (by intro h; exact (not_le_of_gt h3) ((hinv 3).1.mpr h))
  have hr0 : 0≤thresholdReal 1 (3/4) (1/2) := by linarith
  have hf : ⌊thresholdReal 1 (3/4) (1/2)⌋₊=2 := (Nat.floor_eq_iff hr0).mpr ⟨hr2.le,by simpa only [Nat.cast_ofNat, show (2 : ℝ)+1=3 by norm_num] using hr3⟩
  have hc : ⌈thresholdReal 1 (3/4) (1/2)⌉₊=3 :=
    (Nat.ceil_eq_iff (by norm_num : (3 : ℕ)≠0)).mpr ⟨by simpa using hr2,hr3.le⟩
  have he := bestCase_attained 1 2 (3/4) (by norm_num) (by norm_num)
  refine ⟨by norm_num [bestCaseBound],by norm_num [bestCaseBound],h2,h3,hr2,hr3,hf,hc,?_,he.1,he.2.1,?_⟩
  · intro k heq
    have hkreal := (hinv k).2.2.mp heq
    have hkn2 : 2<k := by exact_mod_cast (show (2 : ℝ)<k by linarith)
    have hkn3 : k<3 := by exact_mod_cast (show (k : ℝ)<3 by linarith)
    omega
  · rw [he.2.2]; norm_num [bestCaseBound]


/-- Kernel-checkable interval multiplication used in the numerical Figure 4
certificates. Bounds are rounded outward, and all rational comparisons are proved. Supporting finite inequality for the numerical worked counterexamples and corrections to Figure 4 (Supplement p. 2). -/
theorem product_interval {x y xl xu yl yu lo hi : ℝ}
    (hx : xl≤x ∧ x≤xu) (hy : yl≤y ∧ y≤yu) (hxl : 0≤xl) (hyl : 0≤yl)
    (hl : lo≤xl*yl) (hu : xu*yu≤hi) : lo≤x*y ∧ x*y≤hi := by
  constructor
  · exact hl.trans (mul_le_mul hx.1 hy.1 hyl (hxl.trans hx.1))
  · exact (mul_le_mul hx.2 hy.2 (hyl.trans hy.1) ((hxl.trans hx.1).trans hx.2)).trans hu


/-- P007-T7(b), T8(v): the exact lower bound at n=10000,k=33,q=3/4.
The proof uses outward rational intervals and repeated squaring, avoiding enormous
expanded rational powers. -/
theorem figure4_numeric_33 :
    (0.47075 : ℝ) ≤ bestCaseBound 10000 (3/4) 33 ∧ bestCaseBound 10000 (3/4) 33 < 0.47085 ∧ bestCaseBound 10000 (3/4) 33 < 1/2 := by
  have hqbase : (3 : ℝ)/4 ≤ (3 : ℝ)/4 ∧ (3 : ℝ)/4 ≤ (3 : ℝ)/4 := ⟨le_rfl,le_rfl⟩
  have q1 : (3 : ℝ)/4 ≤ ((3 : ℝ)/4)^1 ∧ ((3 : ℝ)/4)^1 ≤ (3 : ℝ)/4 := by
    simpa using hqbase
  have q2 : (9 : ℝ)/16 ≤ ((3 : ℝ)/4)^2 ∧ ((3 : ℝ)/4)^2 ≤ (9 : ℝ)/16 := by
    rw [pow_two]
    exact product_interval hqbase hqbase (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q4 : (81 : ℝ)/256 ≤ ((3 : ℝ)/4)^4 ∧ ((3 : ℝ)/4)^4 ≤ (81 : ℝ)/256 := by
    rw [show 4 = 2+2 by norm_num, pow_add]
    exact product_interval q2 q2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q8 : (6561 : ℝ)/65536 ≤ ((3 : ℝ)/4)^8 ∧ ((3 : ℝ)/4)^8 ≤ (6561 : ℝ)/65536 := by
    rw [show 8 = 4+4 by norm_num, pow_add]
    exact product_interval q4 q4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q16 : (100225957576185464859 : ℝ)/10000000000000000000000 ≤ ((3 : ℝ)/4)^16 ∧ ((3 : ℝ)/4)^16 ≤ (10022595757618546485901 : ℝ)/1000000000000000000000000 := by
    rw [show 16 = 8+8 by norm_num, pow_add]
    exact product_interval q8 q8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q32 : (100452425720633285819 : ℝ)/1000000000000000000000000 ≤ ((3 : ℝ)/4)^32 ∧ ((3 : ℝ)/4)^32 ≤ (5022621286031664291 : ℝ)/50000000000000000000000 := by
    rw [show 32 = 16+16 by norm_num, pow_add]
    exact product_interval q16 q16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q33 : (18834829822618741091 : ℝ)/250000000000000000000000 ≤ ((3 : ℝ)/4)^33 ∧ ((3 : ℝ)/4)^33 ≤ (15067863858094992873 : ℝ)/200000000000000000000000 := by
    rw [show 33 = 1+32 by norm_num, pow_add]
    exact product_interval q1 q32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsbase : (199984932136141905007127 : ℝ)/200000000000000000000000 ≤ 1-((3 : ℝ)/4)^33 ∧ 1-((3 : ℝ)/4)^33 ≤ (249981165170177381258909 : ℝ)/250000000000000000000000 := by
    constructor
    · calc
        (199984932136141905007127 : ℝ)/200000000000000000000000 = 1-((15067863858094992873 : ℝ)/200000000000000000000000) := by norm_num
        _ ≤ 1-((3 : ℝ)/4)^33 := sub_le_sub_left q33.2 1
    · calc
        1-((3 : ℝ)/4)^33 ≤ 1-((18834829822618741091 : ℝ)/250000000000000000000000) := sub_le_sub_left q33.1 1
        _ = (249981165170177381258909 : ℝ)/250000000000000000000000 := by norm_num
  have s1 : (199984932136141905007127 : ℝ)/200000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^1 ∧ (1-((3 : ℝ)/4)^33)^1 ≤ (249981165170177381258909 : ℝ)/250000000000000000000000 := by
    simpa using hsbase
  have s2 : (999849327037432081223403 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^2 ∧ (1-((3 : ℝ)/4)^33)^2 ≤ (499924663518716040611703 : ℝ)/500000000000000000000000 := by
    rw [pow_two]
    exact product_interval hsbase hsbase (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4 : (499849338388602905720129 : ℝ)/500000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^4 ∧ (1-((3 : ℝ)/4)^33)^4 ≤ (199939735355441162288053 : ℝ)/200000000000000000000000 := by
    rw [show 4 = 2+2 by norm_num, pow_add]
    exact product_interval s2 s2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s8 : (124924680543762027244589 : ℝ)/125000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^8 ∧ (1-((3 : ℝ)/4)^33)^8 ≤ (999397444350096217956727 : ℝ)/1000000000000000000000000 := by
    rw [show 8 = 4+4 by norm_num, pow_add]
    exact product_interval s4 s4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s16 : (998795251773503666882577 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^16 ∧ (1-((3 : ℝ)/4)^33)^16 ≤ (62424703235843979180163 : ℝ)/62500000000000000000000 := by
    rw [show 16 = 8+8 by norm_num, pow_add]
    exact product_interval s8 s8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s32 : (199518390993059315965023 : ℝ)/200000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^32 ∧ (1-((3 : ℝ)/4)^33)^32 ≤ (498795977482648289912589 : ℝ)/500000000000000000000000 := by
    rw [show 32 = 16+16 by norm_num, pow_add]
    exact product_interval s16 s16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s64 : (31099678394108822482697 : ℝ)/31250000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^64 ∧ (1-((3 : ℝ)/4)^33)^64 ≤ (995189708611482319446431 : ℝ)/1000000000000000000000000 := by
    rw [show 64 = 32+32 by norm_num, pow_add]
    exact product_interval s32 s32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s128 : (99040255612620708624777 : ℝ)/100000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^128 ∧ (1-((3 : ℝ)/4)^33)^128 ≤ (123800319515775885781003 : ℝ)/125000000000000000000000 := by
    rw [show 128 = 64+64 by norm_num, pow_add]
    exact product_interval s64 s64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s256 : (196179444636264955525227 : ℝ)/200000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^256 ∧ (1-((3 : ℝ)/4)^33)^256 ≤ (12261215289766559720333 : ℝ)/12500000000000000000000 := by
    rw [show 256 = 128+128 by norm_num, pow_add]
    exact product_interval s128 s128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s512 : (192431872488966734140403 : ℝ)/200000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^512 ∧ (1-((3 : ℝ)/4)^33)^512 ≤ (962159362444833670703007 : ℝ)/1000000000000000000000000 := by
    rw [show 512 = 256+256 by norm_num, pow_add]
    exact product_interval s256 s256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s1024 : (462875319370124402897707 : ℝ)/500000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^1024 ∧ (1-((3 : ℝ)/4)^33)^1024 ≤ (231437659685062201449331 : ℝ)/250000000000000000000000 := by
    rw [show 1024 = 512+512 by norm_num, pow_add]
    exact product_interval s512 s512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s2048 : (857014245127978653035653 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^2048 ∧ (1-((3 : ℝ)/4)^33)^2048 ≤ (85701424512797865303919 : ℝ)/100000000000000000000000 := by
    rw [show 2048 = 1024+1024 by norm_num, pow_add]
    exact product_interval s1024 s1024 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4096 : (45904588522017442651957 : ℝ)/62500000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^4096 ∧ (1-((3 : ℝ)/4)^33)^4096 ≤ (2869036782626090165771 : ℝ)/3906250000000000000000 := by
    rw [show 4096 = 2048+2048 by norm_num, pow_add]
    exact product_interval s2048 s2048 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s8192 : (539451199328188298241443 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^8192 ∧ (1-((3 : ℝ)/4)^33)^8192 ≤ (539451199328188298250351 : ℝ)/1000000000000000000000000 := by
    rw [show 8192 = 4096+4096 by norm_num, pow_add]
    exact product_interval s4096 s4096 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s272 : (489857744495660949373653 : ℝ)/500000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^272 ∧ (1-((3 : ℝ)/4)^33)^272 ≤ (489857744495660949373921 : ℝ)/500000000000000000000000 := by
    rw [show 272 = 16+256 by norm_num, pow_add]
    exact product_interval s16 s256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s784 : (188528486053043747769393 : ℝ)/200000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^784 ∧ (1-((3 : ℝ)/4)^33)^784 ≤ (471321215132609369424227 : ℝ)/500000000000000000000000 := by
    rw [show 784 = 272+512 by norm_num, pow_add]
    exact product_interval s272 s512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s1808 : (109081478990210836249131 : ℝ)/125000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^1808 ∧ (1-((3 : ℝ)/4)^33)^1808 ≤ (218162957980421672499057 : ℝ)/250000000000000000000000 := by
    rw [show 1808 = 784+1024 by norm_num, pow_add]
    exact product_interval s784 s1024 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s10000 : (470753077326094478694747 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^33)^10000 ∧ (1-((3 : ℝ)/4)^33)^10000 ≤ (470753077326094478704237 : ℝ)/1000000000000000000000000 := by
    rw [show 10000 = 1808+8192 by norm_num, pow_add]
    exact product_interval s1808 s8192 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold bestCaseBound
  refine ⟨?_,?_,?_⟩
  · calc
      (0.47075 : ℝ) ≤ (470753077326094478694747 : ℝ)/1000000000000000000000000 := by norm_num
      _ ≤ (1-(3/4 : ℝ)^33)^10000 := s10000.1
  · calc
      (1-(3/4 : ℝ)^33)^10000 ≤ (470753077326094478704237 : ℝ)/1000000000000000000000000 := s10000.2
      _ < (0.47085 : ℝ) := by norm_num
  · calc
      (1-(3/4 : ℝ)^33)^10000 ≤ (470753077326094478704237 : ℝ)/1000000000000000000000000 := s10000.2
      _ < (1/2 : ℝ) := by norm_num

/-- P007-T7(b), T8(v): the exact lower bound at n=10000,k=34,q=3/4.
The proof uses outward rational intervals and repeated squaring, avoiding enormous
expanded rational powers. -/
theorem figure4_numeric_34 :
    (1/2 : ℝ) < bestCaseBound 10000 (3/4) 34 := by
  have hqbase : (3 : ℝ)/4 ≤ (3 : ℝ)/4 ∧ (3 : ℝ)/4 ≤ (3 : ℝ)/4 := ⟨le_rfl,le_rfl⟩
  have q1 : (3 : ℝ)/4 ≤ ((3 : ℝ)/4)^1 ∧ ((3 : ℝ)/4)^1 ≤ (3 : ℝ)/4 := by
    simpa using hqbase
  have q2 : (9 : ℝ)/16 ≤ ((3 : ℝ)/4)^2 ∧ ((3 : ℝ)/4)^2 ≤ (9 : ℝ)/16 := by
    rw [pow_two]
    exact product_interval hqbase hqbase (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q4 : (81 : ℝ)/256 ≤ ((3 : ℝ)/4)^4 ∧ ((3 : ℝ)/4)^4 ≤ (81 : ℝ)/256 := by
    rw [show 4 = 2+2 by norm_num, pow_add]
    exact product_interval q2 q2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q8 : (6561 : ℝ)/65536 ≤ ((3 : ℝ)/4)^8 ∧ ((3 : ℝ)/4)^8 ≤ (6561 : ℝ)/65536 := by
    rw [show 8 = 4+4 by norm_num, pow_add]
    exact product_interval q4 q4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q16 : (100225957576185464859 : ℝ)/10000000000000000000000 ≤ ((3 : ℝ)/4)^16 ∧ ((3 : ℝ)/4)^16 ≤ (10022595757618546485901 : ℝ)/1000000000000000000000000 := by
    rw [show 16 = 8+8 by norm_num, pow_add]
    exact product_interval q8 q8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q32 : (100452425720633285819 : ℝ)/1000000000000000000000000 ≤ ((3 : ℝ)/4)^32 ∧ ((3 : ℝ)/4)^32 ≤ (5022621286031664291 : ℝ)/50000000000000000000000 := by
    rw [show 32 = 16+16 by norm_num, pow_add]
    exact product_interval q16 q16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q34 : (56504489467856223273 : ℝ)/1000000000000000000000000 ≤ ((3 : ℝ)/4)^34 ∧ ((3 : ℝ)/4)^34 ≤ (28252244733928111637 : ℝ)/500000000000000000000000 := by
    rw [show 34 = 2+32 by norm_num, pow_add]
    exact product_interval q2 q32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsbase : (499971747755266071888363 : ℝ)/500000000000000000000000 ≤ 1-((3 : ℝ)/4)^34 ∧ 1-((3 : ℝ)/4)^34 ≤ (999943495510532143776727 : ℝ)/1000000000000000000000000 := by
    constructor
    · calc
        (499971747755266071888363 : ℝ)/500000000000000000000000 = 1-((28252244733928111637 : ℝ)/500000000000000000000000) := by norm_num
        _ ≤ 1-((3 : ℝ)/4)^34 := sub_le_sub_left q34.2 1
    · calc
        1-((3 : ℝ)/4)^34 ≤ 1-((56504489467856223273 : ℝ)/1000000000000000000000000) := sub_le_sub_left q34.1 1
        _ = (999943495510532143776727 : ℝ)/1000000000000000000000000 := by norm_num
  have s1 : (499971747755266071888363 : ℝ)/500000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^1 ∧ (1-((3 : ℝ)/4)^34)^1 ≤ (999943495510532143776727 : ℝ)/1000000000000000000000000 := by
    simpa using hsbase
  have s2 : (499943497106910808788263 : ℝ)/500000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^2 ∧ (1-((3 : ℝ)/4)^34)^2 ≤ (999886994213821617576529 : ℝ)/1000000000000000000000000 := by
    rw [pow_two]
    exact product_interval hsbase hsbase (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4 : (999774001197950944947339 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^4 ∧ (1-((3 : ℝ)/4)^34)^4 ≤ (499887000598975472473673 : ℝ)/500000000000000000000000 := by
    rw [show 4 = 2+2 by norm_num, pow_add]
    exact product_interval s2 s2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s8 : (124943506683920052187831 : ℝ)/125000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^8 ∧ (1-((3 : ℝ)/4)^34)^8 ≤ (999548053471360417502663 : ℝ)/1000000000000000000000000 := by
    rw [show 8 = 4+4 by norm_num, pow_add]
    exact product_interval s4 s4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s16 : (499548155599192792187129 : ℝ)/500000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^16 ∧ (1-((3 : ℝ)/4)^34)^16 ≤ (999096311198385584374289 : ℝ)/1000000000000000000000000 := by
    rw [show 16 = 8+8 by norm_num, pow_add]
    exact product_interval s8 s8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s32 : (998193439050221332047157 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^32 ∧ (1-((3 : ℝ)/4)^34)^32 ≤ (49909671952511066602361 : ℝ)/50000000000000000000000 := by
    rw [show 32 = 16+16 by norm_num, pow_add]
    exact product_interval s16 s16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s64 : (996390141762907929297147 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^64 ∧ (1-((3 : ℝ)/4)^34)^64 ≤ (498195070881453964648637 : ℝ)/500000000000000000000000 := by
    rw [show 64 = 32+32 by norm_num, pow_add]
    exact product_interval s32 s32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s128 : (992793314602307760066833 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^128 ∧ (1-((3 : ℝ)/4)^34)^128 ≤ (992793314602307760067087 : ℝ)/1000000000000000000000000 := by
    rw [show 128 = 64+64 by norm_num, pow_add]
    exact product_interval s64 s64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s256 : (98563856551903683069211 : ℝ)/100000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^256 ∧ (1-((3 : ℝ)/4)^34)^256 ≤ (197127713103807366138523 : ℝ)/200000000000000000000000 := by
    rw [show 256 = 128+128 by norm_num, pow_add]
    exact product_interval s128 s128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s512 : (971483381838424659240437 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^512 ∧ (1-((3 : ℝ)/4)^34)^512 ≤ (485741690919212329620717 : ℝ)/500000000000000000000000 := by
    rw [show 512 = 256+256 by norm_num, pow_add]
    exact product_interval s256 s256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s1024 : (943779961188222407048301 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^1024 ∧ (1-((3 : ℝ)/4)^34)^1024 ≤ (943779961188222407050239 : ℝ)/1000000000000000000000000 := by
    rw [show 1024 = 512+512 by norm_num, pow_add]
    exact product_interval s512 s512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s2048 : (89072061514044259300217 : ℝ)/100000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^2048 ∧ (1-((3 : ℝ)/4)^34)^2048 ≤ (89072061514044259300583 : ℝ)/100000000000000000000000 := by
    rw [show 2048 = 1024+1024 by norm_num, pow_add]
    exact product_interval s1024 s1024 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4096 : (793383214236168450641899 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^4096 ∧ (1-((3 : ℝ)/4)^34)^4096 ≤ (39669160711808422532421 : ℝ)/50000000000000000000000 := by
    rw [show 4096 = 2048+2048 by norm_num, pow_add]
    exact product_interval s2048 s2048 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s8192 : (125891384926342792977423 : ℝ)/200000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^8192 ∧ (1-((3 : ℝ)/4)^34)^8192 ≤ (78682115578964245612183 : ℝ)/125000000000000000000000 := by
    rw [show 8192 = 4096+4096 by norm_num, pow_add]
    exact product_interval s4096 s4096 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s272 : (492373927492468990309959 : ℝ)/500000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^272 ∧ (1-((3 : ℝ)/4)^34)^272 ≤ (492373927492468990310227 : ℝ)/500000000000000000000000 := by
    rw [show 272 = 16+256 by norm_num, pow_add]
    exact product_interval s16 s256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s784 : (119583272052362767280181 : ℝ)/125000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^784 ∧ (1-((3 : ℝ)/4)^34)^784 ≤ (956666176418902138242951 : ℝ)/1000000000000000000000000 := by
    rw [show 784 = 272+512 by norm_num, pow_add]
    exact product_interval s272 s512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s1808 : (90288236685071659015959 : ℝ)/100000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^1808 ∧ (1-((3 : ℝ)/4)^34)^1808 ≤ (56430147928169786885179 : ℝ)/62500000000000000000000 := by
    rw [show 1808 = 784+1024 by norm_num, pow_add]
    exact product_interval s784 s1024 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s10000 : (568325557942055031827553 : ℝ)/1000000000000000000000000 ≤ (1-((3 : ℝ)/4)^34)^10000 ∧ (1-((3 : ℝ)/4)^34)^10000 ≤ (284162778971027515919479 : ℝ)/500000000000000000000000 := by
    rw [show 10000 = 1808+8192 by norm_num, pow_add]
    exact product_interval s1808 s8192 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold bestCaseBound
  calc
    (1/2 : ℝ) < (568325557942055031827553 : ℝ)/1000000000000000000000000 := by norm_num
    _ ≤ (1-(3/4 : ℝ)^34)^10000 := s10000.1

/-- P007-T7(b), T8(v): the exact lower bound at n=10000,k=952,q=99/100.
The proof uses outward rational intervals and repeated squaring, avoiding enormous
expanded rational powers. -/
theorem figure4_numeric_952 :
    (0.49685 : ℝ) ≤ bestCaseBound 10000 (99/100) 952 ∧ bestCaseBound 10000 (99/100) 952 < 0.49695 ∧ bestCaseBound 10000 (99/100) 952 < 1/2 := by
  have hqbase : (99 : ℝ)/100 ≤ (99 : ℝ)/100 ∧ (99 : ℝ)/100 ≤ (99 : ℝ)/100 := ⟨le_rfl,le_rfl⟩
  have q1 : (99 : ℝ)/100 ≤ ((99 : ℝ)/100)^1 ∧ ((99 : ℝ)/100)^1 ≤ (99 : ℝ)/100 := by
    simpa using hqbase
  have q2 : (9801 : ℝ)/10000 ≤ ((99 : ℝ)/100)^2 ∧ ((99 : ℝ)/100)^2 ≤ (9801 : ℝ)/10000 := by
    rw [pow_two]
    exact product_interval hqbase hqbase (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q4 : (96059601 : ℝ)/100000000 ≤ ((99 : ℝ)/100)^4 ∧ ((99 : ℝ)/100)^4 ≤ (96059601 : ℝ)/100000000 := by
    rw [show 4 = 2+2 by norm_num, pow_add]
    exact product_interval q2 q2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q8 : (9227446944279201 : ℝ)/10000000000000000 ≤ ((99 : ℝ)/100)^8 ∧ ((99 : ℝ)/100)^8 ≤ (9227446944279201 : ℝ)/10000000000000000 := by
    rw [show 8 = 4+4 by norm_num, pow_add]
    exact product_interval q4 q4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q16 : (425728885547437819822507 : ℝ)/500000000000000000000000 ≤ ((99 : ℝ)/100)^16 ∧ ((99 : ℝ)/100)^16 ≤ (170291554218975127929003 : ℝ)/200000000000000000000000 := by
    rw [show 16 = 8+8 by norm_num, pow_add]
    exact product_interval q8 q8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q32 : (724980335957853642317687 : ℝ)/1000000000000000000000000 ≤ ((99 : ℝ)/100)^32 ∧ ((99 : ℝ)/100)^32 ≤ (724980335957853642317689 : ℝ)/1000000000000000000000000 := by
    rw [show 32 = 16+16 by norm_num, pow_add]
    exact product_interval q16 q16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q64 : (525596487525562334894377 : ℝ)/1000000000000000000000000 ≤ ((99 : ℝ)/100)^64 ∧ ((99 : ℝ)/100)^64 ≤ (525596487525562334894381 : ℝ)/1000000000000000000000000 := by
    rw [show 64 = 32+32 by norm_num, pow_add]
    exact product_interval q32 q32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q128 : (276251667699208603116219 : ℝ)/1000000000000000000000000 ≤ ((99 : ℝ)/100)^128 ∧ ((99 : ℝ)/100)^128 ≤ (11050066707968344124649 : ℝ)/40000000000000000000000 := by
    rw [show 128 = 64+64 by norm_num, pow_add]
    exact product_interval q64 q64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q256 : (38157491953296986936043 : ℝ)/500000000000000000000000 ≤ ((99 : ℝ)/100)^256 ∧ ((99 : ℝ)/100)^256 ≤ (7631498390659397387209 : ℝ)/100000000000000000000000 := by
    rw [show 256 = 128+128 by norm_num, pow_add]
    exact product_interval q128 q128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q512 : (2911988384331848614907 : ℝ)/500000000000000000000000 ≤ ((99 : ℝ)/100)^512 ∧ ((99 : ℝ)/100)^512 ≤ (1164795353732739445963 : ℝ)/200000000000000000000000 := by
    rw [show 512 = 256+256 by norm_num, pow_add]
    exact product_interval q256 q256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q24 : (785678140807218961624989 : ℝ)/1000000000000000000000000 ≤ ((99 : ℝ)/100)^24 ∧ ((99 : ℝ)/100)^24 ≤ (78567814080721896162499 : ℝ)/100000000000000000000000 := by
    rw [show 24 = 8+16 by norm_num, pow_add]
    exact product_interval q8 q16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q56 : (569601202477159442078819 : ℝ)/1000000000000000000000000 ≤ ((99 : ℝ)/100)^56 ∧ ((99 : ℝ)/100)^56 ≤ (569601202477159442078823 : ℝ)/1000000000000000000000000 := by
    rw [show 56 = 24+32 by norm_num, pow_add]
    exact product_interval q24 q32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q184 : (39338320526947471604109 : ℝ)/250000000000000000000000 ≤ ((99 : ℝ)/100)^184 ∧ ((99 : ℝ)/100)^184 ≤ (78676641053894943208221 : ℝ)/500000000000000000000000 := by
    rw [show 184 = 56+128 by norm_num, pow_add]
    exact product_interval q56 q128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q440 : (6004206595852863338679 : ℝ)/500000000000000000000000 ≤ ((99 : ℝ)/100)^440 ∧ ((99 : ℝ)/100)^440 ≤ (150105164896321583467 : ℝ)/12500000000000000000000 := by
    rw [show 440 = 184+256 by norm_num, pow_add]
    exact product_interval q184 q256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q952 : (69936719457008833031 : ℝ)/1000000000000000000000000 ≤ ((99 : ℝ)/100)^952 ∧ ((99 : ℝ)/100)^952 ≤ (8742089932126104129 : ℝ)/125000000000000000000000 := by
    rw [show 952 = 440+512 by norm_num, pow_add]
    exact product_interval q440 q512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsbase : (124991257910067873895871 : ℝ)/125000000000000000000000 ≤ 1-((99 : ℝ)/100)^952 ∧ 1-((99 : ℝ)/100)^952 ≤ (999930063280542991166969 : ℝ)/1000000000000000000000000 := by
    constructor
    · calc
        (124991257910067873895871 : ℝ)/125000000000000000000000 = 1-((8742089932126104129 : ℝ)/125000000000000000000000) := by norm_num
        _ ≤ 1-((99 : ℝ)/100)^952 := sub_le_sub_left q952.2 1
    · calc
        1-((99 : ℝ)/100)^952 ≤ 1-((69936719457008833031 : ℝ)/1000000000000000000000000) := sub_le_sub_left q952.1 1
        _ = (999930063280542991166969 : ℝ)/1000000000000000000000000 := by norm_num
  have s1 : (124991257910067873895871 : ℝ)/125000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^1 ∧ (1-((99 : ℝ)/100)^952)^1 ≤ (999930063280542991166969 : ℝ)/1000000000000000000000000 := by
    simpa using hsbase
  have s2 : (999860131452230710742293 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^2 ∧ (1-((99 : ℝ)/100)^952)^2 ≤ (124982516431528838842787 : ℝ)/125000000000000000000000 := by
    rw [pow_two]
    exact product_interval hsbase hsbase (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4 : (124965035308459009571817 : ℝ)/125000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^4 ∧ (1-((99 : ℝ)/100)^952)^4 ≤ (999720282467672076574543 : ℝ)/1000000000000000000000000 := by
    rw [show 4 = 2+2 by norm_num, pow_add]
    exact product_interval s2 s2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s8 : (499720321588621022385979 : ℝ)/500000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^8 ∧ (1-((99 : ℝ)/100)^952)^8 ≤ (999440643177242044771973 : ℝ)/1000000000000000000000000 := by
    rw [show 8 = 4+4 by norm_num, pow_add]
    exact product_interval s4 s4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s16 : (199776319846907851083691 : ℝ)/200000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^16 ∧ (1-((99 : ℝ)/100)^952)^16 ≤ (499440799617269627709243 : ℝ)/500000000000000000000000 := by
    rw [show 16 = 8+8 by norm_num, pow_add]
    exact product_interval s8 s8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s32 : (3118013904029220918801 : ℝ)/3125000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^32 ∧ (1-((99 : ℝ)/100)^952)^32 ≤ (997764449289350694016383 : ℝ)/1000000000000000000000000 := by
    rw [show 32 = 16+16 by norm_num, pow_add]
    exact product_interval s16 s16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s64 : (497766948132840636324823 : ℝ)/500000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^64 ∧ (1-((99 : ℝ)/100)^952)^64 ≤ (248883474066420318162443 : ℝ)/250000000000000000000000 := by
    rw [show 64 = 32+32 by norm_num, pow_add]
    exact product_interval s32 s32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s128 : (991087738613928240980867 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^128 ∧ (1-((99 : ℝ)/100)^952)^128 ≤ (991087738613928240981119 : ℝ)/1000000000000000000000000 := by
    rw [show 128 = 64+64 by norm_num, pow_add]
    exact product_interval s64 s64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s256 : (982254905630870147673 : ℝ)/1000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^256 ∧ (1-((99 : ℝ)/100)^952)^256 ≤ (982254905630870147673501 : ℝ)/1000000000000000000000000 := by
    rw [show 256 = 128+128 by norm_num, pow_add]
    exact product_interval s128 s128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s512 : (482412349817954809668877 : ℝ)/500000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^512 ∧ (1-((99 : ℝ)/100)^952)^512 ≤ (964824699635909619338739 : ℝ)/1000000000000000000000000 := by
    rw [show 512 = 256+256 by norm_num, pow_add]
    exact product_interval s256 s256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s1024 : (930886701027523215541887 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^1024 ∧ (1-((99 : ℝ)/100)^952)^1024 ≤ (232721675256880803885947 : ℝ)/250000000000000000000000 := by
    rw [show 1024 = 512+512 by norm_num, pow_add]
    exact product_interval s512 s512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s2048 : (173310010029981078326831 : ℝ)/200000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^2048 ∧ (1-((99 : ℝ)/100)^952)^2048 ≤ (173310010029981078327539 : ℝ)/200000000000000000000000 := by
    rw [show 2048 = 1024+1024 by norm_num, pow_add]
    exact product_interval s1024 s1024 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4096 : (187727247353700887313541 : ℝ)/250000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^4096 ∧ (1-((99 : ℝ)/100)^952)^4096 ≤ (7509089894148035492603 : ℝ)/10000000000000000000000 := by
    rw [show 4096 = 2048+2048 by norm_num, pow_add]
    exact product_interval s2048 s2048 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s8192 : (563864310383961548780173 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^8192 ∧ (1-((99 : ℝ)/100)^952)^8192 ≤ (56386431038396154878939 : ℝ)/100000000000000000000000 := by
    rw [show 8192 = 4096+4096 by norm_num, pow_add]
    exact product_interval s4096 s4096 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s272 : (981156350992535011066761 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^272 ∧ (1-((99 : ℝ)/100)^952)^272 ≤ (981156350992535011067293 : ℝ)/1000000000000000000000000 := by
    rw [show 272 = 16+256 by norm_num, pow_add]
    exact product_interval s16 s256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s784 : (236660970410559426242483 : ℝ)/250000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^784 ∧ (1-((99 : ℝ)/100)^952)^784 ≤ (236660970410559426242853 : ℝ)/250000000000000000000000 := by
    rw [show 784 = 272+512 by norm_num, pow_add]
    exact product_interval s272 s512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s1808 : (881218200029831803033119 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^1808 ∧ (1-((99 : ℝ)/100)^952)^1808 ≤ (881218200029831803036297 : ℝ)/1000000000000000000000000 := by
    rw [show 1808 = 784+1024 by norm_num, pow_add]
    exact product_interval s784 s1024 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s10000 : (62110936582202124241257 : ℝ)/125000000000000000000000 ≤ (1-((99 : ℝ)/100)^952)^10000 ∧ (1-((99 : ℝ)/100)^952)^10000 ≤ (496887492657616993939971 : ℝ)/1000000000000000000000000 := by
    rw [show 10000 = 1808+8192 by norm_num, pow_add]
    exact product_interval s1808 s8192 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold bestCaseBound
  refine ⟨?_,?_,?_⟩
  · calc
      (0.49685 : ℝ) ≤ (62110936582202124241257 : ℝ)/125000000000000000000000 := by norm_num
      _ ≤ (1-(99/100 : ℝ)^952)^10000 := s10000.1
  · calc
      (1-(99/100 : ℝ)^952)^10000 ≤ (496887492657616993939971 : ℝ)/1000000000000000000000000 := s10000.2
      _ < (0.49695 : ℝ) := by norm_num
  · calc
      (1-(99/100 : ℝ)^952)^10000 ≤ (496887492657616993939971 : ℝ)/1000000000000000000000000 := s10000.2
      _ < (1/2 : ℝ) := by norm_num

/-- P007-T7(b), T8(v): the exact lower bound at n=10000,k=953,q=99/100.
The proof uses outward rational intervals and repeated squaring, avoiding enormous
expanded rational powers. -/
theorem figure4_numeric_953 :
    (1/2 : ℝ) < bestCaseBound 10000 (99/100) 953 := by
  have hqbase : (99 : ℝ)/100 ≤ (99 : ℝ)/100 ∧ (99 : ℝ)/100 ≤ (99 : ℝ)/100 := ⟨le_rfl,le_rfl⟩
  have q1 : (99 : ℝ)/100 ≤ ((99 : ℝ)/100)^1 ∧ ((99 : ℝ)/100)^1 ≤ (99 : ℝ)/100 := by
    simpa using hqbase
  have q2 : (9801 : ℝ)/10000 ≤ ((99 : ℝ)/100)^2 ∧ ((99 : ℝ)/100)^2 ≤ (9801 : ℝ)/10000 := by
    rw [pow_two]
    exact product_interval hqbase hqbase (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q4 : (96059601 : ℝ)/100000000 ≤ ((99 : ℝ)/100)^4 ∧ ((99 : ℝ)/100)^4 ≤ (96059601 : ℝ)/100000000 := by
    rw [show 4 = 2+2 by norm_num, pow_add]
    exact product_interval q2 q2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q8 : (9227446944279201 : ℝ)/10000000000000000 ≤ ((99 : ℝ)/100)^8 ∧ ((99 : ℝ)/100)^8 ≤ (9227446944279201 : ℝ)/10000000000000000 := by
    rw [show 8 = 4+4 by norm_num, pow_add]
    exact product_interval q4 q4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q16 : (425728885547437819822507 : ℝ)/500000000000000000000000 ≤ ((99 : ℝ)/100)^16 ∧ ((99 : ℝ)/100)^16 ≤ (170291554218975127929003 : ℝ)/200000000000000000000000 := by
    rw [show 16 = 8+8 by norm_num, pow_add]
    exact product_interval q8 q8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q32 : (724980335957853642317687 : ℝ)/1000000000000000000000000 ≤ ((99 : ℝ)/100)^32 ∧ ((99 : ℝ)/100)^32 ≤ (724980335957853642317689 : ℝ)/1000000000000000000000000 := by
    rw [show 32 = 16+16 by norm_num, pow_add]
    exact product_interval q16 q16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q64 : (525596487525562334894377 : ℝ)/1000000000000000000000000 ≤ ((99 : ℝ)/100)^64 ∧ ((99 : ℝ)/100)^64 ≤ (525596487525562334894381 : ℝ)/1000000000000000000000000 := by
    rw [show 64 = 32+32 by norm_num, pow_add]
    exact product_interval q32 q32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q128 : (276251667699208603116219 : ℝ)/1000000000000000000000000 ≤ ((99 : ℝ)/100)^128 ∧ ((99 : ℝ)/100)^128 ≤ (11050066707968344124649 : ℝ)/40000000000000000000000 := by
    rw [show 128 = 64+64 by norm_num, pow_add]
    exact product_interval q64 q64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q256 : (38157491953296986936043 : ℝ)/500000000000000000000000 ≤ ((99 : ℝ)/100)^256 ∧ ((99 : ℝ)/100)^256 ≤ (7631498390659397387209 : ℝ)/100000000000000000000000 := by
    rw [show 256 = 128+128 by norm_num, pow_add]
    exact product_interval q128 q128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q512 : (2911988384331848614907 : ℝ)/500000000000000000000000 ≤ ((99 : ℝ)/100)^512 ∧ ((99 : ℝ)/100)^512 ≤ (1164795353732739445963 : ℝ)/200000000000000000000000 := by
    rw [show 512 = 256+256 by norm_num, pow_add]
    exact product_interval q256 q256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q9 : (913517247483640899 : ℝ)/1000000000000000000 ≤ ((99 : ℝ)/100)^9 ∧ ((99 : ℝ)/100)^9 ≤ (913517247483640899 : ℝ)/1000000000000000000 := by
    rw [show 9 = 1+8 by norm_num, pow_add]
    exact product_interval q1 q8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q25 : (777821359399146772008739 : ℝ)/1000000000000000000000000 ≤ ((99 : ℝ)/100)^25 ∧ ((99 : ℝ)/100)^25 ≤ (777821359399146772008741 : ℝ)/1000000000000000000000000 := by
    rw [show 25 = 9+16 by norm_num, pow_add]
    exact product_interval q9 q16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q57 : (563905190452387847658031 : ℝ)/1000000000000000000000000 ≤ ((99 : ℝ)/100)^57 ∧ ((99 : ℝ)/100)^57 ≤ (112781038090477569531607 : ℝ)/200000000000000000000000 := by
    rw [show 57 = 25+32 by norm_num, pow_add]
    exact product_interval q25 q32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q185 : (9736234330419499222017 : ℝ)/62500000000000000000000 ≤ ((99 : ℝ)/100)^185 ∧ ((99 : ℝ)/100)^185 ≤ (77889874643355993776139 : ℝ)/500000000000000000000000 := by
    rw [show 185 = 57+128 by norm_num, pow_add]
    exact product_interval q57 q128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q441 : (2377665811957733882117 : ℝ)/200000000000000000000000 ≤ ((99 : ℝ)/100)^441 ∧ ((99 : ℝ)/100)^441 ≤ (11888329059788669410587 : ℝ)/1000000000000000000000000 := by
    rw [show 441 = 185+256 by norm_num, pow_add]
    exact product_interval q185 q256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q953 : (692373522624387447 : ℝ)/10000000000000000000000 ≤ ((99 : ℝ)/100)^953 ∧ ((99 : ℝ)/100)^953 ≤ (34618676131219372351 : ℝ)/500000000000000000000000 := by
    rw [show 953 = 441+512 by norm_num, pow_add]
    exact product_interval q441 q512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsbase : (499965381323868780627649 : ℝ)/500000000000000000000000 ≤ 1-((99 : ℝ)/100)^953 ∧ 1-((99 : ℝ)/100)^953 ≤ (9999307626477375612553 : ℝ)/10000000000000000000000 := by
    constructor
    · calc
        (499965381323868780627649 : ℝ)/500000000000000000000000 = 1-((34618676131219372351 : ℝ)/500000000000000000000000) := by norm_num
        _ ≤ 1-((99 : ℝ)/100)^953 := sub_le_sub_left q953.2 1
    · calc
        1-((99 : ℝ)/100)^953 ≤ 1-((692373522624387447 : ℝ)/10000000000000000000000) := sub_le_sub_left q953.1 1
        _ = (9999307626477375612553 : ℝ)/10000000000000000000000 := by norm_num
  have s1 : (499965381323868780627649 : ℝ)/500000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^1 ∧ (1-((99 : ℝ)/100)^953)^1 ≤ (9999307626477375612553 : ℝ)/10000000000000000000000 := by
    simpa using hsbase
  have s2 : (999861530089286070823627 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^2 ∧ (1-((99 : ℝ)/100)^953)^2 ≤ (62491345630580379426477 : ℝ)/62500000000000000000000 := by
    rw [pow_two]
    exact product_interval hsbase hsbase (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4 : (249930769838122078692693 : ℝ)/250000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^4 ∧ (1-((99 : ℝ)/100)^953)^4 ≤ (999723079352488314770783 : ℝ)/1000000000000000000000000 := by
    rw [show 4 = 2+2 by norm_num, pow_add]
    exact product_interval s2 s2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s8 : (499723117695010823916281 : ℝ)/500000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^8 ∧ (1-((99 : ℝ)/100)^953)^8 ≤ (199889247078004329566517 : ℝ)/200000000000000000000000 := by
    rw [show 8 = 4+4 by norm_num, pow_add]
    exact product_interval s4 s4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s16 : (62430798589705410008851 : ℝ)/62500000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^16 ∧ (1-((99 : ℝ)/100)^953)^16 ≤ (998892777435286560141663 : ℝ)/1000000000000000000000000 := by
    rw [show 16 = 8+8 by norm_num, pow_add]
    exact product_interval s8 s8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s32 : (997786780812380930890747 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^32 ∧ (1-((99 : ℝ)/100)^953)^32 ≤ (997786780812380930890841 : ℝ)/1000000000000000000000000 := by
    rw [show 32 = 16+16 by norm_num, pow_add]
    exact product_interval s16 s16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s64 : (248894614990983576748431 : ℝ)/250000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^64 ∧ (1-((99 : ℝ)/100)^953)^64 ≤ (995578459963934306993913 : ℝ)/1000000000000000000000000 := by
    rw [show 64 = 32+32 by norm_num, pow_add]
    exact product_interval s32 s32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s128 : (495588234972079572898629 : ℝ)/500000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^128 ∧ (1-((99 : ℝ)/100)^953)^128 ≤ (247794117486039786449409 : ℝ)/250000000000000000000000 := by
    rw [show 128 = 64+64 by norm_num, pow_add]
    exact product_interval s64 s64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s256 : (982430794570964618502201 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^256 ∧ (1-((99 : ℝ)/100)^953)^256 ≤ (982430794570964618502951 : ℝ)/1000000000000000000000000 := by
    rw [show 256 = 128+128 by norm_num, pow_add]
    exact product_interval s128 s128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s512 : (965170266121336883328049 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^512 ∧ (1-((99 : ℝ)/100)^953)^512 ≤ (241292566530334220832381 : ℝ)/250000000000000000000000 := by
    rw [show 512 = 256+256 by norm_num, pow_add]
    exact product_interval s256 s256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s1024 : (93155364260473225992941 : ℝ)/100000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^1024 ∧ (1-((99 : ℝ)/100)^953)^1024 ≤ (465776821302366129966129 : ℝ)/500000000000000000000000 := by
    rw [show 1024 = 512+512 by norm_num, pow_add]
    exact product_interval s512 s512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s2048 : (433896094525072621354983 : ℝ)/500000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^2048 ∧ (1-((99 : ℝ)/100)^953)^2048 ≤ (867792189050145242715273 : ℝ)/1000000000000000000000000 := by
    rw [show 2048 = 1024+1024 by norm_num, pow_add]
    exact product_interval s1024 s1024 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4096 : (753063283376443020880949 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^4096 ∧ (1-((99 : ℝ)/100)^953)^4096 ≤ (753063283376443020890161 : ℝ)/1000000000000000000000000 := by
    rw [show 4096 = 2048+2048 by norm_num, pow_add]
    exact product_interval s2048 s2048 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s8192 : (567104308769708923475799 : ℝ)/1000000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^8192 ∧ (1-((99 : ℝ)/100)^953)^8192 ≤ (283552154384854461744837 : ℝ)/500000000000000000000000 := by
    rw [show 8192 = 4096+4096 by norm_num, pow_add]
    exact product_interval s4096 s4096 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s272 : (490671512513473146245199 : ℝ)/500000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^272 ∧ (1-((99 : ℝ)/100)^953)^272 ≤ (196268605005389258498239 : ℝ)/200000000000000000000000 := by
    rw [show 272 = 16+256 by norm_num, pow_add]
    exact product_interval s16 s256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s784 : (23679077715539387860579 : ℝ)/25000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^784 ∧ (1-((99 : ℝ)/100)^953)^784 ≤ (473581554310787757212689 : ℝ)/500000000000000000000000 := by
    rw [show 784 = 272+512 by norm_num, pow_add]
    exact product_interval s272 s512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s1808 : (27572913874289073669919 : ℝ)/31250000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^1808 ∧ (1-((99 : ℝ)/100)^953)^1808 ≤ (882333243977250357442173 : ℝ)/1000000000000000000000000 := by
    rw [show 1808 = 784+1024 by norm_num, pow_add]
    exact product_interval s784 s1024 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s10000 : (125093746107563375766483 : ℝ)/250000000000000000000000 ≤ (1-((99 : ℝ)/100)^953)^10000 ∧ (1-((99 : ℝ)/100)^953)^10000 ≤ (250187492215126751540439 : ℝ)/500000000000000000000000 := by
    rw [show 10000 = 1808+8192 by norm_num, pow_add]
    exact product_interval s1808 s8192 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold bestCaseBound
  calc
    (1/2 : ℝ) < (125093746107563375766483 : ℝ)/250000000000000000000000 := by norm_num
    _ ≤ (1-(99/100 : ℝ)^953)^10000 := s10000.1

/-- An adjacent integer bracket B(k)<a<B(k+1) determines the corrected floor and
ceiling, without approximating logarithms. 
Supporting finite lemma for the corrected Figure 4 inverse and worked floors and ceilings (Supplement p. 2; P007-T8). -/
theorem adjacent_bracket_rounding {n : ℕ} (hn : 0<n) {q a : ℝ}
    (hq0 : 0<q) (hq1 : q<1) (ha0 : 0<a) (ha1 : a<1) (k : ℕ)
    (hl : bestCaseBound n q k<a) (hu : a<bestCaseBound n q (k+1)) :
    ⌊thresholdReal n q a⌋₊=k ∧ ⌈thresholdReal n q a⌉₊=k+1 := by
  have hinv (j : ℕ) := threshold_integer_inversion hn hq0 hq1 ha0 ha1 j
  have hrlo : (k : ℝ)<thresholdReal n q a :=
    lt_of_not_ge (by intro h; exact (not_le_of_gt hl) ((hinv k).2.1.mpr h))
  have hrhi : thresholdReal n q a<(k+1 : ℕ) :=
    lt_of_not_ge (by intro h; exact (not_le_of_gt hu) ((hinv (k+1)).1.mpr h))
  have hr0 := (threshold_root hn hq0 hq1 ha0 ha1).1.le
  constructor
  · exact (Nat.floor_eq_iff hr0).mpr ⟨hrlo.le,by simpa using hrhi⟩
  · exact (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).mpr ⟨by simpa using hrlo,hrhi.le⟩

/-- P007-T8(v): at n=10000,a=1/2 the plotted floors are 33 and 952, whereas the
first guaranteed 50% lower-bound crossings are 34 and 953. The corrected approximate
best-case probabilities round to 47.08% and 49.69%, respectively. -/
theorem figure4_corrected_worked_values :
    ⌊thresholdReal 10000 (3/4) (1/2)⌋₊=33 ∧ ⌈thresholdReal 10000 (3/4) (1/2)⌉₊=34 ∧
    ⌊thresholdReal 10000 (99/100) (1/2)⌋₊=952 ∧ ⌈thresholdReal 10000 (99/100) (1/2)⌉₊=953 ∧
    (0.47075 : ℝ)≤bestCaseBound 10000 (3/4) 33 ∧ bestCaseBound 10000 (3/4) 33<0.47085 ∧
    (0.49685 : ℝ)≤bestCaseBound 10000 (99/100) 952 ∧ bestCaseBound 10000 (99/100) 952<0.49695 := by
  have h75 := adjacent_bracket_rounding (n:=10000) (by norm_num) (q:=3/4) (a:=1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 33
    figure4_numeric_33.2.2 figure4_numeric_34
  have h99 := adjacent_bracket_rounding (n:=10000) (by norm_num) (q:=99/100) (a:=1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 952
    figure4_numeric_952.2.2 figure4_numeric_953
  exact ⟨h75.1,h75.2,h99.1,h99.2,figure4_numeric_33.1,figure4_numeric_33.2.1,
    figure4_numeric_952.1,figure4_numeric_952.2.1⟩

/-- P007-T7(b): the explicit equal-probability laws at both printed parameter sets
satisfy every hypothesis, but their actual all-deletion probabilities are below 50%.
The next integer's lower bound is above 50%; these are counterexamples to the worked
first-crossing sentences, not to Lemma 3. -/
theorem figure4_printed_worked_counterexamples :
    RowsIndependent (equalProbabilityLaw 10000 33 (3/4) (by norm_num) (by norm_num)) ∧
    ConditionalObservationBound (equalProbabilityLaw 10000 33 (3/4) (by norm_num) (by norm_num)) (3/4) ∧
    pAll (equalProbabilityLaw 10000 33 (3/4) (by norm_num) (by norm_num)) = bestCaseBound 10000 (3/4) 33 ∧
    pAll (equalProbabilityLaw 10000 33 (3/4) (by norm_num) (by norm_num)) < 1/2 ∧
    (1/2 : ℝ) < bestCaseBound 10000 (3/4) 34 ∧
    RowsIndependent (equalProbabilityLaw 10000 952 (99/100) (by norm_num) (by norm_num)) ∧
    ConditionalObservationBound (equalProbabilityLaw 10000 952 (99/100) (by norm_num) (by norm_num)) (99/100) ∧
    pAll (equalProbabilityLaw 10000 952 (99/100) (by norm_num) (by norm_num)) = bestCaseBound 10000 (99/100) 952 ∧
    pAll (equalProbabilityLaw 10000 952 (99/100) (by norm_num) (by norm_num)) < 1/2 ∧
    (1/2 : ℝ) < bestCaseBound 10000 (99/100) 953 := by
  have h75 := bestCase_attained 10000 33 (3/4) (by norm_num) (by norm_num)
  have h99 := bestCase_attained 10000 952 (99/100) (by norm_num) (by norm_num)
  refine ⟨h75.1,h75.2.1,h75.2.2,?_,figure4_numeric_34,h99.1,h99.2.1,h99.2.2,?_,figure4_numeric_953⟩
  · rw [h75.2.2]; exact figure4_numeric_33.2.2
  · rw [h99.2.2]; exact figure4_numeric_952.2.2

/-- P007-T7(c3), with both sides compared: the actual admissible all-deletion
probability exceeds 99% while the printed sharp lower bound is below 50%. -/
theorem figure4_printed_lower_bound_not_upper :
    RowsIndependent (unequalProbabilityLaw 10000 33) ∧
    ConditionalObservationBound (unequalProbabilityLaw 10000 33) (3/4) ∧
    bestCaseBound 10000 (3/4) 33 < 1/2 ∧
    (99/100 : ℝ)<pAll (unequalProbabilityLaw 10000 33) :=
  ⟨printed_parameters_actual_deletion_high.1,printed_parameters_actual_deletion_high.2.1,
    figure4_numeric_33.2.2,printed_parameters_actual_deletion_high.2.2.2⟩

end AronowAudit.P007

