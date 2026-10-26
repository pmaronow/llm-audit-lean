import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
P030: finite randomization tests and interference. Printed page numbers are used throughout (PDF page + 2).
Finite probabilities count assignments, retaining multiplicity of tied statistics.
All arithmetic is over fixed potential outcomes and a finite randomization design.
-/
namespace AronowAudit.P030

open scoped BigOperators
noncomputable section

/-- "the treatment status Z for N units is binary" (p. 4). Indices are zero-based. -/
abbrev Assignment (N : ℕ) := Fin N → Bool

/-- "Ω is the set of all possible randomizations of Z" (p. 4).
Every finite assignment support used below is a Finset of Assignment N. -/
abbrev AssignmentSet (N : ℕ) := Finset (Assignment N)

/-- "S_i = 1 if unit i is fixed, S_i = 0 if unit i is variant" (p. 6).
The Boolean true represents one and false represents zero. -/
abbrev FixedIndicator (N : ℕ) := Fin N → Bool

/-- "Each potential outcome for unit i ... represents the outcome, Y_i, that
would be observed" (p. 4); the paper writes Y_{i,Z} from p. 6 onward.
The entire schedule is fixed before assignment and may depend on all of Z. -/
abbrev PotentialOutcomes (N : ℕ) := Fin N → Assignment N → ℝ

/-- The numerical binary treatment indicator Z_i, used in the models on pp. 5, 10. -/
def treatment {N : ℕ} (z : Assignment N) (i : Fin N) : ℝ := if z i then 1 else 0

/-- "all possible randomizations conditional on observing Z_fixed" (p. 6).
The corrected prime compares the SAME unit under two assignment vectors. -/
def conditionalAssignments {N : ℕ} (Ω : AssignmentSet N)
    (S : FixedIndicator N) (obs : Assignment N) : Finset (Assignment N) := by
  classical
  exact Ω.filter (fun z => ∀ i, S i = true → z i = obs i)

/-- H_0': "no treatment effect whatsoever (neither direct nor indirect)" (p. 6). -/
def NoEffects {N : ℕ} (Ω : AssignmentSet N)
    (Y : PotentialOutcomes N) : Prop :=
  ∀ i, ∀ z ∈ Ω, ∀ z' ∈ Ω, Y i z = Y i z'

/-- H_0'': "conditional on Z_i, Y_i should be invariant across all randomizations"
(p. 6), with the corrected condition Z_i = Z'_i (P030-T7). -/
def NoInterference {N : ℕ} (Ω : AssignmentSet N)
    (Y : PotentialOutcomes N) : Prop :=
  ∀ i, ∀ z ∈ Ω, ∀ z' ∈ Ω, z i = z' i → Y i z = Y i z'

/-- Corrected Equation (1), P030-T6: fixed OUTCOMES invariant over Ω' (p. 7). -/
def FixedOutcomeNull {N : ℕ} (Ω' : AssignmentSet N)
    (S : FixedIndicator N) (Y : PotentialOutcomes N) : Prop :=
  ∀ i, S i = true → ∀ z ∈ Ω', ∀ z' ∈ Ω', Y i z = Y i z'

/-- "S_i = 1 if unit i is fixed" (p. 6); Y_fixed is its outcome subvector. -/
def fixedOutcomes {N : ℕ} (S : FixedIndicator N)
    (Y : PotentialOutcomes N) (z : Assignment N) : {i // S i = true} → ℝ :=
  fun i => Y i.val z

/-- t_Z: "a metric of the dependence of Y_fixed on Z_variant" (pp. 6-7).
The fixed function g may include pretreatment characteristics. Allowing g to
read the whole assignment is equivalent on Ω', where its fixed part is constant. -/
def statistic {N : ℕ} (S : FixedIndicator N) (Y : PotentialOutcomes N)
    (g : ({i // S i = true} → ℝ) → Assignment N → ℝ) (z : Assignment N) : ℝ :=
  g (fixedOutcomes S Y z) z

/-- t_0(Z) computed holding the observed Y_fixed constant (p. 10). -/
def referenceStatistic {N : ℕ} (S : FixedIndicator N) (Y : PotentialOutcomes N)
    (g : ({i // S i = true} → ℝ) → Assignment N → ℝ)
    (obs z : Assignment N) : ℝ := g (fixedOutcomes S Y obs) z

/-- A conditional finite randomization law (p. 7). For the correction P030-T3,
the law may be arbitrary: masses are nonnegative and sum to one. -/
structure FiniteLaw (A : Type*) where
  support : Finset A
  mass : A → ℝ
  nonneg : ∀ z ∈ support, 0 ≤ mass z
  total : ∑ z ∈ support, mass z = 1

/-- Probability over random assignments; tied statistic values keep all their
assignment masses (Equation (2), p. 7; explicit count on p. 10). -/
def probability {A : Type*} (μ : FiniteLaw A) (P : A → Prop) : ℝ := by
  classical
  exact ∑ z ∈ μ.support, if P z then μ.mass z else 0

/-- Inclusive lower tail p = Pr(t_0 ≤ t), Equation (2), p. 7. -/
def lowerTail {A : Type*} (μ : FiniteLaw A) (f : A → ℝ) (x : ℝ) : ℝ :=
  probability μ (fun z => f z ≤ x)

/-- Inclusive upper tail in the correction P030-T3 to the two-tailed rule, p. 7. -/
def upperTail {A : Type*} (μ : FiniteLaw A) (f : A → ℝ) (x : ℝ) : ℝ :=
  probability μ (fun z => x ≤ f z)

/-- Equation (2) under uniform conditional assignments (p. 7), counting assignments. -/
def uniformProbability {A : Type*} (Ω : Finset A) (P : A → Prop) : ℝ := by
  classical
  exact ((Ω.filter P).card : ℝ) / (Ω.card : ℝ)

/-- Printed rule after Equation (2), p. 7: reject outside the CLOSED interval. -/
def printedReject (α p : ℝ) : Prop := p < α / 2 ∨ 1 - α / 2 < p

/-- Corrected rule P030-T3, replacing the rule on p. 7: reject if either
INCLUSIVE tail is strictly below α/2. -/
def correctedReject (α pL pU : ℝ) : Prop := pL < α / 2 ∨ pU < α / 2

/-- The conventional inclusive-cutoff two-tailed p-value in P030-T3(vi),
an alternative correction to the rule on p. 7. -/
def twoTailP (pL pU : ℝ) : ℝ := min 1 (2 * min pL pU)

/-- "Whenever values are tied, the average rank is used" (p. 8).
The rank is # strictly smaller + (# equal + 1)/2. -/
def averageRank {n : ℕ} (a : Fin n → ℝ) (k : Fin n) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun l => a l < a k)).card : ℝ) +
    (((Finset.univ.filter (fun l => a l = a k)).card : ℝ) + 1) / 2

/-- Average ranks centred at their mean (n+1)/2 (p. 8). -/
def centeredRanks {n : ℕ} (a : Fin n → ℝ) (k : Fin n) : ℝ :=
  averageRank a k - ((n : ℝ) + 1) / 2

/-- Sum of products of centred ranks in Pearson correlation (p. 8, corrected T9). -/
def rankCross {n : ℕ} (a b : Fin n → ℝ) : ℝ := ∑ k, centeredRanks a k * centeredRanks b k

/-- Sum of squared centred ranks (p. 8, corrected T9). -/
def rankSquares {n : ℕ} (a : Fin n → ℝ) : ℝ := ∑ k, centeredRanks a k ^ 2

/-- Spearman ρ: "the Pearson correlation coefficient of the ranks" (p. 8).
The square root repairs the printed denominator. Assertions about ρ include
nonzero rank variances; the totalized quotient at zero is not an extension of
the paper's defined statistic. -/
def spearman {n : ℕ} (a b : Fin n → ℝ) : ℝ :=
  rankCross a b / Real.sqrt (rankSquares a * rankSquares b)

/-- The covariance of ranks with moment divisor m (population n or sample n-1), p. 8. -/
def rankCov {n : ℕ} (m : ℝ) (a b : Fin n → ℝ) : ℝ := rankCross a b / m

/-- The printed formula WITHOUT the square root (p. 8), checked under both divisors. -/
def printedRho {n : ℕ} (m : ℝ) (a b : Fin n → ℝ) : ℝ :=
  rankCov m a b / ((rankSquares a / m) * (rankSquares b / m))

/-- D_nearest: "distance to the nearest unit of a given treatment status in the
variant subset" (p. 7), here treated. Positions are on the real line in the
counterexamples and Table 1. Only nonempty treated-variant sets are used. -/
def nearestDistance {N : ℕ} (x : Fin N → ℝ) (S : FixedIndicator N)
    (z : Assignment N) (i : Fin N) : ℝ := by
  classical
  let V := Finset.univ.filter (fun j => S j = false ∧ z j = true)
  exact if h : V.Nonempty then V.inf' h (fun j => |x i - x j|) else 0

/-- P030-T1's explicit five positions. -/
def fiveX : Fin 5 → ℝ := ![0, 4, 8, -1, -2]
/-- P030-T1's nonexperimental fixed units 1,2,3 (p. 6 allows this choice). -/
def fiveS : FixedIndicator 5 := ![true, true, true, false, false]
/-- P030-T1's fixed outcome schedule, under every binary assignment. -/
def fiveY (i : Fin 5) (_z : Assignment 5) : ℝ := (![0, 1, 2, 0, 0] : Fin 5 → ℝ) i
/-- P030-T1 treats exactly one of units 4 and 5. -/
def fiveAssignment (a : Fin 2) : Assignment 5 := fun i => decide (i.val = a.val + 3)
/-- P030-T1's two equally likely assignments. -/
def fiveΩ : Finset (Assignment 5) := Finset.univ.image fiveAssignment
/-- Enumeration of P030-T1's three fixed units, in the target's order. -/
def fiveFixed (i : Fin 3) : Fin 5 := ⟨i.val, by omega⟩
/-- P030-T1's outcome subvector. -/
def fiveOutcomes : Fin 3 → ℝ := fun i => fiveY (fiveFixed i) (fiveAssignment 0)
/-- P030-T1's exposure subvector computed with the actual nearest distance
(p. 7 distance definition). -/
def fiveDistances (a : Fin 2) : Fin 3 → ℝ :=
  fun i => nearestDistance fiveX fiveS (fiveAssignment a) (fiveFixed i)
/-- P030-T1 uses the paper's Spearman statistic (p. 8). -/
def fiveStatistic (a : Fin 2) : ℝ := spearman (fiveDistances a) fiveOutcomes

/-- The five-unit counterexample has no treatment effect of any kind (T1, p. 7 claim). -/
theorem five_no_effects : NoEffects fiveΩ fiveY := by
  intro i z hz z' hz'
  rfl

/-- Distances in T1 are (1,5,9) and (2,6,10), from the coordinates and assignments. -/
theorem five_distances : fiveDistances 0 = ![1, 5, 9] ∧ fiveDistances 1 = ![2, 6, 10] := by
  classical
  have h0 : Finset.univ.filter (fun j => fiveS j = false ∧ fiveAssignment 0 j = true) =
      ({3} : Finset (Fin 5)) := by
    ext j; fin_cases j <;> norm_num [fiveS, fiveAssignment]
  have h1 : Finset.univ.filter (fun j => fiveS j = false ∧ fiveAssignment 1 j = true) =
      ({4} : Finset (Fin 5)) := by
    ext j; fin_cases j <;> norm_num [fiveS, fiveAssignment]
  constructor <;> funext i <;> fin_cases i <;>
    norm_num [fiveDistances, nearestDistance, h0, h1, fiveX, fiveFixed]

/-- T1's rank vectors are (1,2,3), with nonzero sums of squares 2 and correlation 1. -/
theorem five_correlations :
    (∀ a : Fin 2, rankSquares (fiveDistances a) = 2 ∧
      rankSquares fiveOutcomes = 2 ∧ fiveStatistic a = 1) := by
  intro a
  fin_cases a <;> simp only [fiveStatistic] <;>
    norm_num [spearman, rankCross, rankSquares, centeredRanks, averageRank,
      five_distances.1, five_distances.2, fiveOutcomes, fiveY, fiveFixed,
      Fin.sum_univ_succ, Fin.card_filter_univ_succ]

/-- Sharp no-effect implies no interference, p. 6 (P030-T7(d)). -/
theorem no_effects_implies_no_interference {N : ℕ} (Ω : AssignmentSet N)
    (Y : PotentialOutcomes N) (h : NoEffects Ω Y) : NoInterference Ω Y := by
  intro i z hz z' hz' _
  exact h i z hz z' hz'

/-- T1's fixed units are never treated and Ω' = Ω, with exactly two assignments. -/
theorem five_design :
    fiveΩ.card = 2 ∧
    conditionalAssignments fiveΩ fiveS (fiveAssignment 0) = fiveΩ ∧
    (∀ z ∈ fiveΩ, ∀ i, fiveS i = true → z i = false) ∧
    (∀ a : Fin 2, (Finset.univ.filter (fun i => fiveAssignment a i = true)).card = 1) := by
  classical
  have hinj : Function.Injective fiveAssignment := by
    intro a b hab
    have h := congrFun hab (⟨a.val + 3, by omega⟩ : Fin 5)
    simp [fiveAssignment] at h
    apply Fin.ext
    omega
  have hfixed : ∀ z ∈ fiveΩ, ∀ i, fiveS i = true → z i = false := by
    intro z hz i hi
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i <;> fin_cases a <;> norm_num [fiveS, fiveAssignment] at *
  refine ⟨?_, ?_, hfixed, ?_⟩
  · simpa [fiveΩ] using Finset.card_image_of_injective Finset.univ hinj
  · apply Finset.filter_eq_self.mpr
    intro z hz i hi
    rw [hfixed z hz i hi, hfixed (fiveAssignment 0) (by simp [fiveΩ]) i hi]
  · intro a; fin_cases a <;> norm_num [fiveAssignment, Fin.card_filter_univ_succ]

/-- T1's complete counterexample to the p. 7 printed two-tailed exactness claim:
no interference; uniform two-assignment reference law; defined Spearman statistic
identically 1; both inclusive tails 1; printed size 1 and corrected size 0 for
every 0 < α < 1. Explicit α=1/20 is included as a consequence. -/
theorem five_unit_counterexample :
    NoEffects fiveΩ fiveY ∧ NoInterference fiveΩ fiveY ∧
    fiveΩ.card = 2 ∧ conditionalAssignments fiveΩ fiveS (fiveAssignment 0) = fiveΩ ∧
    (∀ z ∈ fiveΩ, ∀ i, fiveS i = true → z i = false) ∧
    (∀ a : Fin 2, (Finset.univ.filter (fun i => fiveAssignment a i = true)).card = 1) ∧
    (∀ a : Fin 2, 0 < rankSquares (fiveDistances a) ∧ 0 < rankSquares fiveOutcomes ∧
      fiveStatistic a = 1) ∧
    (∀ a : Fin 2,
      uniformProbability Finset.univ (fun b => fiveStatistic b ≤ fiveStatistic a) = 1 ∧
      uniformProbability Finset.univ (fun b => fiveStatistic a ≤ fiveStatistic b) = 1) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      uniformProbability (Finset.univ : Finset (Fin 2))
        (fun a => printedReject α
          (uniformProbability Finset.univ (fun b => fiveStatistic b ≤ fiveStatistic a))) = 1 ∧
      uniformProbability (Finset.univ : Finset (Fin 2))
        (fun a => correctedReject α
          (uniformProbability Finset.univ (fun b => fiveStatistic b ≤ fiveStatistic a))
          (uniformProbability Finset.univ (fun b => fiveStatistic a ≤ fiveStatistic b))) = 0 ∧
      α < 1) ∧ printedReject (1/20) 1 := by
  classical
  have ht : ∀ a : Fin 2, fiveStatistic a = 1 := fun a => (five_correlations a).2.2
  have tails : ∀ a : Fin 2,
      uniformProbability Finset.univ (fun b => fiveStatistic b ≤ fiveStatistic a) = 1 ∧
      uniformProbability Finset.univ (fun b => fiveStatistic a ≤ fiveStatistic b) = 1 := by
    intro a
    simp [uniformProbability, ht]
  refine ⟨five_no_effects, no_effects_implies_no_interference _ _ five_no_effects,
    five_design.1, five_design.2.1, five_design.2.2.1, five_design.2.2.2,
    ?_, tails, ?_, ?_⟩
  · intro a; rw [(five_correlations a).1, (five_correlations a).2.1]
    exact ⟨by norm_num, by norm_num, ht a⟩
  · intro α hα hα1
    have hp : printedReject α 1 := Or.inr (by linarith)
    have hc : ¬ correctedReject α 1 1 := by
      intro h; rcases h with h | h <;> linarith
    simp only [tails]
    simp [uniformProbability, hp, hc, hα1]
  · norm_num [printedReject]

/-- Nonnegativity of finite randomization probabilities (Equation (2), p. 7). -/
theorem probability_nonneg {A : Type*} (μ : FiniteLaw A) (P : A → Prop) :
    0 ≤ probability μ P := by
  classical
  apply Finset.sum_nonneg
  intro z hz
  split_ifs <;> simp [μ.nonneg z hz]

/-- Inclusion of assignment events implies the probability inequality (p. 7). -/
theorem probability_mono {A : Type*} (μ : FiniteLaw A) (P Q : A → Prop)
    (h : ∀ z ∈ μ.support, P z → Q z) : probability μ P ≤ probability μ Q := by
  classical
  apply Finset.sum_le_sum
  intro z hz
  by_cases hp : P z
  · simp [hp, h z hz hp]
  · simp [hp]; split_ifs <;> simp [μ.nonneg z hz]

/-- Total finite assignment probability is one (p. 7). -/
theorem probability_true {A : Type*} (μ : FiniteLaw A) :
    probability μ (fun _ => True) = 1 := by simp [probability, μ.total]

/-- A probability is at most one (p. 7). -/
theorem probability_le_one {A : Type*} (μ : FiniteLaw A) (P : A → Prop) :
    probability μ P ≤ 1 := by
  rw [← probability_true μ]
  exact probability_mono μ P _ (by simp)

/-- Inclusive tail identity in P030-T3(i): p_U = 1-p_L + Pr(t=x). -/
theorem tail_identity {A : Type*} (μ : FiniteLaw A) (f : A → ℝ) (x : ℝ) :
    upperTail μ f x = 1 - lowerTail μ f x + probability μ (fun z => f z = x) := by
  classical
  have h : lowerTail μ f x + upperTail μ f x =
      1 + probability μ (fun z => f z = x) := by
    unfold lowerTail upperTail probability
    rw [← μ.total, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    rcases lt_trichotomy (f z) x with h | h | h
    · simp [h.le, not_le.mpr h, ne_of_lt h]
    · simp [h]
    · simp [h.le, not_le.mpr h, ne_of_gt h]
  linarith

/-- Lower tails are monotone in their threshold (P030-T3(ii), p. 7 correction). -/
theorem lowerTail_mono {A : Type*} (μ : FiniteLaw A) (f : A → ℝ)
    {x y : ℝ} (h : x ≤ y) : lowerTail μ f x ≤ lowerTail μ f y :=
  probability_mono μ _ _ (fun _ _ hz => hz.trans h)

/-- P030-T3(ii): the inclusive lower-tail p-value is super-uniform for ANY
finite probability law, including ties and zero-mass assignments. -/
theorem lower_tail_valid {A : Type*} (μ : FiniteLaw A) (f : A → ℝ)
    (u : ℝ) (hu : 0 ≤ u) :
    probability μ (fun z => lowerTail μ f (f z) ≤ u) ≤ u := by
  classical
  let E := μ.support.filter (fun z => lowerTail μ f (f z) ≤ u)
  by_cases hE : E.Nonempty
  · obtain ⟨m, hm, hmax⟩ := E.exists_max_image f hE
    have hm' := (Finset.mem_filter.mp hm).2
    calc
      probability μ (fun z => lowerTail μ f (f z) ≤ u) ≤ lowerTail μ f (f m) := by
        apply probability_mono
        intro z hz hp
        exact hmax z (Finset.mem_filter.mpr ⟨hz, hp⟩)
      _ ≤ u := hm'
  · have hp : probability μ (fun z => lowerTail μ f (f z) ≤ u) = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      have hn : ¬ lowerTail μ f (f z) ≤ u := fun h => hE ⟨z, Finset.mem_filter.mpr ⟨hz, h⟩⟩
      simp [hn]
    rw [hp]; exact hu

/-- P030-T3(iii): the inclusive upper-tail p-value is super-uniform, by -f. -/
theorem upper_tail_valid {A : Type*} (μ : FiniteLaw A) (f : A → ℝ)
    (u : ℝ) (hu : 0 ≤ u) :
    probability μ (fun z => upperTail μ f (f z) ≤ u) ≤ u := by
  simpa [lowerTail, upperTail, neg_le_neg_iff] using
    lower_tail_valid μ (fun z => -f z) u hu

/-- The union bound for the assignment law (P030-T3(iv)). -/
theorem probability_union_le {A : Type*} (μ : FiniteLaw A) (P Q : A → Prop) :
    probability μ (fun z => P z ∨ Q z) ≤ probability μ P + probability μ Q := by
  classical
  unfold probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  by_cases hp : P z <;> by_cases hq : Q z <;> simp [hp, hq, μ.nonneg z hz]

/-- Corrected strict-endpoint two-tailed test has conditional size ≤ α,
P030-T3(iv), repairing the exactness claim on p. 7. -/
theorem corrected_two_tailed_valid {A : Type*} (μ : FiniteLaw A) (f : A → ℝ)
    (α : ℝ) (hα : 0 < α) (_hα1 : α < 1) :
    probability μ (fun z => correctedReject α (lowerTail μ f (f z))
      (upperTail μ f (f z))) ≤ α := by
  calc
    _ ≤ probability μ (fun z => lowerTail μ f (f z) ≤ α/2 ∨ upperTail μ f (f z) ≤ α/2) :=
      probability_mono μ _ _ (fun _ _ h => h.elim
        (fun h => Or.inl h.le) (fun h => Or.inr h.le))
    _ ≤ probability μ (fun z => lowerTail μ f (f z) ≤ α/2) +
        probability μ (fun z => upperTail μ f (f z) ≤ α/2) := probability_union_le μ _ _
    _ ≤ α := by
      have hl := lower_tail_valid μ f (α/2) (by linarith)
      have hu := upper_tail_valid μ f (α/2) (by linarith)
      linarith

/-- P030-T3(v): every corrected strict rejection is a printed rejection. -/
theorem corrected_reject_subset_printed {A : Type*} (μ : FiniteLaw A)
    (f : A → ℝ) (α x : ℝ) :
    correctedReject α (lowerTail μ f x) (upperTail μ f x) →
      printedReject α (lowerTail μ f x) := by
  intro h
  rcases h with h | h
  · exact Or.inl h
  · apply Or.inr
    have hi := tail_identity μ f x
    have hn := probability_nonneg μ (fun z => f z = x)
    linarith

/-- P030-T3(vi): the conventional two-tailed p-value has the inclusive rejection
event p_L ≤ α/2 or p_U ≤ α/2 when 0 < α < 1. -/
theorem twoTailP_event (pL pU α : ℝ) (_hα : 0 < α) (hα1 : α < 1) :
    twoTailP pL pU ≤ α ↔ pL ≤ α/2 ∨ pU ≤ α/2 := by
  simp only [twoTailP, min_le_iff]
  constructor
  · intro h
    rcases h with h | h
    · linarith
    · have : min pL pU ≤ α/2 := by linarith
      exact min_le_iff.mp this
  · intro h
    exact Or.inr (by have := min_le_iff.mpr h; linarith)

/-- P030-T3(vi): the conventional inclusive-cutoff rule also has size ≤ α. -/
theorem conventional_two_tailed_valid {A : Type*} (μ : FiniteLaw A) (f : A → ℝ)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    probability μ (fun z => twoTailP (lowerTail μ f (f z))
      (upperTail μ f (f z)) ≤ α) ≤ α := by
  simp_rw [twoTailP_event _ _ α hα hα1]
  have h := probability_union_le μ
    (fun z => lowerTail μ f (f z) ≤ α/2) (fun z => upperTail μ f (f z) ≤ α/2)
  have hl := lower_tail_valid μ f (α/2) (by linarith)
  have hu := upper_tail_valid μ f (α/2) (by linarith)
  linarith

/-- Uniform conditional law, "all Z in Ω' occur with equal probability" (p. 7). -/
def uniformLaw {A : Type*} (Ω : Finset A) (hΩ : Ω.Nonempty) : FiniteLaw A where
  support := Ω
  mass := fun _ => (Ω.card : ℝ)⁻¹
  nonneg := by intros; positivity
  total := by
    have hn : (Ω.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hΩ)
    simp [hn]

/-- The uniform law gives exactly the assignment-counted formula (2), p. 7. -/
theorem uniformLaw_probability {A : Type*} (Ω : Finset A) (hΩ : Ω.Nonempty)
    (P : A → Prop) : probability (uniformLaw Ω hΩ) P = uniformProbability Ω P := by
  classical
  unfold probability uniformLaw uniformProbability
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- Ω' keeps the treatment of each fixed unit constant, p. 6, corrected P030-T7(a). -/
theorem conditional_preserves_treatments {N : ℕ} (Ω : AssignmentSet N)
    (S : FixedIndicator N) (a : Assignment N) :
    ∀ z ∈ conditionalAssignments Ω S a, ∀ z' ∈ conditionalAssignments Ω S a,
      ∀ i, S i = true → z i = z' i := by
  classical
  intro z hz z' hz' i hi
  exact ((Finset.mem_filter.mp hz).2 i hi).trans ((Finset.mem_filter.mp hz').2 i hi).symm

/-- No interference implies the corrected focal-outcome null, T6(a), T7(b), p. 6. -/
theorem no_interference_fixed {N : ℕ} (Ω : AssignmentSet N)
    (S : FixedIndicator N) (a : Assignment N) (Y : PotentialOutcomes N)
    (h : NoInterference Ω Y) : FixedOutcomeNull (conditionalAssignments Ω S a) S Y := by
  classical
  intro i hi z hz z' hz'
  exact h i z (Finset.mem_filter.mp hz).1 z' (Finset.mem_filter.mp hz').1
    (conditional_preserves_treatments Ω S a z hz z' hz' i hi)

/-- T7(b): variation of a fixed outcome on Ω' refutes global no interference (p. 6). -/
theorem fixed_dependence_implies_interference {N : ℕ} (Ω : AssignmentSet N)
    (S : FixedIndicator N) (a : Assignment N) (Y : PotentialOutcomes N)
    (h : ∃ i, S i = true ∧ ∃ z ∈ conditionalAssignments Ω S a,
      ∃ z' ∈ conditionalAssignments Ω S a, Y i z ≠ Y i z') : ¬ NoInterference Ω Y := by
  intro hn
  obtain ⟨i, hi, z, hz, z', hz', hne⟩ := h
  exact hne (no_interference_fixed Ω S a Y hn i hi z hz z' hz')

/-- T7(c): arbitrary direct effects c_i + τ_i Z_i satisfy no interference (p. 6). -/
theorem direct_effects_no_interference {N : ℕ} (Ω : AssignmentSet N)
    (c τ : Fin N → ℝ) :
    NoInterference Ω (fun i z => c i + τ i * treatment z i) := by
  intro i z hz z' hz' hi
  simp [treatment, hi]

/-- Corrected P030-T6(b)-(c), p. 7: observed fixed outcomes impute every conditional
statistic, and their reference distribution equals its uniform null distribution. -/
theorem corrected_outcome_null {N : ℕ} (Ω : AssignmentSet N)
    (S : FixedIndicator N) (obs : Assignment N) (hobs : obs ∈ Ω)
    (Y : PotentialOutcomes N)
    (g : ({i // S i = true} → ℝ) → Assignment N → ℝ) :
    (NoInterference Ω Y → FixedOutcomeNull (conditionalAssignments Ω S obs) S Y) ∧
    (FixedOutcomeNull (conditionalAssignments Ω S obs) S Y →
      (∀ z ∈ conditionalAssignments Ω S obs, fixedOutcomes S Y z = fixedOutcomes S Y obs) ∧
      (∀ z ∈ conditionalAssignments Ω S obs,
        referenceStatistic S Y g obs z = statistic S Y g z) ∧
      (∀ x : ℝ, uniformProbability (conditionalAssignments Ω S obs)
        (fun z => referenceStatistic S Y g obs z ≤ x) =
        uniformProbability (conditionalAssignments Ω S obs) (fun z => statistic S Y g z ≤ x))) := by
  classical
  have ho : obs ∈ conditionalAssignments Ω S obs := by simp [conditionalAssignments, hobs]
  refine ⟨no_interference_fixed Ω S obs Y, ?_⟩
  intro hnull
  have hf : ∀ z ∈ conditionalAssignments Ω S obs,
      fixedOutcomes S Y z = fixedOutcomes S Y obs := by
    intro z hz
    funext i
    exact hnull i.val i.property z hz obs ho
  have ht : ∀ z ∈ conditionalAssignments Ω S obs,
      referenceStatistic S Y g obs z = statistic S Y g z := by
    intro z hz
    simp [referenceStatistic, statistic, hf z hz]
  refine ⟨hf, ht, ?_⟩
  intro x
  have he : (conditionalAssignments Ω S obs).filter (fun z => referenceStatistic S Y g obs z ≤ x) =
      (conditionalAssignments Ω S obs).filter (fun z => statistic S Y g z ≤ x) := by
    ext z
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨hz, hx⟩
    · exact ⟨hz, by simpa [ht z hz] using hx⟩
    · exact ⟨hz, by simpa [ht z hz] using hx⟩
  simp only [uniformProbability, he]

/-- P030-T12(d): at every attainable inclusive p-value, the rejection probability
is exactly that p-value, for any finite law (and hence the uniform law of p. 7). -/
theorem attainable_exactness {A : Type*} (μ : FiniteLaw A) (f : A → ℝ) (z : A) :
    probability μ (fun w => lowerTail μ f (f w) ≤ lowerTail μ f (f z)) =
      lowerTail μ f (f z) := by
  apply le_antisymm
  · exact lower_tail_valid μ f _ (probability_nonneg μ _)
  · exact probability_mono μ _ _ (fun w _ hw => lowerTail_mono μ f hw)

/-- P030-T12(d): at an arbitrary threshold, the exact rejection probability is
the greatest attainable p-value below the threshold, or zero if there is none.
IsGreatest expresses exactly the target's maximum of {0} ∪ {p(z) ≤ u}. -/
theorem exact_rejection_max {A : Type*} (μ : FiniteLaw A) (f : A → ℝ) (u : ℝ) :
    IsGreatest ({0} ∪ {p | ∃ z ∈ μ.support, p = lowerTail μ f (f z) ∧ p ≤ u})
      (probability μ (fun z => lowerTail μ f (f z) ≤ u)) := by
  classical
  let E := μ.support.filter (fun z => lowerTail μ f (f z) ≤ u)
  have hb : ∀ p ∈ ({0} ∪ {p | ∃ z ∈ μ.support, p = lowerTail μ f (f z) ∧ p ≤ u} : Set ℝ),
      p ≤ probability μ (fun z => lowerTail μ f (f z) ≤ u) := by
    intro p hp
    rcases hp with hp | ⟨z, hz, rfl, hpu⟩
    · have hp0 : p = 0 := Set.mem_singleton_iff.mp hp
      subst p
      exact probability_nonneg μ (fun z => lowerTail μ f (f z) ≤ u)
    · rw [← attainable_exactness μ f z]
      exact probability_mono μ _ _ (fun w _ hw => hw.trans hpu)
  refine ⟨?_, hb⟩
  by_cases hE : E.Nonempty
  · obtain ⟨m, hm, hmax⟩ := E.exists_max_image f hE
    have hmp := Finset.mem_filter.mp hm
    have heq : probability μ (fun z => lowerTail μ f (f z) ≤ u) = lowerTail μ f (f m) := by
      apply le_antisymm
      · apply probability_mono
        intro z hz hp
        exact hmax z (Finset.mem_filter.mpr ⟨hz, hp⟩)
      · exact probability_mono μ _ _ (fun z _ hz => (lowerTail_mono μ f hz).trans hmp.2)
    right
    exact ⟨m, hmp.1, heq, by rw [heq]; exact hmp.2⟩
  · left
    change probability μ (fun z => lowerTail μ f (f z) ≤ u) = 0
    apply Finset.sum_eq_zero
    intro z hz
    have hn : ¬ lowerTail μ f (f z) ≤ u := fun h => hE ⟨z, Finset.mem_filter.mpr ⟨hz, h⟩⟩
    simp [hn]

/-- P030-T12(a)-(d), Equation (2) and the abstract's exact significance level:
under the corrected outcome null and the uniform CONDITIONAL law, observed-data
imputation is valid, the assignment-counted p-value is super-uniform and exact
at all attainable levels, with ties and arbitrary direct effects allowed. -/
theorem one_tailed_randomization_valid {N : ℕ} (Ω : AssignmentSet N)
    (S : FixedIndicator N) (a : Assignment N)
    (hΩ' : (conditionalAssignments Ω S a).Nonempty)
    (Y : PotentialOutcomes N)
    (g : ({i // S i = true} → ℝ) → Assignment N → ℝ)
    (hnull : NoInterference Ω Y ∨ FixedOutcomeNull (conditionalAssignments Ω S a) S Y) :
    let Ω' := conditionalAssignments Ω S a
    let μ := uniformLaw Ω' hΩ'
    let t := statistic S Y g
    (∀ z ∈ Ω', ∀ w ∈ Ω', referenceStatistic S Y g z w = t w) ∧
    (∀ z ∈ Ω', lowerTail μ t (t z) = uniformProbability Ω' (fun w => t w ≤ t z)) ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 → probability μ (fun z => lowerTail μ t (t z) ≤ u) ≤ u) ∧
    (∀ z ∈ Ω', probability μ (fun w => lowerTail μ t (t w) ≤ lowerTail μ t (t z)) =
      lowerTail μ t (t z)) ∧
    (∀ u : ℝ, IsGreatest ({0} ∪ {p | ∃ z ∈ Ω', p = lowerTail μ t (t z) ∧ p ≤ u})
      (probability μ (fun z => lowerTail μ t (t z) ≤ u))) := by
  dsimp only
  have hf : FixedOutcomeNull (conditionalAssignments Ω S a) S Y :=
    hnull.elim (no_interference_fixed Ω S a Y) id
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz w hw
    unfold referenceStatistic statistic
    congr 1
    funext i
    exact hf i.val i.property z hz w hw
  · intro z hz; exact uniformLaw_probability _ hΩ' _
  · intro u hu hu1; exact lower_tail_valid _ _ u hu
  · intro z hz; exact attainable_exactness _ _ z
  · intro u; exact exact_rejection_max _ _ u

/-- Single treated variant: the nearest treated distance is |x_i-x_j| (p. 9). -/
theorem nearest_single_treated {N : ℕ} (x : Fin N → ℝ) (S : FixedIndicator N)
    (j i : Fin N) (hj : S j = false) :
    nearestDistance x S (fun k => decide (k = j)) i = |x i - x j| := by
  classical
  have hV : Finset.univ.filter (fun k => S k = false ∧ decide (k = j) = true) = {j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
      Finset.mem_singleton]
    constructor
    · exact And.right
    · intro h; subst k; exact ⟨hj, rfl⟩
  unfold nearestDistance
  dsimp only
  rw [hV]
  simp

/-- Ten equidistant positions, units 1,...,10 (p. 9). -/
def tenX (i : Fin 10) : ℝ := (i.val : ℝ) + 1
/-- Fixed units 1,8,9,10, selected in advance for T2/T5; also the paper's p. 9 choice. -/
def tenS (i : Fin 10) : Bool := decide (i.val = 0 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9)
/-- z^(j) treats exactly unit j, whose probability is 1/10 (p. 9). -/
def tenAssignment (j : Fin 10) : Assignment 10 := fun i => decide (i = j)
/-- Full one-treated-unit design in the ten-unit example (p. 9). -/
def tenΩ : Finset (Assignment 10) := Finset.univ.image tenAssignment
/-- Fixed outcome schedule in the null counterexamples T2/T5, distinct from
the paper's DGP. -/
def tenYnull (i : Fin 10) (_z : Assignment 10) : ℝ :=
  (![1,2,2,2,2,3,2,3,2,1] : Fin 10 → ℝ) i
/-- Enumeration of fixed units (1,8,9,10), p. 9. -/
def tenFixed : Fin 4 → Fin 10 := ![0,7,8,9]
/-- The six conditional treated-unit indices, units 2,...,7 (p. 9 Table 1). -/
def tableTreatment (r : Fin 6) : Fin 10 := ⟨r.val + 1, by omega⟩
/-- Ω' of Table 1, p. 9, as an explicit image of six distinct assignments. -/
def tableΩ : Finset (Assignment 10) := Finset.univ.image (fun r => tenAssignment (tableTreatment r))
/-- The observed and null-imputed Y_fixed = (1,3,2,1) (pp. 9-10). -/
def tableY : Fin 4 → ℝ := fun i => tenYnull (tenFixed i) (tenAssignment 6)
/-- D_nearest in each row of Table 1, p. 9, computed from its single treated variant. -/
def tableDistances (r : Fin 6) : Fin 4 → ℝ :=
  fun i => nearestDistance tenX tenS (tenAssignment (tableTreatment r)) (tenFixed i)
/-- Table 1's ρ_0, p. 9, using held-fixed Y_fixed and the corrected Pearson formula. -/
def tableRho (r : Fin 6) : ℝ := spearman (tableDistances r) tableY
/-- Exact values which round to Table 1's printed correlations (p. 9). -/
def tableValues : Fin 6 → ℝ :=
  ![-1 / Real.sqrt 90, -1 / Real.sqrt 90, -1 / Real.sqrt 90,
    -5/6, -3 / Real.sqrt 10, -3 / Real.sqrt 10]

/-- The computed fixed outcomes equal the vector printed in Table 1 (p. 9). -/
theorem table_y_vector : tableY = ![1,3,2,1] := by
  funext i; fin_cases i <;> norm_num [tableY, tenYnull, tenFixed]
/-- Table 1's distance column (p. 9), derived from positions and assignments. -/
theorem table_distances : tableDistances =
    ![![1,6,7,8], ![2,5,6,7], ![3,4,5,6], ![4,3,4,5], ![5,2,3,4], ![6,1,2,3]] := by
  funext r i
  have hs : tenS (tableTreatment r) = false := by
    fin_cases r <;> norm_num [tenS, tableTreatment]
  unfold tableDistances tenAssignment
  rw [nearest_single_treated tenX tenS _ _ hs]
  fin_cases r <;> fin_cases i <;> norm_num [tenX, tenFixed, tableTreatment]

/-- The three distinct correlations are strictly ordered, with exact rational
squares 1/90, 25/36, 9/10 (T2/T5/Table 1, p. 9). -/
theorem table_value_order :
    -3 / Real.sqrt 10 < (-5/6 : ℝ) ∧ (-5/6 : ℝ) < -1 / Real.sqrt 90 ∧
    -1 / Real.sqrt 90 < 0 := by
  have h10 : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  have h90 : 0 < Real.sqrt 90 := Real.sqrt_pos.mpr (by norm_num)
  have hsq10 := Real.sq_sqrt (show (0:ℝ) ≤ 10 by norm_num)
  have hsq90 := Real.sq_sqrt (show (0:ℝ) ≤ 90 by norm_num)
  have hA : (-3 / Real.sqrt 10)^2 = (9/10 : ℝ) := by rw [div_pow, hsq10]; norm_num
  have hB : (-1 / Real.sqrt 90)^2 = (1/90 : ℝ) := by rw [div_pow, hsq90]; norm_num
  have hnA : -3 / Real.sqrt 10 < 0 := div_neg_of_neg_of_pos (by norm_num) h10
  have hnB : -1 / Real.sqrt 90 < 0 := div_neg_of_neg_of_pos (by norm_num) h90
  exact ⟨by nlinarith, by nlinarith, hnB⟩

/-- Average-rank computation reproduces all six exact Table 1 correlations;
rank variances are positive, including rows with distance ties (p. 9). -/
theorem table_correlations :
    tableRho = tableValues ∧ (∀ r, 0 < rankSquares (tableDistances r)) ∧
    rankSquares tableY = 9/2 := by
  have hs10 := Real.sq_sqrt (show (0:ℝ) ≤ 10 by norm_num)
  have hden : Real.sqrt (5*(9/2)) = (3/2) * Real.sqrt 10 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
    nlinarith
  have h90 : Real.sqrt 90 = 3 * Real.sqrt 10 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
    nlinarith
  have h10 : Real.sqrt 10 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hmid : Real.sqrt ((9/2)*(9/2)) = (9/2:ℝ) := Real.sqrt_mul_self (by norm_num)
  have hY : rankSquares tableY = 9/2 := by
    rw [table_y_vector]
    norm_num [rankSquares, centeredRanks, averageRank, Fin.sum_univ_succ, Fin.card_filter_univ_succ]
  have hcert : ∀ r : Fin 6,
      rankCross (tableDistances r) tableY = (![-1/2,-1/2,-1/2,-15/4,-9/2,-9/2] : Fin 6 → ℝ) r ∧
      rankSquares (tableDistances r) = (![5,5,5,9/2,5,5] : Fin 6 → ℝ) r := by
    intro r
    rw [table_y_vector, table_distances]
    fin_cases r <;> norm_num [rankCross, rankSquares, centeredRanks, averageRank,
      Fin.sum_univ_succ, Fin.card_filter_univ_succ]
  refine ⟨?_, ?_, ?_⟩
  · funext r
    unfold tableRho spearman
    rw [(hcert r).1, (hcert r).2, hY]
    fin_cases r <;> simp only [tableValues, Matrix.cons_val_zero', Matrix.cons_val_succ', hden, hmid, h90] <;>
      field_simp [h10] <;> ring
  · intro r; rw [(hcert r).2]; fin_cases r <;> norm_num
  · exact hY

/-- Assignment-counted lower and upper tails of the six Table 1 values (pp. 9-10). -/
theorem table_tail_probabilities :
    (∀ r : Fin 6, uniformProbability Finset.univ (fun s => tableRho s ≤ tableRho r) =
      (![1,1,1,1/2,1/3,1/3] : Fin 6 → ℝ) r) ∧
    (∀ r : Fin 6, uniformProbability Finset.univ (fun s => tableRho r ≤ tableRho s) =
      (![1/2,1/2,1/2,2/3,1,1] : Fin 6 → ℝ) r) := by
  have h := table_value_order
  have hab : -3 / Real.sqrt 10 < -1 / Real.sqrt 90 := h.1.trans h.2.1
  constructor <;> intro r <;> fin_cases r <;>
    norm_num [uniformProbability, table_correlations.1, tableValues,
      Fin.card_filter_univ_succ, h.1.le, h.2.1.le, hab.le,
      not_le.mpr h.1, not_le.mpr h.2.1, not_le.mpr hab] <;>
      split_ifs <;> norm_num <;> linarith [h.1, h.2.1]

/-- T2's printed size is 1/2 and corrected size is 0, for every 0<α≤2/3. -/
theorem table_rejection_probabilities (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 2/3) :
    uniformProbability (Finset.univ : Finset (Fin 6)) (fun r => printedReject α
      (uniformProbability Finset.univ (fun s => tableRho s ≤ tableRho r))) = 1/2 ∧
    uniformProbability (Finset.univ : Finset (Fin 6)) (fun r => correctedReject α
      (uniformProbability Finset.univ (fun s => tableRho s ≤ tableRho r))
      (uniformProbability Finset.univ (fun s => tableRho r ≤ tableRho s))) = 0 := by
  classical
  have h1 : printedReject α 1 := Or.inr (by linarith)
  have h2 : ¬ printedReject α (1/2) := by intro h; rcases h with h | h <;> linarith
  have h3 : ¬ printedReject α (1/3) := by intro h; rcases h with h | h <;> linarith
  have hc1 : ¬ correctedReject α 1 (1/2) := by intro h; rcases h with h | h <;> linarith
  have hc2 : ¬ correctedReject α (1/2) (2/3) := by intro h; rcases h with h | h <;> linarith
  have hc3 : ¬ correctedReject α (1/3) 1 := by intro h; rcases h with h | h <;> linarith
  simp only [table_tail_probabilities]
  norm_num [uniformProbability, Fin.card_filter_univ_succ, h1, h2, h3, hc1, hc2, hc3]

/-- The ten-unit design conditions to exactly Table 1's six assignments (p. 9),
with event probability 6/10. This also verifies the design hypotheses of T2/T5. -/
theorem ten_design :
    tenΩ.card = 10 ∧ tableΩ.card = 6 ∧
    conditionalAssignments tenΩ tenS (tenAssignment 6) = tableΩ ∧
    uniformProbability tenΩ (fun z => ∀ i, tenS i = true → z i = tenAssignment 6 i) = 3/5 ∧
    (∀ j : Fin 10, (Finset.univ.filter (fun i => tenAssignment j i = true)).card = 1) := by
  classical
  have hinj : Function.Injective tenAssignment := by
    intro a b h
    have hi := congrFun h a
    simpa [tenAssignment] using hi
  have htinj : Function.Injective (fun r => tenAssignment (tableTreatment r)) := by
    intro a b h
    have h' := congrArg Fin.val (hinj h)
    apply Fin.ext
    simp [tableTreatment] at h'
    omega
  have hcard : tenΩ.card = 10 := by
    simpa [tenΩ] using Finset.card_image_of_injective Finset.univ hinj
  have htable : tableΩ.card = 6 := by
    simpa [tableΩ] using Finset.card_image_of_injective Finset.univ htinj
  have hcond : conditionalAssignments tenΩ tenS (tenAssignment 6) = tableΩ := by
    ext z
    constructor
    · intro hz
      obtain ⟨hz, hf⟩ := Finset.mem_filter.mp hz
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
      have h0 := hf 0 (by norm_num [tenS])
      have h7 := hf 7 (by norm_num [tenS])
      have h8 := hf 8 (by norm_num [tenS])
      have h9 := hf 9 (by norm_num [tenS])
      simp [tenAssignment, Fin.ext_iff] at h0 h7 h8 h9
      let r : Fin 6 := ⟨j.val - 1, by omega⟩
      apply Finset.mem_image.mpr
      refine ⟨r, Finset.mem_univ _, ?_⟩
      congr 1
      apply Fin.ext
      dsimp [tableTreatment, r]
      omega
    · intro hz
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨tableTreatment r, Finset.mem_univ _, rfl⟩, ?_⟩
      intro i hi
      have hi' : i.val = 0 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by simpa [tenS] using hi
      have hr : 1 ≤ (tableTreatment r).val ∧ (tableTreatment r).val ≤ 6 := by
        dsimp [tableTreatment]; omega
      have hl : i ≠ tableTreatment r := by intro he; have := congrArg Fin.val he; omega
      have hr6 : i ≠ (6 : Fin 10) := by intro he; have := congrArg Fin.val he; omega
      simp [tenAssignment, hl, hr6]
  refine ⟨hcard, htable, hcond, ?_, ?_⟩
  · calc
      _ = (tableΩ.card : ℝ)/(tenΩ.card : ℝ) := by
        unfold uniformProbability
        congr 2
        apply congrArg Finset.card
        rw [← hcond]
        ext z
        simp only [conditionalAssignments, Finset.mem_filter]
      _ = 3/5 := by rw [htable, hcard]; norm_num
  · intro j
    have hs : Finset.univ.filter (fun i => tenAssignment j i = true) = {j} := by
      ext i; simp [tenAssignment]
    rw [hs]; simp

/-- Uniform laws commute with an injective enumeration of assignments (p. 7). -/
theorem uniformProbability_image {A B : Type*} [DecidableEq B] (s : Finset A) (e : A → B)
    (he : Function.Injective e) (P : B → Prop) :
    uniformProbability (s.image e) P = uniformProbability s (fun a => P (e a)) := by
  classical
  unfold uniformProbability
  rw [Finset.filter_image, Finset.card_image_of_injective _ he,
    Finset.card_image_of_injective _ he]

/-- T2: a genuine no-effect schedule on ALL binary assignments realizes the
nonconstant Table 1 reference law; the printed conditional Type I error is 1/2
for 0<α≤2/3, exceeding α whenever α<1/2 (in particular α=1/20). -/
theorem ten_unit_counterexample :
    (∀ i, ∀ z z' : Assignment 10, tenYnull i z = tenYnull i z') ∧
    NoEffects tenΩ tenYnull ∧ NoInterference tenΩ tenYnull ∧
    tenΩ.card = 10 ∧ tableΩ.card = 6 ∧
    conditionalAssignments tenΩ tenS (tenAssignment 6) = tableΩ ∧
    uniformProbability tenΩ (fun z => ∀ i, tenS i = true → z i = tenAssignment 6 i) = 3/5 ∧
    tableY = ![1,3,2,1] ∧ tableRho = tableValues ∧
    (∀ r, 0 < rankSquares (tableDistances r)) ∧ rankSquares tableY = 9/2 ∧
    (∀ α : ℝ, 0 < α → α ≤ 2/3 →
      uniformProbability (Finset.univ : Finset (Fin 6)) (fun r => printedReject α
        (uniformProbability Finset.univ (fun s => tableRho s ≤ tableRho r))) = 1/2 ∧
      uniformProbability (Finset.univ : Finset (Fin 6)) (fun r => correctedReject α
        (uniformProbability Finset.univ (fun s => tableRho s ≤ tableRho r))
        (uniformProbability Finset.univ (fun s => tableRho r ≤ tableRho s))) = 0) ∧
    (1/20 : ℝ) < 1/2 := by
  have hn : NoEffects tenΩ tenYnull := by intro i z hz z' hz'; rfl
  refine ⟨by intros; rfl, hn, no_effects_implies_no_interference _ _ hn,
    ten_design.1, ten_design.2.1, ten_design.2.2.1, ten_design.2.2.2.1,
    ?_, table_correlations.1, table_correlations.2.1, table_correlations.2.2,
    table_rejection_probabilities, by norm_num⟩
  funext i; fin_cases i <;> norm_num [tableY, tenYnull, tenFixed]

/-- Printed Equation (1) would give p=1 whenever its invariant-statistic null
holds, as contrasted with the actual p=1/3 in P030-T5 (p. 7). -/
theorem constant_statistic_p_one {A : Type*} (Ω : Finset A) (hΩ : Ω.Nonempty)
    (t : A → ℝ) (h : ∀ z ∈ Ω, ∀ z' ∈ Ω, t z = t z') :
    ∀ z ∈ Ω, uniformProbability Ω (fun w => t w ≤ t z) = 1 := by
  classical
  intro z hz
  have he : Ω.filter (fun w => t w ≤ t z) = Ω := by
    apply Finset.filter_eq_self.mpr
    intro w hw; rw [h w hw z hz]
  have hn : (Ω.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hΩ
  simp [uniformProbability, he, hn]

/-- P030-T5: no interference (even no effects) does NOT imply the printed
statistic invariance of Equation (1): rows treating units 2 and 5 differ,
while the observed row treating unit 7 has the paper's p=1/3. -/
theorem statistic_invariance_counterexample :
    NoEffects tenΩ tenYnull ∧ NoInterference tenΩ tenYnull ∧
    FixedOutcomeNull tableΩ tenS tenYnull ∧
    tenAssignment (tableTreatment 0) ∈ tableΩ ∧
    tenAssignment (tableTreatment 3) ∈ tableΩ ∧
    tableRho 0 ≠ tableRho 3 ∧
    uniformProbability Finset.univ (fun s => tableRho s ≤ tableRho 5) = 1/3 := by
  classical
  have hn : NoEffects tenΩ tenYnull := by intro i z hz z' hz'; rfl
  refine ⟨hn, no_effects_implies_no_interference _ _ hn, by intro i hi z hz z' hz'; rfl,
    by simp [tableΩ], by simp [tableΩ], ?_, ?_⟩
  · simp only [table_correlations.1, tableValues, Matrix.cons_val_zero]
    exact ne_of_gt table_value_order.2.1
  · simpa using table_tail_probabilities.1 5

/-- Printed exactness claim after Equation (2), p. 7 (P030-T4), with all design,
null, statistic and uniform conditional-law quantifiers. This definition states
the FALSE claim faithfully; the following theorem refutes it rather than assumes it. -/
def PrintedTwoTailedExactness : Prop :=
  ∀ (N : ℕ) (Ω : AssignmentSet N) (S : FixedIndicator N) (a : Assignment N),
    (conditionalAssignments Ω S a).Nonempty →
    ∀ (Y : PotentialOutcomes N)
      (g : ({i // S i = true} → ℝ) → Assignment N → ℝ), NoInterference Ω Y →
    ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      uniformProbability (conditionalAssignments Ω S a) (fun z => printedReject α
        (uniformProbability (conditionalAssignments Ω S a)
          (fun w => referenceStatistic S Y g z w ≤ statistic S Y g z))) ≤ α

/-- The actual five-unit Spearman statistic as a function of observed Y_fixed
and the assignment, for instantiating the full P030-T4 claim (p. 7). -/
def fiveG (y : {i // fiveS i = true} → ℝ) (z : Assignment 5) : ℝ :=
  spearman (fun i : Fin 3 => nearestDistance fiveX fiveS z (fiveFixed i))
    (fun i : Fin 3 => y ⟨fiveFixed i, by fin_cases i <;> norm_num [fiveS, fiveFixed]⟩)

/-- P030-T4's claim as printed is false, refuted by P030-T1 at α=1/20. -/
theorem printed_two_tailed_claim_false : ¬ PrintedTwoTailedExactness := by
  classical
  intro h
  have hΩ : (conditionalAssignments fiveΩ fiveS (fiveAssignment 0)).Nonempty := by
    rw [five_design.2.1]; exact ⟨fiveAssignment 0, by simp [fiveΩ]⟩
  have hf : ∀ z ∈ fiveΩ, statistic fiveS fiveY fiveG z = 1 := by
    intro z hz
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hz
    exact (five_correlations r).2.2
  have href : ∀ z w : Assignment 5,
      referenceStatistic fiveS fiveY fiveG z w = statistic fiveS fiveY fiveG w := by
    intros; rfl
  have hsize := h 5 fiveΩ fiveS (fiveAssignment 0) hΩ fiveY fiveG
    (no_effects_implies_no_interference _ _ five_no_effects) (1/20) (by norm_num) (by norm_num)
  rw [five_design.2.1] at hsize
  have hp : ∀ z ∈ fiveΩ,
      uniformProbability fiveΩ (fun w => referenceStatistic fiveS fiveY fiveG z w ≤
        statistic fiveS fiveY fiveG z) = 1 := by
    intro z hz
    have he : fiveΩ.filter (fun w => referenceStatistic fiveS fiveY fiveG z w ≤
        statistic fiveS fiveY fiveG z) = fiveΩ := by
      apply Finset.filter_eq_self.mpr
      intro w hw; rw [href, hf w hw, hf z hz]
    norm_num [uniformProbability, he, five_design.1]
  have he : fiveΩ.filter (fun z => printedReject (1/20)
      (uniformProbability fiveΩ (fun w => referenceStatistic fiveS fiveY fiveG z w ≤
        statistic fiveS fiveY fiveG z))) = fiveΩ := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    rw [hp z hz]; norm_num [printedReject]
  have hprob : uniformProbability fiveΩ (fun z => printedReject (1/20)
      (uniformProbability fiveΩ (fun w => referenceStatistic fiveS fiveY fiveG z w ≤
        statistic fiveS fiveY fiveG z))) = 1 := by
    change ((fiveΩ.filter _).card : ℝ) / (fiveΩ.card : ℝ) = 1
    rw [he, five_design.1]
    norm_num
  rw [hprob] at hsize
  norm_num at hsize

/-- "Ψ is a spatial effect ... equal to the number of units immediately adjacent to each unit" (p. 9). Adjacency means distance one. -/
def tenPsi (i : Fin 10) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun j => |tenX i - tenX j| = 1)).card : ℝ)
/-- "Θ is an indirect effect equal to the number of treated units directly proximal to each unit" (p. 9). Here this means distance one. -/
def tenTheta (i : Fin 10) (z : Assignment 10) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun j => z j = true ∧ |tenX i - tenX j| = 1)).card : ℝ)
/-- The paper's illustrative DGP Y_i = Ψ_i+Θ_i, which DOES have interference (p. 9). -/
def tenYexample (i : Fin 10) (z : Assignment 10) : ℝ := tenPsi i + tenTheta i z

set_option maxHeartbeats 800000 in
/-- T14(a)-(b): observed spatial, indirect, total and fixed outcomes when unit 7
is treated; this verifies the actual paper DGP, separate from the null T2/T5. -/
theorem example_observed_outcomes :
    tenPsi = ![1,2,2,2,2,2,2,2,2,1] ∧
    (fun i => tenTheta i (tenAssignment 6)) = ![0,0,0,0,0,1,0,1,0,0] ∧
    (fun i => tenYexample i (tenAssignment 6)) = ![1,2,2,2,2,3,2,3,2,1] ∧
    (fun i : Fin 4 => tenYexample (tenFixed i) (tenAssignment 6)) = ![1,3,2,1] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals funext i
  all_goals fin_cases i <;> norm_num [tenYexample, tenPsi, tenTheta, tenX, tenAssignment,
    tenFixed, Fin.card_filter_univ_succ]

/-- T14(e): the exact three correlation values round to the printed three decimals. -/
theorem table_rounding :
    |(-1 / Real.sqrt 90) + 0.105| < 0.0005 ∧
    |(-5/6 : ℝ) + 0.833| < 0.0005 ∧
    |(-3 / Real.sqrt 10) + 0.949| < 0.0005 := by
  have s10 := Real.sq_sqrt (show (0:ℝ) ≤ 10 by norm_num)
  have s90 := Real.sq_sqrt (show (0:ℝ) ≤ 90 by norm_num)
  have p10 : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  have p90 : 0 < Real.sqrt 90 := Real.sqrt_pos.mpr (by norm_num)
  have lo10 : (79/25:ℝ) < Real.sqrt 10 := by nlinarith
  have hi10 : Real.sqrt 10 < (253/80:ℝ) := by nlinarith
  have lo90 : (237/25:ℝ) < Real.sqrt 90 := by nlinarith
  have hi90 : Real.sqrt 90 < (949/100:ℝ) := by nlinarith
  have alo : (-211/2000:ℝ) < -1/Real.sqrt 90 := (lt_div_iff₀ p90).mpr (by nlinarith)
  have ahi : -1/Real.sqrt 90 < (-209/2000:ℝ) := (div_lt_iff₀ p90).mpr (by nlinarith)
  have blo : (-1899/2000:ℝ) < -3/Real.sqrt 10 := (lt_div_iff₀ p10).mpr (by nlinarith)
  have bhi : -3/Real.sqrt 10 < (-1897/2000:ℝ) := (div_lt_iff₀ p10).mpr (by nlinarith)
  refine ⟨?_, by norm_num, ?_⟩ <;> rw [abs_lt] <;> constructor <;> linarith

/-- P030-T14's exact worked reference distribution (Table 1, pp. 9-10):
the six correct correlations, their printed roundings, p=1/3 and all negative.
Together with example_observed_outcomes and ten_design this covers (a)-(g). -/
theorem worked_table_result :
    tableRho = tableValues ∧
    (∀ r, tableRho r < 0) ∧ tableRho 5 = -3 / Real.sqrt 10 ∧
    (Finset.univ.filter (fun r : Fin 6 => tableRho r ≤ tableRho 5)).card = 2 ∧
    uniformProbability Finset.univ (fun r => tableRho r ≤ tableRho 5) = 1/3 ∧
    |(-1 / Real.sqrt 90) + 0.105| < 0.0005 ∧
    |(-5/6 : ℝ) + 0.833| < 0.0005 ∧
    |(-3 / Real.sqrt 10) + 0.949| < 0.0005 := by
  classical
  have h := table_value_order
  have hl : -3 / Real.sqrt 10 < -1 / Real.sqrt 90 := h.1.trans h.2.1
  refine ⟨table_correlations.1, ?_, ?_, ?_, table_tail_probabilities.1 5,
    table_rounding.1, table_rounding.2.1, table_rounding.2.2⟩
  · intro r; fin_cases r <;> simp [table_correlations.1, tableValues] <;> linarith
  · simp [table_correlations.1, tableValues]
  · norm_num [table_correlations.1, tableValues, Fin.card_filter_univ_succ,
      not_le.mpr hl, not_le.mpr h.1]; linarith [h.1]

/-- P030-T8(a): both usual moment divisors give wrong values with the printed
denominator; all six rows are checked, and the observed -4/5 and -3/5 disagree
with the true -3/√10. Printed p. 8 formula, compared with p. 9 Table 1. -/
theorem printed_formula_counterexample :
    (∀ r : Fin 6, printedRho 4 (tableDistances r) tableY =
      (![-4/45,-4/45,-4/45,-20/27,-4/5,-4/5] : Fin 6 → ℝ) r) ∧
    (∀ r : Fin 6, printedRho 3 (tableDistances r) tableY =
      (![-1/15,-1/15,-1/15,-5/9,-3/5,-3/5] : Fin 6 → ℝ) r) ∧
    (-4/5 : ℝ) ≠ -3 / Real.sqrt 10 ∧ (-3/5 : ℝ) ≠ -3 / Real.sqrt 10 ∧
    (-4/5 : ℝ) ≠ -3/5 := by
  have hs : (-3 / Real.sqrt 10)^2 = (9/10 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩
  · intro r; fin_cases r <;>
      norm_num [printedRho, rankCov, rankCross, rankSquares, centeredRanks, averageRank,
        table_distances, table_y_vector, Fin.sum_univ_succ, Fin.card_filter_univ_succ]
  · intro r; fin_cases r <;>
      norm_num [printedRho, rankCov, rankCross, rankSquares, centeredRanks, averageRank,
        table_distances, table_y_vector, Fin.sum_univ_succ, Fin.card_filter_univ_succ]
  · intro he; rw [← he] at hs; norm_num at hs
  · intro he; rw [← he] at hs; norm_num at hs

/-- P030-T8(b): the literal formula reverses an ordering when distance ties vary.
This is a statistic counterexample, not a claim about the simulation code (p. 8). -/
theorem printed_ordering_counterexample :
    spearman (![1,2,1,1] : Fin 4 → ℝ) tableY = Real.sqrt 6 / 3 ∧
    spearman (![0,2,1,1] : Fin 4 → ℝ) tableY = 5/6 ∧
    printedRho 4 (![1,2,1,1] : Fin 4 → ℝ) tableY = 8/9 ∧
    printedRho 4 (![0,2,1,1] : Fin 4 → ℝ) tableY = 20/27 ∧
    Real.sqrt 6 / 3 < (5/6 : ℝ) ∧ (20/27 : ℝ) < 8/9 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hp : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hd : Real.sqrt (27/2) = (3/2)*Real.sqrt 6 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, by nlinarith, by norm_num⟩
  all_goals norm_num [spearman, printedRho, rankCov, rankCross, rankSquares,
    centeredRanks, averageRank, table_y_vector, Fin.sum_univ_succ,
    Fin.card_filter_univ_succ, hd]
  field_simp
  nlinarith

/-- P030-T8(c)/T9(vi): D=(1,2,3), Y=(0,0,1) is weakly monotone and
nonconstant, but its defined Spearman correlation √3/2 is neither 1 nor -1.
This refutes the p. 8 sentence when "monotone" means weakly monotone. -/
theorem weak_monotonicity_counterexample :
    (∀ i j : Fin 3, (![1,2,3] : Fin 3 → ℝ) i ≤ (![1,2,3] : Fin 3 → ℝ) j →
      (![0,0,1] : Fin 3 → ℝ) i ≤ (![0,0,1] : Fin 3 → ℝ) j) ∧
    rankSquares (![1,2,3] : Fin 3 → ℝ) = 2 ∧
    rankSquares (![0,0,1] : Fin 3 → ℝ) = 3/2 ∧
    spearman (![1,2,3] : Fin 3 → ℝ) ![0,0,1] = Real.sqrt 3 / 2 ∧
    Real.sqrt 3 / 2 ≠ 1 ∧ Real.sqrt 3 / 2 ≠ -1 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num
  · norm_num [rankSquares, centeredRanks, averageRank, Fin.sum_univ_succ, Fin.card_filter_univ_succ]
  · norm_num [rankSquares, centeredRanks, averageRank, Fin.sum_univ_succ, Fin.card_filter_univ_succ]
  · norm_num [spearman, rankCross, rankSquares, centeredRanks, averageRank,
      Fin.sum_univ_succ, Fin.card_filter_univ_succ]
    field_simp
    nlinarith
  · intro h; have : Real.sqrt 3 = 2 := by linarith
    rw [this] at hs; norm_num at hs
  · intro h; linarith

/-- Nonconstant raw vectors, the domain of the paper's rank correlation (p. 8). -/
def Nonconstant {n : ℕ} (a : Fin n → ℝ) : Prop := ∃ i j, a i ≠ a j

/-- Pairwise contributions to average ranks, including half weight for ties
(p. 8 definition, used to prove the general corrected correlation statements). -/
def rankWeight {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (if a j < a i then 1 else 0) + (if a j = a i then 1/2 else 0)

/-- Average-rank definition as a finite sum of pairwise weights (p. 8). -/
theorem average_rank_weight {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    averageRank a i = 1/2 + ∑ j, rankWeight a i j := by
  classical
  simp [rankWeight, Finset.sum_add_distrib, ← Finset.sum_filter, averageRank]
  ring

/-- Opposite pairwise rank contributions sum to one, including ties (p. 8). -/
theorem rank_weight_pair {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) :
    rankWeight a i j + rankWeight a j i = 1 := by
  rcases lt_trichotomy (a i) (a j) with h | h | h
  · simp [rankWeight, h, not_lt.mpr h.le, ne_of_lt h, ne_of_gt h]
  · simp [rankWeight, h]; norm_num
  · simp [rankWeight, h, not_lt.mpr h.le, ne_of_lt h, ne_of_gt h]

/-- Average ranks have mean (n+1)/2 even with ties (T9 standing definition, p. 8). -/
theorem average_rank_sum {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, averageRank a i) = (n : ℝ)*((n : ℝ)+1)/2 := by
  have hp : (∑ i, ∑ j, rankWeight a i j) + (∑ i, ∑ j, rankWeight a i j) = (n : ℝ)^2 := by
    calc
      _ = ∑ i, ∑ j, (rankWeight a i j + rankWeight a j i) := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j => rankWeight a j i)]
      _ = (n : ℝ)^2 := by simp [rank_weight_pair]; ring
  simp_rw [average_rank_weight]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith

/-- A strict raw-data inequality induces a strict average-rank inequality, p. 8. -/
theorem average_rank_strict {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) (h : a i < a j) :
    averageRank a i < averageRank a j := by
  classical
  have hm : ∀ k : Fin n, rankWeight a i k ≤ rankWeight a j k := by
    intro k
    rcases lt_trichotomy (a k) (a i) with hk | hk | hk
    · simp [rankWeight, hk, hk.trans h, ne_of_lt hk, ne_of_lt (hk.trans h)]
    · simp [rankWeight, hk, h, ne_of_lt h]; norm_num
    · have hn : ¬ a k < a i := not_lt.mpr hk.le
      have he : a k ≠ a i := ne_of_gt hk
      simp [rankWeight, hn, he]
      split_ifs <;> norm_num
  rw [average_rank_weight, average_rank_weight]
  apply add_lt_add_right
  apply Finset.sum_lt_sum (fun k _ => hm k)
  exact ⟨i, Finset.mem_univ _, by norm_num [rankWeight, h, ne_of_lt h]⟩

/-- Nonconstant raw data have a positive sum of squared centred average ranks,
so the corrected statistic is defined (P030-T9, p. 8). -/
theorem nonconstant_rank_variance {n : ℕ} (a : Fin n → ℝ) (ha : Nonconstant a) :
    0 < rankSquares a := by
  have hn : 0 ≤ rankSquares a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_contra hp
  have hz : rankSquares a = 0 := by linarith
  have hv : ∀ i, centeredRanks a i = 0 := by
    intro i
    exact (Finset.sum_sq_eq_zero_iff Finset.univ (centeredRanks a)).mp hz i (Finset.mem_univ _)
  obtain ⟨i, j, hij⟩ := ha
  rcases lt_or_gt_of_ne hij with h | h
  · have hs := average_rank_strict a i j h
    have hvi := hv i; have hvj := hv j
    unfold centeredRanks at hvi hvj
    linarith
  · have hs := average_rank_strict a j i h
    have hvi := hv i; have hvj := hv j
    unfold centeredRanks at hvi hvj
    linarith

/-- Cauchy-Schwarz gives [-1,1] for the corrected rank correlation, T9(ii), p. 8. -/
theorem spearman_bounds {n : ℕ} (a b : Fin n → ℝ)
    (ha : 0 < rankSquares a) (hb : 0 < rankSquares b) :
    -1 ≤ spearman a b ∧ spearman a b ≤ 1 := by
  have hcs : rankCross a b ^ 2 ≤ rankSquares a * rankSquares b :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (centeredRanks a) (centeredRanks b)
  have hp : 0 < Real.sqrt (rankSquares a * rankSquares b) := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hab : |spearman a b| ≤ 1 := by
    rw [spearman, abs_div, abs_of_pos hp]
    exact (div_le_one hp).mpr (Real.abs_le_sqrt hcs)
  exact abs_le.mp hab

/-- The common moment divisor cancels with the corrected square root, T9(i).
This holds for every positive divisor, including n and n-1 (p. 8). -/
theorem spearman_divisor {n : ℕ} (a b : Fin n → ℝ)
    (ha : 0 < rankSquares a) (hb : 0 < rankSquares b) (m : ℝ) (hm : 0 < m) :
    spearman a b = rankCov m a b / Real.sqrt ((rankSquares a/m)*(rankSquares b/m)) := by
  have hs : Real.sqrt ((rankSquares a/m)*(rankSquares b/m)) =
      Real.sqrt (rankSquares a*rankSquares b)/m := by
    rw [div_mul_div_comm, ← pow_two, Real.sqrt_div (mul_pos ha hb).le,
      Real.sqrt_sq hm.le]
  rw [hs]
  unfold spearman rankCov
  field_simp

/-- Expansion of the squared residual used for the equality case of Cauchy-
Schwarz in T9(iii), p. 8 corrected correlation. -/
theorem rank_residual_squares {n : ℕ} (a b : Fin n → ℝ) (c : ℝ) :
    (∑ k, (centeredRanks a k-c*centeredRanks b k)^2) =
      rankSquares a-2*c*rankCross a b+c^2*rankSquares b := by
  calc
    _ = ∑ k, (centeredRanks a k^2 - (2*c)*(centeredRanks a k*centeredRanks b k) +
        c^2*centeredRanks b k^2) := by apply Finset.sum_congr rfl; intros; ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl

/-- T9(iii): perfect absolute correlation forces proportional centred ranks. -/
theorem spearman_perfect_implies_proportional {n : ℕ} (a b : Fin n → ℝ)
    (ha : 0 < rankSquares a) (hb : 0 < rankSquares b) (h : |spearman a b| = 1) :
    ∃ c : ℝ, c ≠ 0 ∧ centeredRanks a = fun k => c*centeredRanks b k := by
  have hsq : (spearman a b)^2 = 1 := by
    have hh := congrArg (fun x : ℝ => x^2) h
    rw [sq_abs] at hh
    simpa only [one_pow] using hh
  unfold spearman at hsq
  rw [div_pow, Real.sq_sqrt (mul_pos ha hb).le] at hsq
  have he : (rankCross a b)^2 = rankSquares a*rankSquares b :=
    (div_eq_one_iff_eq (mul_pos ha hb).ne').mp hsq
  have hc : rankCross a b ≠ 0 := by intro hz; rw [hz] at he; nlinarith [mul_pos ha hb]
  let c := rankCross a b / rankSquares b
  have hz : (∑ k, (centeredRanks a k-c*centeredRanks b k)^2) = 0 := by
    rw [rank_residual_squares]
    dsimp [c]
    field_simp
    nlinarith
  refine ⟨c, div_ne_zero hc hb.ne', ?_⟩
  funext k
  have hk := (Finset.sum_sq_eq_zero_iff Finset.univ
    (fun k => centeredRanks a k-c*centeredRanks b k)).mp hz k (Finset.mem_univ _)
  linarith

/-- T9(iii): proportional centred ranks give absolute correlation one, and
the correlation sign agrees with the nonzero proportionality constant. -/
theorem spearman_proportional {n : ℕ} (a b : Fin n → ℝ)
    (hb : 0 < rankSquares b) (c : ℝ) (hc : c ≠ 0)
    (h : centeredRanks a = fun k => c*centeredRanks b k) :
    |spearman a b| = 1 ∧ (0 < c → spearman a b = 1) ∧ (c < 0 → spearman a b = -1) := by
  have hC : rankCross a b = c*rankSquares b := by
    unfold rankCross rankSquares
    simp_rw [congrFun h]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros; ring
  have hA : rankSquares a = c^2*rankSquares b := by
    unfold rankSquares
    simp_rw [congrFun h, mul_pow]
    rw [Finset.mul_sum]
  have hD : Real.sqrt (rankSquares a*rankSquares b) = |c| * rankSquares b := by
    apply (Real.sqrt_eq_iff_eq_sq (by rw [hA]; positivity) (by positivity)).mpr
    rw [hA, mul_pow, sq_abs]
    ring
  have he : spearman a b = c/|c| := by
    rw [spearman, hC, hD]
    field_simp
  rw [he]
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_div, abs_abs, div_self (abs_ne_zero.mpr hc)]
  · intro hp; rw [abs_of_pos hp, div_self hc]
  · intro hn; rw [abs_of_neg hn]; field_simp

/-- Strict increasing order equivalence preserves ties and average ranks (T9(iv)). -/
theorem rank_order_preserving {n : ℕ} (a b : Fin n → ℝ)
    (h : ∀ k l, a k < a l ↔ b k < b l) : averageRank a = averageRank b := by
  classical
  have he : ∀ k l, a k = a l ↔ b k = b l := by
    intro k l
    constructor <;> intro he
    · apply le_antisymm <;> apply not_lt.mp <;> intro hh
      · have := (h l k).mpr hh; linarith
      · have := (h k l).mpr hh; linarith
    · apply le_antisymm <;> apply not_lt.mp <;> intro hh
      · have := (h l k).mp hh; linarith
      · have := (h k l).mp hh; linarith
  funext k
  have hl : Finset.univ.filter (fun j => a j < a k) = Finset.univ.filter (fun j => b j < b k) := by
    ext j; simp [h]
  have heq : Finset.univ.filter (fun j => a j = a k) = Finset.univ.filter (fun j => b j = b k) := by
    ext j; simp [he]
  simp only [averageRank, hl, heq]

/-- Strict decreasing order equivalence reverses tied average ranks (T9(v)). -/
theorem rank_order_reversing {n : ℕ} (a b : Fin n → ℝ)
    (h : ∀ k l, a k < a l ↔ b l < b k) :
    ∀ k, averageRank a k = (n : ℝ)+1-averageRank b k := by
  classical
  intro k
  have hw : ∀ j, rankWeight a k j + rankWeight b k j = 1 := by
    intro j
    rcases lt_trichotomy (a j) (a k) with hj | hj | hj
    · have hb := (h j k).mp hj
      simp [rankWeight, hj, not_lt.mpr hb.le, ne_of_lt hj, ne_of_gt hb]
    · have he : b j = b k := by
        apply le_antisymm <;> apply not_lt.mp <;> intro hh
        · have := (h j k).mpr hh; linarith
        · have := (h k j).mpr hh; linarith
      simp [rankWeight, hj, he]; norm_num
    · have hb := (h k j).mp hj
      simp [rankWeight, hb, not_lt.mpr hj.le, ne_of_gt hj, ne_of_lt hb]
  have hs : averageRank a k + averageRank b k = (n : ℝ)+1 := by
    rw [average_rank_weight, average_rank_weight]
    have hp : (∑ j, rankWeight a k j) + (∑ j, rankWeight b k j) = (n : ℝ) := by
      rw [← Finset.sum_add_distrib]
      simp [hw]
    linarith
  linarith

/-- Full generic correction P030-T9(i)-(v), p. 8: the rank means, positive
variances, divisor invariance, bounds, exact proportionality characterization,
and strictly increasing/decreasing tie-preserving cases. The concrete checks
in (vi)-(vii) are weak_monotonicity_counterexample and worked_table_result. -/
theorem corrected_spearman {n : ℕ} (_hn : 2 ≤ n) (a b : Fin n → ℝ)
    (ha : Nonconstant a) (hb : Nonconstant b) :
    (∑ k, averageRank a k) = (n : ℝ) * ((n : ℝ)+1)/2 ∧
    (∑ k, averageRank b k) = (n : ℝ) * ((n : ℝ)+1)/2 ∧
    0 < rankSquares a ∧ 0 < rankSquares b ∧
    (∀ m : ℝ, 0 < m → spearman a b =
      rankCov m a b / Real.sqrt ((rankSquares a / m)*(rankSquares b / m))) ∧
    (-1 ≤ spearman a b ∧ spearman a b ≤ 1) ∧
    (|spearman a b| = 1 ↔ ∃ c : ℝ, c ≠ 0 ∧ centeredRanks a = fun k => c * centeredRanks b k) ∧
    (∀ c : ℝ, c ≠ 0 → centeredRanks a = (fun k => c * centeredRanks b k) →
      (0 < c → spearman a b = 1) ∧ (c < 0 → spearman a b = -1)) ∧
    ((∀ k l, a k < a l ↔ b k < b l) → averageRank a = averageRank b ∧ spearman a b = 1) ∧
    ((∀ k l, a k < a l ↔ b l < b k) →
      (∀ k, averageRank a k = (n : ℝ)+1-averageRank b k) ∧ spearman a b = -1) := by
  have hA := nonconstant_rank_variance a ha
  have hB := nonconstant_rank_variance b hb
  refine ⟨average_rank_sum a, average_rank_sum b, hA, hB, spearman_divisor a b hA hB,
    spearman_bounds a b hA hB, ?_, ?_, ?_, ?_⟩
  · constructor
    · exact spearman_perfect_implies_proportional a b hA hB
    · rintro ⟨c, hc, he⟩; exact (spearman_proportional a b hB c hc he).1
  · intro c hc he; exact (spearman_proportional a b hB c hc he).2
  · intro h
    have hr := rank_order_preserving a b h
    have hc : centeredRanks a = fun k => (1:ℝ)*centeredRanks b k := by
      funext k; simp [centeredRanks, hr]
    exact ⟨hr, (spearman_proportional a b hB 1 (by norm_num) hc).2.1 (by norm_num)⟩
  · intro h
    have hr := rank_order_reversing a b h
    have hc : centeredRanks a = fun k => (-1:ℝ)*centeredRanks b k := by
      funext k; unfold centeredRanks; rw [hr k]; ring
    exact ⟨hr, (spearman_proportional a b hB (-1) (by norm_num) hc).2.2 (by norm_num)⟩

/-- Ordinary real division has a value only for a nonzero denominator.
This partial-quotient convention represents the undefined self summand in
P030-T10(i), p. 10, without using Mathlib's totalized division at zero. -/
def partialRealQuotient (a b : ℝ) : Option ℝ := by
  classical
  exact if b = 0 then none else some (a / b)

/-- P030-T10(i), p. 10: at j=i, δ_ii=1 and d_ii=0 make both numerator
and denominator zero, so the ordinary real quotient has no value. -/
theorem inverse_square_self_term_undefined {N : ℕ} (d : Fin N → Fin N → ℝ)
    (z : Assignment N) (i : Fin N) (hself : d i i = 0) :
    (1 - (if i = i then (1 : ℝ) else 0)) * treatment z i = 0 ∧
    ((3/2 : ℝ) * d i i)^2 = 0 ∧
    partialRealQuotient ((1 - (if i = i then (1 : ℝ) else 0)) * treatment z i)
      (((3/2 : ℝ) * d i i)^2) = none := by
  simp [hself, partialRealQuotient]

/-- Corrected inverse-square kernel, Θ and Ψ on p. 10 (P030-T10).
The printed self summand is undefined, as inverse_square_self_term_undefined
states using ordinary partial division; the corrected sums exclude self. -/
def inverseSquare (d : ℝ) : ℝ := 1 / (((3/2 : ℝ)*d)^2)

/-- P030-T10(i): positive off-diagonal distances give nonzero denominators in
every corrected summand; a metric on distinct positions has this property. -/
theorem inverse_square_sums_defined {N : ℕ} (d : Fin N → Fin N → ℝ)
    (hd : ∀ i j, i ≠ j → 0 < d i j) :
    ∀ i j, j ∈ Finset.univ.erase i → ((3/2 : ℝ)*d i j)^2 ≠ 0 := by
  intro i j hj
  have hji := (Finset.mem_erase.mp hj).1
  have hpos := hd i j (Ne.symm hji)
  positivity

/-- P030-T10(ii): inverse-square algebra and exact doubling ratio, p. 10 kernel. -/
theorem inverse_square_decay (d : ℝ) (hd : 0 < d) :
    inverseSquare d = 4/(9*d^2) ∧ inverseSquare (2*d) / inverseSquare d = 1/4 ∧
    inverseSquare (2/3) = 1 ∧ inverseSquare 1 = 4/9 ∧ inverseSquare 2 = 1/9 := by
  have hn : d ≠ 0 := hd.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> unfold inverseSquare
  · field_simp; ring
  · field_simp; ring
  all_goals norm_num

/-- P030-T10(iii): the kernel cannot be A exp(-c d) for all positive distances. -/
theorem inverse_square_not_exponential :
    ¬ ∃ A c : ℝ, ∀ d : ℝ, 0 < d → inverseSquare d = A * Real.exp (-c*d) := by
  rintro ⟨A, c, h⟩
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have e2 : Real.exp (-c*2) = Real.exp (-c)^2 := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-c*3) = Real.exp (-c)^3 := by
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [e2] at h2
  rw [e3] at h3
  norm_num [inverseSquare] at h1 h2 h3
  have hp : (A * Real.exp (-c)^2)^2 = (A * Real.exp (-c)) * (A * Real.exp (-c)^3) := by ring
  rw [← h1, ← h2, ← h3] at hp
  norm_num at hp

/-- P030-T10(iv): the explicit right-neighborhood bound proves divergence of
the corrected inverse-square kernel as distance tends to zero. -/
theorem inverse_square_unbounded (B d : ℝ) (hB : 0 < B) (hd : 0 < d)
    (hsmall : d < 2/(3*Real.sqrt B)) : B < inverseSquare d := by
  have hs := Real.sq_sqrt hB.le
  have hp : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hm : d*(3*Real.sqrt B) < 2 := (lt_div_iff₀ (by positivity)).mp hsmall
  have hsq : (d*(3*Real.sqrt B))^2 < 4 := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ d*(3*Real.sqrt B)) (by linarith : 0 ≤ 2-d*(3*Real.sqrt B))]
  rw [(inverse_square_decay d hd).1]
  apply (lt_div_iff₀ (by positivity)).mpr
  nlinarith

/-- P030-T10(iv): in contrast, every exponential A exp(-c d) tends to the finite
value A as d→0+, so its behavior is not the printed inverse-square divergence. -/
theorem exponential_finite_at_zero (A c : ℝ) :
    Filter.Tendsto (fun d : ℝ => A*Real.exp (-c*d)) (nhdsWithin 0 (Set.Ioi 0)) (nhds A) := by
  have hc : Continuous (fun d : ℝ => A*Real.exp (-c*d)) := by fun_prop
  have hc0 : ContinuousAt (fun d : ℝ => A*Real.exp (-c*d)) 0 := hc.continuousAt
  simpa using hc0.tendsto.mono_left nhdsWithin_le_nhds

/-- T11(a): the fixed, control and neighbors groups partition the voter sample
(pp. 12-13), so their three cardinalities must add to N. -/
theorem sample_partition_count {A : Type*} [DecidableEq A] (U F C T : Finset A)
    (hU : U = (F ∪ C) ∪ T) (hFC : Disjoint F C) (hFT : Disjoint F T) (hCT : Disjoint C T) :
    U.card = F.card + C.card + T.card := by
  rw [hU, Finset.card_union_of_disjoint (by simpa using And.intro hFT hCT),
    Finset.card_union_of_disjoint hFC]

/-- T11(b): the four printed counts cannot describe any such finite partition,
because the group total is 344055, one below printed N=344056 (p. 13). -/
theorem printed_sample_counts_inconsistent {A : Type*} [DecidableEq A] (U F C T : Finset A)
    (hU : U = (F ∪ C) ∪ T) (hFC : Disjoint F C) (hFT : Disjoint F T) (hCT : Disjoint C T) :
    ¬ (U.card = 344056 ∧ F.card = 114629 ∧ C.card = 191228 ∧ T.card = 38198) := by
  intro h
  have he := sample_partition_count U F C T hU hFC hFT hCT
  omega

/-- T11(c)-(d): all and only one-entry reconciliations of the printed count
quadruple. This does not identify which actual count was misreported (p. 13). -/
theorem sample_count_reconciliations (N F C T : ℕ) :
    (N = F+C+T ∧
      ((N ≠ 344056 ∧ F = 114629 ∧ C = 191228 ∧ T = 38198) ∨
       (N = 344056 ∧ F ≠ 114629 ∧ C = 191228 ∧ T = 38198) ∨
       (N = 344056 ∧ F = 114629 ∧ C ≠ 191228 ∧ T = 38198) ∨
       (N = 344056 ∧ F = 114629 ∧ C = 191228 ∧ T ≠ 38198))) ↔
      (N = 344055 ∧ F = 114629 ∧ C = 191228 ∧ T = 38198) ∨
      (N = 344056 ∧ F = 114630 ∧ C = 191228 ∧ T = 38198) ∨
      (N = 344056 ∧ F = 114629 ∧ C = 191229 ∧ T = 38198) ∨
      (N = 344056 ∧ F = 114629 ∧ C = 191228 ∧ T = 38199) := by omega

/-- T11's exact sum, discrepancy and conditional fixed-count repair, p. 13. -/
theorem sample_count_arithmetic :
    114629 + 191228 + 38198 = (344055 : ℕ) ∧ (344055 : ℕ) ≠ 344056 ∧
    (344056 : ℕ) - 191228 - 38198 = 114630 := by norm_num

/-- Complete randomization of exactly M of N units, p. 5. -/
def completeAssignments (N M : ℕ) : Finset (Assignment N) := by
  classical
  exact Finset.univ.filter (fun z => (Finset.univ.filter (fun i => z i = true)).card = M)
/-- "P, the number of proximal treated units (i.e., within a given radius r)" (p. 5). Neighbor sets exclude
the unit itself; an arbitrary metric and radius enter only through this fixed set. -/
def proximalExposure {N : ℕ} (neighbors : Finset (Fin N)) (z : Assignment N) : ℝ :=
  ∑ j ∈ neighbors, treatment z j
/-- Design-based expectation as a uniform finite sum (p. 5). -/
def uniformMean {A : Type*} (Ω : Finset A) (X : A → ℝ) : ℝ := (∑ z ∈ Ω, X z) / (Ω.card : ℝ)

/-- The exact finite linearity lemma behind the three p. 5 exposure formulas. -/
theorem exposure_mean_linearity {N : ℕ} (Ω : AssignmentSet N)
    (neighbors : Finset (Fin N)) :
    uniformMean Ω (proximalExposure neighbors) = ∑ j ∈ neighbors, uniformMean Ω (fun z => treatment z j) := by
  unfold uniformMean proximalExposure
  rw [Finset.sum_comm, Finset.sum_div]

/-- If the design's neighbor treatment marginals equal p, linearity gives K_i p.
This finite lemma is separate from the full complete-randomization result T13. -/
theorem exposure_mean_from_marginals {N : ℕ} (Ω : AssignmentSet N)
    (neighbors : Finset (Fin N)) (p : ℝ)
    (h : ∀ j ∈ neighbors, uniformMean Ω (fun z => treatment z j) = p) :
    uniformMean Ω (proximalExposure neighbors) = (neighbors.card : ℝ)*p := by
  rw [exposure_mean_linearity]
  simp only [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

/-- Relabeling two units in a complete randomization (p. 5). -/
def swapUnits {N : ℕ} (i j : Fin N) (z : Assignment N) : Assignment N :=
  fun k => z (Equiv.swap i j k)

/-- Unit relabeling is an involution, used for finite-design symmetry (p. 5). -/
theorem swap_units_involution {N : ℕ} (i j : Fin N) : Function.Involutive (swapUnits i j) := by
  intro z; funext k; simp [swapUnits]

/-- Total number treated is the sum of the binary numerical indicators (p. 5). -/
theorem treatment_total {N : ℕ} (z : Assignment N) :
    (∑ i, treatment z i) = ((Finset.univ.filter (fun i => z i = true)).card : ℝ) := by
  classical
  simp [treatment]

/-- Swapping unit labels preserves the complete randomization support (p. 5). -/
theorem complete_swap_mem (N M : ℕ) (i j : Fin N) (z : Assignment N)
    (hz : z ∈ completeAssignments N M) : swapUnits i j z ∈ completeAssignments N M := by
  classical
  have hsum : (∑ k, treatment (swapUnits i j z) k) = ∑ k, treatment z k := by
    exact Fintype.sum_equiv (Equiv.swap i j) (fun k => treatment (swapUnits i j z) k)
      (treatment z) (by intro k; rfl)
  have hc := (Finset.mem_filter.mp hz).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hcc : ((Finset.univ.filter (fun k => swapUnits i j z k = true)).card : ℝ) = M := by
    rw [← treatment_total, hsum, treatment_total, hc]
  exact_mod_cast hcc

/-- The complete design is nonempty whenever 0≤M≤N, including endpoint designs (p. 5). -/
theorem complete_nonempty (N M : ℕ) (hM : M ≤ N) : (completeAssignments N M).Nonempty := by
  classical
  refine ⟨fun i => decide (i.val < M), ?_⟩
  simp [completeAssignments, Fin.card_filter_val_lt, min_eq_right hM]

/-- Uniform expectation is unchanged by a support-preserving involution (p. 5). -/
theorem uniform_mean_involution {A : Type*} (Ω : Finset A) (e : A → A)
    (hi : Function.Involutive e) (he : ∀ z ∈ Ω, e z ∈ Ω) (X : A → ℝ) :
    uniformMean Ω (fun z => X (e z)) = uniformMean Ω X := by
  unfold uniformMean
  congr 1
  exact Finset.sum_nbij' e e he he (fun z _ => hi z) (fun z _ => hi z) (by intros; rfl)

/-- Finite symmetry lemma: if R unit labels are exchangeable and the design
always treats q of them, each has treatment expectation q/|R| (p. 5). -/
theorem symmetric_treatment_mean {N : ℕ} (Ω : AssignmentSet N) (hΩ : Ω.Nonempty)
    (R : Finset (Fin N)) (j : Fin N) (hj : j ∈ R) (q : ℝ)
    (hcount : ∀ z ∈ Ω, proximalExposure R z = q)
    (hswap : ∀ a ∈ R, ∀ b ∈ R, ∀ z ∈ Ω, swapUnits a b z ∈ Ω) :
    uniformMean Ω (fun z => treatment z j) = q/(R.card : ℝ) := by
  have hsame : ∀ k ∈ R, uniformMean Ω (fun z => treatment z k) =
      uniformMean Ω (fun z => treatment z j) := by
    intro k hk
    have h := uniform_mean_involution Ω (swapUnits k j) (swap_units_involution k j)
      (hswap k hk j hj) (fun z => treatment z j)
    simpa [swapUnits, treatment] using h
  have hR : (R.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr ⟨j, hj⟩
  have hΩn : (Ω.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hΩ
  have htotal : uniformMean Ω (proximalExposure R) = q := by
    unfold uniformMean
    rw [Finset.sum_congr rfl hcount]
    simp [hΩn]
  have he := exposure_mean_from_marginals Ω R (uniformMean Ω (fun z => treatment z j)) hsame
  rw [htotal] at he
  apply (eq_div_iff hR).mpr
  nlinarith

/-- Unconditional neighbor treatment expectation M/N under complete randomization,
the exact finite marginal behind P030-T13(a), p. 5. -/
theorem complete_treatment_mean (N M : ℕ) (hM : M ≤ N) (j : Fin N) :
    uniformMean (completeAssignments N M) (fun z => treatment z j) = (M : ℝ)/(N : ℝ) := by
  have hc : ∀ z ∈ completeAssignments N M, proximalExposure Finset.univ z = (M : ℝ) := by
    intro z hz
    unfold proximalExposure
    rw [treatment_total, (Finset.mem_filter.mp hz).2]
  simpa only [Finset.card_univ, Fintype.card_fin] using symmetric_treatment_mean _
    (complete_nonempty N M hM) Finset.univ j (Finset.mem_univ j) (M : ℝ) hc
    (fun a _ b _ z hz => complete_swap_mem N M a b z hz)

/-- The conditioning event Z_i=b has positive probability exactly in the ranges
used in P030-T13(b)-(c); here nonemptiness is proved with explicit swapped assignments. -/
theorem conditioned_complete_nonempty (N M : ℕ) (hN : 2 ≤ N) (hM : M ≤ N)
    (i : Fin N) (b : Bool) (htrue : b = true → 1 ≤ M) (hfalse : b = false → M ≤ N-1) :
    ((completeAssignments N M).filter (fun z => z i = b)).Nonempty := by
  classical
  let z : Assignment N := fun k => decide (k.val < M)
  have hz : z ∈ completeAssignments N M := by
    simp [z, completeAssignments, Fin.card_filter_val_lt, min_eq_right hM]
  cases b
  · let k : Fin N := ⟨N-1, by omega⟩
    refine ⟨swapUnits k i z, Finset.mem_filter.mpr ⟨complete_swap_mem N M k i z hz, ?_⟩⟩
    simp [swapUnits, z, k]
    have hm := hfalse rfl
    omega
  · let k : Fin N := ⟨0, by omega⟩
    refine ⟨swapUnits k i z, Finset.mem_filter.mpr ⟨complete_swap_mem N M k i z hz, ?_⟩⟩
    simp [swapUnits, z, k]
    have hm := htrue rfl
    omega

/-- Conditional neighbor treatment marginal (M-b)/(N-1), proved from exact
remaining treatment totals and symmetry, P030-T13(b)-(c), p. 5. -/
theorem conditioned_treatment_mean (N M : ℕ) (hN : 2 ≤ N) (hM : M ≤ N)
    (i j : Fin N) (hji : j ≠ i) (b : Bool)
    (htrue : b = true → 1 ≤ M) (hfalse : b = false → M ≤ N-1) :
    uniformMean ((completeAssignments N M).filter (fun z => z i = b))
      (fun z => treatment z j) = ((M : ℝ)-(if b then 1 else 0))/((N : ℝ)-1) := by
  classical
  have he := symmetric_treatment_mean
    ((completeAssignments N M).filter (fun z => z i = b))
    (conditioned_complete_nonempty N M hN hM i b htrue hfalse)
    (Finset.univ.erase i) j (by simp [hji]) ((M : ℝ)-(if b then 1 else 0))
  have hcount : ∀ z ∈ (completeAssignments N M).filter (fun z => z i = b),
      proximalExposure (Finset.univ.erase i) z = (M : ℝ)-(if b then 1 else 0) := by
    intro z hz
    obtain ⟨hz, hzi⟩ := Finset.mem_filter.mp hz
    have htotal : (∑ k, treatment z k) = (M : ℝ) := by
      rw [treatment_total, (Finset.mem_filter.mp hz).2]
    have hsum := Finset.sum_erase_add Finset.univ (treatment z) (Finset.mem_univ i)
    rw [htotal] at hsum
    have hown : treatment z i = (if b then 1 else 0) := by simp [treatment, hzi]
    rw [hown] at hsum
    unfold proximalExposure
    linarith
  have hswap : ∀ a ∈ Finset.univ.erase i, ∀ c ∈ Finset.univ.erase i,
      ∀ z ∈ (completeAssignments N M).filter (fun z => z i = b),
        swapUnits a c z ∈ (completeAssignments N M).filter (fun z => z i = b) := by
    intro a ha c hc z hz
    obtain ⟨hz, hzi⟩ := Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨complete_swap_mem N M a c z hz, ?_⟩
    have hia : i ≠ a := Ne.symm (Finset.mem_erase.mp ha).1
    have hic : i ≠ c := Ne.symm (Finset.mem_erase.mp hc).1
    simpa [swapUnits, Equiv.swap_apply_of_ne_of_ne hia hic] using hzi
  have hcard : ((Finset.univ.erase i).card : ℝ) = (N : ℝ)-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega)]
    simp
  simpa only [hcard] using he hcount hswap

/-- Full P030-T13(a)-(f), p. 5: complete-randomization unconditional and own-
treatment-conditional expectations, strict qualitative consequences and total
expectation. Conditional expectations occur only at positive-probability levels. -/
theorem proximal_exposure_expectations (N M : ℕ) (hN : 2 ≤ N) (hM : M ≤ N)
    (i : Fin N) (neighbors : Finset (Fin N)) (hself : i ∉ neighbors) :
    let Ω := completeAssignments N M
    let Ω1 := Ω.filter (fun z => z i = true)
    let Ω0 := Ω.filter (fun z => z i = false)
    let E := uniformMean Ω (proximalExposure neighbors)
    let E1 := uniformMean Ω1 (proximalExposure neighbors)
    let E0 := uniformMean Ω0 (proximalExposure neighbors)
    E = (neighbors.card : ℝ)*(M : ℝ)/(N : ℝ) ∧
    (1 ≤ M → E1 = (neighbors.card : ℝ)*((M : ℝ)-1)/((N : ℝ)-1)) ∧
    (M ≤ N-1 → E0 = (neighbors.card : ℝ)*(M : ℝ)/((N : ℝ)-1)) ∧
    (∀ j : Fin N, ∀ neighbors' : Finset (Fin N), j ∉ neighbors' → 1 ≤ M →
      neighbors.card < neighbors'.card →
        E < uniformMean Ω (proximalExposure neighbors')) ∧
    (1 ≤ M → M ≤ N-1 → 1 ≤ neighbors.card → E1 < E ∧ E < E0) ∧
    (1 ≤ M → M ≤ N-1 → (M : ℝ)/(N : ℝ)*E1 + ((N : ℝ)-(M : ℝ))/(N : ℝ)*E0 = E) := by
  classical
  dsimp only
  have hE : uniformMean (completeAssignments N M) (proximalExposure neighbors) =
      (neighbors.card : ℝ)*(M : ℝ)/(N : ℝ) := by
    rw [exposure_mean_from_marginals _ _ _ (fun j _ => complete_treatment_mean N M hM j)]
    ring
  have hE1 : 1 ≤ M → uniformMean ((completeAssignments N M).filter (fun z => z i = true))
      (proximalExposure neighbors) = (neighbors.card : ℝ)*((M : ℝ)-1)/((N : ℝ)-1) := by
    intro hm
    rw [exposure_mean_from_marginals _ _ _ (fun j hj =>
      conditioned_treatment_mean N M hN hM i j (by intro he; subst j; exact hself hj) true
        (by intros; exact hm) (by simp))]
    simp; ring
  have hE0 : M ≤ N-1 → uniformMean ((completeAssignments N M).filter (fun z => z i = false))
      (proximalExposure neighbors) = (neighbors.card : ℝ)*(M : ℝ)/((N : ℝ)-1) := by
    intro hm
    rw [exposure_mean_from_marginals _ _ _ (fun j hj =>
      conditioned_treatment_mean N M hN hM i j (by intro he; subst j; exact hself hj) false
        (by simp) (by intros; exact hm))]
    simp; ring
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  have hNm1 : 0 < (N : ℝ)-1 := by linarith
  refine ⟨hE, hE1, hE0, ?_, ?_, ?_⟩
  · intro j neighbors' hj hm hK
    have hE' := exposure_mean_from_marginals (completeAssignments N M) neighbors'
      ((M : ℝ)/(N : ℝ)) (fun k _ => complete_treatment_mean N M hM k)
    rw [hE, hE']
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hm
    have hKr : (neighbors.card : ℝ) < neighbors'.card := by exact_mod_cast hK
    have hp := div_pos (by linarith : (0:ℝ) < M) hNp
    simpa only [div_eq_mul_inv, mul_assoc] using mul_lt_mul_of_pos_right hKr hp
  · intro hm hmN hK
    rw [hE1 hm, hE, hE0 hmN]
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hm
    have hMN' : (M : ℝ)+1 ≤ (N : ℝ) := by exact_mod_cast (show M+1 ≤ N by omega)
    have hMN : (M : ℝ) ≤ (N : ℝ)-1 := by linarith
    have hKr : (1 : ℝ) ≤ neighbors.card := by exact_mod_cast hK
    constructor
    · apply (div_lt_div_iff₀ hNm1 hNp).mpr
      nlinarith
    · apply (div_lt_div_iff₀ hNp hNm1).mpr
      nlinarith
  · intro hm hmN
    rw [hE1 hm, hE0 hmN, hE]
    field_simp
    ring

/-- Equation (3)'s objective when f control units are fixed, pp. 8-9.
Integer counts are represented by integers with 0≤f≤C, C,M≥1. -/
def fixedSizeObjective (C M f : ℤ) : ℤ := f*(C-f)*M
/-- Real completion of the square underlying the half-controls recommendation (T15(a)). -/
theorem half_controls_square (C f : ℝ) : f*(C-f) = C^2/4-(f-C/2)^2 := by ring

/-- T15(b)-(c), Equation (3), pp. 8-9: even C=2k has unique integer maximizer k;
odd C=2k+1 has exactly k and k+1. These are C/2, and (C±1)/2 respectively. -/
theorem half_controls_maximizers (C M : ℤ) (hC : 1 ≤ C) (hM : 1 ≤ M) :
    (∀ k : ℤ, C = 2*k → ∀ f : ℤ, 0 ≤ f → f ≤ C →
      ((∀ g : ℤ, 0 ≤ g → g ≤ C → fixedSizeObjective C M g ≤ fixedSizeObjective C M f) ↔ f = k)) ∧
    (∀ k : ℤ, C = 2*k+1 → ∀ f : ℤ, 0 ≤ f → f ≤ C →
      ((∀ g : ℤ, 0 ≤ g → g ≤ C → fixedSizeObjective C M g ≤ fixedSizeObjective C M f) ↔
        f = k ∨ f = k+1)) := by
  have hMp : 0 < M := by omega
  constructor
  · intro k hk f hf hfC
    constructor
    · intro hm
      have h := hm k (by omega) (by omega)
      have h' : k*(C-k) ≤ f*(C-f) := (mul_le_mul_iff_left₀ hMp).mp h
      nlinarith [sq_nonneg (f-k)]
    · intro hef
      subst f
      intro g hg hgC
      apply (mul_le_mul_iff_left₀ hMp).mpr
      nlinarith [sq_nonneg (g-k)]
  · intro k hk f hf hfC
    constructor
    · intro hm
      have h := hm k (by omega) (by omega)
      have h' : k*(C-k) ≤ f*(C-f) := (mul_le_mul_iff_left₀ hMp).mp h
      have hp : (f-k)*(f-(k+1)) ≤ 0 := by nlinarith
      rcases mul_nonpos_iff.mp hp with h | h <;> omega
    · intro hf
      have hprod : ∀ g : ℤ, 0 ≤ (g-k)*(g-(k+1)) := by
        intro g
        by_cases hg : g ≤ k
        · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
        · exact mul_nonneg (by omega) (by omega)
      intro g hg hgC
      apply (mul_le_mul_iff_left₀ hMp).mpr
      rcases hf with rfl | rfl <;> nlinarith [hprod g]

/-- A point in a uniform assignment design has probability 1/|Ω| (p. 7).
The proof does not enumerate the ambient space of all binary assignments. -/
theorem uniform_point_probability {A : Type*} (Ω : Finset A) (z : A) (hz : z ∈ Ω) :
    uniformProbability Ω (fun w => w = z) = 1/(Ω.card : ℝ) := by
  classical
  calc
    _ = (({z} : Finset A).card : ℝ)/(Ω.card : ℝ) := by
      unfold uniformProbability
      congr 2
      apply congrArg Finset.card
      ext w
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact And.right
      · intro h; subst w; exact ⟨hz, rfl⟩
    _ = _ := by simp

/-- Table 1 is a bijective enumeration of Ω', so probabilities computed over
its six rows are the ACTUAL uniform conditional assignment probabilities (p. 9). -/
theorem table_enumeration_probability (P : Assignment 10 → Prop) :
    uniformProbability tableΩ P = uniformProbability Finset.univ
      (fun r : Fin 6 => P (tenAssignment (tableTreatment r))) := by
  classical
  unfold tableΩ
  apply uniformProbability_image
  intro a b h
  have hv := congrFun h (tableTreatment a)
  have he : tableTreatment a = tableTreatment b := by simpa [tenAssignment] using hv
  have hval := congrArg Fin.val he
  apply Fin.ext
  simp [tableTreatment] at hval
  omega

/-- T2/T5/T14: all ten original assignments have probability 1/10 and all six
conditional assignments have probability 1/6 = (1/10)/(6/10), p. 9. -/
theorem ten_assignment_probabilities :
    (∀ j : Fin 10, uniformProbability tenΩ (fun z => z = tenAssignment j) = 1/10) ∧
    (∀ r : Fin 6, uniformProbability tableΩ (fun z => z = tenAssignment (tableTreatment r)) = 1/6) ∧
    (∀ r : Fin 6, uniformProbability tableΩ (fun z => z = tenAssignment (tableTreatment r)) =
      uniformProbability tenΩ (fun z => z = tenAssignment (tableTreatment r)) /
        uniformProbability tenΩ (fun z => ∀ i, tenS i = true → z i = tenAssignment 6 i)) := by
  classical
  have hp10 : ∀ j : Fin 10, uniformProbability tenΩ (fun z => z = tenAssignment j) = 1/10 := by
    intro j
    rw [uniform_point_probability _ _ (by simp [tenΩ]), ten_design.1]
    norm_num
  have hp6 : ∀ r : Fin 6,
      uniformProbability tableΩ (fun z => z = tenAssignment (tableTreatment r)) = 1/6 := by
    intro r
    rw [uniform_point_probability _ _ (by simp [tableΩ]), ten_design.2.1]
    norm_num
  refine ⟨hp10, hp6, ?_⟩
  intro r
  rw [hp6, hp10, ten_design.2.2.2.1]
  norm_num

/-- The paper's Spearman statistic as a function g of fixed outcomes and an
assignment in the ten-unit examples (pp. 7-9). -/
def tenG (y : {i // tenS i = true} → ℝ) (z : Assignment 10) : ℝ :=
  spearman (fun i : Fin 4 => nearestDistance tenX tenS z (tenFixed i))
    (fun i : Fin 4 => y ⟨tenFixed i, by fin_cases i <;> norm_num [tenS, tenFixed]⟩)

/-- Under the constant null schedule of T2/T5, each statistic is the table value. -/
theorem ten_null_statistic_value (r : Fin 6) :
    statistic tenS tenYnull tenG (tenAssignment (tableTreatment r)) = tableRho r := by rfl

/-- Under that same null schedule, observed-data reference values equal the
table statistics under every actual conditional assignment (T2/T5, p. 7). -/
theorem ten_null_reference_value (r s : Fin 6) :
    referenceStatistic tenS tenYnull tenG (tenAssignment (tableTreatment r))
      (tenAssignment (tableTreatment s)) = tableRho s := by rfl

/-- T2's Type I error 1/2 and corrected size 0, written directly over Ω' and
the statistic computed from observed data. This explicitly connects the row
calculations to the actual ten-unit experiment, for every 0<α≤2/3. -/
theorem ten_actual_conditional_size (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 2/3) :
    uniformProbability tableΩ (fun z => printedReject α
      (uniformProbability tableΩ (fun w => referenceStatistic tenS tenYnull tenG z w ≤
        statistic tenS tenYnull tenG z))) = 1/2 ∧
    uniformProbability tableΩ (fun z => correctedReject α
      (uniformProbability tableΩ (fun w => referenceStatistic tenS tenYnull tenG z w ≤
        statistic tenS tenYnull tenG z))
      (uniformProbability tableΩ (fun w => statistic tenS tenYnull tenG z ≤
        referenceStatistic tenS tenYnull tenG z w))) = 0 := by
  simp only [table_enumeration_probability, ten_null_reference_value, ten_null_statistic_value]
  exact table_rejection_probabilities α hα hα2

/-- T14: the actual example's observed fixed outcomes give exactly Table 1
when imputed under the null, even though its actual DGP has interference (pp. 9-10). -/
theorem example_reference_rho (r : Fin 6) :
    referenceStatistic tenS tenYexample tenG (tenAssignment 6)
      (tenAssignment (tableTreatment r)) = tableRho r := by
  change spearman (tableDistances r) (fun i => tenYexample (tenFixed i) (tenAssignment 6)) =
    spearman (tableDistances r) tableY
  rw [example_observed_outcomes.2.2.2, table_y_vector]

/-- T14: the observed statistic is -3/√10 and the OBSERVED-DATA reference
calculation is exactly p=1/3 over the actual Ω' (pp. 9-10). -/
theorem example_observed_statistic_and_p :
    statistic tenS tenYexample tenG (tenAssignment 6) = -3 / Real.sqrt 10 ∧
    uniformProbability tableΩ (fun w => referenceStatistic tenS tenYexample tenG
      (tenAssignment 6) w ≤ statistic tenS tenYexample tenG (tenAssignment 6)) = 1/3 := by
  have ht : statistic tenS tenYexample tenG (tenAssignment 6) = tableRho 5 := example_reference_rho 5
  refine ⟨by rw [ht]; exact worked_table_result.2.2.1, ?_⟩
  rw [table_enumeration_probability, ht]
  simp only [example_reference_rho]
  exact table_tail_probabilities.1 5

/-- T1's rank and centred-product certificates, derived from its data (p. 8
statistic). -/
theorem five_rank_certificate :
    averageRank fiveOutcomes = ![1,2,3] ∧ centeredRanks fiveOutcomes = ![-1,0,1] ∧
    (∀ r : Fin 2, averageRank (fiveDistances r) = ![1,2,3] ∧
      centeredRanks (fiveDistances r) = ![-1,0,1] ∧ rankCross (fiveDistances r) fiveOutcomes = 2) := by
  have hy : fiveOutcomes = ![0,1,2] := by
    funext i; fin_cases i <;> norm_num [fiveOutcomes, fiveY, fiveFixed]
  rw [hy]
  refine ⟨?_, ?_, ?_⟩
  · funext i; fin_cases i <;> norm_num [average_rank_weight, rankWeight, Fin.sum_univ_succ]
  · funext i; fin_cases i <;> norm_num [centeredRanks, average_rank_weight, rankWeight,
      Fin.sum_univ_succ]
  · intro r; fin_cases r <;> refine ⟨?_, ?_, ?_⟩
    all_goals first
      | (funext i; fin_cases i <;> norm_num [centeredRanks, averageRank, five_distances.1,
          five_distances.2, Fin.card_filter_univ_succ])
      | norm_num [rankCross, centeredRanks, averageRank, fiveOutcomes, fiveY, fiveFixed,
          five_distances.1, five_distances.2, Fin.sum_univ_succ, Fin.card_filter_univ_succ]

end
end AronowAudit.P030

