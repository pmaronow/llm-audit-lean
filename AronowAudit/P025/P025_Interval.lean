import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Order.Lattice
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Push
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

/-!
P025, Aronow and Lee (2013), Biometrika 100(1), 235--240.
Indices `i : Fin n` are zero based: `i.val` denotes printed unit `i.val + 1`.
A cut `k : ℕ` still means the number of entries in the first block.
All sums are exact finite sums; weights and outcomes are real numbers.
-/
namespace AronowAudit.P025
noncomputable section
open scoped BigOperators

/-- "The goal is to estimate the population mean, μ = ∑ y_i / N"
(Section 2, p. 235). Also used for the unweighted sample mean. -/
def populationMean {n : ℕ} (y : Fin n → ℝ) : ℝ := (∑ i, y i) / n

/-- "w = (π₁⁻¹, ..., πₙ⁻¹)" and "μ̂ = w'y / w'1ₙ"
(equation (1), p. 236). `a = 1` represents individual sampled units;
`a = mass` represents outcome-class totals in (6)--(7), p. 237. -/
def ratio {ι : Type*} [Fintype ι] (y a w : ι → ℝ) : ℝ :=
  (∑ i, a i * w i * y i) / (∑ i, a i * w i)

/-- "1/β ≤ w₁, ..., wₙ ≤ 1/α" (equations (2)--(3), p. 236).
The same box applies to class weights W in (6)--(7), p. 237. -/
def weightBox {ι : Type*} (α β : ℝ) (w : ι → ℝ) : Prop :=
  ∀ i, 1 / β ≤ w i ∧ w i ≤ 1 / α

/-- The normalized box [1,γ], obtained by `u = β w`, with
"γ = β/α ≥ 1" (Proposition 1, p. 236). -/
def normBox {ι : Type*} (γ : ℝ) (w : ι → ℝ) : Prop :=
  ∀ i, 1 ≤ w i ∧ w i ≤ γ

/-- "the first k entries 1/α and the remaining n-k entries 1/β"
(Proposition 1, lower half, p. 236; Proposition 2, p. 238), after scaling by β. -/
def lowerWeights {n : ℕ} (γ : ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => if i.val < k then γ else 1

/-- "the first k entries 1/β and the remaining n-k entries 1/α"
(Proposition 1, upper half, p. 236; Proposition 2, p. 238), after scaling by β. -/
def upperWeights {n : ℕ} (γ : ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => if i.val < k then 1 else γ

/-- Fᴸ_k for unit masses and G⁻_k for masses mass, using the correctly
partitioned prefix and tail (pp. 236--237, lower bound display). -/
def lowerValue {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  ratio y a (lowerWeights γ k)

/-- Fᴴ_k for unit masses and G⁺_k for masses mass (equation (4), p. 236,
and Proposition 2, p. 237). -/
def upperValue {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  ratio y a (upperWeights γ k)

/-- "the smallest nonnegative integer k that satisfies ... ≤ y_{k+1}"
(Proposition 1 upper rule, p. 236; both corrected lower rules, T3--T4).
`Fin n` enforces precisely the valid domain 0 ≤ k < n. -/
def lowerCut {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : Fin n) : Prop :=
  IsLeast {j : Fin n | lowerValue y a γ j.val ≤ y j} k

/-- The upper first-cut rule "smallest nonnegative integer k" satisfying
the next-outcome test (Proposition 1, p. 236; Proposition 2, p. 237). -/
def upperCut {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : Fin n) : Prop :=
  IsLeast {j : Fin n | upperValue y a γ j.val ≤ y j} k

/-- The printed "≥ y_{k+1}" lower stopping test
(Proposition 1, p. 236; Proposition 2, p. 238). This definition deliberately
retains the erroneous direction for the printed claims and counterexamples. -/
def printedLowerCut {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : Fin n) : Prop :=
  IsLeast {j : Fin n | y j ≤ lowerValue y a γ j.val} k

/-- The attainable values in (2)--(3) or (6)--(7), not merely box vertices. -/
def attainable {ι : Type*} [Fintype ι] (y a : ι → ℝ) (α β : ℝ) : Set ℝ :=
  {v | ∃ w, weightBox α β w ∧ ratio y a w = v}

/-- The minimum (3)/(7) and maximum (2)/(6), p. 236--237. The real
infimum/supremum are total definitions; under the paper's positive-mass,
nonempty-population assumptions the extrema are attained. -/
noncomputable def lowerEndpoint {ι : Type*} [Fintype ι] (y a : ι → ℝ) (α β : ℝ) : ℝ :=
  sInf (attainable y a α β)
/-- "The maximum" in (2) and (6), pp. 236--237. Under the paper's
positive-mass assumptions it is attained; see corrected_weighted_bounds. -/
noncomputable def upperEndpoint {ι : Type*} [Fintype ι] (y a : ι → ℝ) (α β : ℝ) : ℝ :=
  sSup (attainable y a α β)

/-- "For any k ≥ 0, y_(k+1) ≠ [upper ratio], y_(k+1) ≠ [lower ratio]"
(Assumption 2, p. 238), with the valid index range 0 ≤ k < |Y|. -/
def separation {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) : Prop :=
  ∀ k : Fin n, y k ≠ upperValue y a γ k.val ∧
    y k ≠ lowerValue y a γ k.val

/-- A two-unit sample `(0,1)` used in the exact counterexamples (T1, T2, T12). -/
def binaryTwo : Fin 2 → ℝ := ![0, 1]

/-- Concrete marginal inclusion probabilities `(1/2,1)` from the design
"include unit 2 always and unit 1 with probability 1/2". -/
def twoPi : Fin 2 → ℝ := ![1/2, 1]

/-- T1: the printed lower rule chooses zero for y=(0,1), α=1/2, β=1,
returns 1/2, and misses the feasible value 1/3. The true extrema over
ALL real weights in the box are 1/3 and 2/3 (Proposition 1, p. 236). -/
theorem sample_sign_counterexample :
    (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) ≤ 1 ∧
    Monotone binaryTwo ∧
    printedLowerCut binaryTwo (fun _ => 1) 2 (0 : Fin 2) ∧
    lowerValue binaryTwo (fun _ => 1) 2 0 = 1/2 ∧
    lowerValue binaryTwo (fun _ => 1) 2 1 = 1/3 ∧
    upperCut binaryTwo (fun _ => 1) 2 (1 : Fin 2) ∧
    upperValue binaryTwo (fun _ => 1) 2 1 = 2/3 ∧
    ((1/2 : ℝ) - 1/3 = 1/6) ∧
    (∀ u v : ℝ, 1 ≤ u → u ≤ 2 → 1 ≤ v → v ≤ 2 →
      1/3 ≤ v/(u+v) ∧ v/(u+v) ≤ 2/3) := by
  have hm : Monotone binaryTwo := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [binaryTwo] at *
  have hl : printedLowerCut binaryTwo (fun _ => 1) 2 (0 : Fin 2) := by
    constructor
    · norm_num [lowerValue, ratio, lowerWeights, binaryTwo, Fin.sum_univ_two]
    · intro j _; exact Fin.zero_le j
  have hh : upperCut binaryTwo (fun _ => 1) 2 (1 : Fin 2) := by
    constructor
    · norm_num [upperValue, ratio, upperWeights, binaryTwo, Fin.sum_univ_two]
    · intro j hj
      fin_cases j
      · norm_num [upperValue, ratio, upperWeights, binaryTwo, Fin.sum_univ_two] at hj
      · rfl
  refine ⟨by norm_num, by norm_num, hm, hl, ?_, ?_, hh, ?_, by norm_num, ?_⟩
  all_goals try norm_num [lowerValue, upperValue, ratio, lowerWeights, upperWeights,
    binaryTwo, Fin.sum_univ_two]
  intro u v hu1 hu2 hv1 hv2
  have hd : 0 < u+v := by linarith
  constructor
  · apply (le_div_iff₀ hd).2; linarith
  · apply (div_le_iff₀ hd).2; linarith

/-- T2: with class totals mass=(1/2,1), the printed lower rule chooses zero
and gives 2/3, exceeding the population mean and the true minimum 1/2.
The maximum is 4/5, and Assumption 2 holds (Proposition 2, pp. 237--238). -/
theorem class_sign_counterexample :
    (∀ i, (1/2 : ℝ) ≤ twoPi i ∧ twoPi i ≤ 1) ∧
    StrictMono binaryTwo ∧ populationMean binaryTwo = 1/2 ∧
    printedLowerCut binaryTwo twoPi 2 (0 : Fin 2) ∧
    lowerValue binaryTwo twoPi 2 0 = 2/3 ∧
    lowerValue binaryTwo twoPi 2 1 = 1/2 ∧
    upperValue binaryTwo twoPi 2 1 = 4/5 ∧
    separation binaryTwo twoPi 2 ∧
    (1/2 : ℝ) < 2/3 ∧
    (∀ u v : ℝ, 1 ≤ u → u ≤ 2 → 1 ≤ v → v ≤ 2 →
      1/2 ≤ v/(u/2+v) ∧ v/(u/2+v) ≤ 4/5) := by
  have hp : ∀ i, (1/2 : ℝ) ≤ twoPi i ∧ twoPi i ≤ 1 := by
    intro i; fin_cases i <;> norm_num [twoPi]
  have hm : StrictMono binaryTwo := by
    intro i j h; fin_cases i <;> fin_cases j <;> norm_num [binaryTwo] at *
  have hl : printedLowerCut binaryTwo twoPi 2 (0 : Fin 2) := by
    constructor
    · norm_num [lowerValue, ratio, lowerWeights, binaryTwo, twoPi, Fin.sum_univ_two]
    · intro j _; exact Fin.zero_le j
  have hs : separation binaryTwo twoPi 2 := by
    intro k; fin_cases k <;>
      norm_num [upperValue, lowerValue, ratio, upperWeights, lowerWeights,
        binaryTwo, twoPi, Fin.sum_univ_two]
  refine ⟨hp, hm, ?_, hl, ?_, ?_, ?_, hs, by norm_num, ?_⟩
  all_goals try norm_num [populationMean, lowerValue, upperValue, ratio, lowerWeights,
    upperWeights, binaryTwo, twoPi, Fin.sum_univ_two]
  intro u v hu1 hu2 hv1 hv2
  have hd : 0 < u/2+v := by linarith
  constructor
  · apply (le_div_iff₀ hd).2; linarith
  · apply (div_le_iff₀ hd).2; linarith

/-- Positive finite masses and positive weights give the positive denominator
required in equations (1)--(3) and (6)--(7). -/
theorem denominator_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (a w : ι → ℝ) (ha : ∀ i, 0 < a i) (hw : ∀ i, 0 < w i) :
    0 < ∑ i, a i * w i := by
  exact Finset.sum_pos (fun i _ => mul_pos (ha i) (hw i)) Finset.univ_nonempty

/-- A positive weighted mean cannot exceed an upper bound on its outcomes
(the average argument used for existence of the last valid cut, T3--T4). -/
theorem ratio_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (y a w : ι → ℝ) (ha : ∀ i, 0 < a i) (hw : ∀ i, 0 < w i)
    (M : ℝ) (hy : ∀ i, y i ≤ M) : ratio y a w ≤ M := by
  apply (div_le_iff₀ (denominator_pos a w ha hw)).2
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hy i) (le_of_lt (mul_pos (ha i) (hw i))))

/-- A positive weighted mean is at least every common lower bound on outcomes
(used in the printed-rule diagnosis and uniform convergence lemma). -/
theorem le_ratio {ι : Type*} [Fintype ι] [Nonempty ι]
    (y a w : ι → ℝ) (ha : ∀ i, 0 < a i) (hw : ∀ i, 0 < w i)
    (m : ℝ) (hy : ∀ i, m ≤ y i) : m ≤ ratio y a w := by
  apply (le_div_iff₀ (denominator_pos a w ha hw)).2
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hy i) (le_of_lt (mul_pos (ha i) (hw i))))

/-- Multiplying every weight by a nonzero constant leaves the Hajek ratio
unchanged (p. 236, paragraph after (5), T18). -/
theorem ratio_scale_weights {ι : Type*} [Fintype ι]
    (y a w : ι → ℝ) (c : ℝ) (hc : c ≠ 0) :
    ratio y a (fun i => c * w i) = ratio y a w := by
  simp only [ratio]
  simp_rw [show ∀ i, a i * (c * w i) * y i = c * (a i * w i * y i)
    from fun i => by ring,
    show ∀ i, a i * (c * w i) = c * (a i * w i) from fun i => by ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_mul_left _ _ hc]

/-- Multiplying all class masses by a nonzero constant leaves (6)--(7)
unchanged (normalized shares display, p. 237; (B4) in the Supplement). -/
theorem ratio_scale_masses {ι : Type*} [Fintype ι]
    (y a w : ι → ℝ) (c : ℝ) (hc : c ≠ 0) :
    ratio y (fun i => c * a i) w = ratio y a w := by
  simp only [ratio]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_mul_left _ _ hc]

/-- The two boxes are exactly related by u=βw; no normalization of mass is
assumed (Proposition 1, p. 236; class optimization (6)--(7), p. 237). -/
theorem normalize_box {ι : Type*} (α β : ℝ)
    (hα : 0 < α) (hαβ : α ≤ β) (w : ι → ℝ) :
    weightBox α β w ↔ normBox (β/α) (fun i => β * w i) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  constructor
  · intro h i
    constructor
    · have hi := (h i).1
      have hm := mul_le_mul_of_nonneg_left hi hβ.le
      simpa [div_eq_mul_inv, hβ.ne'] using hm
    · have hi := (h i).2
      have hm := mul_le_mul_of_nonneg_left hi hβ.le
      simpa [div_eq_mul_inv] using hm
  · intro h i
    constructor
    · apply (div_le_iff₀ hβ).2
      simpa [mul_comm] using (h i).1
    · apply (mul_le_mul_iff_right₀ hβ).1
      simpa [div_eq_mul_inv, mul_comm] using (h i).2

/-- The generic two-level threshold vector from Propositions 1--2;
`l=γ,b=1` is the lower vector and `l=1,b=γ` is the upper vector. -/
def threshold {n : ℕ} (l b : ℝ) (k : ℕ) (i : Fin n) : ℝ :=
  if i.val < k then l else b

/-- Exact numerator update when one entry moves from the tail to the
prefix. This finite identity underlies T3(e), T4(d), and T11(A1). -/
theorem threshold_sum_update {n : ℕ} (a y : Fin n → ℝ)
    (l b : ℝ) (k : Fin n) :
    (∑ i, a i * threshold l b (k.val+1) i * y i) =
    (∑ i, a i * threshold l b k.val i * y i) + (l-b) * a k * y k := by
  classical
  have hp (i : Fin n) : a i * threshold l b (k.val+1) i * y i =
      a i * threshold l b k.val i * y i +
        (if i = k then (l-b) * a k * y k else 0) := by
    by_cases hi : i = k
    · subst i
      simp [threshold]
      ring
    · have hv : i.val ≠ k.val := fun h => hi (Fin.ext h)
      have hh : i.val < k.val+1 ↔ i.val < k.val := by omega
      simp [threshold, hi, hh]
  simp_rw [hp, Finset.sum_add_distrib]
  simp

/-- Exact denominator update accompanying the numerator update. -/
theorem threshold_den_update {n : ℕ} (a : Fin n → ℝ)
    (l b : ℝ) (k : Fin n) :
    (∑ i, a i * threshold l b (k.val+1) i) =
    (∑ i, a i * threshold l b k.val i) + (l-b) * a k := by
  simpa using threshold_sum_update a (fun _ => 1) l b k

/-- The exact ratio increment (T3(e), T4(d), T11(A1)), for arbitrary
positive class masses and either orientation of the threshold vector. -/
theorem threshold_increment {n : ℕ} (hn : 0 < n) (a y : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (l b : ℝ) (hl : 0 < l) (hb : 0 < b) (k : Fin n) :
    ratio y a (threshold l b (k.val+1)) - ratio y a (threshold l b k.val) =
      (l-b) * a k * (y k - ratio y a (threshold l b k.val)) /
        (∑ i, a i * threshold l b (k.val+1) i) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hw (j : ℕ) (i : Fin n) : 0 < threshold l b j i := by
    simp only [threshold]; split <;> assumption
  have hd := (denominator_pos a (threshold l b k.val) ha (hw k.val)).ne'
  have hd' := (denominator_pos a (threshold l b (k.val+1)) ha (hw (k.val+1))).ne'
  simp only [ratio]
  rw [threshold_sum_update]
  have hu := threshold_den_update a l b k
  field_simp
  rw [hu]
  ring

/-- Moving an entry to the prefix preserves the sign of the difference
from that entry's outcome (the strict separator argument, T3(f), T19). -/
theorem threshold_shift {n : ℕ} (hn : 0 < n) (a y : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (l b : ℝ) (hl : 0 < l) (hb : 0 < b) (k : Fin n) :
    ratio y a (threshold l b (k.val+1)) - y k =
      ((∑ i, a i * threshold l b k.val i) /
       (∑ i, a i * threshold l b (k.val+1) i)) *
      (ratio y a (threshold l b k.val) - y k) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hw (j : ℕ) (i : Fin n) : 0 < threshold l b j i := by
    simp only [threshold]; split <;> assumption
  have hd := (denominator_pos a (threshold l b k.val) ha (hw k.val)).ne'
  have hd' := (denominator_pos a (threshold l b (k.val+1)) ha (hw (k.val+1))).ne'
  simp only [ratio]
  rw [threshold_sum_update]
  have hu := threshold_den_update a l b k
  field_simp
  rw [hu]
  ring

/-- Every positive two-level threshold rule has a valid first cut,
because the last test is an average bounded above by the last outcome.
This proves T3(a) and T4(a), including n=1 and tied outcomes. -/
theorem threshold_cut_exists {n : ℕ} (hn : 0 < n) (a y : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hy : Monotone y)
    (l b : ℝ) (hl : 0 < l) (hb : 0 < b) :
    ∃ k : Fin n, IsLeast {j : Fin n |
      ratio y a (threshold l b j.val) ≤ y j} k := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let last : Fin n := ⟨n-1, by omega⟩
  have hlast : ratio y a (threshold l b last.val) ≤ y last := by
    apply ratio_le y a _ ha
    · intro i; simp only [threshold]; split <;> assumption
    · intro i; apply hy; change i.val ≤ n-1; have := i.isLt; omega
  let s := Finset.univ.filter (fun j : Fin n =>
    ratio y a (threshold l b j.val) ≤ y j)
  have hs : s.Nonempty := ⟨last, by simp [s, hlast]⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (s.min'_mem hs)).2
  · intro j hj
    exact Finset.min'_le s j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

/-- The first cut separates outcomes strictly below its value from
outcomes at least its value. The statement covers both H and corrected L
weights; its lower instance gives T3(f). -/
theorem threshold_separator {n : ℕ} (hn : 0 < n) (a y : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hy : Monotone y)
    (l b : ℝ) (hl : 0 < l) (hb : 0 < b) (k : Fin n)
    (hk : IsLeast {j : Fin n | ratio y a (threshold l b j.val) ≤ y j} k) :
    (∀ i : Fin n, i.val < k.val → y i < ratio y a (threshold l b k.val)) ∧
    (∀ i : Fin n, k.val ≤ i.val → ratio y a (threshold l b k.val) ≤ y i) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · intro i hi
    let prev : Fin n := ⟨k.val-1, by have := k.isLt; omega⟩
    have hprev : prev.val < k.val := by dsimp [prev]; omega
    have hfail : y prev < ratio y a (threshold l b prev.val) := by
      by_contra h
      have ht : ratio y a (threshold l b prev.val) ≤ y prev := le_of_not_gt h
      have hm := hk.2 ht
      exact (not_le_of_gt hprev) hm
    have hw (j : ℕ) (z : Fin n) : 0 < threshold l b j z := by
      simp only [threshold]; split <;> assumption
    have hd := denominator_pos a (threshold l b prev.val) ha (hw prev.val)
    have hd' := denominator_pos a (threshold l b (prev.val+1)) ha (hw (prev.val+1))
    have hshift := threshold_shift hn a y ha l b hl hb prev
    have hpositive : 0 < ratio y a (threshold l b (prev.val+1)) - y prev := by
      rw [hshift]
      exact mul_pos (div_pos hd hd') (sub_pos.mpr hfail)
    have hp : prev.val+1 = k.val := by dsimp [prev]; omega
    rw [hp] at hpositive
    exact lt_of_le_of_lt (hy (by change i.val ≤ prev.val; dsimp [prev]; omega))
      (sub_pos.mp hpositive)
  · intro i hi
    exact hk.1.trans (hy hi)

/-- A zero weighted residual is the exact identity defining the ratio.
It is reused for the termwise optimality and uniform error certificates. -/
theorem ratio_residual_zero {ι : Type*} [Fintype ι] (y a w : ι → ℝ)
    (hd : (∑ i, a i * w i) ≠ 0) :
    (∑ i, a i * w i * (y i - ratio y a w)) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  dsimp [ratio]
  field_simp
  <;> ring

/-- The corrected lower threshold vector globally minimizes the ratio
over the WHOLE normalized weight box (T3(c), T4(c)). -/
theorem lower_threshold_optimal {n : ℕ} (hn : 0 < n) (a y : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hy : Monotone y) (γ : ℝ) (hγ : 1 ≤ γ)
    (k : Fin n) (hk : lowerCut y a γ k) (w : Fin n → ℝ) (hw : normBox γ w) :
    lowerValue y a γ k.val ≤ ratio y a w := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hγp : 0 < γ := lt_of_lt_of_le zero_lt_one hγ
  have hs := threshold_separator hn a y ha hy γ 1 hγp zero_lt_one k hk
  let v : Fin n → ℝ := lowerWeights γ k.val
  let m := lowerValue y a γ k.val
  have hvp (i : Fin n) : 0 < v i := by dsimp [v, lowerWeights]; split <;> positivity
  have hzero := ratio_residual_zero y a v (denominator_pos a v ha hvp).ne'
  have hc : 0 ≤ ∑ i, a i * (w i - v i) * (y i - m) := by
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : i.val < k.val
    · have hwv : w i - v i ≤ 0 := by dsimp [v, lowerWeights]; rw [if_pos hi]; linarith [(hw i).2]
      have hym : y i - m ≤ 0 := le_of_lt (sub_neg.mpr (hs.1 i hi))
      have := mul_nonneg_of_nonpos_of_nonpos hwv hym
      nlinarith [mul_nonneg (ha i).le this]
    · have hwv : 0 ≤ w i - v i := by dsimp [v, lowerWeights]; rw [if_neg hi]; linarith [(hw i).1]
      have hym : 0 ≤ y i - m := sub_nonneg.mpr (hs.2 i (by omega))
      exact mul_nonneg (mul_nonneg (ha i).le hwv) hym
  have hsum : 0 ≤ ∑ i, a i * w i * (y i - m) := by
    have he : (∑ i, a i * (w i - v i) * (y i - m)) =
        (∑ i, a i * w i * (y i - m)) - (∑ i, a i * v i * (y i - m)) := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    change (∑ i, a i * v i * (y i - m)) = 0 at hzero
    rw [he, hzero, sub_zero] at hc
    exact hc
  apply (le_div_iff₀ (denominator_pos a w ha (fun i => by linarith [(hw i).1]))).2
  simp_rw [mul_sub] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  nlinarith

/-- The upper threshold vector globally maximizes the ratio over the
WHOLE normalized box (printed upper halves of Propositions 1--2). -/
theorem upper_threshold_optimal {n : ℕ} (hn : 0 < n) (a y : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hy : Monotone y) (γ : ℝ) (hγ : 1 ≤ γ)
    (k : Fin n) (hk : upperCut y a γ k) (w : Fin n → ℝ) (hw : normBox γ w) :
    ratio y a w ≤ upperValue y a γ k.val := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hγp : 0 < γ := lt_of_lt_of_le zero_lt_one hγ
  have hs := threshold_separator hn a y ha hy 1 γ zero_lt_one hγp k hk
  let v : Fin n → ℝ := upperWeights γ k.val
  let m := upperValue y a γ k.val
  have hvp (i : Fin n) : 0 < v i := by dsimp [v, upperWeights]; split <;> positivity
  have hzero := ratio_residual_zero y a v (denominator_pos a v ha hvp).ne'
  have hc : (∑ i, a i * (w i - v i) * (y i - m)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    by_cases hi : i.val < k.val
    · have hwv : 0 ≤ w i - v i := by dsimp [v, upperWeights]; rw [if_pos hi]; linarith [(hw i).1]
      have hym : y i - m ≤ 0 := le_of_lt (sub_neg.mpr (hs.1 i hi))
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (ha i).le hwv) hym
    · have hwv : w i - v i ≤ 0 := by dsimp [v, upperWeights]; rw [if_neg hi]; linarith [(hw i).2]
      have hym : 0 ≤ y i - m := sub_nonneg.mpr (hs.2 i (by omega))
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (ha i).le hwv) hym
  have hsum : (∑ i, a i * w i * (y i - m)) ≤ 0 := by
    have he : (∑ i, a i * (w i - v i) * (y i - m)) =
        (∑ i, a i * w i * (y i - m)) - (∑ i, a i * v i * (y i - m)) := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    change (∑ i, a i * v i * (y i - m)) = 0 at hzero
    rw [he, hzero, sub_zero] at hc
    exact hc
  apply (div_le_iff₀ (denominator_pos a w ha (fun i => by linarith [(hw i).1]))).2
  simp_rw [mul_sub] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  nlinarith

/-- "p/{γ(1-p)+p}" and "γp/{(1-p)+γp}", the dichotomous
bound endpoints (unnumbered display, p. 237). -/
def binaryLower (p γ : ℝ) : ℝ := p / (γ*(1-p)+p)
/-- The printed upper binary endpoint γp/((1-p)+γp), p. 237. -/
def binaryUpper (p γ : ℝ) : ℝ := γ*p / ((1-p)+γ*p)

/-- The two intervals compared in the application, pp. 238--239. -/
def binaryInterval (p γ : ℝ) : Set ℝ := Set.Icc (binaryLower p γ) (binaryUpper p γ)

/-- The Hajek estimate with constant inclusion probabilities in the
positive and negative strata (equation (1), p. 236; T5--T6). -/
def reweightedPrevalence (p π₁ π₀ : ℝ) : ℝ :=
  (p/π₁) / (p/π₁ + (1-p)/π₀)

/-- The sample odds ratio K=p_G(1-p_E)/{(1-p_G)p_E}. -/
def sampleOddsRatio (pG pE : ℝ) : ℝ := pG*(1-pE)/((1-pG)*pE)

/-- T5(A)--(B): the two exact fixed-quota populations have the reported
sample counts, equal true and reweighted prevalences, and respectively
r_E<3 and r_G<3. Inclusion probabilities are the quota divided by its
stratum population size. -/
theorem application_counterexample_numbers :
    (48 : ℝ)/(48+16) = 3/4 ∧ (864 : ℝ)/(864+288) = 3/4 ∧
    (48 : ℝ)/(48+12) = 4/5 ∧ (1156 : ℝ)/(1156+289) = 4/5 ∧
    ((44:ℕ)+4 = 48) ∧ ((291:ℕ)+288 = 579) ∧
    (1/4 : ℝ) ≤ 11/12 ∧ (11/12 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 97/288 ∧ (97/288 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 1/3 ∧ (1/4 : ℝ) ≤ 291/1156 ∧ (291/1156 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 288/289 ∧ (288/289 : ℝ) ≤ 1 ∧
    reweightedPrevalence (44/48) (11/12) (1/4) = 3/4 ∧
    reweightedPrevalence (291/579) (97/288) 1 = 3/4 ∧
    reweightedPrevalence (44/48) (11/12) (1/3) = 4/5 ∧
    reweightedPrevalence (291/579) (291/1156) (288/289) = 4/5 ∧
    ((11/12 : ℝ)/(1/4) = 11/3) ∧ (3 : ℝ) < 11/3 ∧
    ((1:ℝ)/(97/288) = 288/97) ∧ (288/97 : ℝ) < 3 ∧
    ((11/12 : ℝ)/(1/3) = 11/4) ∧ (11/4 : ℝ) < 3 ∧
    ((288/289 : ℝ)/(291/1156) = 384/97) ∧ (3 : ℝ) < 384/97 ∧
    (11/3 : ℝ)*(288/97) = 1056/97 ∧
    (11/4 : ℝ)*(384/97) = 1056/97 ∧
    binaryLower (44/48) 4 ≤ 3/4 ∧ (3/4 : ℝ) < 4/5 ∧
    (4/5 : ℝ) ≤ binaryUpper (291/579) 4 := by
  norm_num [reweightedPrevalence, binaryLower, binaryUpper]

/-- T5(D): even treating the printed rounded percentages as exact limiting
selected shares gives equal prevalences and a directional ratio below three. -/
theorem application_rounded_counterexamples :
    (1/4 : ℝ) ≤ 249/917 ∧ (249/917 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 503/1491 ∧ (503/1491 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 332/917 ∧ (332/917 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 503/1988 ∧ (503/1988 : ℝ) ≤ 1 ∧
    ((3/4 : ℝ)*1/((3/4)*1+(1-3/4)*(249/917)) = 917/1000) ∧
    ((3/4 : ℝ)*(503/1491)/((3/4)*(503/1491)+(1-3/4)*1) = 503/1000) ∧
    (1491/503 : ℝ) < 3 ∧
    ((4/5 : ℝ)*1/((4/5)*1+(1-4/5)*(332/917)) = 917/1000) ∧
    ((4/5 : ℝ)*(503/1988)/((4/5)*(503/1988)+(1-4/5)*1) = 503/1000) ∧
    (917/332 : ℝ) < 3 := by norm_num

/-- Positive denominators in the dichotomous formula, including γ=1. -/
theorem binary_denominators (p γ : ℝ) (hp : 0 < p) (hp1 : p < 1) (hγ : 1 ≤ γ) :
    0 < γ*(1-p)+p ∧ 0 < (1-p)+γ*p := by
  have hγp : 0 < γ := by linarith
  constructor <;> nlinarith [mul_pos hγp (sub_pos.mpr hp1), mul_pos hγp hp]

/-- For an interior binary proportion and γ≥1, L(p,γ)≤H(p,γ). -/
theorem binary_endpoints_order (p γ : ℝ) (hp : 0 < p) (hp1 : p < 1) (hγ : 1 ≤ γ) :
    binaryLower p γ ≤ binaryUpper p γ := by
  have hd := binary_denominators p γ hp hp1 hγ
  rw [binaryLower, binaryUpper, div_le_div_iff₀ hd.1 hd.2]
  have hg : 0 ≤ γ^2-1 := by nlinarith
  have hp' : 0 ≤ p*(1-p) := mul_nonneg hp.le (sub_nonneg.mpr hp1.le)
  nlinarith [mul_nonneg hg hp']

/-- L is increasing in the observed binary sample proportion. -/
theorem binaryLower_monotone (p q γ : ℝ) (hp : 0 < p) (hq1 : q < 1)
    (hpq : p ≤ q) (hγ : 1 ≤ γ) : binaryLower p γ ≤ binaryLower q γ := by
  have hd := binary_denominators p γ hp (lt_of_le_of_lt hpq hq1) hγ
  have hd' := binary_denominators q γ (lt_of_lt_of_le hp hpq) hq1 hγ
  rw [binaryLower, binaryLower, div_le_div_iff₀ hd.1 hd'.1]
  nlinarith [mul_nonneg (by linarith : 0 ≤ γ) (sub_nonneg.mpr hpq)]

/-- T6(a): gallery and exchange intervals overlap exactly when their
opposing endpoints cross, equivalently when γ² is at least their sample
odds ratio. Equality permits touching (Section 4, corrected). -/
theorem overlap_criterion (pG pE γ : ℝ)
    (hE : 0 < pE) (hEG : pE < pG) (hG : pG < 1) (hγ : 1 ≤ γ) :
    (((binaryInterval pG γ) ∩ (binaryInterval pE γ)).Nonempty ↔
      binaryLower pG γ ≤ binaryUpper pE γ) ∧
    (binaryLower pG γ ≤ binaryUpper pE γ ↔ sampleOddsRatio pG pE ≤ γ^2) := by
  have hdG := binary_denominators pG γ (hE.trans hEG) hG hγ
  have hdE := binary_denominators pE γ hE (hEG.trans hG) hγ
  have hK : 0 < (1-pG)*pE := mul_pos (sub_pos.mpr hG) hE
  constructor
  · constructor
    · rintro ⟨x, hxG, hxE⟩
      exact hxG.1.trans hxE.2
    · intro h
      refine ⟨binaryLower pG γ, ⟨le_rfl, ?_⟩, ⟨?_, h⟩⟩
      · exact binary_endpoints_order pG γ (hE.trans hEG) hG hγ
      · exact binaryLower_monotone pE pG γ hE hG hEG.le hγ
  · rw [binaryLower, binaryUpper, div_le_div_iff₀ hdG.1 hdE.2,
      sampleOddsRatio, div_le_iff₀ hK]
    constructor <;> intro h <;> nlinarith

/-- T6(b),(d): the exact odds ratios and rational square brackets for the
printed percentages and the inferred counts, plus the two ratio tradeoffs. -/
theorem overlap_threshold_numbers :
    sampleOddsRatio (917/1000) (503/1000) = 455749/41749 ∧
    (330/100 : ℝ)^2 < 455749/41749 ∧ (455749/41749 : ℝ) < (331/100)^2 ∧
    sampleOddsRatio (44/48) (291/579) = 1056/97 ∧
    (329/100 : ℝ)^2 < 1056/97 ∧ (1056/97 : ℝ) < (330/100)^2 ∧
    (9 : ℝ) < 455749/41749 ∧ (455749/41749 : ℝ) < 16 ∧
    (9 : ℝ) < 1056/97 ∧ (1056/97 : ℝ) < 16 ∧
    ((11/3 : ℝ)*(288/97) = 1056/97 ∧ (288/97 : ℝ) < 3) ∧
    ((11/4 : ℝ)*(384/97) = 1056/97 ∧ (11/4 : ℝ) < 3) := by
  norm_num [sampleOddsRatio]

/-- The inverse-probability expression equals its cross-multiplied
stratum form, with every probability and sample fraction positive (T6(c)). -/
theorem reweighted_formula (p a b : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (hb : 0 < b) :
    reweightedPrevalence p a b = p*b/(p*b+(1-p)*a) := by
  have hd : 0 < p/a+(1-p)/b := add_pos (div_pos hp ha) (div_pos (sub_pos.mpr hp1) hb)
  have hd' : 0 < p*b+(1-p)*a := add_pos (mul_pos hp hb) (mul_pos (sub_pos.mpr hp1) ha)
  unfold reweightedPrevalence
  field_simp
  <;> ring

/-- T6(c): equal Hajek estimates impose a PRODUCT identity on the two
opposing directional selection ratios, rather than a lower bound on each. -/
theorem equal_estimates_product (pG pE g₁ g₀ e₁ e₀ : ℝ)
    (hE : 0 < pE) (hEG : pE < pG) (hG : pG < 1)
    (hg₁ : 0 < g₁) (hg₀ : 0 < g₀) (he₁ : 0 < e₁) (he₀ : 0 < e₀) :
    reweightedPrevalence pG g₁ g₀ = reweightedPrevalence pE e₁ e₀ ↔
      (g₁/g₀)*(e₀/e₁) = sampleOddsRatio pG pE := by
  have hGp := hE.trans hEG
  have hE1 := hEG.trans hG
  rw [reweighted_formula pG g₁ g₀ hGp hG hg₁ hg₀,
      reweighted_formula pE e₁ e₀ hE hE1 he₁ he₀]
  have dG : 0 < pG*g₀+(1-pG)*g₁ := add_pos (mul_pos hGp hg₀) (mul_pos (sub_pos.mpr hG) hg₁)
  have dE : 0 < pE*e₀+(1-pE)*e₁ := add_pos (mul_pos hE he₀) (mul_pos (sub_pos.mpr hE1) he₁)
  rw [div_eq_div_iff dG.ne' dE.ne']
  unfold sampleOddsRatio
  have dK : (1-pG)*pE ≠ 0 := (mul_pos (sub_pos.mpr hG) hE).ne'
  rw [div_mul_div_comm, div_eq_div_iff (mul_pos hg₀ he₁).ne' dK]
  constructor <;> intro h <;> nlinarith

/-- T6(d): a common upper cap on both positive directional ratios bounds
their product by γ². -/
theorem common_cap_product (rG rE K γ : ℝ)
    (hrG : 0 < rG) (hrE : 0 < rE) (hG : rG ≤ γ) (hE : rE ≤ γ)
    (hK : rG*rE = K) : K ≤ γ^2 := by
  rw [← hK, pow_two]
  exact mul_le_mul hG hE hrE.le (lt_of_lt_of_le hrG hG).le

/-- Rounded one-decimal percentage, represented by its exact half-open
rounding interval [entry-0.05,entry+0.05), Table 1 correction T17. -/
def roundsTenth (x : ℝ) (t : ℕ) : Prop :=
  (t : ℝ)/10 - 1/20 ≤ x ∧ x < (t : ℝ)/10 + 1/20

/-- The unique integer positive counts implied by the three printed
sample sizes and percentages (T17(a), Table 1/Section 4, p. 238). -/
theorem reported_counts_unique :
    (∀ k : ℤ, |100*(k:ℝ)/48 - 917/10| ≤ 1/20 ↔ k = 44) ∧
    (∀ k : ℤ, |100*(k:ℝ)/160 - 675/10| ≤ 1/20 ↔ k = 108) ∧
    (∀ k : ℤ, |100*(k:ℝ)/579 - 503/10| ≤ 1/20 ↔ k = 291) := by
  constructor
  · intro k; constructor
    · intro h; have hh := abs_le.mp h
      have h1 : (43:ℝ) < k := by linarith
      have h2 : (k:ℝ) < 45 := by linarith
      have hi1 : (43:ℤ) < k := by exact_mod_cast h1
      have hi2 : k < (45:ℤ) := by exact_mod_cast h2
      omega
    · intro h; subst k; norm_num
  constructor
  · intro k; constructor
    · intro h; have hh := abs_le.mp h
      have h1 : (107:ℝ) < k := by linarith
      have h2 : (k:ℝ) < 109 := by linarith
      have hi1 : (107:ℤ) < k := by exact_mod_cast h1
      have hi2 : k < (109:ℤ) := by exact_mod_cast h2
      omega
    · intro h; subst k; norm_num
  · intro k; constructor
    · intro h; have hh := abs_le.mp h
      have h1 : (290:ℝ) < k := by linarith
      have h2 : (k:ℝ) < 292 := by linarith
      have hi1 : (290:ℤ) < k := by exact_mod_cast h1
      have hi2 : k < (292:ℤ) := by exact_mod_cast h2
      omega
    · intro h; subst k; norm_num

/-- T17(b): exact endpoint percentages for all six corrected cells. -/
theorem table_six_exact :
    100*binaryLower (44/48) 2 = 1100/13 ∧
    100*binaryLower (44/48) 4 = 220/3 ∧
    100*binaryUpper (291/579) (5/4) = 48500/869 ∧
    100*binaryLower (291/579) (3/2) = 9700/241 ∧
    100*binaryUpper (291/579) (3/2) = 9700/161 ∧
    100*binaryUpper (291/579) (5/2) = 48500/677 := by
  norm_num [binaryLower, binaryUpper]

/-- A Table 1 cell records the count proportion, printed input proportion,
γ, whether H is used, printed tenths of a percent, and corrected tenths. -/
abbrev TableCell := ℝ × ℝ × ℝ × Bool × ℕ × ℕ

/-- All 42 Table 1 cells (p. 238).
Only the six entries singled out by T17 differ in the last column. -/
def tableCells : List TableCell := [
  (44/48,917/1000,1,false,917,917),(44/48,917/1000,1,true,917,917),
  (44/48,917/1000,5/4,false,898,898),(44/48,917/1000,5/4,true,932,932),
  (44/48,917/1000,3/2,false,880,880),(44/48,917/1000,3/2,true,943,943),
  (44/48,917/1000,2,false,847,846),(44/48,917/1000,2,true,957,957),
  (44/48,917/1000,5/2,false,815,815),(44/48,917/1000,5/2,true,965,965),
  (44/48,917/1000,3,false,786,786),(44/48,917/1000,3,true,971,971),
  (44/48,917/1000,4,false,734,733),(44/48,917/1000,4,true,978,978),
  (108/160,675/1000,1,false,675,675),(108/160,675/1000,1,true,675,675),
  (108/160,675/1000,5/4,false,624,624),(108/160,675/1000,5/4,true,722,722),
  (108/160,675/1000,3/2,false,581,581),(108/160,675/1000,3/2,true,757,757),
  (108/160,675/1000,2,false,509,509),(108/160,675/1000,2,true,806,806),
  (108/160,675/1000,5/2,false,454,454),(108/160,675/1000,5/2,true,839,839),
  (108/160,675/1000,3,false,409,409),(108/160,675/1000,3,true,862,862),
  (108/160,675/1000,4,false,342,342),(108/160,675/1000,4,true,893,893),
  (291/579,503/1000,1,false,503,503),(291/579,503/1000,1,true,503,503),
  (291/579,503/1000,5/4,false,447,447),(291/579,503/1000,5/4,true,559,558),
  (291/579,503/1000,3/2,false,403,402),(291/579,503/1000,3/2,true,603,602),
  (291/579,503/1000,2,false,336,336),(291/579,503/1000,2,true,669,669),
  (291/579,503/1000,5/2,false,288,288),(291/579,503/1000,5/2,true,717,716),
  (291/579,503/1000,3,false,252,252),(291/579,503/1000,3,true,752,752),
  (291/579,503/1000,4,false,202,202),(291/579,503/1000,4,true,802,802)]

/-- Evaluate a binary Table 1 cell from either the count input or the
printed rounded input; the side flag chooses L or H. -/
def cellPercent (p γ : ℝ) (high : Bool) : ℝ :=
  100 * (if high then binaryUpper p γ else binaryLower p γ)

/-- T17(b)--(d): every corrected count-based cell rounds correctly,
every printed cell is reproduced from the rounded inputs, and precisely
six of 42 printed cells are one tenth of a percent too high. -/
theorem table_all_cells :
    List.Forall (fun c : TableCell =>
      roundsTenth (cellPercent c.1 c.2.2.1 c.2.2.2.1) c.2.2.2.2.2 ∧
      roundsTenth (cellPercent c.2.1 c.2.2.1 c.2.2.2.1) c.2.2.2.2.1)
      tableCells ∧
    tableCells.length = 42 ∧
    (tableCells.filter (fun c => c.2.2.2.2.1 != c.2.2.2.2.2)).length = 6 ∧
    List.Forall (fun c : TableCell => c.2.2.2.2.1 = c.2.2.2.2.2 ∨
      c.2.2.2.2.1 = c.2.2.2.2.2 + 1) tableCells := by
  norm_num [tableCells, cellPercent, roundsTenth, binaryLower, binaryUpper]

/-- T17(e): using count proportions preserves the gallery/exchange
comparison at γ=3 and γ=4 (Table 1, p. 238). -/
theorem table_grid_comparison :
    binaryLower (44/48) 3 = 11/14 ∧ binaryUpper (291/579) 3 = 291/387 ∧
    binaryLower (44/48) 3 > binaryUpper (291/579) 3 ∧
    binaryLower (44/48) 4 = 11/15 ∧ binaryUpper (291/579) 4 = 97/121 ∧
    binaryLower (44/48) 4 < binaryUpper (291/579) 4 := by
  norm_num [binaryLower, binaryUpper]

/-- The normalized attainable values, using the exactly equivalent box
[1,γ] (p. 236, paragraph after (5)). -/
def normAttainable {ι : Type*} [Fintype ι] (y a : ι → ℝ) (γ : ℝ) : Set ℝ :=
  {v | ∃ w, normBox γ w ∧ ratio y a w = v}

/-- T18(a): the attainable set depends on α and β only through γ=β/α. -/
theorem attainable_normalization {ι : Type*} [Fintype ι] (y a : ι → ℝ)
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    attainable y a α β = normAttainable y a (β/α) := by
  have hβ : 0 < β := hα.trans_le hαβ
  ext v
  constructor
  · rintro ⟨w, hw, hv⟩
    refine ⟨fun i => β*w i, (normalize_box α β hα hαβ w).1 hw, ?_⟩
    rw [ratio_scale_weights y a w β hβ.ne', hv]
  · rintro ⟨w, hw, hv⟩
    refine ⟨fun i => (1/β)*w i, ?_, ?_⟩
    · apply (normalize_box α β hα hαβ _).2
      simpa [← mul_assoc, hβ.ne'] using hw
    · rw [ratio_scale_weights y a w (1/β) (one_div_ne_zero hβ.ne'), hv]

/-- Every intermediate ratio is attained on the feasible segment joining
any two feasible vectors. This is the continuous-attainment step of (5),
p. 236, and includes coincident endpoint values. -/
theorem ratio_segment_attains {ι : Type*} [Fintype ι] [Nonempty ι]
    (y a : ι → ℝ) (ha : ∀ i, 0 < a i) (γ : ℝ) (u v : ι → ℝ)
    (hu : normBox γ u) (hv : normBox γ v) (z : ℝ)
    (hz : ratio y a u ≤ z ∧ z ≤ ratio y a v) :
    z ∈ normAttainable y a γ := by
  let w : ℝ → ι → ℝ := fun t i => (1-t)*u i+t*v i
  have hw (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : normBox γ (w t) := by
    intro i
    have h1 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hu i).1)
    have h2 := mul_nonneg ht.1 (sub_nonneg.mpr (hv i).1)
    have h3 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hu i).2)
    have h4 := mul_nonneg ht.1 (sub_nonneg.mpr (hv i).2)
    dsimp [w]; constructor <;> nlinarith
  let f : ℝ → ℝ := fun t => ratio y a (w t)
  have hf : ContinuousOn f (Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.div
    · change ContinuousOn (fun t => ∑ i, a i * ((1-t)*u i+t*v i) * y i) _
      fun_prop
    · change ContinuousOn (fun t => ∑ i, a i * ((1-t)*u i+t*v i)) _
      fun_prop
    · intro t ht
      exact (denominator_pos a (w t) ha (fun i => by linarith [(hw t ht i).1])).ne'
  have hf0 : f 0 = ratio y a u := by simp [f, w]
  have hf1 : f 1 = ratio y a v := by simp [f, w]
  have hz' : z ∈ Set.Icc (f 0) (f 1) := by simpa [hf0, hf1] using hz
  obtain ⟨t, ht, htz⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hf hz'
  exact ⟨w t, hw t ht, htz⟩

/-- Corrected Proposition 1 and corrected Proposition 2 in one finite
weighted statement (T3(a)--(d), T4(a)--(c)). The smallest valid cut points
exist, their threshold vectors are feasible and attain the global extrema,
and the entire real range is the closed interval between those values.
Unit masses give Proposition 1; positive class totals mass give Proposition 2. -/
theorem corrected_weighted_bounds {n : ℕ} (hn : 0 < n)
    (y a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hy : Monotone y)
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (hβ1 : β ≤ 1) :
    ∃ kL kH : Fin n,
      lowerCut y a (β/α) kL ∧ upperCut y a (β/α) kH ∧
      weightBox α β (fun i : Fin n => (1/β)*lowerWeights (β/α) kL.val i) ∧
      weightBox α β (fun i : Fin n => (1/β)*upperWeights (β/α) kH.val i) ∧
      ratio y a (fun i => (1/β)*lowerWeights (β/α) kL.val i) = lowerValue y a (β/α) kL.val ∧
      ratio y a (fun i => (1/β)*upperWeights (β/α) kH.val i) = upperValue y a (β/α) kH.val ∧
      IsLeast (attainable y a α β) (lowerValue y a (β/α) kL.val) ∧
      IsGreatest (attainable y a α β) (upperValue y a (β/α) kH.val) ∧
      lowerEndpoint y a α β = lowerValue y a (β/α) kL.val ∧
      upperEndpoint y a α β = upperValue y a (β/α) kH.val ∧
      attainable y a α β = Set.Icc (lowerValue y a (β/α) kL.val) (upperValue y a (β/α) kH.val) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hβ : 0 < β := hα.trans_le hαβ
  have hγ : 1 ≤ β/α := (le_div_iff₀ hα).2 (by linarith)
  have hγp : 0 < β/α := div_pos hβ hα
  obtain ⟨kL, hkL⟩ := threshold_cut_exists hn a y ha hy (β/α) 1 hγp zero_lt_one
  obtain ⟨kH, hkH⟩ := threshold_cut_exists hn a y ha hy 1 (β/α) zero_lt_one hγp
  have hL : normBox (β/α) (lowerWeights (n:=n) (β/α) kL.val) := by
    intro i; simp only [lowerWeights]; split <;> exact ⟨by linarith, by linarith⟩
  have hH : normBox (β/α) (upperWeights (n:=n) (β/α) kH.val) := by
    intro i; simp only [upperWeights]; split <;> exact ⟨by linarith, by linarith⟩
  have hwL : weightBox α β (fun i : Fin n => (1/β)*lowerWeights (β/α) kL.val i) := by
    apply (normalize_box α β hα hαβ _).2
    simpa [← mul_assoc, hβ.ne'] using hL
  have hwH : weightBox α β (fun i : Fin n => (1/β)*upperWeights (β/α) kH.val i) := by
    apply (normalize_box α β hα hαβ _).2
    simpa [← mul_assoc, hβ.ne'] using hH
  have heL : ratio y a (fun i => (1/β)*lowerWeights (β/α) kL.val i) = lowerValue y a (β/α) kL.val :=
    ratio_scale_weights y a _ (1/β) (one_div_ne_zero hβ.ne')
  have heH : ratio y a (fun i => (1/β)*upperWeights (β/α) kH.val i) = upperValue y a (β/α) kH.val :=
    ratio_scale_weights y a _ (1/β) (one_div_ne_zero hβ.ne')
  have hleast : IsLeast (normAttainable y a (β/α)) (lowerValue y a (β/α) kL.val) := by
    refine ⟨⟨lowerWeights (β/α) kL.val, hL, rfl⟩, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    exact lower_threshold_optimal hn a y ha hy (β/α) hγ kL hkL w hw
  have hgreatest : IsGreatest (normAttainable y a (β/α)) (upperValue y a (β/α) kH.val) := by
    refine ⟨⟨upperWeights (β/α) kH.val, hH, rfl⟩, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    exact upper_threshold_optimal hn a y ha hy (β/α) hγ kH hkH w hw
  have hrange : normAttainable y a (β/α) =
      Set.Icc (lowerValue y a (β/α) kL.val) (upperValue y a (β/α) kH.val) := by
    ext z; constructor
    · intro hz; exact ⟨hleast.2 hz, hgreatest.2 hz⟩
    · intro hz
      exact ratio_segment_attains y a ha (β/α) _ _ hL hH z hz
  have hnorm := attainable_normalization y a α β hα hαβ
  rw [← hnorm] at hleast hgreatest hrange
  exact ⟨kL,kH,hkL,hkH,hwL,hwH,heL,heH,hleast,hgreatest,
    hleast.csInf_eq,hgreatest.csSup_eq,hrange⟩

/-- T3: corrected Proposition 1 and equation (5) for the paper's sorted,
nonempty observed sample; no hypotheses are added to the probability box. -/
theorem corrected_proposition_one {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : Monotone y) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (hβ1 : β ≤ 1) :
    ∃ kL kH : Fin n, lowerCut y (fun _ => 1) (β/α) kL ∧
      upperCut y (fun _ => 1) (β/α) kH ∧
      IsLeast (attainable y (fun _ => 1) α β) (lowerValue y (fun _ => 1) (β/α) kL.val) ∧
      IsGreatest (attainable y (fun _ => 1) α β) (upperValue y (fun _ => 1) (β/α) kH.val) ∧
      attainable y (fun _ => 1) α β = Set.Icc
        (lowerValue y (fun _ => 1) (β/α) kL.val) (upperValue y (fun _ => 1) (β/α) kH.val) := by
  obtain ⟨kL,kH,hL,hH,_,_,_,_,hl,hh,_,_,hr⟩ :=
    corrected_weighted_bounds hn y (fun _ => 1) (fun _ => zero_lt_one) hy α β hα hαβ hβ1
  exact ⟨kL,kH,hL,hH,hl,hh,hr⟩

/-- T4: corrected Proposition 2, with its strictly ordered distinct outcomes
and positive totals mass; the threshold vectors attain (6)--(7), not a claim
that the optimizers are unique (pp. 237--238). -/
theorem corrected_proposition_two {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ)
    (hy : StrictMono y) (hmass : ∀ j, 0 < mass j) (α β : ℝ)
    (hα : 0 < α) (hαβ : α ≤ β) (hβ1 : β ≤ 1) :
    ∃ kL kH : Fin J, lowerCut y mass (β/α) kL ∧ upperCut y mass (β/α) kH ∧
      IsLeast (attainable y mass α β) (lowerValue y mass (β/α) kL.val) ∧
      IsGreatest (attainable y mass α β) (upperValue y mass (β/α) kH.val) ∧
      lowerEndpoint y mass α β = lowerValue y mass (β/α) kL.val ∧
      upperEndpoint y mass α β = upperValue y mass (β/α) kH.val := by
  obtain ⟨kL,kH,hL,hH,_,_,_,_,hl,hh,el,eh,_⟩ :=
    corrected_weighted_bounds hJ y mass hmass hy.monotone α β hα hαβ hβ1
  exact ⟨kL,kH,hL,hH,hl,hh,el,eh⟩

/-- T9(a): the threshold objective is exactly the disjoint prefix/tail
formula, for every cut, including empty prefix or empty tail (p. 237
corrected lower display). -/
theorem threshold_partition {n : ℕ} (y a : Fin n → ℝ) (l b : ℝ) (k : ℕ) :
    ratio y a (threshold l b k) =
      (l*(∑ i with i.val < k, a i*y i) + b*(∑ i with k ≤ i.val, a i*y i)) /
      (l*(∑ i with i.val < k, a i) + b*(∑ i with k ≤ i.val, a i)) := by
  classical
  simp only [ratio, threshold, mul_ite, ite_mul]
  rw [Finset.sum_ite, Finset.sum_ite]
  simp only [not_lt]
  simp_rw [mul_comm (a _) l, mul_comm (a _) b, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

/-- T18: two admissible probability intervals with the same ratio γ have
exactly the same attainable set; at γ=1 the set is the singleton sample
mean (p. 236, paragraph after (5)). -/
theorem ratio_only_and_equal_probabilities {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (α β α' β' : ℝ) (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1)
    (hα' : 0 < α') (hab' : α' ≤ β') (hb1' : β' ≤ 1) (heq : β/α = β'/α') :
    attainable y (fun _ => 1) α β = attainable y (fun _ => 1) α' β' ∧
    (β/α = 1 → attainable y (fun _ => 1) α β = {populationMean y}) := by
  constructor
  · rw [attainable_normalization y (fun _ => 1) α β hα hab,
      attainable_normalization y (fun _ => 1) α' β' hα' hab', heq]
  · intro hγ
    rw [attainable_normalization y (fun _ => 1) α β hα hab, hγ]
    ext z; constructor
    · rintro ⟨w, hw, rfl⟩
      have hw1 : w = fun _ => 1 := funext (fun i => le_antisymm (hw i).2 (hw i).1)
      simp [hw1, ratio, populationMean]
    · intro hz
      have hz' : z = populationMean y := hz
      refine ⟨fun _ => 1, fun _ => ⟨le_rfl,le_rfl⟩, ?_⟩
      simp [hz', ratio, populationMean]

/-- T19: tied outcomes share the weights selected by the first-cut rule
for H and corrected L (Lemma 1, p. 237; Supplement p. 1). All equal-outcome
pairs are included; consecutive tied pairs are the printed special case. -/
theorem tied_outcomes_equal_weights {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : Monotone y) (γ : ℝ) (hγ : 1 ≤ γ) (kL kH : Fin n)
    (hL : lowerCut y (fun _ => 1) γ kL) (hH : upperCut y (fun _ => 1) γ kH) :
    ∀ i j : Fin n, y i = y j →
      lowerWeights γ kL.val i = lowerWeights γ kL.val j ∧
      upperWeights γ kH.val i = upperWeights γ kH.val j := by
  have hg : 0 < γ := by linarith
  have hsL := threshold_separator hn (fun _ => 1) y (fun _ => zero_lt_one) hy γ 1 hg zero_lt_one kL hL
  have hsH := threshold_separator hn (fun _ => 1) y (fun _ => zero_lt_one) hy 1 γ zero_lt_one hg kH hH
  intro i j heq
  have hsame (k : Fin n) (l b : ℝ)
      (hs : (∀ i : Fin n, i.val < k.val → y i < ratio y (fun _ => 1) (threshold l b k.val)) ∧
        (∀ i : Fin n, k.val ≤ i.val → ratio y (fun _ => 1) (threshold l b k.val) ≤ y i)) :
      threshold l b k.val i = threshold l b k.val j := by
    by_cases hi : i.val < k.val <;> by_cases hj : j.val < k.val
    · simp [threshold, hi, hj]
    · have h1 := hs.1 i hi; have h2 := hs.2 j (by omega); linarith
    · have h1 := hs.1 j hj; have h2 := hs.2 i (by omega); linarith
    · simp [threshold, hi, hj]
  exact ⟨hsame kL γ 1 hsL, hsame kH 1 γ hsH⟩

/-- The four-class support (0,1,2,3) from the six-unit
population (0,0,1,1,2,3) (T10). -/
def fourOutcomes : Fin 4 → ℝ := ![0,1,2,3]

/-- The printed lower expression's tail starts at printed class k-1.
Its value is deliberately partial: for k<2 the lower limit is not a class
index, so the expression has no value. For valid k its tail has zero-based
indices i≥k-2 and overlaps the prefix (Proposition 2, p. 237; T8--T10). -/
def printedLowerExpression {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : ℕ) : Option ℝ :=
  if 2 ≤ k ∧ k ≤ n then some
    ((γ*(∑ i with i.val < k, a i*y i) + (∑ i with k-2 ≤ i.val, a i*y i)) /
    (γ*(∑ i with i.val < k, a i) + (∑ i with k-2 ≤ i.val, a i))) else none

/-- T10: at the independently correct lower cut k=2 the printed overlapping
partition gives 1 instead of the minimum 7/6. The inequality covers every
real weight vector in [1,2]^4. The printed ≥ rule instead gives zero,
where its literal lower expression is undefined (p. 237). -/
theorem tail_index_counterexample :
    StrictMono fourOutcomes ∧
    lowerCut fourOutcomes (fun _ => 1) 2 (2 : Fin 4) ∧
    lowerValue fourOutcomes (fun _ => 1) 2 2 = 7/6 ∧
    printedLowerExpression fourOutcomes (fun _ => 1) 2 2 = some 1 ∧
    printedLowerCut fourOutcomes (fun _ => 1) 2 (0 : Fin 4) ∧
    printedLowerExpression fourOutcomes (fun _ => 1) 2 0 = none ∧
    (1 : ℝ) ≠ 7/6 ∧
    (∀ w : Fin 4 → ℝ, normBox 2 w → 7/6 ≤ ratio fourOutcomes (fun _ => 1) w) := by
  have hm : StrictMono fourOutcomes := by
    intro i j h; fin_cases i <;> fin_cases j <;> norm_num [fourOutcomes] at *
  have hL : lowerCut fourOutcomes (fun _ => 1) 2 (2 : Fin 4) := by
    constructor
    · norm_num [lowerValue, ratio, lowerWeights, fourOutcomes, Fin.sum_univ_succ]
    · intro j hj; fin_cases j <;>
        norm_num [lowerValue, ratio, lowerWeights, fourOutcomes, Fin.sum_univ_succ] at *
  have hpL : printedLowerCut fourOutcomes (fun _ => 1) 2 (0 : Fin 4) := by
    constructor
    · norm_num [lowerValue, ratio, lowerWeights, fourOutcomes, Fin.sum_univ_succ]
    · intro j _; exact Fin.zero_le j
  refine ⟨hm,hL,?_,?_,hpL,?_,by norm_num,?_⟩
  · norm_num [lowerValue, ratio, lowerWeights, fourOutcomes, Fin.sum_univ_succ]
  · simp only [printedLowerExpression, show (2 ≤ 2 ∧ 2 ≤ 4) from ⟨by decide, by decide⟩,
      ite_true, Finset.sum_filter]
    have hc : ((Finset.univ : Finset (Fin 4)).filter (fun i => i.val ≤ 1)).card = 2 := by decide
    norm_num [fourOutcomes, Fin.sum_univ_succ, hc]
  · simp [printedLowerExpression]
  · intro w hw
    have hopt := lower_threshold_optimal (by norm_num) (fun _ => 1) fourOutcomes
      (fun _ => zero_lt_one) hm.monotone 2 (by norm_num) 2 hL w hw
    norm_num [lowerValue,ratio,lowerWeights,fourOutcomes,Fin.sum_univ_succ] at hopt
    simpa [ratio,fourOutcomes,Fin.sum_univ_succ] using hopt

/-- T12: with a census of (0,1), α=β=γ=1, all three threshold values
are 1/2. The first stationary index is zero and the outcome-test cut is one;
the appendix implication and the supplement's strict improvement fail.
The actual optimization endpoints remain the sample mean (pp. 239--240). -/
theorem equal_probability_proof_counterexample :
    (1 : ℝ)/(1:ℝ) = 1 ∧
    upperValue binaryTwo (fun _ => 1) 1 0 = 1/2 ∧
    upperValue binaryTwo (fun _ => 1) 1 1 = 1/2 ∧
    upperValue binaryTwo (fun _ => 1) 1 2 = 1/2 ∧
    upperValue binaryTwo (fun _ => 1) 1 1 - upperValue binaryTwo (fun _ => 1) 1 0 ≤ 0 ∧
    ¬ upperValue binaryTwo (fun _ => 1) 1 0 ≤ binaryTwo 0 ∧
    IsLeast {k : Fin 2 | upperValue binaryTwo (fun _ => 1) 1 k.val ≥
      upperValue binaryTwo (fun _ => 1) 1 (k.val+1)} (0 : Fin 2) ∧
    upperCut binaryTwo (fun _ => 1) 1 (1 : Fin 2) ∧
    ((0:ℝ)*0-0+1*1*(0-1) = -1) ∧
    ((0:ℝ)-0*1+1*1*(0-1) = -1) ∧
    ¬ ratio binaryTwo (fun _ => 1) ![1,1] > ratio binaryTwo (fun _ => 1) ![1,1] := by
  have hstationary : IsLeast {k : Fin 2 | upperValue binaryTwo (fun _ => 1) 1 k.val ≥
      upperValue binaryTwo (fun _ => 1) 1 (k.val+1)} (0 : Fin 2) := by
    constructor
    · norm_num [upperValue, ratio, upperWeights, binaryTwo, Fin.sum_univ_two]
    · intro j _; exact Fin.zero_le j
  have hcut : upperCut binaryTwo (fun _ => 1) 1 (1 : Fin 2) := by
    constructor
    · norm_num [upperValue, ratio, upperWeights, binaryTwo, Fin.sum_univ_two]
    · intro j hj; fin_cases j <;>
        norm_num [upperValue, ratio, upperWeights, binaryTwo, Fin.sum_univ_two] at *
  refine ⟨by norm_num,?_,?_,?_,?_,?_,hstationary,hcut,by norm_num,by norm_num,lt_irrefl _⟩
  all_goals norm_num [upperValue, ratio, upperWeights, binaryTwo, Fin.sum_univ_two]

/-- All uniformly possible fixed-quota subsets of a stratum of N labeled
units, the design used in the application counterexamples.
An independent choice of one such subset in each stratum defines the
stratified uniform fixed-size design, with exactly the indicated counts. -/
def quotaDraws (N s : ℕ) : Finset (Finset (Fin N)) := Finset.univ.powersetCard s

/-- A unit's inclusion probability under the uniform fixed-quota design
is the number of possible draws containing it divided by all possible draws. -/
def quotaMarginal (N s : ℕ) (i : Fin N) : ℝ :=
  ((quotaDraws N s).filter (fun t => i ∈ t)).card / ((quotaDraws N s).card : ℝ)

/-- The uniform finite-quota design is a nonzero probability distribution,
and all its possible draws have exactly s selected units. No enumeration
of the large application populations is used. -/
theorem quota_design_valid (N s : ℕ) (hsN : s ≤ N) :
    (quotaDraws N s).Nonempty ∧
    (∑ t ∈ quotaDraws N s, (1 : ℝ)/((quotaDraws N s).card : ℝ)) = 1 ∧
    (∀ t ∈ quotaDraws N s, t.card = s) := by
  have hnon : (quotaDraws N s).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using hsN
  have hc : (0:ℝ) < (quotaDraws N s).card := by
    exact_mod_cast Finset.card_pos.mpr hnon
  refine ⟨hnon, ?_, ?_⟩
  · simp [Finset.sum_const, nsmul_eq_mul, hc.ne']
  · intro t ht; exact (Finset.mem_powersetCard.mp ht).2

/-- Every unit's marginal inclusion probability under the uniform quota
law is s/N. This supplies the actual design hypothesis of T5 rather than
merely assuming the application probabilities. -/
theorem quota_marginal_eq (N s : ℕ) (hs : 0 < s) (hsN : s ≤ N) (i : Fin N) :
    quotaMarginal N s i = (s:ℝ)/N := by
  have hN : 0 < N := hs.trans_le hsN
  have hc : ((quotaDraws N s).filter (fun t => i ∈ t)).card = (N-1).choose (s-1) := by
    simpa [quotaDraws, Finset.singleton_subset_iff] using
      Finset.card_filter_powersetCard_subset ({i} : Finset (Fin N)) Finset.univ s
        (Finset.subset_univ _) (by simpa using (Nat.succ_le_iff.mpr hs))
  have hc' : (quotaDraws N s).card = N.choose s := by
    simp [quotaDraws, Finset.card_powersetCard]
  have hi := Nat.add_one_mul_choose_eq (N-1) (s-1)
  have hN1 : N-1+1 = N := by omega
  have hs1 : s-1+1 = s := by omega
  rw [hN1, hs1] at hi
  have hiR : (N:ℝ)*((N-1).choose (s-1) : ℝ) = (N.choose s : ℝ)*(s:ℝ) := by
    exact_mod_cast hi
  have hcp : (0:ℝ) < (N.choose s : ℝ) := by exact_mod_cast Nat.choose_pos hsN
  unfold quotaMarginal
  rw [hc, hc', div_eq_div_iff hcp.ne' (by exact_mod_cast hN.ne')]
  nlinarith

/-- T5(A)--(B): the four uniform stratum laws in each example have
nonempty support and the stated unit marginal inclusion probabilities.
The population sizes and quotas are the explicit integers in the statement. -/
theorem application_counterexample_designs :
    (quotaDraws 48 44).Nonempty ∧ (quotaDraws 16 4).Nonempty ∧
    (quotaDraws 864 291).Nonempty ∧ (quotaDraws 288 288).Nonempty ∧
    (quotaDraws 12 4).Nonempty ∧ (quotaDraws 1156 291).Nonempty ∧
    (quotaDraws 289 288).Nonempty ∧
    (∀ i : Fin 48, quotaMarginal 48 44 i = 11/12) ∧
    (∀ i : Fin 16, quotaMarginal 16 4 i = 1/4) ∧
    (∀ i : Fin 864, quotaMarginal 864 291 i = 97/288) ∧
    (∀ i : Fin 288, quotaMarginal 288 288 i = 1) ∧
    (∀ i : Fin 12, quotaMarginal 12 4 i = 1/3) ∧
    (∀ i : Fin 1156, quotaMarginal 1156 291 i = 291/1156) ∧
    (∀ i : Fin 289, quotaMarginal 289 288 i = 288/289) := by
  refine ⟨(quota_design_valid 48 44 (by norm_num)).1,
    (quota_design_valid 16 4 (by norm_num)).1,
    (quota_design_valid 864 291 (by norm_num)).1,
    (quota_design_valid 288 288 (by norm_num)).1,
    (quota_design_valid 12 4 (by norm_num)).1,
    (quota_design_valid 1156 291 (by norm_num)).1,
    (quota_design_valid 289 288 (by norm_num)).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro i; rw [quota_marginal_eq _ _ (by norm_num) (by norm_num)]; norm_num

/-- T11(A2): at γ=1 every upper and lower threshold value equals the
sample mean, regardless of the cut; the feasible box is a singleton. -/
theorem equal_probability_thresholds {n : ℕ} (y : Fin n → ℝ) (k : ℕ) :
    upperValue y (fun _ => 1) 1 k = populationMean y ∧
    lowerValue y (fun _ => 1) 1 k = populationMean y ∧
    (∀ w : Fin n → ℝ, normBox 1 w ↔ w = fun _ => 1) := by
  have hu : upperWeights (n:=n) 1 k = fun _ => 1 := by funext i; simp [upperWeights]
  have hl : lowerWeights (n:=n) 1 k = fun _ => 1 := by funext i; simp [lowerWeights]
  refine ⟨?_,?_,?_⟩
  · simp [upperValue, hu, ratio, populationMean]
  · simp [lowerValue, hl, ratio, populationMean]
  · intro w; constructor
    · intro hw; funext i; exact le_antisymm (hw i).2 (hw i).1
    · intro hw; subst w; exact fun _ => ⟨le_rfl,le_rfl⟩

/-- T11(A1),(A3): for γ>1, the appendix increment identity and equality
of the stationary and outcome-test index sets.
Class masses generalize the unit-sample identity. -/
theorem strict_gamma_stationarity {n : ℕ} (hn : 0 < n) (y a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (γ : ℝ) (hγ : 1 < γ) :
    (∀ k : Fin n, upperValue y a γ (k.val+1) - upperValue y a γ k.val =
      (1-γ)*a k*(y k-upperValue y a γ k.val) /
        (∑ i, a i*upperWeights γ (k.val+1) i)) ∧
    {k : Fin n | upperValue y a γ k.val ≥ upperValue y a γ (k.val+1)} =
      {k : Fin n | upperValue y a γ k.val ≤ y k} := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hg : 0 < γ := by linarith
  have hden (k : ℕ) : 0 < ∑ i, a i*upperWeights γ k i := by
    apply denominator_pos _ _ ha
    intro i; dsimp [upperWeights]; split <;> positivity
  have hinc (k : Fin n) : upperValue y a γ (k.val+1) - upperValue y a γ k.val =
      (1-γ)*a k*(y k-upperValue y a γ k.val) /
        (∑ i, a i*upperWeights γ (k.val+1) i) :=
    threshold_increment hn a y ha 1 γ zero_lt_one hg k
  constructor
  · exact hinc
  · ext k
    have hc : (1-γ)*a k < 0 := mul_neg_of_neg_of_pos (by linarith) (ha k)
    change upperValue y a γ (k.val+1) ≤ upperValue y a γ k.val ↔ upperValue y a γ k.val ≤ y k
    rw [← sub_nonpos, hinc k, div_le_iff₀ (hden (k.val+1)), zero_mul]
    constructor
    · intro h; by_contra hn
      have hneg : y k-upperValue y a γ k.val < 0 := sub_neg.mpr (lt_of_not_ge hn)
      exact (not_le_of_gt (mul_pos_of_neg_of_neg hc hneg)) h
    · intro h; exact mul_nonpos_of_nonpos_of_nonneg hc.le (sub_nonneg.mpr h)

/-- T11(A3): after an upper cut qualifies, the next ratio is no greater
than the same outcome. -/
theorem upper_cut_persistence {n : ℕ} (hn : 0 < n) (y a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hy : Monotone y) (γ : ℝ) (hγ : 1 ≤ γ)
    (k : Fin n) (hk : upperValue y a γ k.val ≤ y k) :
    upperValue y a γ (k.val+1) ≤ y k := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hg : 0 < γ := by linarith
  have hd (j : ℕ) : 0 < ∑ i, a i * threshold 1 γ j i := by
    apply denominator_pos _ _ ha
    intro i; simp only [threshold]; split <;> positivity
  have hs := threshold_shift hn a y ha 1 γ zero_lt_one hg k
  apply sub_nonpos.mp
  change ratio y a (threshold 1 γ (k.val+1)) - y k ≤ 0
  change ratio y a (threshold 1 γ k.val) ≤ y k at hk
  rw [hs]
  exact mul_nonpos_of_nonneg_of_nonpos (div_pos (hd k.val) (hd (k.val+1))).le (sub_nonpos.mpr hk)

/-- The supplement's two-coordinate objective μ(x,z), after fixing all
other classes (Supplement p. 2, proof of Proposition 2, (B1)--(B2)). -/
def pairObjective (c₁ c₂ p q u v x z : ℝ) : ℝ :=
  (c₁+x*p*u+z*q*v)/(c₂+x*p+z*q)

/-- T11(B-i),(B-ii): exact cross-multiplied identities expose the factor
a-b omitted at α=β. The sum of E₁ and E₂ is strictly negative for distinct
outcomes, including the boundary where both objective differences vanish. -/
theorem pair_difference_identities (c₁ c₂ p q u v a b : ℝ)
    (hc : 0 ≤ c₂) (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) (hab : a ≤ b) (huv : u < v) :
    (c₂+a*p+a*q)*(c₂+b*p+a*q)*
      (pairObjective c₁ c₂ p q u v a a - pairObjective c₁ c₂ p q u v b a) =
        (a-b)*p*(c₂*u-c₁+a*q*(u-v)) ∧
    (c₂+b*p+b*q)*(c₂+b*p+a*q)*
      (pairObjective c₁ c₂ p q u v b b - pairObjective c₁ c₂ p q u v b a) =
        (a-b)*q*(c₁-c₂*v+b*p*(u-v)) ∧
    (c₂*u-c₁+a*q*(u-v))+(c₁-c₂*v+b*p*(u-v)) =
      (c₂+b*p+a*q)*(u-v) ∧
    (c₂*u-c₁+a*q*(u-v))+(c₁-c₂*v+b*p*(u-v)) < 0 := by
  have hb : 0 < b := ha.trans_le hab
  have daa : 0 < c₂+a*p+a*q := by positivity
  have dba : 0 < c₂+b*p+a*q := by positivity
  have dbb : 0 < c₂+b*p+b*q := by positivity
  have he : (c₂*u-c₁+a*q*(u-v))+(c₁-c₂*v+b*p*(u-v)) =
      (c₂+b*p+a*q)*(u-v) := by ring
  refine ⟨?_,?_,he,?_⟩
  · unfold pairObjective; field_simp <;> ring
  · unfold pairObjective; field_simp <;> ring
  · rw [he]; exact mul_neg_of_pos_of_neg dba (sub_neg.mpr huv)

/-- T11(B-iii),(B-iv): if a<b, each strict improvement is equivalent to
its printed negative residual and at least one improvement holds. If a=b,
the objective differences are zero, regardless of those residuals.
Here a=1/β and b=1/α, so this is exactly the repaired supplement argument. -/
theorem pair_boundary_repair (c₁ c₂ p q u v a b : ℝ)
    (hc : 0 ≤ c₂) (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) (hab : a ≤ b) (huv : u < v) :
    (a < b →
      (pairObjective c₁ c₂ p q u v a a > pairObjective c₁ c₂ p q u v b a ↔
        c₂*u-c₁+a*q*(u-v) < 0) ∧
      (pairObjective c₁ c₂ p q u v b b > pairObjective c₁ c₂ p q u v b a ↔
        c₁-c₂*v+b*p*(u-v) < 0) ∧
      (pairObjective c₁ c₂ p q u v a a > pairObjective c₁ c₂ p q u v b a ∨
        pairObjective c₁ c₂ p q u v b b > pairObjective c₁ c₂ p q u v b a)) ∧
    (a = b → pairObjective c₁ c₂ p q u v a a = pairObjective c₁ c₂ p q u v b a ∧
      pairObjective c₁ c₂ p q u v b b = pairObjective c₁ c₂ p q u v b a) := by
  have hb : 0 < b := ha.trans_le hab
  have daa : 0 < c₂+a*p+a*q := by positivity
  have dba : 0 < c₂+b*p+a*q := by positivity
  have dbb : 0 < c₂+b*p+b*q := by positivity
  obtain ⟨h1,h2,_,hneg⟩ := pair_difference_identities c₁ c₂ p q u v a b hc hp hq ha hab huv
  constructor
  · intro hlt
    have coef1 : (a-b)*p < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hp
    have coef2 : (a-b)*q < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hq
    have hequiv (A B D C E : ℝ) (hD : 0 < D) (hC : C < 0)
        (hid : D*(A-B)=C*E) : B < A ↔ E < 0 := by
      constructor
      · intro h
        have hprod : 0 < C*E := by rw [← hid]; exact mul_pos hD (sub_pos.mpr h)
        by_contra he
        have := mul_nonpos_of_nonpos_of_nonneg hC.le (le_of_not_gt he)
        linarith
      · intro h
        have hprod : 0 < D*(A-B) := by rw [hid]; exact mul_pos_of_neg_of_neg hC h
        have : 0 < A-B := (mul_pos_iff_of_pos_left hD).1 hprod
        exact sub_pos.mp this
    have he1 := hequiv _ _ _ _ _ (mul_pos daa dba) coef1 h1
    have he2 := hequiv _ _ _ _ _ (mul_pos dbb dba) coef2 h2
    refine ⟨he1,he2,?_⟩
    have hor : c₂*u-c₁+a*q*(u-v) < 0 ∨ c₁-c₂*v+b*p*(u-v) < 0 := by
      by_contra h; push_neg at h; linarith
    exact hor.elim (fun h => Or.inl (he1.2 h)) (fun h => Or.inr (he2.2 h))
  · intro h; subst b; exact ⟨rfl,rfl⟩

/-- Corrected lower formula for EVERY cut in the original probability
box, not depending on a cut-selection theorem (T9(a), p. 237). -/
theorem lower_partition_original_box {n : ℕ} (y a : Fin n → ℝ)
    (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) (k : ℕ) :
    ratio y a (fun i => if i.val < k then 1/α else 1/β) =
      ((β/α)*(∑ i with i.val < k, a i*y i) + (∑ i with k ≤ i.val, a i*y i)) /
      ((β/α)*(∑ i with i.val < k, a i) + (∑ i with k ≤ i.val, a i)) := by
  have hβ : 0 < β := hα.trans_le hab
  have hw : (fun i : Fin n => if i.val < k then 1/α else 1/β) =
      fun i => (1/β)*threshold (β/α) 1 k i := by
    funext i; dsimp [threshold]; split <;> field_simp
  rw [hw, ratio_scale_weights y a _ (1/β) (one_div_ne_zero hβ.ne'), threshold_partition]
  simp

/-- "Under a given sampling design, ... pr(I_i=1)=π_i" (Section 2,
p. 235). A finite probability space may have arbitrary within-sample
indicator dependence. A state specifies a subset of the labeled population;
its probability is nonnegative and the total probability is exactly one. -/
structure FiniteDesign (ι κ : Type*) [Fintype κ] where
  sample : κ → Finset ι
  probability : κ → ℝ
  nonnegative : ∀ ω, 0 ≤ probability ω
  total : ∑ ω, probability ω = 1

/-- Expectations over the sampling design are weighted finite sums,
as prescribed by the paper's design-based setting (Section 2, p. 235). -/
def designExpectation {ι κ : Type*} [Fintype κ] (d : FiniteDesign ι κ) (X : κ → ℝ) : ℝ :=
  ∑ ω, d.probability ω * X ω

/-- "π_i ... pr(I_i=1)" (p. 235), computed from the actual finite design. -/
def inclusion {ι κ : Type*} [Fintype κ] (d : FiniteDesign ι κ) (i : ι) : ℝ := by
  classical
  exact designExpectation d (fun ω => if i ∈ d.sample ω then 1 else 0)

/-- "Υ_j ≡ {i : y_i=y_(j)}" and "Π_j=∑_{i∈Υ_j} π_i"
(Section 3.2, p. 237). `cls` labels exactly these equivalence classes;
in general statements it is surjective and outcomes factor through it. -/
def classTotal {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (j : Fin J) : ℝ :=
  ∑ i with cls i = j, inclusion d i

/-- The number X_{r,j} of class-j units in a replicate sample, as in
(B4), Supplement p. 2. Here the state ω represents one replicate. -/
def classCount {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (j : Fin J) (ω : κ) : ℝ := by
  classical
  exact ∑ i, if cls i = j ∧ i ∈ d.sample ω then 1 else 0

/-- The finite mean identity E X_{r,j}=Π_j used by the strong-law
argument (T13(F4), T21(F5)); it assumes no independence of units in a sample. -/
theorem expected_class_count {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (j : Fin J) :
    designExpectation d (classCount d cls j) = classTotal d cls j := by
  classical
  unfold designExpectation classCount classTotal inclusion designExpectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : cls i = j <;> simp [h]

/-- A realizable two-unit design: state 0 samples only the
one-outcome unit and state 1 samples both units, each with probability 1/2. -/
def twoDesign : FiniteDesign (Fin 2) (Fin 2) where
  sample := fun ω => if ω = 0 then {1} else {0,1}
  probability := fun _ => 1/2
  nonnegative := fun _ => by norm_num
  total := by norm_num [Fin.sum_univ_two]

/-- T1--T2: the stated two-unit counterexample has actual inclusion
probabilities (1/2,1), and its observed two-unit sample has probability 1/2. -/
theorem two_design_realizes_example :
    (∀ i : Fin 2, inclusion twoDesign i = twoPi i) ∧
    designExpectation twoDesign (fun ω => if twoDesign.sample ω = {0,1} then 1 else 0) = 1/2 := by
  constructor
  · intro i; fin_cases i <;>
      norm_num [inclusion,designExpectation,twoDesign,twoPi,Fin.sum_univ_two]
  · have hs : ({1} : Finset (Fin 2)) ≠ {0,1} := by decide
    norm_num [designExpectation,twoDesign,Fin.sum_univ_two,hs]

/-- The six-unit population (0,0,1,1,2,3) (T10). -/
def sixTailOutcomes : Fin 6 → ℝ := ![0,0,1,1,2,3]
/-- The classes {1,2},{3,4},{5},{6} in the six-unit T10 example;
zero-based labels are (0,0,1,1,2,3). -/
def sixTailClass : Fin 6 → Fin 4 := ![0,0,1,1,2,3]

/-- Independently choose one of the two zeros, one of the two
ones, and include the two remaining units. Four equally likely states. -/
def fourClassDesign : FiniteDesign (Fin 6) (Fin 2 × Fin 2) where
  sample := fun ω => {⟨ω.1.val, by omega⟩,⟨ω.2.val+2, by omega⟩,4,5}
  probability := fun _ => 1/4
  nonnegative := fun _ => by norm_num
  total := by norm_num [Fintype.sum_prod_type,Fin.sum_univ_two]

/-- T10(a): the explicit finite design has every required marginal,
class totals all one, class sizes (2,2,1,1), and population mean 7/6. -/
theorem tail_design_realizes_example :
    (∀ i : Fin 6, inclusion fourClassDesign i = (![1/2,1/2,1/2,1/2,1,1] : Fin 6 → ℝ) i) ∧
    (∀ j : Fin 4, classTotal fourClassDesign sixTailClass j = 1) ∧
    (∀ j : Fin 4, (Finset.univ.filter (fun i => sixTailClass i = j)).card =
      (![2,2,1,1] : Fin 4 → ℕ) j) ∧
    populationMean sixTailOutcomes = 7/6 := by
  classical
  have hi : ∀ i : Fin 6, inclusion fourClassDesign i =
      (![1/2,1/2,1/2,1/2,1,1] : Fin 6 → ℝ) i := by
    intro i; fin_cases i <;> norm_num [inclusion,designExpectation,fourClassDesign,
      Fintype.sum_prod_type,Fin.sum_univ_two]
  refine ⟨hi,?_,?_,?_⟩
  · intro j
    unfold classTotal
    rw [Finset.sum_filter]
    simp only [Fin.sum_univ_succ]
    fin_cases j <;> norm_num [hi,sixTailClass]
  · intro j; fin_cases j <;> decide
  · norm_num [populationMean,sixTailOutcomes,Fin.sum_univ_succ]

/-- A census of (0,1) (T12), represented on a one-state
probability space, so both unit inclusion probabilities are one. -/
def censusDesign : FiniteDesign (Fin 2) (Fin 1) where
  sample := fun _ => Finset.univ
  probability := fun _ => 1
  nonnegative := fun _ => by norm_num
  total := by simp

/-- T12(a): the equal-probability boundary counterexample is a valid census
with all the paper's probability bounds holding at α=β=1. -/
theorem census_realizes_boundary : ∀ i : Fin 2, inclusion censusDesign i = 1 := by
  intro i; simp [inclusion,designExpectation,censusDesign]

/-- A nonempty uniform sample of size two from three units: choose the
omitted unit uniformly. Used by T16(A). -/
def omitOneDesign : FiniteDesign (Fin 3) (Fin 3) where
  sample := fun ω => Finset.univ.erase ω
  probability := fun _ => 1/3
  nonnegative := fun _ => by norm_num
  total := by norm_num [Fin.sum_univ_three]

/-- The population (0,1,1) and its two outcome classes (T16(A)). -/
def integralityOutcomes : Fin 3 → ℝ := ![0,1,1]
/-- The outcome classes {1},{2,3} of T16(A), with zero-based labels (0,1,1). -/
def integralityClass : Fin 3 → Fin 2 := ![0,1,1]

/-- T16(A)(i): all three actual marginals are 2/3, the absolute class
totals are (2/3,4/3), and the population mean is 2/3. -/
theorem integrality_design_realizes_example :
    (∀ i : Fin 3, inclusion omitOneDesign i = 2/3) ∧
    classTotal omitOneDesign integralityClass 0 = 2/3 ∧
    classTotal omitOneDesign integralityClass 1 = 4/3 ∧
    populationMean integralityOutcomes = 2/3 := by
  have hi : ∀ i : Fin 3, inclusion omitOneDesign i = 2/3 := by
    intro i; fin_cases i <;> norm_num [inclusion,designExpectation,omitOneDesign,Fin.sum_univ_three]
  refine ⟨hi,?_,?_,?_⟩
  · unfold classTotal
    rw [Finset.sum_filter,Fin.sum_univ_three]
    norm_num [hi,integralityClass]
  · unfold classTotal
    rw [Finset.sum_filter,Fin.sum_univ_three]
    norm_num [hi,integralityClass]
  · norm_num [populationMean,integralityOutcomes,Fin.sum_univ_three]

/-- Class-size compatibility with retained absolute totals: α m_j ≤ Π_j
≤ β m_j, m_j≥1. This is exactly the integer/calibration condition in T15(e)
and T16, derived by summing the paper's probability bounds in each class. -/
def absoluteCompatible {J : ℕ} (α β : ℝ) (mass : Fin J → ℝ) (m : Fin J → ℕ) : Prop :=
  ∀ j, 0 < m j ∧ α*(m j : ℝ) ≤ mass j ∧ mass j ≤ β*(m j : ℝ)

/-- The finite-population mean computed from outcome class sizes
(Section 3.2 identification display, p. 237). -/
def classMean {J : ℕ} (y : Fin J → ℝ) (m : Fin J → ℕ) : ℝ :=
  (∑ j, (m j : ℝ)*y j)/(∑ j, (m j : ℝ))

/-- For m>0, αm≤mass≤βm is equivalent to the existence of m real
values in [α,β] summing to mass; the constant value mass/m suffices.
When 0≤α≤β≤1, these values can be realized as Bernoulli inclusion
probabilities (T15(e)). -/
theorem one_class_compatibility (m : ℕ) (hm : 0 < m) (α β mass : ℝ) :
    (∃ π : Fin m → ℝ, (∀ i, α ≤ π i ∧ π i ≤ β) ∧ ∑ i, π i = mass) ↔
      α*(m:ℝ) ≤ mass ∧ mass ≤ β*(m:ℝ) := by
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  constructor
  · rintro ⟨π,hπ,hsum⟩
    have hl := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => (hπ i).1)
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => (hπ i).2)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hsum] at hl hh
    constructor <;> nlinarith
  · rintro ⟨hl,hh⟩
    refine ⟨fun _ => mass/m,?_,?_⟩
    · intro i; exact ⟨(le_div_iff₀ hmr).2 hl,(div_le_iff₀ hmr).2 hh⟩
    · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

/-- T16(A)(iii)--(v): retained absolute totals force class sizes (1,2),
even when N is unknown. The box endpoints 4/7 and 3/4 straddle the singleton
compatible mean 2/3, so they are not sharp for that information set. -/
theorem integrality_sharpness_counterexample :
    (∀ m : Fin 2 → ℕ, absoluteCompatible (1/2) (3/4) ![2/3,4/3] m ↔ m = ![1,2]) ∧
    classMean binaryTwo ![1,2] = 2/3 ∧
    lowerValue binaryTwo ![2/3,4/3] (3/2) 1 = 4/7 ∧
    upperValue binaryTwo ![2/3,4/3] (3/2) 1 = 3/4 ∧
    (2/3 : ℝ)-4/7 = 2/21 ∧ (3/4 : ℝ)-2/3 = 1/12 ∧
    (4/7 : ℝ) < 2/3 ∧ (2/3 : ℝ) < 3/4 ∧
    separation binaryTwo ![2/3,4/3] (3/2) := by
  have hcounts : ∀ m : Fin 2 → ℕ, absoluteCompatible (1/2) (3/4) ![2/3,4/3] m ↔ m = ![1,2] := by
    intro m; constructor
    · intro h
      have h0 := h 0; have h1 := h 1
      norm_num at h0 h1
      have hm0 : (m 0 : ℝ) < 2 := by linarith
      have hm1a : (1:ℝ) < m 1 := by linarith
      have hm1b : (m 1 : ℝ) < 3 := by linarith
      have h0n : m 0 < 2 := by exact_mod_cast hm0
      have h1n : 1 < m 1 := by exact_mod_cast hm1a
      have h1n' : m 1 < 3 := by exact_mod_cast hm1b
      funext i; fin_cases i <;> norm_num <;> omega
    · intro h; subst m; intro j; fin_cases j <;> norm_num
  refine ⟨hcounts,?_,?_,?_,by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
  all_goals try norm_num [classMean,binaryTwo,lowerValue,upperValue,ratio,
    lowerWeights,upperWeights,Fin.sum_univ_two]
  intro k; fin_cases k <;> norm_num [binaryTwo,lowerValue,upperValue,ratio,
    lowerWeights,upperWeights,Fin.sum_univ_two]

/-- T16(B): known N=1000 further restricts compatible class sizes.
Every integer m₂ from 500 through 750 is possible and no larger mean is.
The continuous upper bound 4/5 exceeds the maximum 3/4 by 1/20. -/
theorem known_size_sharpness_counterexample :
    (∀ m : Fin 2 → ℕ,
      (absoluteCompatible (1/10) (1/5) ![50,100] m ∧ m 0+m 1=1000) ↔
      (m 0+m 1=1000 ∧ 500 ≤ m 1 ∧ m 1 ≤ 750)) ∧
    (∀ k : ℕ, 500 ≤ k → k ≤ 750 →
      absoluteCompatible (1/10) (1/5) ![50,100] ![1000-k,k]) ∧
    classMean binaryTwo ![250,750] = 3/4 ∧
    lowerValue binaryTwo ![50,100] 2 1 = 1/2 ∧
    upperValue binaryTwo ![50,100] 2 1 = 4/5 ∧
    (4/5 : ℝ)-3/4 = 1/20 ∧ (3/4 : ℝ) < 4/5 := by
  have he : ∀ m : Fin 2 → ℕ,
      (absoluteCompatible (1/10) (1/5) ![50,100] m ∧ m 0+m 1=1000) ↔
      (m 0+m 1=1000 ∧ 500 ≤ m 1 ∧ m 1 ≤ 750) := by
    intro m; constructor
    · rintro ⟨hc,hs⟩
      have h0 := hc 0; have h1 := hc 1
      norm_num at h0 h1
      have hl : (500:ℝ) ≤ m 1 := by linarith
      have hu0 : (250:ℝ) ≤ m 0 := by linarith
      have hln : 500 ≤ m 1 := by exact_mod_cast hl
      have hun : 250 ≤ m 0 := by exact_mod_cast hu0
      exact ⟨hs,hln,by omega⟩
    · rintro ⟨hs,hl,hu⟩
      refine ⟨?_,hs⟩
      have hm0 : 250 ≤ m 0 ∧ m 0 ≤ 500 := by omega
      have hr0l : (250:ℝ) ≤ m 0 := by exact_mod_cast hm0.1
      have hr0h : (m 0 : ℝ) ≤ 500 := by exact_mod_cast hm0.2
      have hr1l : (500:ℝ) ≤ m 1 := by exact_mod_cast hl
      have hr1h : (m 1 : ℝ) ≤ 750 := by exact_mod_cast hu
      intro j; fin_cases j <;> norm_num <;> constructor
      · omega
      · constructor <;> linarith
      · omega
      · constructor <;> linarith
  refine ⟨he,?_,?_,?_,?_,by norm_num,by norm_num⟩
  · intro k hl hu
    apply ((he ![1000-k,k]).2 ?_).1
    norm_num
    exact ⟨by omega,hl,hu⟩
  all_goals norm_num [classMean,binaryTwo,lowerValue,upperValue,ratio,
    lowerWeights,upperWeights,Fin.sum_univ_two]

/-- Exact difference certificate for two Hajek ratios at a fixed mass
vector. Termwise signs of the residual prove inequalities over a whole box;
no vertex enumeration is needed (T3(f)). -/
theorem ratio_difference_residual {ι : Type*} [Fintype ι]
    (y a w v : ι → ℝ) (hw : (∑ i, a i*w i) ≠ 0) (hv : (∑ i, a i*v i) ≠ 0) :
    ratio y a w - ratio y a v =
      (∑ i, a i*(w i-v i)*(y i-ratio y a v))/(∑ i, a i*w i) := by
  have hzero := ratio_residual_zero y a v hv
  have hp (i : ι) : a i*(w i-v i)*(y i-ratio y a v) =
      a i*w i*(y i-ratio y a v)-a i*v i*(y i-ratio y a v) := by ring
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,hzero,sub_zero]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul]
  dsimp [ratio]
  field_simp
  <;> ring

/-- T20: the binary closed form is the complete attainable interval,
for every nonempty binary sample, including p=0, p=1 and γ=1 (p. 237).
The outcome-dependent endpoint weights are explicit feasible witnesses. -/
theorem dichotomous_closed_form {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 0 ∨ y i = 1) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1) :
    attainable y (fun _ => 1) α β =
      Set.Icc (binaryLower (populationMean y) (β/α)) (binaryUpper (populationMean y) (β/α)) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hγ : 1 ≤ β/α := (le_div_iff₀ hα).2 (by linarith)
  have hγp : 0 < β/α := by linarith
  let γ : ℝ := β/α
  let L : Fin n → ℝ := fun i => if y i = 0 then γ else 1
  let H : Fin n → ℝ := fun i => if y i = 0 then 1 else γ
  have hL : normBox γ L := by intro i; dsimp [L]; split <;> exact ⟨by linarith,by linarith⟩
  have hH : normBox γ H := by intro i; dsimp [H]; split <;> exact ⟨by linarith,by linarith⟩
  have hpL (i : Fin n) : 0 < L i := by linarith [(hL i).1]
  have hpH (i : Fin n) : 0 < H i := by linarith [(hH i).1]
  have hdL := denominator_pos (fun _ => 1) L (fun _ => zero_lt_one) hpL
  have hdH := denominator_pos (fun _ => 1) H (fun _ => zero_lt_one) hpH
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hLy (i : Fin n) : L i*y i = y i := by
    rcases hy i with h | h <;> simp [L,h]
  have hHy (i : Fin n) : H i*y i = γ*y i := by
    rcases hy i with h | h <;> simp [H,h]
  have hLi (i : Fin n) : L i = γ*(1-y i)+y i := by
    rcases hy i with h | h <;> simp [L,h]
  have hHi (i : Fin n) : H i = (1-y i)+γ*y i := by
    rcases hy i with h | h <;> simp [H,h]
  have hsumL : (∑ i, L i) = γ*((n:ℝ)-(∑ i,y i))+(∑ i,y i) := by
    simp_rw [hLi]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib]
    simp
  have hsumH : (∑ i, H i) = ((n:ℝ)-(∑ i,y i))+γ*(∑ i,y i) := by
    simp_rw [hHi]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    simp
  have heL : ratio y (fun _ => 1) L = binaryLower (populationMean y) γ := by
    have hp : γ*(1-(∑ i,y i)/(n:ℝ))+(∑ i,y i)/(n:ℝ) =
        (γ*((n:ℝ)-(∑ i,y i))+(∑ i,y i))/(n:ℝ) := by field_simp <;> ring
    simp only [ratio,one_mul,hLy,hsumL,binaryLower,populationMean]
    rw [hp,div_div_div_cancel_right₀ hnR]
  have heH : ratio y (fun _ => 1) H = binaryUpper (populationMean y) γ := by
    have hp : (1-(∑ i,y i)/(n:ℝ))+γ*((∑ i,y i)/(n:ℝ)) =
        (((n:ℝ)-(∑ i,y i))+γ*(∑ i,y i))/(n:ℝ) := by field_simp <;> ring
    simp only [ratio,one_mul,hHy,← Finset.mul_sum,hsumH,binaryUpper,populationMean]
    rw [hp,← mul_div_assoc γ (∑ i,y i) (n:ℝ),div_div_div_cancel_right₀ hnR]
  have hy0 (i : Fin n) : 0 ≤ y i := by rcases hy i with h | h <;> simp [h]
  have hy1 (i : Fin n) : y i ≤ 1 := by rcases hy i with h | h <;> simp [h]
  have hRL : 0 ≤ ratio y (fun _ => 1) L :=
    le_ratio y (fun _ => 1) L (fun _ => zero_lt_one) hpL 0 hy0
  have hRL1 : ratio y (fun _ => 1) L ≤ 1 :=
    ratio_le y (fun _ => 1) L (fun _ => zero_lt_one) hpL 1 hy1
  have hRH : 0 ≤ ratio y (fun _ => 1) H :=
    le_ratio y (fun _ => 1) H (fun _ => zero_lt_one) hpH 0 hy0
  have hRH1 : ratio y (fun _ => 1) H ≤ 1 :=
    ratio_le y (fun _ => 1) H (fun _ => zero_lt_one) hpH 1 hy1
  have hbounds (w : Fin n → ℝ) (hw : normBox γ w) :
      ratio y (fun _ => 1) L ≤ ratio y (fun _ => 1) w ∧
      ratio y (fun _ => 1) w ≤ ratio y (fun _ => 1) H := by
    have hdw := denominator_pos (fun _ => 1) w (fun _ => zero_lt_one)
      (fun i => by linarith [(hw i).1])
    constructor
    · apply sub_nonneg.mp
      rw [ratio_difference_residual y (fun _ => 1) w L hdw.ne' hdL.ne']
      apply div_nonneg _ hdw.le
      apply Finset.sum_nonneg
      intro i _
      rcases hy i with hz | ho
      · simp only [one_mul,hz,L,ite_true,zero_sub]
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hw i).2) (neg_nonpos.mpr hRL)
      · simp only [one_mul,ho,L,show (1:ℝ) ≠ 0 from one_ne_zero,ite_false]
        exact mul_nonneg (sub_nonneg.mpr (hw i).1) (sub_nonneg.mpr hRL1)
    · apply sub_nonpos.mp
      rw [ratio_difference_residual y (fun _ => 1) w H hdw.ne' hdH.ne']
      apply div_nonpos_of_nonpos_of_nonneg _ hdw.le
      apply Finset.sum_nonpos
      intro i _
      rcases hy i with hz | ho
      · simp only [one_mul,hz,H,ite_true,zero_sub]
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hw i).1) (neg_nonpos.mpr hRH)
      · simp only [one_mul,ho,H,show (1:ℝ) ≠ 0 from one_ne_zero,ite_false]
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hw i).2) (sub_nonneg.mpr hRH1)
  rw [attainable_normalization y (fun _ => 1) α β hα hab]
  ext z; constructor
  · rintro ⟨w,hw,rfl⟩
    have hb := hbounds w hw
    simpa [heL,heH] using hb
  · intro hz
    apply ratio_segment_attains y (fun _ => 1) (fun _ => zero_lt_one) γ L H hL hH z
    simpa [heL,heH] using hz

/-- With nonnegative observed class totals p and normalized weights u≥1,
the denominator is at least ∑p. This includes classes absent from a sample
(T13(F1)--(F2), Supplement (B3)--(B4)). -/
theorem denominator_ge_total {ι : Type*} [Fintype ι] (p w : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 1 ≤ w i) :
    (∑ i, p i) ≤ ∑ i, p i*w i := by
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (hw i) (hp i))

/-- The positive weighted mean lies between its smallest and largest
outcome even when some empirical class totals are zero (T13(F2)). -/
theorem nonnegative_mass_mean_bounds {ι : Type*} [Fintype ι]
    (y p w : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpSum : 0 < ∑ i,p i)
    (hw : ∀ i, 1 ≤ w i) (l u : ℝ) (hy : ∀ i, l ≤ y i ∧ y i ≤ u) :
    l ≤ ratio y p w ∧ ratio y p w ≤ u := by
  have hd : 0 < ∑ i,p i*w i := hpSum.trans_le (denominator_ge_total p w hp hw)
  constructor
  · apply (le_div_iff₀ hd).2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hwi : 0 ≤ w i := le_trans zero_le_one (hw i)
    simpa [mul_comm,mul_left_comm,mul_assoc] using
      mul_le_mul_of_nonneg_left (hy i).1 (mul_nonneg (hp i) hwi)
  · apply (div_le_iff₀ hd).2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hwi : 0 ≤ w i := le_trans zero_le_one (hw i)
    simpa [mul_comm,mul_left_comm,mul_assoc] using
      mul_le_mul_of_nonneg_left (hy i).2 (mul_nonneg (hp i) hwi)

/-- The exact mass-perturbation identity with m=f(W,p), used for the
uniform bound in the correction to Proposition 3 (T13(F2)). -/
theorem ratio_difference_masses {ι : Type*} [Fintype ι]
    (y p a w : ι → ℝ) (hp : (∑ i,p i*w i) ≠ 0) (ha : (∑ i,a i*w i) ≠ 0) :
    ratio y p w - ratio y a w =
      (∑ i,w i*(p i-a i)*(y i-ratio y p w))/(∑ i,a i*w i) := by
  have hz := ratio_residual_zero y p w hp
  have he (i : ι) : w i*(p i-a i)*(y i-ratio y p w) =
      p i*w i*(y i-ratio y p w)-a i*w i*(y i-ratio y p w) := by ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,hz,zero_sub]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul]
  dsimp [ratio]
  field_simp
  <;> ring

/-- T13(F2): the uniform deterministic error bound for EVERY fixed h
and every feasible W, with R=y_max-y_min and S=∑Π. Scaling weights by β
puts the paper's box into [1,γ]. Zero empirical class counts are allowed;
only the pooled sample must be nonempty. -/
theorem uniform_ratio_error {n : ℕ} (hn : 0 < n) (y p a : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : 0 < ∑ i,p i) (ha : ∀ i, 0 < a i)
    (l u γ : ℝ) (hy : ∀ i, l ≤ y i ∧ y i ≤ u) (hγ : 1 ≤ γ)
    (w : Fin n → ℝ) (hw : normBox γ w) :
    |ratio y p w-ratio y a w| ≤
      (γ*(u-l)/(∑ i,a i))*(∑ i,|p i-a i|) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hwpos (i : Fin n) : 0 < w i := by linarith [(hw i).1]
  have hpD : 0 < ∑ i,p i*w i := hpSum.trans_le (denominator_ge_total p w hp (fun i => (hw i).1))
  have haD : 0 < ∑ i,a i*w i := denominator_pos a w ha hwpos
  have haSum : 0 < ∑ i,a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hD : (∑ i,a i) ≤ ∑ i,a i*w i := denominator_ge_total a w (fun i => (ha i).le) (fun i => (hw i).1)
  have hmean := nonnegative_mass_mean_bounds y p w hp hpSum (fun i => (hw i).1) l u hy
  have hR : 0 ≤ u-l := by have h0 := hy ⟨0,hn⟩; linarith
  have hγ0 : 0 ≤ γ := by linarith
  have habs (i : Fin n) : |y i-ratio y p w| ≤ u-l := by
    apply abs_le.mpr; have hi := hy i; constructor <;> linarith
  have hnum : |∑ i,w i*(p i-a i)*(y i-ratio y p w)| ≤
      γ*(u-l)*(∑ i,|p i-a i|) := by
    calc
      _ ≤ ∑ i,|w i*(p i-a i)*(y i-ratio y p w)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i,γ*(u-l)*|p i-a i| := by
        apply Finset.sum_le_sum
        intro i _
        have hh := mul_le_mul (hw i).2 (habs i) (abs_nonneg _) hγ0
        have ht := mul_le_mul_of_nonneg_right hh (abs_nonneg (p i-a i))
        simpa [abs_mul,abs_of_pos (hwpos i),mul_assoc,mul_comm,mul_left_comm] using ht
      _ = _ := (Finset.mul_sum _ _ _).symm
  let K := (γ*(u-l)/(∑ i,a i))*(∑ i,|p i-a i|)
  have hE : 0 ≤ ∑ i,|p i-a i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hK : 0 ≤ K := mul_nonneg (div_nonneg (mul_nonneg hγ0 hR) haSum.le) hE
  have hKeq : K*(∑ i,a i) = γ*(u-l)*(∑ i,|p i-a i|) := by
    dsimp [K]; field_simp <;> ring
  rw [ratio_difference_masses y p a w hpD.ne' haD.ne',abs_div,abs_of_pos haD]
  apply (div_le_iff₀ haD).2
  calc
    _ ≤ γ*(u-l)*(∑ i,|p i-a i|) := hnum
    _ = K*(∑ i,a i) := hKeq.symm
    _ ≤ K*(∑ i,a i*w i) := mul_le_mul_of_nonneg_left hD hK

/-- T13(F3): maxima over the same feasible set change by at most a
uniform function error. The extrema are explicitly assumed attained. -/
theorem greatest_error_bound {ι : Type*} (B : Set ι) (f g : ι → ℝ) (F G ε : ℝ)
    (hf : IsGreatest (f '' B) F) (hg : IsGreatest (g '' B) G)
    (he : ∀ w ∈ B, |f w-g w| ≤ ε) : |F-G| ≤ ε := by
  obtain ⟨u,hu,rfl⟩ := hf.1
  obtain ⟨v,hv,rfl⟩ := hg.1
  have heu := abs_le.mp (he u hu)
  have hev := abs_le.mp (he v hv)
  have hfg := hf.2 (Set.mem_image_of_mem f hv)
  have hgf := hg.2 (Set.mem_image_of_mem g hu)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- T13(F3), lower counterpart: attained minima have the same error bound. -/
theorem least_error_bound {ι : Type*} (B : Set ι) (f g : ι → ℝ) (F G ε : ℝ)
    (hf : IsLeast (f '' B) F) (hg : IsLeast (g '' B) G)
    (he : ∀ w ∈ B, |f w-g w| ≤ ε) : |F-G| ≤ ε := by
  obtain ⟨u,hu,rfl⟩ := hf.1
  obtain ⟨v,hv,rfl⟩ := hg.1
  have heu := abs_le.mp (he u hu)
  have hev := abs_le.mp (he v hv)
  have hfg := hf.2 (Set.mem_image_of_mem f hv)
  have hgf := hg.2 (Set.mem_image_of_mem g hu)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- "W_j≡|Υ_j|/Π_j" (Section 3.2, p. 237) is feasible whenever the
integer class sizes and absolute totals are compatible (T15(a),(e)). -/
theorem actual_class_weights {J : ℕ} (m : Fin J → ℕ) (mass : Fin J → ℝ)
    (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) (hmass : ∀ j, 0 < mass j)
    (hc : absoluteCompatible α β mass m) :
    weightBox α β (fun j => (m j : ℝ)/mass j) := by
  have hβ : 0 < β := hα.trans_le hab
  intro j
  constructor
  · apply (div_le_div_iff₀ hβ (hmass j)).2
    simpa [mul_comm] using (hc j).2.2
  · apply (div_le_div_iff₀ (hmass j) hα).2
    simpa [mul_comm] using (hc j).2.1

/-- The identification identity μ=∑WΠy/∑WΠ with W=m/Π
(p. 237), an exact identity, not an asymptotic approximation (T15(a)). -/
theorem class_mean_ratio {J : ℕ} (y mass : Fin J → ℝ) (m : Fin J → ℕ)
    (hmass : ∀ j, mass j ≠ 0) :
    ratio y mass (fun j => (m j : ℝ)/mass j) = classMean y m := by
  simp only [ratio,classMean]
  simp_rw [mul_div_cancel₀ _ (hmass _)]

/-- Conditional only on limiting shares q, a population has unrestricted
positive integer class sizes m and an unknown positive absolute scale T.
The condition α m≤Tq≤βm is equivalent to per-unit marginal compatibility
by `one_class_compatibility` (T15). -/
def sharesCompatible {J : ℕ} (α β : ℝ) (q : Fin J → ℝ) (m : Fin J → ℕ) : Prop :=
  ∃ T : ℝ, 0 < T ∧ absoluteCompatible α β (fun j => T*q j) m

/-- Means of the compatible finite populations, with original N unrestricted
and only q retained (T15(b), corrected Proposition 2 first sentence). -/
def compatibleMeans {J : ℕ} (y q : Fin J → ℝ) (α β : ℝ) : Set ℝ :=
  {v | ∃ m : Fin J → ℕ, sharesCompatible α β q m ∧ classMean y m = v}

/-- The continuous population-proportion region C_γ(q) in T15(c):
nonnegative proportions sum to one and every selection ratio obeys γ. -/
def proportionRegion {J : ℕ} (q : Fin J → ℝ) (γ : ℝ) (r : Fin J → ℝ) : Prop :=
  (∀ j, 0 ≤ r j) ∧ (∑ j,r j)=1 ∧ ∀ j k, r j*q k ≤ γ*r k*q j

/-- Finite population proportions m_j/N, as used in the identification
argument on p. 237 and the corrected sharpness statement. -/
def classProportions {J : ℕ} (m : Fin J → ℕ) (j : Fin J) : ℝ :=
  (m j : ℝ)/(∑ k,(m k : ℝ))

/-- The proportions induced by a feasible class weight vector,
r_j=W_j q_j/∑W_k q_k (T15(c)). -/
def weightProportions {J : ℕ} (q W : Fin J → ℝ) (j : Fin J) : ℝ :=
  W j*q j/(∑ k,W k*q k)

/-- A vector has rational coordinates (T15(c)--(d)); no rationality is
imposed on q, γ, or outcomes in the sharp-infimum/supremum statement. -/
def rationalVector {J : ℕ} (r : Fin J → ℝ) : Prop := ∀ j, ∃ x : ℚ, (x:ℝ)=r j

/-- T15(a),(e): every compatible finite population mean is in (6)--(7).
This valid outer bound holds with shares only or retained absolute totals;
it does not assert sharpness for the richer information set. -/
theorem shares_outer_bound {J : ℕ} (hJ : 0 < J) (y q : Fin J → ℝ)
    (hy : StrictMono y) (hq : ∀ j, 0 < q j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1)
    (m : Fin J → ℕ) (hc : sharesCompatible α β q m) :
    lowerEndpoint y q α β ≤ classMean y m ∧ classMean y m ≤ upperEndpoint y q α β := by
  obtain ⟨T,hT,hcomp⟩ := hc
  have hm : ∀ j, 0 < T*q j := fun j => mul_pos hT (hq j)
  have hw := actual_class_weights m (fun j => T*q j) α β hα hab hm hcomp
  have he := class_mean_ratio y (fun j => T*q j) m (fun j => (hm j).ne')
  rw [ratio_scale_masses y q _ T hT.ne'] at he
  have hv : classMean y m ∈ attainable y q α β := ⟨_,hw,he⟩
  obtain ⟨kL,kH,_,_,_,_,_,_,hl,hh,el,eh,_⟩ :=
    corrected_weighted_bounds hJ y q hq hy.monotone α β hα hab hb1
  exact ⟨by rw [el]; exact hl.2 hv,by rw [eh]; exact hh.2 hv⟩

/-- The class total of a finite nonnegative mass vector, with class labels
cls (counts C_h for the pooled sample, Π for the limiting design). This is
the aggregation used in Supplement (B3)--(B4), p. 2. -/
def groupedMass {ι : Type*} [Fintype ι] {J : ℕ} (cls : ι → Fin J) (p : ι → ℝ) (j : Fin J) : ℝ :=
  ∑ i with cls i = j,p i

/-- Exact grouping of the weighted numerator by outcome class, independent
of probability and of optimization (T13(F1), T21(F1)). -/
theorem grouped_numerator {ι : Type*} [Fintype ι] {J : ℕ}
    (cls : ι → Fin J) (y : Fin J → ℝ) (p w : ι → ℝ) :
    (∑ j,(∑ i with cls i=j,p i*w i)*y j) = ∑ i,p i*w i*y (cls i) := by
  classical
  rw [show (∑ j,(∑ i with cls i=j,p i*w i)*y j) =
      ∑ j,∑ i with cls i=j,p i*w i*y (cls i) from by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]]
  exact Finset.sum_fiberwise _ cls _

/-- Giving a common class weight W_j to every unit in that class gives
exactly the class ratio with mass ∑_{cls i=j} p_i (Supplement (B3)). -/
theorem ratio_class_constant_weights {ι : Type*} [Fintype ι] {J : ℕ}
    (cls : ι → Fin J) (y W : Fin J → ℝ) (p : ι → ℝ) :
    ratio (fun i => y (cls i)) p (fun i => W (cls i)) =
      ratio y (groupedMass cls p) W := by
  classical
  have he (j : Fin J) : groupedMass cls p j*W j = ∑ i with cls i=j,p i*W (cls i) := by
    unfold groupedMass
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi; rw [(Finset.mem_filter.mp hi).2]
  simp only [ratio]
  simp_rw [he]
  rw [grouped_numerator,Finset.sum_fiberwise]

/-- The average of arbitrary feasible unit weights within a represented
outcome class is a feasible class weight. Absent classes are given weight
1, contributing zero. Thus the complete attainable sets agree, including
samples with unrepresented classes (T13(F1), T21(F1)). -/
theorem normalized_class_aggregation {ι : Type*} [Fintype ι] {J : ℕ}
    (cls : ι → Fin J) (y : Fin J → ℝ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (γ : ℝ) (hγ : 1 ≤ γ) :
    normAttainable (fun i => y (cls i)) p γ = normAttainable y (groupedMass cls p) γ := by
  classical
  ext z; constructor
  · rintro ⟨w,hw,hz⟩
    let A : Fin J → ℝ := groupedMass cls p
    let B : Fin J → ℝ := fun j => ∑ i with cls i=j,p i*w i
    have hA (j : Fin J) : 0 ≤ A j := Finset.sum_nonneg (fun i _ => hp i)
    have hAB (j : Fin J) : A j ≤ B j ∧ B j ≤ γ*A j := by
      constructor
      · apply Finset.sum_le_sum
        intro i _; simpa using mul_le_mul_of_nonneg_left (hw i).1 (hp i)
      · dsimp [A,B,groupedMass]
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _; simpa [mul_comm] using mul_le_mul_of_nonneg_left (hw i).2 (hp i)
    let W : Fin J → ℝ := fun j => if 0 < A j then B j/A j else 1
    have hW : normBox γ W := by
      intro j; dsimp [W]; split
      · rename_i hj
        constructor
        · apply (le_div_iff₀ hj).2; linarith [(hAB j).1]
        · exact (div_le_iff₀ hj).2 (hAB j).2
      · exact ⟨le_rfl,hγ⟩
    have hAW (j : Fin J) : A j*W j = B j := by
      dsimp [W]; split
      · rename_i hj
        field_simp
      · rename_i hj
        have hAz : A j = 0 := le_antisymm (le_of_not_gt hj) (hA j)
        have hBz : B j = 0 := by have hb := hAB j; rw [hAz] at hb; linarith
        simp [hAz,hBz]
    have he : ratio y A W = ratio (fun i => y (cls i)) p w := by
      simp only [ratio]
      simp_rw [hAW]
      rw [grouped_numerator,Finset.sum_fiberwise]
    exact ⟨W,hW,he.trans hz⟩
  · rintro ⟨W,hW,hz⟩
    refine ⟨fun i => W (cls i),fun i => hW (cls i),?_⟩
    rw [ratio_class_constant_weights]
    exact hz

/-- The grouping equality in the ORIGINAL probability box [1/β,1/α],
obtained by the exact scaling u=βw (T13(F1), T21(F1)). -/
theorem class_aggregation_box {ι : Type*} [Fintype ι] {J : ℕ}
    (cls : ι → Fin J) (y : Fin J → ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) :
    attainable (fun i => y (cls i)) p α β = attainable y (groupedMass cls p) α β := by
  rw [attainable_normalization _ _ α β hα hab,attainable_normalization _ _ α β hα hab]
  exact normalized_class_aggregation cls y p hp (β/α) ((le_div_iff₀ hα).2 (by linarith))

open MeasureTheory ProbabilityTheory Filter

/-- The finite design's probability mass function, with exactly its real
nonnegative probabilities and total mass one. This is the probability law
of one sample in Assumption 1 (p. 237). -/
def designPMF {ι κ : Type*} [Fintype κ] (d : FiniteDesign ι κ) : PMF κ :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (d.probability ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => d.nonnegative ω),d.total]
    norm_num)

/-- "For each h, a sample s_h is drawn ... according to the original
sampling design, independent of s_1,...,s_(h-1)" (Assumption 1, p. 237).
The sample path law is the canonical countable iid product of the actual
finite design law, not an arbitrary or zero measure. -/
def jointLaw {ι κ : Type*} [Fintype κ] [MeasurableSpace κ] (d : FiniteDesign ι κ) :
    Measure (ℕ → κ) := Measure.infinitePi (fun _ : ℕ => (designPMF d).toMeasure)

instance jointLaw_isProbability {ι κ : Type*} [Fintype κ] [MeasurableSpace κ]
    (d : FiniteDesign ι κ) : IsProbabilityMeasure (jointLaw d) := by
  unfold jointLaw
  infer_instance

/-- The canonical replication law satisfies Assumption 1: the coordinate
samples are independent, identically distributed copies of the finite law.
This lemma makes the nonvacuous probability model explicit. -/
theorem joint_replications_iid {ι κ : Type*} [Fintype κ] [MeasurableSpace κ]
    (d : FiniteDesign ι κ) :
    iIndepFun (fun r : ℕ => fun ω : ℕ → κ => ω r) (jointLaw d) ∧
    (∀ r : ℕ, (jointLaw d).map (fun ω : ℕ → κ => ω r) = (designPMF d).toMeasure) := by
  constructor
  · exact iIndepFun_infinitePi (X := fun _ (x : κ) => x) (fun _ => measurable_id)
  · intro r; exact Measure.infinitePi_map_eval _ r

/-- The empirical class totals P_(h,j)=C_(h,j)/h in Supplement (B4), p. 2.
`Fin h` indexes the h independent replicates (zero-based instead of 1-based). -/
def empiricalTotals {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (h : ℕ) (ω : ℕ → κ) (j : Fin J) : ℝ :=
  (∑ r : Fin h, classCount d cls j (ω r.val))/(h:ℝ)

/-- Membership indicator on the h replicated populations: I_(r,i)=1
exactly when i∈s_r. The finite pooled population is `Fin h × ι`, and all
probability is over `jointLaw d` (Assumption 1, p. 237). -/
def pooledIndicator {ι κ : Type*} [Fintype κ]
    (d : FiniteDesign ι κ) (h : ℕ) (ω : ℕ → κ) : Fin h × ι → ℝ := by
  classical
  exact fun ri => if ri.2 ∈ d.sample (ω ri.1.val) then 1 else 0

/-- The estimators μ̂ᴸ_h and μ̂ᴴ_h are exactly (3) and (2) on the pooled
sample S_h (Assumption 1, p. 237). Giving box weights also to unsampled
units adds zero contributions and has no effect on the extrema. If an
initial pooled sample is empty, the total real division convention assigns
zero; the theorems explicitly require eventual nonemptiness. -/
def pooledLower {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (y : Fin J → ℝ)
    (α β : ℝ) (h : ℕ) (ω : ℕ → κ) : ℝ :=
  lowerEndpoint (fun ri : Fin h × ι => y (cls ri.2)) (pooledIndicator d h ω) α β

/-- The estimator μ̂ᴴ_h is "computed from each S_h using (2)"
(Assumption 1, p. 237), on the actual pooled membership indicators. -/
def pooledUpper {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (y : Fin J → ℝ)
    (α β : ℝ) (h : ℕ) (ω : ℕ → κ) : ℝ :=
  upperEndpoint (fun ri : Fin h × ι => y (cls ri.2)) (pooledIndicator d h ω) α β

/-- The pooled sample S_h is nonempty (Assumption 1). -/
def pooledNonempty {ι κ : Type*} [Fintype κ]
    (d : FiniteDesign ι κ) (h : ℕ) (ω : ℕ → κ) : Prop :=
  ∃ r : Fin h, (d.sample (ω r.val)).Nonempty

/-- T13(F1), T21(F1): exact class aggregation at a fixed nonempty pooled
sample, including unrepresented classes. The attainable sets, hence the
maxima and minima of (2)--(3), coincide with those of f(W,P_h), (B3).
This includes classes absent from an initial sample, by assigning their
zero-contribution weight arbitrarily within the box. -/
theorem pooled_class_aggregation {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (y : Fin J → ℝ)
    (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) (h : ℕ) (hh : 0 < h)
    (ω : ℕ → κ) (hne : pooledNonempty d h ω) :
    attainable (fun ri : Fin h × ι => y (cls ri.2)) (pooledIndicator d h ω) α β =
      attainable y (empiricalTotals d cls h ω) α β := by
  classical
  have hp : ∀ ri : Fin h × ι,0 ≤ pooledIndicator d h ω ri := by
    intro ri; unfold pooledIndicator; split <;> norm_num
  have hC : groupedMass (fun ri : Fin h × ι => cls ri.2) (pooledIndicator d h ω) =
      fun j => ∑ r : Fin h,classCount d cls j (ω r.val) := by
    funext j
    unfold groupedMass
    rw [Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro r _
    unfold classCount pooledIndicator
    apply Finset.sum_congr rfl
    intro i _
    by_cases hj : cls i=j <;> by_cases hi : i ∈ d.sample (ω r.val) <;> simp [hj,hi]
  have hn : (h:ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have he (W : Fin J → ℝ) :
      ratio y (fun j => ∑ r : Fin h,classCount d cls j (ω r.val)) W =
        ratio y (empiricalTotals d cls h ω) W := by
    unfold empiricalTotals
    simp_rw [div_eq_mul_inv,mul_comm _ (h:ℝ)⁻¹]
    exact (ratio_scale_masses y _ W (h:ℝ)⁻¹ (inv_ne_zero hn)).symm
  rw [class_aggregation_box _ _ _ hp α β hα hab,hC]
  ext z; constructor
  · rintro ⟨W,hW,hz⟩; exact ⟨W,hW,(he W).symm.trans hz⟩
  · rintro ⟨W,hW,hz⟩; exact ⟨W,hW,(he W).trans hz⟩

/-- T13(F1), T21(F2): dividing all class counts by the positive replicate
number h leaves the fixed-class-weight objective μ_h(W) unchanged (B4). -/
theorem empirical_ratio_identity {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (y W : Fin J → ℝ)
    (h : ℕ) (hh : 0 < h) (ω : ℕ → κ) :
    ratio y (fun j => ∑ r : Fin h,classCount d cls j (ω r.val)) W =
      ratio y (empiricalTotals d cls h ω) W := by
  have hn : (h:ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  unfold empiricalTotals
  simp_rw [div_eq_mul_inv, mul_comm _ (h:ℝ)⁻¹]
  exact (ratio_scale_masses y _ W (h:ℝ)⁻¹ (inv_ne_zero hn)).symm

/-- T21(F4): for fixed positive W, f(W,p) is continuous at the strictly
positive class-total vector Π (Supplement (B4), p. 2). -/
theorem fixed_weight_continuity {J : ℕ} (hJ : 0 < J) (y mass W : Fin J → ℝ)
    (hmass : ∀ j, 0 < mass j) (hW : ∀ j, 0 < W j) :
    ContinuousAt (fun p : Fin J → ℝ => ratio y p W) mass := by
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  apply ContinuousAt.div
  · have hc : Continuous (fun p : Fin J → ℝ => ∑ j,p j*W j*y j) := by fun_prop
    exact hc.continuousAt
  · have hc : Continuous (fun p : Fin J → ℝ => ∑ j,p j*W j) := by fun_prop
    exact hc.continuousAt
  · exact (denominator_pos mass W hmass hW).ne'

/-- Counts in each replicate lie between zero and N. This supplies the
boundedness in T13(F4) and T21(F5), with arbitrary dependence inside a sample. -/
theorem class_count_bounded {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) (j : Fin J) (ω : κ) :
    0 ≤ classCount d cls j ω ∧ classCount d cls j ω ≤ Fintype.card ι := by
  classical
  constructor
  · apply Finset.sum_nonneg
    intro i _; split <;> norm_num
  · calc
      classCount d cls j ω ≤ ∑ _i : ι,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _; split <;> norm_num
      _ = Fintype.card ι := by simp

/-- Strong law for the actual iid class counts: P_(h,j) tends almost
surely to Π_j, simultaneously for all finitely many classes (Supplement
(B4), p. 2; T13(F4), T21(F5)). No limit theorem is assumed as a new axiom. -/
theorem empirical_totals_strong_law {ι κ : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] {J : ℕ}
    (d : FiniteDesign ι κ) (cls : ι → Fin J) :
    ∀ᵐ ω ∂jointLaw d, ∀ j : Fin J,
      Tendsto (fun h => empiricalTotals d cls h ω j) atTop (nhds (classTotal d cls j)) := by
  classical
  rw [ae_all_iff]
  intro j
  let X : ℕ → (ℕ → κ) → ℝ := fun r ω => classCount d cls j (ω r)
  have hm : Measurable (classCount d cls j) := measurable_of_finite _
  have hi := (joint_replications_iid d).1
  have he (r : ℕ) : IdentDistrib (fun ω : ℕ → κ => ω r) (fun x : κ => x)
      (jointLaw d) (designPMF d).toMeasure := by
    refine ⟨(measurable_pi_apply r).aemeasurable,measurable_id.aemeasurable,?_⟩
    change (jointLaw d).map (fun ω : ℕ → κ => ω r) = Measure.map id (designPMF d).toMeasure
    rw [Measure.map_id]
    exact (joint_replications_iid d).2 r
  have hx (r : ℕ) : IdentDistrib (X r) (classCount d cls j)
      (jointLaw d) (designPMF d).toMeasure := (he r).comp hm
  have hint : Integrable (X 0) (jointLaw d) := (hx 0).symm.integrable_snd .of_finite
  have hind : ∀ ⦃i k : ℕ⦄, i ≠ k → IndepFun (X i) (X k) (jointLaw d) := by
    intro i k hik
    exact (hi.indepFun hik).comp hm hm
  have hid : ∀ r, IdentDistrib (X r) (X 0) (jointLaw d) (jointLaw d) :=
    fun r => (hx r).trans (hx 0).symm
  have hmean : (∫ ω, X 0 ω ∂jointLaw d) = classTotal d cls j := by
    rw [(hx 0).integral_eq,PMF.integral_eq_sum]
    simp only [designPMF,PMF.ofFintype_apply,ENNReal.toReal_ofReal (d.nonnegative _),smul_eq_mul]
    exact expected_class_count d cls j
  have hs := strong_law_ae_real X hint hind hid
  rw [hmean] at hs
  filter_upwards [hs] with ω hω
  have hfn : (fun h => empiricalTotals d cls h ω j) =
      (fun h => (∑ r ∈ Finset.range h,X r ω)/(h:ℝ)) := by
    funext h
    unfold empiricalTotals
    rw [Fin.sum_univ_eq_sum_range (fun r => classCount d cls j (ω r)) h]
  rw [hfn]
  exact hω

/-- Positive class totals follow from positive inclusion probabilities
and nonempty outcome classes (Section 3.2, p. 237). -/
theorem class_totals_positive {N J : ℕ} {κ : Type*} [Fintype κ]
    (d : FiniteDesign (Fin N) κ) (cls : Fin N → Fin J)
    (hcls : Function.Surjective cls) (hπ : ∀ i,0 < inclusion d i) :
    ∀ j,0 < classTotal d cls j := by
  classical
  intro j
  apply Finset.sum_pos'
  · intro i _; exact (hπ i).le
  · obtain ⟨i,hi⟩ := hcls j
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,hπ i⟩

/-- The class box extrema are the minimum and maximum of the finitely
many threshold values, including ties of optimal cut values (T13). -/
theorem endpoints_as_finite_thresholds {J : ℕ} (hJ : 0 < J) (y p : Fin J → ℝ)
    (hy : StrictMono y) (hp : ∀ j,0 < p j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1) :
    letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
    lowerEndpoint y p α β = Finset.univ.inf' Finset.univ_nonempty (fun k : Fin J => lowerValue y p (β/α) k.val) ∧
    upperEndpoint y p α β = Finset.univ.sup' Finset.univ_nonempty (fun k : Fin J => upperValue y p (β/α) k.val) := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  obtain ⟨kL,kH,_,_,hl,hh,el,eh⟩ := corrected_proposition_two hJ y p hy hp α β hα hab hb1
  rw [attainable_normalization y p α β hα hab] at hl hh
  have hγ : 1 ≤ β/α := (le_div_iff₀ hα).2 (by linarith)
  have hL (k : Fin J) : normBox (β/α) (lowerWeights (n:=J) (β/α) k.val) := by
    intro i; dsimp [lowerWeights]; split <;> exact ⟨by linarith,by linarith⟩
  have hH (k : Fin J) : normBox (β/α) (upperWeights (n:=J) (β/α) k.val) := by
    intro i; dsimp [upperWeights]; split <;> exact ⟨by linarith,by linarith⟩
  rw [el,eh]
  constructor
  · apply le_antisymm
    · apply (Finset.le_inf'_iff _ _).2
      intro k _; exact hl.2 ⟨_,hL k,rfl⟩
    · exact Finset.inf'_le (fun k : Fin J => lowerValue y p (β/α) k.val) (Finset.mem_univ kL)
  · apply le_antisymm
    · exact Finset.le_sup' (fun k : Fin J => upperValue y p (β/α) k.val) (Finset.mem_univ kH)
    · apply (Finset.sup'_le_iff _ _).2
      intro k _; exact hh.2 ⟨_,hH k,rfl⟩

/-- Convergence of positive class-total vectors implies convergence of
both box extrema without any separation condition on a cut. This uses the
finite threshold representation and fixed-vertex continuity (T13(iv)). -/
theorem endpoints_tendsto {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ)
    (hy : StrictMono y) (hmass : ∀ j,0 < mass j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1) (p : ℕ → Fin J → ℝ)
    (ht : Tendsto p atTop (nhds mass)) :
    Tendsto (fun h => lowerEndpoint y (p h) α β) atTop (nhds (lowerEndpoint y mass α β)) ∧
    Tendsto (fun h => upperEndpoint y (p h) α β) atTop (nhds (upperEndpoint y mass α β)) := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  have hγp : 0 < β/α := div_pos (hα.trans_le hab) hα
  have hwpL (k : Fin J) : ∀ j,0 < lowerWeights (n:=J) (β/α) k.val j := by
    intro j; dsimp [lowerWeights]; split <;> positivity
  have hwpH (k : Fin J) : ∀ j,0 < upperWeights (n:=J) (β/α) k.val j := by
    intro j; dsimp [upperWeights]; split <;> positivity
  have hcl : ContinuousAt
      (fun p : Fin J → ℝ => Finset.univ.inf' Finset.univ_nonempty
        (fun k : Fin J => lowerValue y p (β/α) k.val)) mass := by
    apply ContinuousAt.finset_inf'_apply
    intro k _
    exact fixed_weight_continuity hJ y mass _ hmass (hwpL k)
  have hch : ContinuousAt
      (fun p : Fin J → ℝ => Finset.univ.sup' Finset.univ_nonempty
        (fun k : Fin J => upperValue y p (β/α) k.val)) mass := by
    apply ContinuousAt.finset_sup'_apply
    intro k _
    exact fixed_weight_continuity hJ y mass _ hmass (hwpH k)
  have hpos : ∀ᶠ h in atTop, ∀ j,0 < p h j := by
    rw [eventually_all]
    intro j
    exact (tendsto_pi_nhds.mp ht j).eventually (eventually_gt_nhds (hmass j))
  obtain ⟨el,eh⟩ := endpoints_as_finite_thresholds hJ y mass hy hmass α β hα hab hb1
  constructor
  · rw [el]
    apply (hcl.tendsto.comp ht).congr'
    filter_upwards [hpos] with h hh
    exact (endpoints_as_finite_thresholds hJ y (p h) hy hh α β hα hab hb1).1.symm
  · rw [eh]
    apply (hch.tendsto.comp ht).congr'
    filter_upwards [hpos] with h hh
    exact (endpoints_as_finite_thresholds hJ y (p h) hy hh α β hα hab hb1).2.symm

/-- T13(iv): Proposition 3 with Assumption 2 REMOVED. Any finite nonempty
population, strictly ordered distinct outcomes with nonempty classes, and
any sampling design with 0<α≤π_i≤β≤1 have almost-sure convergence of the
actual pooled-sample extrema to (6)--(7) under iid Brewer replication.
The proof uses Mathlib's strong law and continuity of the finite threshold
minimum/maximum; no separation assumption is needed. -/
theorem corrected_proposition_three {N J : ℕ} (hN : 0 < N) (hJ : 0 < J)
    {κ : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (d : FiniteDesign (Fin N) κ) (cls : Fin N → Fin J) (hcls : Function.Surjective cls)
    (y : Fin J → ℝ) (hy : StrictMono y) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1)
    (hπ : ∀ i, α ≤ inclusion d i ∧ inclusion d i ≤ β) :
    ∀ᵐ ω ∂jointLaw d,
      (∀ᶠ h in atTop, pooledNonempty d h ω) ∧
      Tendsto (fun h => pooledLower d cls y α β h ω) atTop
        (nhds (lowerEndpoint y (classTotal d cls) α β)) ∧
      Tendsto (fun h => pooledUpper d cls y α β h ω) atTop
        (nhds (upperEndpoint y (classTotal d cls) α β)) := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  have hmass : ∀ j,0 < classTotal d cls j :=
    class_totals_positive d cls hcls (fun i => hα.trans_le (hπ i).1)
  filter_upwards [empirical_totals_strong_law d cls] with ω hω
  have ht : Tendsto (fun h => empiricalTotals d cls h ω) atTop (nhds (classTotal d cls)) :=
    tendsto_pi_nhds.mpr hω
  have hend := endpoints_tendsto hJ y (classTotal d cls) hy hmass α β hα hab hb1
    (fun h => empiricalTotals d cls h ω) ht
  have hpos : ∀ᶠ h in atTop,0 < empiricalTotals d cls h ω ⟨0,hJ⟩ :=
    (hω ⟨0,hJ⟩).eventually (eventually_gt_nhds (hmass ⟨0,hJ⟩))
  have hne : ∀ᶠ h in atTop,pooledNonempty d h ω := by
    filter_upwards [hpos] with h hh
    by_contra hn
    unfold pooledNonempty at hn
    push_neg at hn
    have hx (r : Fin h) : d.sample (ω r.val) = ∅ := hn r
    simp [empiricalTotals,classCount,hx] at hh
  have heL : (fun h => lowerEndpoint y (empiricalTotals d cls h ω) α β) =ᶠ[atTop]
      (fun h => pooledLower d cls y α β h ω) := by
    filter_upwards [hne,eventually_gt_atTop 0] with h hn hh
    unfold pooledLower lowerEndpoint
    rw [pooled_class_aggregation d cls y α β hα hab h hh ω hn]
  have heH : (fun h => upperEndpoint y (empiricalTotals d cls h ω) α β) =ᶠ[atTop]
      (fun h => pooledUpper d cls y α β h ω) := by
    filter_upwards [hne,eventually_gt_atTop 0] with h hn hh
    unfold pooledUpper upperEndpoint
    rw [pooled_class_aggregation d cls y α β hα hab h hh ω hn]
  exact ⟨hne,hend.1.congr' heL,hend.2.congr' heH⟩

/-- T21 and T13(iii): printed Proposition 3, with hats restored and the
valid range of Assumption 2. Its almost-sure sufficient-condition conclusion
is stated about the actual pooled estimators and optimization endpoints,
not the false printed lower stopping rule. It follows from the stronger
corrected statement (p. 238). -/
theorem printed_proposition_three {N J : ℕ} (hN : 0 < N) (hJ : 0 < J)
    {κ : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (d : FiniteDesign (Fin N) κ) (cls : Fin N → Fin J) (hcls : Function.Surjective cls)
    (y : Fin J → ℝ) (hy : StrictMono y) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1)
    (hπ : ∀ i, α ≤ inclusion d i ∧ inclusion d i ≤ β)
    (hsep : separation y (classTotal d cls) (β/α)) :
    ∀ᵐ ω ∂jointLaw d,
      (∀ᶠ h in atTop, pooledNonempty d h ω) ∧
      Tendsto (fun h => pooledLower d cls y α β h ω) atTop
        (nhds (lowerEndpoint y (classTotal d cls) α β)) ∧
      Tendsto (fun h => pooledUpper d cls y α β h ω) atTop
        (nhds (upperEndpoint y (classTotal d cls) α β)) := by
  exact corrected_proposition_three hN hJ d cls hcls y hy α β hα hab hb1 hπ

/- P025-T7 and P025-T8: the universal printed assertions are stated and refuted
in AronowAudit.P025.P025_PrintedRefutations, by printed_proposition_one_refuted
and printed_proposition_two_formula_refuted. Their valid upper halves are
proved below by printed_proposition_one_upper and printed_proposition_two_upper. -/


/-- Compatible means when the absolute totals Π are retained, with N
unrestricted (T16(A); the richer reading of the printed sharpness claim). -/
def absoluteCompatibleMeans {J : ℕ} (y mass : Fin J → ℝ) (α β : ℝ) : Set ℝ :=
  {v | ∃ m : Fin J → ℕ, absoluteCompatible α β mass m ∧ classMean y m = v}

/- The absolute-information sharpness assertion is stated and refuted by
printed_sharpness_absolute_information_refuted in
AronowAudit.P025.P025_PrintedRefutations. The shares-only corrected statement
is shares_sharpness_and_attainment below. -/


/-- The three outcome classes (0,2,3) in T14. Each class has
two population units, represented as `Fin 3 × Fin 2`. -/
def threeOutcomes : Fin 3 → ℝ := ![0,2,3]

/-- One equally likely choice from each pair (T14). -/
def pairChoice (ω : Fin 2 × Fin 2 × Fin 2) : Fin 3 → Fin 2 := ![ω.1,ω.2.1,ω.2.2]

/-- The explicit eight-state finite sampling design of T14: independently
choose one of the two units in each of three classes, each state probability
1/8. Replication is under `jointLaw pairDesign`. -/
def pairDesign : FiniteDesign (Fin 3 × Fin 2) (Fin 2 × Fin 2 × Fin 2) where
  sample := fun ω => Finset.univ.image (fun j => (j,pairChoice ω j))
  probability := fun _ => 1/8
  nonnegative := fun _ => by norm_num
  total := by norm_num [Fintype.sum_prod_type,Fin.sum_univ_two]

/-- Membership in a pair sample is exactly the selected member of its
class; the class counts are deterministic even though unit identities vary. -/
theorem pair_membership (ω : Fin 2 × Fin 2 × Fin 2) (j : Fin 3) (b : Fin 2) :
    (j,b) ∈ pairDesign.sample ω ↔ b = pairChoice ω j := by
  simp [pairDesign,Prod.mk.injEq,eq_comm]

/-- T14(a): all six inclusion probabilities are 1/2, all class totals are
one, and every possible sample contains one unit in each class. -/
theorem pair_design_realizes_example :
    (∀ i : Fin 3 × Fin 2, inclusion pairDesign i = 1/2) ∧
    (∀ j : Fin 3, classTotal pairDesign Prod.fst j = 1) ∧
    (∀ ω : Fin 2 × Fin 2 × Fin 2, ∀ j : Fin 3, classCount pairDesign Prod.fst j ω = 1) := by
  have hi : ∀ i : Fin 3 × Fin 2, inclusion pairDesign i = 1/2 := by
    rintro ⟨j,b⟩; fin_cases j <;> fin_cases b <;>
      norm_num [inclusion,designExpectation,pair_membership,pairDesign,pairChoice,
        Fintype.sum_prod_type,Fin.sum_univ_two]
  refine ⟨hi,?_,?_⟩
  · intro j; unfold classTotal
    rw [Finset.sum_filter]
    simp only [Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two]
    fin_cases j <;> norm_num [hi]
  · rintro ⟨a,b,c⟩ j
    have hc0 : ((Finset.univ : Finset (Fin 2)).filter (fun x => x = 0)).card = 1 := by decide
    have hc1 : ((Finset.univ : Finset (Fin 2)).filter (fun x => x = 1)).card = 1 := by decide
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases j <;>
      norm_num [classCount,pair_membership,pairChoice,Fintype.sum_prod_type,
        Fin.sum_univ_three,Fin.sum_univ_two,hc0,hc1]

/-- Reindexing the actual pooled pair sample by replicate and class
leaves the Hajek ratio unchanged for EVERY real unit-weight vector (T14(d)).
Weights on unselected units have zero contribution. -/
theorem pair_pooled_ratio (h : ℕ) (ω : ℕ → Fin 2 × Fin 2 × Fin 2)
    (w : Fin h × (Fin 3 × Fin 2) → ℝ) :
    ratio (fun ri => threeOutcomes ri.2.1) (pooledIndicator pairDesign h ω) w =
      ratio (fun rj : Fin h × Fin 3 => threeOutcomes rj.2) (fun _ => 1)
        (fun rj => w (rj.1,(rj.2,pairChoice (ω rj.1.val) rj.2))) := by
  have hsum (r : Fin h) (f : Fin 3 × Fin 2 → ℝ) :
      (∑ i ∈ pairDesign.sample (ω r.val),f i) =
        ∑ j : Fin 3,f (j,pairChoice (ω r.val) j) := by
    change (∑ i ∈ Finset.univ.image (fun j => (j,pairChoice (ω r.val) j)),f i) = _
    apply Finset.sum_image
    intro i _ j _ hij
    exact congrArg Prod.fst hij
  have hterm (r : Fin h) (f : Fin 3 × Fin 2 → ℝ) :
      (∑ i,pooledIndicator pairDesign h ω (r,i)*f i) =
        ∑ j : Fin 3,f (j,pairChoice (ω r.val) j) := by
    simp only [pooledIndicator,ite_mul,one_mul,zero_mul,← Finset.sum_filter]
    simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter] using hsum r f
  have hnum : (∑ ri : Fin h × (Fin 3 × Fin 2),
      pooledIndicator pairDesign h ω ri*w ri*threeOutcomes ri.2.1) =
      ∑ rj : Fin h × Fin 3,w (rj.1,(rj.2,pairChoice (ω rj.1.val) rj.2))*threeOutcomes rj.2 := by
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro r _
    simpa only [mul_assoc] using hterm r (fun i => w (r,i)*threeOutcomes i.1)
  have hden : (∑ ri : Fin h × (Fin 3 × Fin 2),
      pooledIndicator pairDesign h ω ri*w ri) =
      ∑ rj : Fin h × Fin 3,w (rj.1,(rj.2,pairChoice (ω rj.1.val) rj.2)) := by
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro r _
    exact hterm r (fun i => w (r,i))
  simpa only [ratio,one_mul] using congrArg₂ (fun x y : ℝ => x/y) hnum hden

/-- The actual pooled pair-sample attainable set is exactly the attainable
set for h copies of each of the three outcomes. This equality covers the
whole continuous box, not only class-constant unit weights (T14(d)). -/
theorem pair_pooled_attainable (h : ℕ) (ω : ℕ → Fin 2 × Fin 2 × Fin 2) (α β : ℝ) :
    attainable (fun ri => threeOutcomes ri.2.1) (pooledIndicator pairDesign h ω) α β =
      attainable (fun rj : Fin h × Fin 3 => threeOutcomes rj.2) (fun _ => 1) α β := by
  ext z; constructor
  · rintro ⟨w,hw,hz⟩
    refine ⟨fun rj => w (rj.1,(rj.2,pairChoice (ω rj.1.val) rj.2)),?_,?_⟩
    · intro rj; exact hw _
    · rw [← pair_pooled_ratio]; exact hz
  · rintro ⟨u,hu,hz⟩
    refine ⟨fun ri => u (ri.1,ri.2.1),?_,?_⟩
    · intro ri; exact hu _
    · rw [pair_pooled_ratio]; exact hz

/-- T14(c): the exact class optimization extrema are 5/4 and 2 and
Assumption 2 fails at the valid cut k=1, where G⁺₁=y_(2)=2. -/
theorem nonseparation_class_extrema :
    IsLeast (attainable threeOutcomes (fun _ => 1) (1/4) (1/2)) (5/4) ∧
    IsGreatest (attainable threeOutcomes (fun _ => 1) (1/4) (1/2)) 2 ∧
    upperValue threeOutcomes (fun _ => 1) 2 1 = threeOutcomes 1 ∧
    ¬ separation threeOutcomes (fun _ => 1) 2 := by
  have hb (w : Fin 3 → ℝ) (hw : weightBox (1/4) (1/2) w) :
      5/4 ≤ ratio threeOutcomes (fun _ => 1) w ∧ ratio threeOutcomes (fun _ => 1) w ≤ 2 := by
    have h0 := hw 0; have h1 := hw 1; have h2 := hw 2
    norm_num at h0 h1 h2
    have hd : 0 < w 0+w 1+w 2 := by linarith
    norm_num [ratio,threeOutcomes,Fin.sum_univ_three]
    constructor
    · apply (le_div_iff₀ hd).2; nlinarith
    · apply (div_le_iff₀ hd).2; nlinarith
  have hs : upperValue threeOutcomes (fun _ => 1) 2 1 = threeOutcomes 1 := by
    norm_num [upperValue,ratio,upperWeights,threeOutcomes,Fin.sum_univ_three]
  refine ⟨⟨⟨![4,2,2],?_,?_⟩,?_⟩,⟨⟨![2,4,4],?_,?_⟩,?_⟩,hs,?_⟩
  · intro i; fin_cases i <;> norm_num
  · norm_num [ratio,threeOutcomes,Fin.sum_univ_three]
  · rintro z ⟨w,hw,rfl⟩; exact (hb w hw).1
  · intro i; fin_cases i <;> norm_num
  · norm_num [ratio,threeOutcomes,Fin.sum_univ_three]
  · rintro z ⟨w,hw,rfl⟩; exact (hb w hw).2
  · intro h; exact (h 1).1 hs.symm

/-- T14(d): for every positive integer h, the extremized ratio for h
units at each outcome 0,2,3 is exactly [5/4,2]. The proof compares sums
one replicate at a time and uses no large finite-type enumeration. -/
theorem three_replicate_extrema (h : ℕ) (hh : 0 < h) :
    lowerEndpoint (fun rj : Fin h × Fin 3 => threeOutcomes rj.2) (fun _ => 1) (1/4) (1/2) = 5/4 ∧
    upperEndpoint (fun rj : Fin h × Fin 3 => threeOutcomes rj.2) (fun _ => 1) (1/4) (1/2) = 2 := by
  letI : Nonempty (Fin h) := ⟨⟨0,hh⟩⟩
  have hn : (h:ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  let low : Fin h × Fin 3 → ℝ := fun rj => (![4,2,2] : Fin 3 → ℝ) rj.2
  let high : Fin h × Fin 3 → ℝ := fun rj => (![2,4,4] : Fin 3 → ℝ) rj.2
  have hl : weightBox (1/4) (1/2) low := by rintro ⟨r,j⟩; fin_cases j <;> norm_num [low]
  have hh' : weightBox (1/4) (1/2) high := by rintro ⟨r,j⟩; fin_cases j <;> norm_num [high]
  have hel : ratio (fun rj => threeOutcomes rj.2) (fun _ => 1) low = 5/4 := by
    norm_num [ratio,low,threeOutcomes,Fintype.sum_prod_type,Fin.sum_univ_three]
    field_simp <;> ring
  have heh : ratio (fun rj => threeOutcomes rj.2) (fun _ => 1) high = 2 := by
    norm_num [ratio,high,threeOutcomes,Fintype.sum_prod_type,Fin.sum_univ_three]
    field_simp <;> ring
  have hb (w : Fin h × Fin 3 → ℝ) (hw : weightBox (1/4) (1/2) w) :
      5/4 ≤ ratio (fun rj => threeOutcomes rj.2) (fun _ => 1) w ∧
      ratio (fun rj => threeOutcomes rj.2) (fun _ => 1) w ≤ 2 := by
    have hwp (ri : Fin h × Fin 3) : 0 < w ri := by have hi := (hw ri).1; norm_num at hi; linarith
    have hd := denominator_pos (fun _ => 1) w (fun _ => zero_lt_one) hwp
    constructor
    · apply (le_div_iff₀ hd).2
      simp only [one_mul,Fintype.sum_prod_type,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r _
      have h0 := hw (r,0); have h1 := hw (r,1); have h2 := hw (r,2)
      norm_num at h0 h1 h2
      norm_num [threeOutcomes,Fin.sum_univ_three]
      nlinarith
    · apply (div_le_iff₀ hd).2
      simp only [one_mul,Fintype.sum_prod_type,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r _
      have h0 := hw (r,0); have h1 := hw (r,1); have h2 := hw (r,2)
      norm_num at h0 h1 h2
      norm_num [threeOutcomes,Fin.sum_univ_three]
      nlinarith
  have hleast : IsLeast (attainable (fun rj : Fin h × Fin 3 => threeOutcomes rj.2) (fun _ => 1) (1/4) (1/2)) (5/4) := by
    refine ⟨⟨low,hl,hel⟩,?_⟩
    rintro z ⟨w,hw,rfl⟩; exact (hb w hw).1
  have hgreat : IsGreatest (attainable (fun rj : Fin h × Fin 3 => threeOutcomes rj.2) (fun _ => 1) (1/4) (1/2)) 2 := by
    refine ⟨⟨high,hh',heh⟩,?_⟩
    rintro z ⟨w,hw,rfl⟩; exact (hb w hw).2
  exact ⟨hleast.csInf_eq,hgreat.csSup_eq⟩

/-- T14(e): a valid random design violates Assumption 2 yet both actual
pooled estimators equal their limiting endpoints for every h≥1 on EVERY
sample path. Thus both converge on every path, establishing that Assumption
2 is unnecessary for convergence of the endpoint values (p. 238). -/
theorem assumption_two_not_necessary :
    (∀ i : Fin 3 × Fin 2, (1/4 : ℝ) ≤ inclusion pairDesign i ∧ inclusion pairDesign i ≤ 1/2) ∧
    ¬ separation threeOutcomes (classTotal pairDesign Prod.fst) 2 ∧
    lowerEndpoint threeOutcomes (classTotal pairDesign Prod.fst) (1/4) (1/2) = 5/4 ∧
    upperEndpoint threeOutcomes (classTotal pairDesign Prod.fst) (1/4) (1/2) = 2 ∧
    (∀ ω : ℕ → Fin 2 × Fin 2 × Fin 2, ∀ h : ℕ, 0 < h →
      pooledLower pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω = 5/4 ∧
      pooledUpper pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω = 2) ∧
    (∀ ω : ℕ → Fin 2 × Fin 2 × Fin 2,
      Tendsto (fun h => pooledLower pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω) atTop (nhds (5/4)) ∧
      Tendsto (fun h => pooledUpper pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω) atTop (nhds 2)) := by
  obtain ⟨hi,hclass,_⟩ := pair_design_realizes_example
  obtain ⟨hl,hh,_,hsep⟩ := nonseparation_class_extrema
  have hc : classTotal pairDesign Prod.fst = fun _ => 1 := funext hclass
  have he (ω : ℕ → Fin 2 × Fin 2 × Fin 2) (h : ℕ) (hpos : 0 < h) :
      pooledLower pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω = 5/4 ∧
      pooledUpper pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω = 2 := by
    unfold pooledLower pooledUpper lowerEndpoint upperEndpoint
    rw [pair_pooled_attainable]
    exact three_replicate_extrema h hpos
  refine ⟨?_,by simpa [hc] using hsep,by simpa [hc,lowerEndpoint] using hl.csInf_eq,
    by simpa [hc,upperEndpoint] using hh.csSup_eq,he,?_⟩
  · intro i; rw [hi]; norm_num
  · intro ω
    have el : (fun h => pooledLower pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω) =ᶠ[atTop] (fun _ => (5/4:ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with h hh
      exact (he ω h hh).1
    have eh : (fun h => pooledUpper pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω) =ᶠ[atTop] (fun _ => (2:ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with h hh
      exact (he ω h hh).2
    exact ⟨(tendsto_congr' el).2 tendsto_const_nhds,(tendsto_congr' eh).2 tendsto_const_nhds⟩

/-- T1(g), T2(h): for ANY sorted nonempty sample or positive class totals,
the printed ≥ lower stopping rule always selects zero (pp. 236,238).
This is a general diagnosis, not only the concrete two-unit counterexample. -/
theorem printed_lower_rule_always_zero {n : ℕ} (hn : 0 < n)
    (y a : Fin n → ℝ) (hy : Monotone y) (ha : ∀ i, 0 < a i) (γ : ℝ) :
    printedLowerCut y a γ ⟨0,hn⟩ := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  constructor
  · have h := le_ratio y a (fun _ => 1) ha (fun _ => zero_lt_one) (y ⟨0,hn⟩)
      (fun i => hy (Fin.zero_le i))
    have hw : lowerWeights (n:=n) γ 0 = fun _ => 1 := by
      funext i; simp [lowerWeights]
    change y ⟨0,hn⟩ ≤ lowerValue y a γ 0
    simpa only [lowerValue,hw] using h
  · intro j _; exact Fin.zero_le j

/-- T1(g), T2(h): with γ>1 and at least one outcome strictly above the
first, changing only the first normalized weight from 1 to γ strictly
lowers the objective. Thus the printed all-equal lower vector is not optimal. -/
theorem printed_lower_vector_not_optimal {n : ℕ} (hn : 0 < n)
    (y a : Fin n → ℝ) (hy : Monotone y) (ha : ∀ i, 0 < a i)
    (γ : ℝ) (hγ : 1 < γ) (hvar : ∃ i, y ⟨0,hn⟩ < y i) :
    lowerValue y a γ 1 < lowerValue y a γ 0 ∧
    ¬ IsLeast (normAttainable y a γ) (lowerValue y a γ 0) := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let z : Fin n := ⟨0,hn⟩
  have hg : 0 < γ := by linarith
  have hsum : 0 < ∑ i,a i*(y i-y z) := by
    apply Finset.sum_pos'
    · intro i _; exact mul_nonneg (ha i).le (sub_nonneg.mpr (hy (Fin.zero_le i)))
    · obtain ⟨i,hi⟩ := hvar
      exact ⟨i,Finset.mem_univ _,mul_pos (ha i) (sub_pos.mpr hi)⟩
  have hd : 0 < ∑ i,a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hmean : y z < lowerValue y a γ 0 := by
    simp only [lowerValue,ratio,lowerWeights,Nat.not_lt_zero,ite_false,mul_one]
    apply (lt_div_iff₀ hd).2
    simp_rw [mul_sub] at hsum
    rw [Finset.sum_sub_distrib,← Finset.sum_mul] at hsum
    nlinarith
  have hinc := threshold_increment hn a y ha γ 1 hg zero_lt_one z
  have hden : 0 < ∑ i,a i*threshold γ 1 (z.val+1) i := by
    apply denominator_pos _ _ ha
    intro i; dsimp [threshold]; split <;> positivity
  have hdec : lowerValue y a γ 1 < lowerValue y a γ 0 := by
    apply sub_neg.mp
    change ratio y a (threshold γ 1 (z.val+1)) - ratio y a (threshold γ 1 z.val) < 0
    rw [hinc]
    apply div_neg_of_neg_of_pos _ hden
    exact mul_neg_of_pos_of_neg (mul_pos (sub_pos.mpr hγ) (ha z)) (sub_neg.mpr hmean)
  refine ⟨hdec,?_⟩
  intro hm
  have hw : normBox γ (lowerWeights (n:=n) γ 1) := by
    intro i; dsimp [lowerWeights]; split <;> exact ⟨by linarith,by linarith⟩
  have ht := hm.2 (show lowerValue y a γ 1 ∈ normAttainable y a γ from ⟨_,hw,rfl⟩)
  linarith

/-- T1(f): the true attainable range [1/3,2/3] is strictly larger than
the printed [1/2,2/3] in the sample counterexample (equation (5), p. 236). -/
theorem sample_counterexample_range :
    attainable binaryTwo (fun _ => 1) (1/2) 1 = Set.Icc (1/3) (2/3) ∧
    (1/3 : ℝ) ∉ Set.Icc (1/2) (2/3) := by
  have hy : ∀ i : Fin 2, binaryTwo i = 0 ∨ binaryTwo i = 1 := by
    intro i; fin_cases i <;> norm_num [binaryTwo]
  have hr := dichotomous_closed_form (by norm_num) binaryTwo hy (1/2) 1
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [binaryLower,binaryUpper,populationMean,binaryTwo,Fin.sum_univ_two] at hr
  exact ⟨hr,by norm_num⟩

/-- T16(A)(ii), T16(B)(i): exact global extrema over the continuous
probability-weight boxes. These are certified over all REAL weights,
not inferred from evaluating two vertices. -/
theorem sharpness_counterexample_box_extrema :
    IsLeast (attainable binaryTwo ![2/3,4/3] (1/2) (3/4)) (4/7) ∧
    IsGreatest (attainable binaryTwo ![2/3,4/3] (1/2) (3/4)) (3/4) ∧
    IsLeast (attainable binaryTwo ![50,100] (1/10) (1/5)) (1/2) ∧
    IsGreatest (attainable binaryTwo ![50,100] (1/10) (1/5)) (4/5) := by
  have ha (w : Fin 2 → ℝ) (hw : weightBox (1/2) (3/4) w) :
      4/7 ≤ ratio binaryTwo ![2/3,4/3] w ∧ ratio binaryTwo ![2/3,4/3] w ≤ 3/4 := by
    have h0 := hw 0; have h1 := hw 1
    norm_num at h0 h1
    have hd : 0 < (2/3:ℝ)*w 0+(4/3)*w 1 := by linarith
    norm_num [ratio,binaryTwo,Fin.sum_univ_two]
    constructor
    · apply (le_div_iff₀ hd).2; nlinarith
    · apply (div_le_iff₀ hd).2; nlinarith
  have hb (w : Fin 2 → ℝ) (hw : weightBox (1/10) (1/5) w) :
      1/2 ≤ ratio binaryTwo ![50,100] w ∧ ratio binaryTwo ![50,100] w ≤ 4/5 := by
    have h0 := hw 0; have h1 := hw 1
    norm_num at h0 h1
    have hd : 0 < (50:ℝ)*w 0+100*w 1 := by linarith
    norm_num [ratio,binaryTwo,Fin.sum_univ_two]
    constructor
    · apply (le_div_iff₀ hd).2; nlinarith
    · apply (div_le_iff₀ hd).2; nlinarith
  refine ⟨⟨⟨![2,4/3],?_,?_⟩,?_⟩,⟨⟨![4/3,2],?_,?_⟩,?_⟩,
    ⟨⟨![10,5],?_,?_⟩,?_⟩,⟨⟨![5,10],?_,?_⟩,?_⟩⟩
  · intro i; fin_cases i <;> norm_num
  · norm_num [ratio,binaryTwo,Fin.sum_univ_two]
  · rintro z ⟨w,hw,rfl⟩; exact (ha w hw).1
  · intro i; fin_cases i <;> norm_num
  · norm_num [ratio,binaryTwo,Fin.sum_univ_two]
  · rintro z ⟨w,hw,rfl⟩; exact (ha w hw).2
  · intro i; fin_cases i <;> norm_num
  · norm_num [ratio,binaryTwo,Fin.sum_univ_two]
  · rintro z ⟨w,hw,rfl⟩; exact (hb w hw).1
  · intro i; fin_cases i <;> norm_num
  · norm_num [ratio,binaryTwo,Fin.sum_univ_two]
  · rintro z ⟨w,hw,rfl⟩; exact (hb w hw).2

/-- T16(A)(iv): with absolute class totals retained, the EXACT set of
compatible finite-population means is {2/3}, and neither printed box
endpoint is a sharp infimum/supremum for that information set. -/
theorem integrality_mean_set_and_gaps :
    absoluteCompatibleMeans binaryTwo ![2/3,4/3] (1/2) (3/4) = {(2/3:ℝ)} ∧
    ¬ IsGLB (absoluteCompatibleMeans binaryTwo ![2/3,4/3] (1/2) (3/4)) (4/7) ∧
    ¬ IsLUB (absoluteCompatibleMeans binaryTwo ![2/3,4/3] (1/2) (3/4)) (3/4) := by
  have hm := integrality_sharpness_counterexample.1
  have hmean := integrality_sharpness_counterexample.2.1
  have hs : absoluteCompatibleMeans binaryTwo ![2/3,4/3] (1/2) (3/4) = {(2/3:ℝ)} := by
    ext z; constructor
    · rintro ⟨m,hc,rfl⟩; rw [(hm m).1 hc]; exact hmean
    · intro hz; have hz' : z = (2/3:ℝ) := hz
      exact ⟨![1,2],(hm _).2 rfl,hmean.trans hz'.symm⟩
  refine ⟨hs,?_,?_⟩
  · rw [hs]; intro h
    have hb : (2/3:ℝ) ∈ lowerBounds {(2/3:ℝ)} := by intro x hx; have he : x = (2/3:ℝ) := hx; rw [he]
    have he := h.2 hb; norm_num at he
  · rw [hs]; intro h
    have hb : (2/3:ℝ) ∈ upperBounds {(2/3:ℝ)} := by intro x hx; have he : x = (2/3:ℝ) := hx; rw [he]
    have he := h.2 hb; norm_num at he

/-- The valid upper half of printed Proposition 1, separate from its false
printed lower rule (T7). The vector's weights are exactly 1/β or 1/α. -/
theorem printed_proposition_one_upper {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : Monotone y) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1) :
    ∃ kH : Fin n, upperCut y (fun _ => 1) (β/α) kH ∧
      IsGreatest (attainable y (fun _ => 1) α β) (upperValue y (fun _ => 1) (β/α) kH.val) := by
  obtain ⟨_,kH,_,hH,_,hg,_⟩ := corrected_proposition_one hn y hy α β hα hab hb1
  exact ⟨kH,hH,hg⟩

/-- The valid upper half of printed Proposition 2, separately certified
for arbitrary positive class totals and strictly ordered outcomes (T8). -/
theorem printed_proposition_two_upper {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ)
    (hy : StrictMono y) (hmass : ∀ j, 0 < mass j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1) :
    ∃ kH : Fin J, upperCut y mass (β/α) kH ∧
      IsGreatest (attainable y mass α β) (upperValue y mass (β/α) kH.val) ∧
      upperEndpoint y mass α β = upperValue y mass (β/α) kH.val := by
  obtain ⟨_,kH,_,hH,_,hg,_,eh⟩ := corrected_proposition_two hJ y mass hy hmass α β hα hab hb1
  exact ⟨kH,hH,hg,eh⟩

/-- T9(c): the printed tail includes exactly the two extra classes
k-1 and k. This finite identity records the overlap independently of the
choice of an optimal cut. -/
theorem printed_tail_overlap {J : ℕ} (f : Fin J → ℝ) (k : ℕ)
    (hk2 : 2 ≤ k) (hkJ : k ≤ J) :
    (∑ i with k-2 ≤ i.val,f i) = (∑ i with k ≤ i.val,f i) +
      f ⟨k-2,by omega⟩ + f ⟨k-1,by omega⟩ := by
  classical
  let u : Fin J := ⟨k-2,by omega⟩
  let v : Fin J := ⟨k-1,by omega⟩
  have huv : u ≠ v := by intro h; have := congrArg Fin.val h; dsimp [u,v] at this; omega
  have he (i : Fin J) : (if k-2 ≤ i.val then f i else 0) =
      (if k ≤ i.val then f i else 0) + (if i=u then f i else 0) + (if i=v then f i else 0) := by
    by_cases hi : k ≤ i.val
    · have hu : i ≠ u := by intro h; have := congrArg Fin.val h; dsimp [u] at this; omega
      have hv : i ≠ v := by intro h; have := congrArg Fin.val h; dsimp [v] at this; omega
      simp [hi,hu,hv,show k-2 ≤ i.val by omega]
    · by_cases hu : i=u
      · subst i; simp [u,v,huv,hi,show k-2 ≤ k-2 by omega]
      · by_cases hv : i=v
        · subst i; simp [u,v,hu,hi,show k-2 ≤ k-1 by omega]
        · have hun : i.val ≠ k-2 := by intro h; apply hu; exact Fin.ext h
          have hvn : i.val ≠ k-1 := by intro h; apply hv; exact Fin.ext h
          simp [hi,hu,hv,show ¬ k-2 ≤ i.val by omega]
  rw [Finset.sum_filter,Finset.sum_filter]
  simp_rw [he,Finset.sum_add_distrib]
  simp [u,v]

/-- Exact algebra for the difference caused by two duplicated classes
(T9(c)). Denominators are explicitly nonzero. -/
theorem duplicated_classes_difference (N D a b x z : ℝ)
    (hD : D ≠ 0) (hD' : D+a+b ≠ 0) :
    (N+a*x+b*z)/(D+a+b)-N/D =
      (a*(x-N/D)+b*(z-N/D))/(D+a+b) := by
  field_simp
  <;> ring

/-- T9(c): the literal printed expression is the correctly partitioned
numerator/denominator augmented by classes k-1,k. The residual formula
gives its exact deviation from the corrected threshold ratio. The cases
k=0,1 have no literal class-index value (p. 237). -/
theorem printed_partition_discrepancy {J : ℕ} (hJ : 0 < J) (y a : Fin J → ℝ)
    (ha : ∀ j,0 < a j) (γ : ℝ) (hγ : 0 < γ) (k : ℕ)
    (hk2 : 2 ≤ k) (hkJ : k ≤ J) :
    let u : Fin J := ⟨k-2,by omega⟩
    let v : Fin J := ⟨k-1,by omega⟩
    let N := γ*(∑ i with i.val < k,a i*y i)+(∑ i with k ≤ i.val,a i*y i)
    let D := γ*(∑ i with i.val < k,a i)+(∑ i with k ≤ i.val,a i)
    printedLowerExpression y a γ k = some ((N+a u*y u+a v*y v)/(D+a u+a v)) ∧
    (N+a u*y u+a v*y v)/(D+a u+a v)-lowerValue y a γ k =
      (a u*(y u-lowerValue y a γ k)+a v*(y v-lowerValue y a γ k))/(D+a u+a v) ∧
    printedLowerExpression y a γ 0 = none ∧ printedLowerExpression y a γ 1 = none := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  dsimp only
  let N := γ*(∑ i with i.val < k,a i*y i)+(∑ i with k ≤ i.val,a i*y i)
  let D := γ*(∑ i with i.val < k,a i)+(∑ i with k ≤ i.val,a i)
  have he : lowerValue y a γ k = N/D := by
    change ratio y a (threshold γ 1 k) = N/D
    simpa [N,D] using threshold_partition y a γ 1 k
  have hd : 0 < D := by
    have h := denominator_pos a (threshold γ 1 k) ha (by intro i; dsimp [threshold]; split <;> positivity)
    have hp := threshold_partition (fun _ : Fin J => 1) a γ 1 k
    have heD : (∑ i,a i*threshold γ 1 k i) = D := by
      simp only [threshold,mul_ite,mul_one]
      rw [Finset.sum_ite]
      simp [D,Finset.sum_mul,Finset.mul_sum,mul_comm,not_lt]
    rwa [heD] at h
  refine ⟨?_,?_,by norm_num [printedLowerExpression],by norm_num [printedLowerExpression]⟩
  · unfold printedLowerExpression
    rw [if_pos ⟨hk2,hkJ⟩,printed_tail_overlap (fun i => a i*y i) k hk2 hkJ,
      printed_tail_overlap a k hk2 hkJ]
    congr 1 <;> ring
  · rw [he]
    apply duplicated_classes_difference
    · exact hd.ne'
    · have h1 := ha ⟨k-2,by omega⟩; have h2 := ha ⟨k-1,by omega⟩
      positivity

/-- T15(e): with absolute totals retained, compatible class sizes are
EXACTLY positive integers in [Π_j/β,Π_j/α]. Known N additionally fixes
the sum, as represented by knownSizeCompatibleMeans below. -/
theorem absolute_integer_calibration {J : ℕ} (mass : Fin J → ℝ) (m : Fin J → ℕ)
    (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) :
    absoluteCompatible α β mass m ↔
      ∀ j,0 < m j ∧ mass j/β ≤ (m j:ℝ) ∧ (m j:ℝ) ≤ mass j/α := by
  have hβ : 0 < β := hα.trans_le hab
  constructor
  · intro hm j
    refine ⟨(hm j).1,?_,?_⟩
    · apply (div_le_iff₀ hβ).2; simpa [mul_comm] using (hm j).2.2
    · apply (le_div_iff₀ hα).2; simpa [mul_comm] using (hm j).2.1
  · intro hm j
    refine ⟨(hm j).1,?_,?_⟩
    · simpa [mul_comm] using (le_div_iff₀ hα).1 (hm j).2.2
    · simpa [mul_comm] using (div_le_iff₀ hβ).1 (hm j).2.1

/-- T15(a),(e): every population compatible with retained absolute totals
lies in the continuous optimization interval. This is an outer bound;
no claim of integer endpoint attainment is made (p. 237, corrected sharpness). -/
theorem absolute_outer_bound {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ)
    (hy : StrictMono y) (hmass : ∀ j,0 < mass j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1) (m : Fin J → ℕ)
    (hm : absoluteCompatible α β mass m) :
    lowerEndpoint y mass α β ≤ classMean y m ∧ classMean y m ≤ upperEndpoint y mass α β := by
  obtain ⟨_,_,_,_,hl,hh,el,eh⟩ := corrected_proposition_two hJ y mass hy hmass α β hα hab hb1
  have hw := actual_class_weights m mass α β hα hab hmass hm
  have he := class_mean_ratio y mass m (fun j => (hmass j).ne')
  have hz : classMean y m ∈ attainable y mass α β := ⟨_,hw,he⟩
  rw [el,eh]
  exact ⟨hl.2 hz,hh.2 hz⟩

/-- Compatible means conditional on the known original population size
N as well as absolute class totals (T16(B)). -/
def knownSizeCompatibleMeans {J : ℕ} (y mass : Fin J → ℝ) (α β : ℝ) (N : ℕ) : Set ℝ :=
  {v | ∃ m : Fin J → ℕ,absoluteCompatible α β mass m ∧ (∑ j,m j)=N ∧ classMean y m=v}

/-- T16(B)(iii): the EXACT compatible mean set with N=1000 is
{k/1000 : k integer,500≤k≤750}; its extrema are 1/2 and 3/4.
The greatest compatible mean is strictly below μ_+=4/5. -/
theorem known_size_mean_set_and_gap :
    knownSizeCompatibleMeans binaryTwo ![50,100] (1/10) (1/5) 1000 =
      {v | ∃ k : ℕ,500 ≤ k ∧ k ≤ 750 ∧ (k:ℝ)/1000=v} ∧
    IsLeast (knownSizeCompatibleMeans binaryTwo ![50,100] (1/10) (1/5) 1000) (1/2) ∧
    IsGreatest (knownSizeCompatibleMeans binaryTwo ![50,100] (1/10) (1/5) 1000) (3/4) ∧
    upperEndpoint binaryTwo ![50,100] (1/10) (1/5) - (3/4) = 1/20 := by
  have hm := known_size_sharpness_counterexample.1
  have he (m : Fin 2 → ℕ) (hs : m 0+m 1=1000) : classMean binaryTwo m = (m 1:ℝ)/1000 := by
    have hsr : (m 0:ℝ)+(m 1:ℝ)=1000 := by exact_mod_cast hs
    simp [classMean,binaryTwo,Fin.sum_univ_two,hsr]
  have hs : knownSizeCompatibleMeans binaryTwo ![50,100] (1/10) (1/5) 1000 =
      {v | ∃ k : ℕ,500 ≤ k ∧ k ≤ 750 ∧ (k:ℝ)/1000=v} := by
    ext v; constructor
    · rintro ⟨m,hc,hN,hv⟩
      have hN' : m 0+m 1=1000 := by simpa [Fin.sum_univ_two] using hN
      obtain ⟨_,hl,hu⟩ := (hm m).1 ⟨hc,hN'⟩
      exact ⟨m 1,hl,hu,(he m hN').symm.trans hv⟩
    · rintro ⟨k,hl,hu,hv⟩
      have hN : 1000-k+k=1000 := by omega
      have hc := known_size_sharpness_counterexample.2.1 k hl hu
      refine ⟨![1000-k,k],hc,?_,?_⟩
      · simpa [Fin.sum_univ_two] using hN
      · exact (he ![1000-k,k] (by simpa using hN)).trans (by simpa using hv)
  refine ⟨hs,?_,?_,?_⟩
  · rw [hs]
    refine ⟨⟨500,by norm_num,by norm_num,by norm_num⟩,?_⟩
    rintro v ⟨k,hl,hu,rfl⟩
    have hkr : (500:ℝ) ≤ k := by exact_mod_cast hl
    linarith
  · rw [hs]
    refine ⟨⟨750,by norm_num,by norm_num,by norm_num⟩,?_⟩
    rintro v ⟨k,hl,hu,rfl⟩
    have hkr : (k:ℝ) ≤ 750 := by exact_mod_cast hu
    linarith
  · rw [show upperEndpoint binaryTwo ![50,100] (1/10) (1/5) = 4/5 from
      sharpness_counterexample_box_extrema.2.2.2.csSup_eq]
    norm_num

/-- T18(b): when γ=1, the original probability-weight box is a single
constant vector and both endpoint estimators equal the unweighted mean
(p. 236). This makes the point-box assertion explicit. -/
theorem equal_probability_box_and_endpoints {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1) (hγ : β/α=1) :
    (∀ w : Fin n → ℝ,weightBox α β w ↔ w=fun _ => 1/α) ∧
    lowerEndpoint y (fun _ => 1) α β = populationMean y ∧
    upperEndpoint y (fun _ => 1) α β = populationMean y := by
  have hba : β=α := (div_eq_one_iff_eq hα.ne').1 hγ
  have hs := (ratio_only_and_equal_probabilities hn y α β α β hα hab hb1 hα hab hb1 rfl).2 hγ
  refine ⟨?_,?_,?_⟩
  · intro w
    rw [hba]
    constructor
    · intro hw; funext i; exact le_antisymm (hw i).2 (hw i).1
    · intro hw; subst w; intro i; exact ⟨le_rfl,le_rfl⟩
  · simp [lowerEndpoint,hs]
  · simp [upperEndpoint,hs]

/-- T9(b): at the corrected first lower cut, the minimum (7) equals
the disjoint-prefix/tail display, whose second sums begin at k+1.
This theorem states the corrected display for the specified cut itself. -/
theorem corrected_lower_display_at_cut {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ)
    (hy : StrictMono y) (hmass : ∀ j,0 < mass j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (k : Fin J)
    (hk : lowerCut y mass (β/α) k) :
    lowerEndpoint y mass α β =
      ((β/α)*(∑ j with j.val < k.val,mass j*y j)+(∑ j with k.val ≤ j.val,mass j*y j)) /
      ((β/α)*(∑ j with j.val < k.val,mass j)+(∑ j with k.val ≤ j.val,mass j)) := by
  have hγ : 1 ≤ β/α := (le_div_iff₀ hα).2 (by linarith)
  have hw : normBox (β/α) (lowerWeights (n:=J) (β/α) k.val) := by
    intro j; dsimp [lowerWeights]; split <;> exact ⟨by linarith,by linarith⟩
  have hl : IsLeast (normAttainable y mass (β/α)) (lowerValue y mass (β/α) k.val) := by
    refine ⟨⟨_,hw,rfl⟩,?_⟩
    rintro z ⟨w,hw',rfl⟩
    exact lower_threshold_optimal hJ mass y hmass hy.monotone (β/α) hγ k hk w hw'
  rw [← attainable_normalization y mass α β hα hab] at hl
  rw [lowerEndpoint,hl.csInf_eq]
  change ratio y mass (threshold (β/α) 1 k.val) = _
  simpa using threshold_partition y mass (β/α) 1 k.val

/-- T21(F3): the two strict neighboring inequalities in Supplement p. 2
force the first upper cut to be exactly k*, and its threshold attains the
whole-box maximum. At k*=0 only the current strict inequality is required. -/
theorem upper_cut_from_strict_neighbors {J : ℕ} (hJ : 0 < J) (y p : Fin J → ℝ)
    (hy : StrictMono y) (hp : ∀ j,0 < p j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1) (k : Fin J)
    (hprev : ∀ hk : 0 < k.val,
      y ⟨k.val-1,by omega⟩ < upperValue y p (β/α) (k.val-1))
    (hnext : upperValue y p (β/α) k.val < y k) :
    upperCut y p (β/α) k ∧
      IsGreatest (attainable y p α β) (upperValue y p (β/α) k.val) := by
  obtain ⟨_,r,_,hr,_,hh,_,_⟩ := corrected_proposition_two hJ y p hy hp α β hα hab hb1
  have hγ : 1 ≤ β/α := (le_div_iff₀ hα).2 (by linarith)
  have hγp : 0 < β/α := div_pos (hα.trans_le hab) hα
  have hrk : r ≤ k := hr.2 hnext.le
  have hkr : k ≤ r := by
    by_contra hn
    have hlt : r.val < k.val := lt_of_not_ge hn
    have hkp : 0 < k.val := by omega
    let prev : Fin J := ⟨k.val-1,by have := k.isLt; omega⟩
    have hs := threshold_separator hJ p y hp hy.monotone 1 (β/α) zero_lt_one hγp r hr
    have hbound : upperValue y p (β/α) r.val ≤ y prev := hs.2 prev (by dsimp [prev]; omega)
    have hw : normBox (β/α) (upperWeights (n:=J) (β/α) prev.val) := by
      intro j; dsimp [upperWeights]; split <;> exact ⟨by linarith,by linarith⟩
    have hhn := hh
    rw [attainable_normalization y p α β hα hab] at hhn
    have hmax : upperValue y p (β/α) prev.val ≤ upperValue y p (β/α) r.val :=
      hhn.2 ⟨_,hw,rfl⟩
    have hfail := hprev hkp
    change y prev < upperValue y p (β/α) prev.val at hfail
    linarith
  have he : r=k := le_antisymm hrk hkr
  subst r
  exact ⟨hr,hh⟩

/-- Scaling all limiting sampled-outcome shares by a nonzero common
constant does not change the induced population proportions (T15(c)). -/
theorem weight_proportions_scale_mass {J : ℕ} (q W : Fin J → ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    weightProportions (fun j => c*q j) W = weightProportions q W := by
  funext j
  simp only [weightProportions]
  simp_rw [show ∀ k,W k*(c*q k)=c*(W k*q k) from fun k => by ring]
  rw [← Finset.mul_sum,mul_div_mul_left _ _ hc]

/-- T15(c), forward direction: every feasible real class-weight vector
maps to C_γ(q), the specified region of population proportions. -/
theorem box_proportions_in_region {J : ℕ} (hJ : 0 < J) (q : Fin J → ℝ)
    (hq : ∀ j,0 < q j) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β)
    (W : Fin J → ℝ) (hW : weightBox α β W) :
    proportionRegion q (β/α) (weightProportions q W) := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  have hβ : 0 < β := hα.trans_le hab
  have hγ : 0 < β/α := div_pos hβ hα
  have hWp (j : Fin J) : 0 < W j := (one_div_pos.mpr hβ).trans_le (hW j).1
  let D := ∑ j,W j*q j
  have hD : 0 < D := Finset.sum_pos (fun j _ => mul_pos (hWp j) (hq j)) Finset.univ_nonempty
  refine ⟨?_,?_,?_⟩
  · intro j
    unfold weightProportions
    exact (div_pos (mul_pos (hWp j) (hq j)) hD).le
  · simp only [weightProportions,← Finset.sum_div]
    exact div_self hD.ne'
  · intro j k
    have hWW : W j ≤ (β/α)*W k := calc
      W j ≤ 1/α := (hW j).2
      _ = (β/α)*(1/β) := by field_simp
      _ ≤ (β/α)*W k := mul_le_mul_of_nonneg_left (hW k).1 hγ.le
    have hb := mul_le_mul_of_nonneg_right hWW (mul_nonneg (hq j).le (hq k).le)
    change ((W j*q j)/D)*q k ≤ (β/α)*((W k*q k)/D)*q j
    apply (mul_le_mul_iff_left₀ hD).mp
    have heL : (((W j*q j)/D)*q k)*D = W j*q j*q k := by field_simp
    have heR : ((β/α)*((W k*q k)/D)*q j)*D = (β/α)*W k*q k*q j := by field_simp
    rw [heL,heR]
    simpa [mul_assoc,mul_comm,mul_left_comm] using hb

/-- Every finite population proportion m_j/N has rational coordinates,
including the total-real-division convention when N=0 (T15(c)). -/
theorem class_proportions_rational {J : ℕ} (m : Fin J → ℕ) :
    rationalVector (classProportions m) := by
  intro j
  refine ⟨(m j:ℚ)/(∑ k,(m k:ℚ)),?_⟩
  simp [classProportions]

/-- The ordinary population mean is the dot product of class
proportions and distinct outcomes (T15(c)--(d), p. 237). -/
theorem class_proportion_mean {J : ℕ} (y : Fin J → ℝ) (m : Fin J → ℕ) :
    (∑ j,classProportions m j*y j) = classMean y m := by
  simp only [classProportions,classMean,div_mul_eq_mul_div,← Finset.sum_div]

/-- T15(c), necessary direction: the class proportions of every
share-compatible finite population belong to C_γ(q) and are rational. -/
theorem compatible_proportions_necessary {J : ℕ} (hJ : 0 < J) (q : Fin J → ℝ)
    (hq : ∀ j,0 < q j) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β)
    (m : Fin J → ℕ) (hm : sharesCompatible α β q m) :
    proportionRegion q (β/α) (classProportions m) ∧ rationalVector (classProportions m) := by
  obtain ⟨T,hT,hc⟩ := hm
  let W : Fin J → ℝ := fun j => (m j:ℝ)/(T*q j)
  have hmass (j : Fin J) : 0 < T*q j := mul_pos hT (hq j)
  have hW : weightBox α β W := actual_class_weights m _ α β hα hab hmass hc
  have he : weightProportions (fun j => T*q j) W = classProportions m := by
    funext j
    simp [weightProportions,classProportions,W,div_mul_cancel₀ _ (hmass _).ne']
  rw [weight_proportions_scale_mass q W T hT.ne'] at he
  refine ⟨?_,class_proportions_rational m⟩
  rw [← he]
  exact box_proportions_in_region hJ q hq α β hα hab W hW

/-- Scaling every weight leaves the induced population proportions
unchanged (T15(c), the same homogeneity as the Hajek objective). -/
theorem weight_proportions_scale_weights {J : ℕ} (q W : Fin J → ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    weightProportions q (fun j => c*W j) = weightProportions q W := by
  funext j
  simp only [weightProportions]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,mul_div_mul_left _ _ hc]

/-- C_γ(q) has no zero coordinate when q is strictly positive:
a zero population share would force every share to be zero, contradicting
sum r=1 (T15(c)). -/
theorem proportion_region_positive {J : ℕ} (q r : Fin J → ℝ)
    (hq : ∀ j,0 < q j) (γ : ℝ) (hr : proportionRegion q γ r) :
    ∀ j,0 < r j := by
  have hex : ∃ k,0 < r k := by
    by_contra hn
    push_neg at hn
    have hs : (∑ k,r k) ≤ 0 := Finset.sum_nonpos (fun k _ => hn k)
    rw [hr.2.1] at hs
    norm_num at hs
  obtain ⟨k,hk⟩ := hex
  intro j
  by_contra hj
  have hz : r j=0 := le_antisymm (le_of_not_gt hj) (hr.1 j)
  have hb := hr.2.2 k j
  rw [hz] at hb
  have hp : 0 < r k*q j := mul_pos hk (hq j)
  nlinarith

/-- T15(c), reverse direction: every point of C_γ(q) is induced by a
weight vector in the original probability box. Divide r_j/q_j by its
smallest coordinate, then divide all normalized weights by β. -/
theorem region_has_box_weights {J : ℕ} (hJ : 0 < J) (q r : Fin J → ℝ)
    (hq : ∀ j,0 < q j) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β)
    (hr : proportionRegion q (β/α) r) :
    ∃ W,weightBox α β W ∧ weightProportions q W=r := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  have hβ : 0 < β := hα.trans_le hab
  have hrp := proportion_region_positive q r hq (β/α) hr
  let t : Fin J → ℝ := fun j => r j/q j
  let c := Finset.univ.inf' Finset.univ_nonempty t
  have ht (j : Fin J) : 0 < t j := div_pos (hrp j) (hq j)
  have hcp : 0 < c := (Finset.lt_inf'_iff _).2 (fun j _ => ht j)
  obtain ⟨k,hk,hck⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty t
  have hl (j : Fin J) : c ≤ t j := Finset.inf'_le t (Finset.mem_univ j)
  have hu (j : Fin J) : t j ≤ (β/α)*c := by
    change r j/q j ≤ (β/α)*c
    change c=t k at hck
    rw [hck]
    dsimp [t]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (hq j) (hq k)).2
    simpa [mul_assoc] using hr.2.2 j k
  let U : Fin J → ℝ := fun j => t j/c
  have hU : normBox (β/α) U := by
    intro j
    exact ⟨(le_div_iff₀ hcp).2 (by simpa using hl j),(div_le_iff₀ hcp).2 (hu j)⟩
  have hUW (j : Fin J) : U j*q j = r j/c := by
    dsimp [U,t]
    field_simp [(hq j).ne',hcp.ne']
  have hsum : (∑ j,U j*q j)=1/c := by
    simp_rw [hUW]
    rw [← Finset.sum_div,hr.2.1]
  have heU : weightProportions q U=r := by
    funext j
    simp only [weightProportions]
    rw [hsum,hUW]
    field_simp [hcp.ne']
  refine ⟨fun j => (1/β)*U j,?_,?_⟩
  · apply (normalize_box α β hα hab _).2
    simpa [← mul_assoc,hβ.ne'] using hU
  · rw [weight_proportions_scale_weights q U (1/β) (one_div_ne_zero hβ.ne')]
    exact heU

/-- T15(c): the real probability-weight box maps ONTO precisely
C_γ(q). This is a geometric statement about continuous weights and is
separate from the integer-population density/attainment assertion. -/
theorem box_proportion_image {J : ℕ} (hJ : 0 < J) (q : Fin J → ℝ)
    (hq : ∀ j,0 < q j) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) :
    {r | ∃ W,weightBox α β W ∧ weightProportions q W=r} =
      {r | proportionRegion q (β/α) r} := by
  ext r; constructor
  · rintro ⟨W,hW,rfl⟩
    exact box_proportions_in_region hJ q hq α β hα hab W hW
  · intro hr
    exact region_has_box_weights hJ q r hq α β hα hab hr

/-- Clearing the finitely many rational denominators realizes every
strictly positive rational probability vector as finite integer class
sizes (T15(c)); population size is unrestricted. -/
theorem rational_proportions_have_sizes {J : ℕ} (r : Fin J → ℝ)
    (hrp : ∀ j,0 < r j) (hrsum : (∑ j,r j)=1) (hrat : rationalVector r) :
    ∃ m : Fin J → ℕ,(∀ j,0 < m j) ∧ classProportions m=r := by
  classical
  let R : Fin J → ℚ := fun j => Classical.choose (hrat j)
  have hR (j : Fin J) : (R j:ℝ)=r j := Classical.choose_spec (hrat j)
  have hRp (j : Fin J) : 0 < R j := by
    have hp : 0 < (R j:ℝ) := by rw [hR]; exact hrp j
    exact_mod_cast hp
  let D : ℕ := ∏ j,(R j).den
  have hDp : 0 < D := Finset.prod_pos (fun j _ => (R j).pos)
  have hDr : 0 < (D:ℝ) := by exact_mod_cast hDp
  have hdvd (j : Fin J) : (R j).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hden (j : Fin J) : ((R j).den:ℝ) ≠ 0 := by exact_mod_cast (R j).pos.ne'
  let m : Fin J → ℕ := fun j => (R j).num.toNat * (D/(R j).den)
  have hnum (j : Fin J) : ((R j).num.toNat:ℝ)=((R j).num:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr (hRp j)).le
  have hm (j : Fin J) : (m j:ℝ)=(D:ℝ)*r j := by
    dsimp [m]
    rw [Nat.cast_mul,Nat.cast_div (hdvd j) (hden j),hnum,← hR j,Rat.cast_def]
    ring
  have hmp (j : Fin J) : 0 < m j := by
    have hp : 0 < (m j:ℝ) := by rw [hm]; exact mul_pos hDr (hrp j)
    exact_mod_cast hp
  have hsum : (∑ j,(m j:ℝ))=D := by
    simp_rw [hm]
    rw [← Finset.mul_sum,hrsum,mul_one]
  refine ⟨m,hmp,?_⟩
  funext j
  simp only [classProportions]
  rw [hsum,hm]
  exact mul_div_cancel_left₀ (r j) hDr.ne'

/-- T15(c), sufficient direction: a rational point of C_γ(q) is the
proportion vector of a compatible finite population, with unrestricted N. -/
theorem rational_region_has_compatible_sizes {J : ℕ} (hJ : 0 < J) (q r : Fin J → ℝ)
    (hq : ∀ j,0 < q j) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β)
    (hr : proportionRegion q (β/α) r) (hrat : rationalVector r) :
    ∃ m : Fin J → ℕ,sharesCompatible α β q m ∧ classProportions m=r := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  obtain ⟨m,hmp,hm⟩ := rational_proportions_have_sizes r
    (proportion_region_positive q r hq (β/α) hr) hr.2.1 hrat
  obtain ⟨W,hW,heW⟩ := region_has_box_weights hJ q r hq α β hα hab hr
  have hβ : 0 < β := hα.trans_le hab
  have hWp (j : Fin J) : 0 < W j := (one_div_pos.mpr hβ).trans_le (hW j).1
  let N : ℝ := ∑ j,(m j:ℝ)
  let D : ℝ := ∑ j,W j*q j
  have hN : 0 < N := Finset.sum_pos (fun j _ => by exact_mod_cast hmp j) Finset.univ_nonempty
  have hD : 0 < D := Finset.sum_pos (fun j _ => mul_pos (hWp j) (hq j)) Finset.univ_nonempty
  let T := N/D
  have hT : 0 < T := div_pos hN hD
  have he (j : Fin J) : (T*q j)*W j=(m j:ℝ) := by
    have heP := congrFun (hm.trans heW.symm) j
    change (m j:ℝ)/N = (W j*q j)/D at heP
    field_simp at heP
    dsimp [T]
    field_simp
    simpa [mul_assoc,mul_comm,mul_left_comm] using heP.symm
  refine ⟨m,⟨T,hT,?_⟩,hm⟩
  apply (absolute_integer_calibration (fun j => T*q j) m α β hα hab).2
  intro j
  have htq : 0 < T*q j := mul_pos hT (hq j)
  refine ⟨hmp j,?_,?_⟩
  · have hb := mul_le_mul_of_nonneg_left (hW j).1 htq.le
    rw [he] at hb
    simpa [div_eq_mul_inv] using hb
  · have hb := mul_le_mul_of_nonneg_left (hW j).2 htq.le
    rw [he] at hb
    simpa [div_eq_mul_inv] using hb

/-- T15(c): exact finite-population realizability is membership in
C_γ(q) together with rational coordinates, as required to distinguish
finite-population attainment from continuous weight-box optimization. -/
theorem compatible_proportions_iff_rational_region {J : ℕ} (hJ : 0 < J) (q r : Fin J → ℝ)
    (hq : ∀ j,0 < q j) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) :
    (∃ m : Fin J → ℕ,sharesCompatible α β q m ∧ classProportions m=r) ↔
      proportionRegion q (β/α) r ∧ rationalVector r := by
  constructor
  · rintro ⟨m,hm,rfl⟩
    exact compatible_proportions_necessary hJ q hq α β hα hab m hm
  · rintro ⟨hr,hRat⟩
    exact rational_region_has_compatible_sizes hJ q r hq α β hα hab hr hRat

/-- T15(d): either variational endpoint is an actual finite-population
mean exactly when its optimizer set contains a rational proportion vector.
The statement holds for any specified value v and thus applies
to both μ_- and μ_+. -/
theorem compatible_mean_iff_rational_region {J : ℕ} (hJ : 0 < J) (y q : Fin J → ℝ)
    (hq : ∀ j,0 < q j) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) (v : ℝ) :
    v ∈ compatibleMeans y q α β ↔
      ∃ r : Fin J → ℝ,proportionRegion q (β/α) r ∧ rationalVector r ∧ (∑ j,r j*y j)=v := by
  constructor
  · rintro ⟨m,hm,hv⟩
    obtain ⟨hr,hRat⟩ := compatible_proportions_necessary hJ q hq α β hα hab m hm
    exact ⟨classProportions m,hr,hRat,(class_proportion_mean y m).trans hv⟩
  · rintro ⟨r,hr,hRat,hv⟩
    obtain ⟨m,hm,hP⟩ := rational_region_has_compatible_sizes hJ q r hq α β hα hab hr hRat
    refine ⟨m,hm,?_⟩
    rw [← class_proportion_mean y m,hP]
    exact hv

/-- Auxiliary strict cone "a_j>0 and a_j q_k<γ a_k q_j for every j,k"
for the density proof of T15(b). Normalizing these vectors gives
population proportions in C_γ(q), on p. 237 as corrected. -/
def strictSelectionCone {J : ℕ} (q : Fin J → ℝ) (γ : ℝ) : Set (Fin J → ℝ) :=
  {a | (∀ j,0 < a j) ∧ ∀ j k,a j*q k < γ*a k*q j}

/-- The strict selection cone is open, since its defining conditions
are finitely many strict inequalities between continuous functions. -/
theorem strict_selection_cone_open {J : ℕ} (q : Fin J → ℝ) (γ : ℝ) :
    IsOpen (strictSelectionCone q γ) := by
  have he : strictSelectionCone q γ =
      ((⋂ j : Fin J,{a : Fin J → ℝ | 0 < a j}) ∩
        ⋂ j : Fin J,⋂ k : Fin J,{a : Fin J → ℝ | a j*q k < γ*a k*q j}) := by
    ext a; simp [strictSelectionCone]
  rw [he]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro j; exact isOpen_lt continuous_const (continuous_apply j)
  · apply isOpen_iInter_of_finite
    intro j; apply isOpen_iInter_of_finite
    intro k
    have hL : Continuous (fun a : Fin J → ℝ => a j*q k) := by fun_prop
    have hH : Continuous (fun a : Fin J → ℝ => γ*a k*q j) := by fun_prop
    exact isOpen_lt hL hH

/-- Rational vectors are dense in the finite real outcome-class space,
by coordinatewise density of the rational numbers (T15 density proof). -/
theorem rational_vectors_dense {J : ℕ} : Dense {a : Fin J → ℝ | rationalVector a} := by
  have hd : DenseRange (fun R : Fin J → ℚ => fun j => (R j:ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have he : Set.range (fun R : Fin J → ℚ => fun j => (R j:ℝ)) =
      {a : Fin J → ℝ | rationalVector a} := by
    ext a; constructor
    · rintro ⟨R,rfl⟩; intro j; exact ⟨R j,rfl⟩
    · intro h
      exact ⟨fun j => Classical.choose (h j),funext (fun j => Classical.choose_spec (h j))⟩
  change Dense (Set.range _) at hd
  rwa [he] at hd

/-- A rational vector in the strict selection cone, after normalization,
is a rational point of C_γ(q), hence yields a compatible population mean
(T15(b)--(c)). The population size is determined by clearing denominators. -/
theorem rational_cone_mean_compatible {J : ℕ} (hJ : 0 < J) (y q a : Fin J → ℝ)
    (hq : ∀ j,0 < q j) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β)
    (ha : a ∈ strictSelectionCone q (β/α)) (hrat : rationalVector a) :
    ratio y a (fun _ => 1) ∈ compatibleMeans y q α β := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  let S : ℝ := ∑ j,a j
  have hS : 0 < S := Finset.sum_pos (fun j _ => ha.1 j) Finset.univ_nonempty
  let r : Fin J → ℝ := fun j => a j/S
  have hr : proportionRegion q (β/α) r := by
    refine ⟨fun j => (div_pos (ha.1 j) hS).le,?_,?_⟩
    · rw [show (∑ j,r j) = (∑ j,a j)/S from by dsimp [r]; rw [← Finset.sum_div]]
      exact div_self hS.ne'
    · intro j k
      apply (mul_le_mul_iff_left₀ hS).mp
      dsimp [r]
      have hL : ((a j/S)*q k)*S = a j*q k := by field_simp
      have hH : ((β/α)*(a k/S)*q j)*S = (β/α)*a k*q j := by field_simp
      rw [hL,hH]
      exact (ha.2 j k).le
  let A : Fin J → ℚ := fun j => Classical.choose (hrat j)
  have hA (j : Fin J) : (A j:ℝ)=a j := Classical.choose_spec (hrat j)
  have hRat : rationalVector r := by
    intro j
    refine ⟨A j/(∑ k,A k),?_⟩
    simp [r,S,hA]
  obtain ⟨m,hm,hP⟩ := rational_region_has_compatible_sizes hJ q r hq α β hα hab hr hRat
  refine ⟨m,hm,?_⟩
  rw [← class_proportion_mean y m,hP]
  simp only [r,S,ratio,mul_one,div_mul_eq_mul_div,← Finset.sum_div]

/-- T15(b): every continuous-region mean is in the closure of the
compatible finite-population mean set when γ>1. Add εq to a boundary
point to obtain strict selection inequalities, approximate by rational
vectors, and normalize. This proves infimum/supremum sharpness, not a
claim that irrational endpoint proportions are attained. -/
theorem region_mean_mem_closure {J : ℕ} (hJ : 0 < J) (y q r : Fin J → ℝ)
    (hq : ∀ j,0 < q j) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β)
    (hγ : 1 < β/α) (hr : proportionRegion q (β/α) r) :
    (∑ j,r j*y j) ∈ closure (compatibleMeans y q α β) := by
  classical
  let S : Set (Fin J → ℝ) := strictSelectionCone q (β/α) ∩ {a | rationalVector a}
  have hopen := strict_selection_cone_open q (β/α)
  have hd : strictSelectionCone q (β/α) ⊆ closure S :=
    rational_vectors_dense.open_subset_closure_inter hopen
  have hrp := proportion_region_positive q r hq (β/α) hr
  let e : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  let a : ℕ → Fin J → ℝ := fun n j => r j+e n*q j
  have he : Tendsto e atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto a atTop (nhds r) := by
    apply tendsto_pi_nhds.mpr
    intro j
    simpa [a] using tendsto_const_nhds.add (he.mul_const (q j))
  have hain (n : ℕ) : a n ∈ strictSelectionCone q (β/α) := by
    have hep : 0 < e n := by dsimp [e]; positivity
    refine ⟨fun j => add_pos (hrp j) (mul_pos hep (hq j)),?_⟩
    intro j k
    have hs : 0 < ((β/α)-1)*e n*q j*q k :=
      mul_pos (mul_pos (mul_pos (sub_pos.mpr hγ) hep) (hq j)) (hq k)
    have hid : (β/α)*(r k+e n*q k)*q j - (r j+e n*q j)*q k =
        ((β/α)*r k*q j-r j*q k)+((β/α)-1)*e n*q j*q k := by ring
    apply sub_pos.mp
    change 0 < (β/α)*(r k+e n*q k)*q j - (r j+e n*q j)*q k
    rw [hid]
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr (hr.2.2 j k)) hs
  have hx : r ∈ closure S := isClosed_closure.mem_of_tendsto ht
    (Filter.Eventually.of_forall (fun n => hd (hain n)))
  have hc : ContinuousAt (fun a : Fin J → ℝ => ratio y a (fun _ => 1)) r :=
    fixed_weight_continuity hJ y r (fun _ => 1) hrp (fun _ => zero_lt_one)
  have hf : ratio y r (fun _ => 1) ∈ closure ((fun a : Fin J → ℝ => ratio y a (fun _ => 1)) '' S) :=
    mem_closure_image hc hx
  have hsub : ((fun a : Fin J → ℝ => ratio y a (fun _ => 1)) '' S) ⊆ compatibleMeans y q α β := by
    rintro v ⟨a,ha,rfl⟩
    exact rational_cone_mean_compatible hJ y q a hq α β hα hab ha.1 ha.2
  have hv := closure_mono hsub hf
  simpa [ratio,hr.2.1] using hv

/-- The dot product of induced proportions and outcomes equals the
class Hajek ratio for every real W (T15(c), p. 237). -/
theorem mean_weight_proportions {J : ℕ} (y q W : Fin J → ℝ) :
    (∑ j,weightProportions q W j*y j) = ratio y q W := by
  simp only [weightProportions,ratio,div_mul_eq_mul_div,← Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _; ring
  · apply Finset.sum_congr rfl
    intro j _; ring

/-- T15(b): both variational endpoints belong to the closure of the
compatible finite-population means. At α=β, existence of a compatible
population (the stated hypothesis) gives the common endpoint itself. -/
theorem compatible_endpoints_mem_closure {J : ℕ} (hJ : 0 < J) (y q : Fin J → ℝ)
    (hy : StrictMono y) (hq : ∀ j,0 < q j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1)
    (hcomp : ∃ m : Fin J → ℕ,sharesCompatible α β q m) :
    lowerEndpoint y q α β ∈ closure (compatibleMeans y q α β) ∧
    upperEndpoint y q α β ∈ closure (compatibleMeans y q α β) := by
  obtain ⟨kL,kH,_,_,hl,hh,el,eh⟩ := corrected_proposition_two hJ y q hy hq α β hα hab hb1
  by_cases hba : β=α
  · have hγ : β/α=1 := by rw [hba]; exact div_self hα.ne'
    have hwL : lowerWeights (n:=J) 1 kL.val = fun _ => 1 := by funext j; simp [lowerWeights]
    have hwH : upperWeights (n:=J) 1 kH.val = fun _ => 1 := by funext j; simp [upperWeights]
    have heq : lowerEndpoint y q α β = upperEndpoint y q α β := by
      rw [el,eh,hγ,lowerValue,upperValue,hwL,hwH]
    obtain ⟨m,hm⟩ := hcomp
    have hb := shares_outer_bound hJ y q hy hq α β hα hab hb1 m hm
    have hmL : classMean y m = lowerEndpoint y q α β := le_antisymm (by simpa [heq] using hb.2) hb.1
    have hmem : lowerEndpoint y q α β ∈ compatibleMeans y q α β := ⟨m,hm,hmL⟩
    exact ⟨subset_closure hmem,by rw [← heq]; exact subset_closure hmem⟩
  · have hγ : 1 < β/α := (lt_div_iff₀ hα).2 (by have := lt_of_le_of_ne hab (Ne.symm hba); linarith)
    have hv (v : ℝ) (hv : v ∈ attainable y q α β) : v ∈ closure (compatibleMeans y q α β) := by
      obtain ⟨W,hW,heW⟩ := hv
      have hr := box_proportions_in_region hJ q hq α β hα hab W hW
      have hm := region_mean_mem_closure hJ y q (weightProportions q W) hq α β hα hab hγ hr
      rwa [mean_weight_proportions,heW] at hm
    exact ⟨hv _ (by rw [el]; exact hl.1),hv _ (by rw [eh]; exact hh.1)⟩

/-- T15(b): the corrected share-only sharpness statement. The variational
lower and upper endpoints are the GLB and LUB of ACTUAL compatible finite
population means, including the rational degenerate γ=1 case. -/
theorem shares_sharp_endpoints {J : ℕ} (hJ : 0 < J) (y q : Fin J → ℝ)
    (hy : StrictMono y) (hq : ∀ j,0 < q j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1)
    (hcomp : ∃ m : Fin J → ℕ,sharesCompatible α β q m) :
    IsGLB (compatibleMeans y q α β) (lowerEndpoint y q α β) ∧
    IsLUB (compatibleMeans y q α β) (upperEndpoint y q α β) := by
  obtain ⟨hL,hH⟩ := compatible_endpoints_mem_closure hJ y q hy hq α β hα hab hb1 hcomp
  constructor
  · refine ⟨?_,?_⟩
    · rintro v ⟨m,hm,rfl⟩
      exact (shares_outer_bound hJ y q hy hq α β hα hab hb1 m hm).1
    · intro b hb
      exact (closure_minimal hb isClosed_Ici) hL
  · refine ⟨?_,?_⟩
    · rintro v ⟨m,hm,rfl⟩
      exact (shares_outer_bound hJ y q hy hq α β hα hab hb1 m hm).2
    · intro b hb
      exact (closure_minimal hb isClosed_Iic) hH

/-- T15(b)--(d), the FULL repaired sharpness claim: with q alone and N
unrestricted the endpoints are sharp infimum/supremum bounds on compatible
finite-population means; the weight-box image is C_γ(q), finite compatible
proportions are exactly its rational points, and endpoint attainment is
exactly rational-point attainment on the optimizing face. Nonempty
compatibility includes the necessary degenerate-case condition at γ=1.
The proof separates rational finite-population realizability from continuous-box
geometry and uses closure, not an assumption of endpoint attainment. -/
theorem shares_sharpness_and_attainment {J : ℕ} (hJ : 0 < J) (y q : Fin J → ℝ)
    (hy : StrictMono y) (hq : ∀ j, 0 < q j) (hqsum : (∑ j,q j)=1)
    (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1)
    (hcomp : ∃ m : Fin J → ℕ, sharesCompatible α β q m) :
    IsGLB (compatibleMeans y q α β) (lowerEndpoint y q α β) ∧
    IsLUB (compatibleMeans y q α β) (upperEndpoint y q α β) ∧
    {r | ∃ W, weightBox α β W ∧ weightProportions q W = r} =
      {r | proportionRegion q (β/α) r} ∧
    (∀ r : Fin J → ℝ, (∃ m : Fin J → ℕ,
      sharesCompatible α β q m ∧ classProportions m = r) ↔
      proportionRegion q (β/α) r ∧ rationalVector r) ∧
    ((lowerEndpoint y q α β ∈ compatibleMeans y q α β) ↔
      ∃ r : Fin J → ℝ, proportionRegion q (β/α) r ∧ rationalVector r ∧
        (∑ j,r j*y j)=lowerEndpoint y q α β) ∧
    ((upperEndpoint y q α β ∈ compatibleMeans y q α β) ↔
      ∃ r : Fin J → ℝ, proportionRegion q (β/α) r ∧ rationalVector r ∧
        (∑ j,r j*y j)=upperEndpoint y q α β) := by
  obtain ⟨hl,hh⟩ := shares_sharp_endpoints hJ y q hy hq α β hα hab hb1 hcomp
  exact ⟨hl,hh,box_proportion_image hJ q hq α β hα hab,
    fun r => compatible_proportions_iff_rational_region hJ q r hq α β hα hab,
    compatible_mean_iff_rational_region hJ y q hq α β hα hab _,
    compatible_mean_iff_rational_region hJ y q hq α β hα hab _⟩

/-- T15(c): the real optimization range is exactly the set of dot
products of outcomes with C_γ(q) proportions (p. 237, corrected sharpness). -/
theorem proportion_region_mean_image {J : ℕ} (hJ : 0 < J) (y q : Fin J → ℝ)
    (hq : ∀ j,0 < q j) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) :
    attainable y q α β = {v | ∃ r : Fin J → ℝ,
      proportionRegion q (β/α) r ∧ (∑ j,r j*y j)=v} := by
  ext v; constructor
  · rintro ⟨W,hW,hv⟩
    exact ⟨weightProportions q W,box_proportions_in_region hJ q hq α β hα hab W hW,
      (mean_weight_proportions y q W).trans hv⟩
  · rintro ⟨r,hr,hv⟩
    obtain ⟨W,hW,hP⟩ := region_has_box_weights hJ q r hq α β hα hab hr
    refine ⟨W,hW,?_⟩
    rw [← mean_weight_proportions y q W,hP]
    exact hv

/-- T15(c): μ_- and μ_+ are the attained minimum and maximum of
∑ r_j y_j over the CONTINUOUS region C_γ(q). This is distinct from the
finite-population infimum/supremum and rational attainment criterion. -/
theorem proportion_region_mean_extrema {J : ℕ} (hJ : 0 < J) (y q : Fin J → ℝ)
    (hy : StrictMono y) (hq : ∀ j,0 < q j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1) :
    IsLeast {v | ∃ r : Fin J → ℝ,proportionRegion q (β/α) r ∧ (∑ j,r j*y j)=v}
      (lowerEndpoint y q α β) ∧
    IsGreatest {v | ∃ r : Fin J → ℝ,proportionRegion q (β/α) r ∧ (∑ j,r j*y j)=v}
      (upperEndpoint y q α β) := by
  rw [← proportion_region_mean_image hJ y q hq α β hα hab]
  obtain ⟨_,_,_,_,hl,hh,el,eh⟩ := corrected_proposition_two hJ y q hy hq α β hα hab hb1
  rw [el,eh]
  exact ⟨hl,hh⟩

end
end AronowAudit.P025
