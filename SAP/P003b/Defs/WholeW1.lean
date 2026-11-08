import Mathlib
import SAP.P003b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section

/-- Observed counts for an arbitrary labeled table and a treatment assignment. -/
def w1Observed {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) : Counts :=
  ⟨(Finset.univ.filter fun i => i ∈ z ∧ (w i).1 = true).card,
   (Finset.univ.filter fun i => i ∈ z ∧ (w i).1 = false).card,
   (Finset.univ.filter fun i => i ∉ z ∧ (w i).2 = true).card,
   (Finset.univ.filter fun i => i ∉ z ∧ (w i).2 = false).card⟩

/-- Query costs count table tests, including the exceptional second zero-effect table. -/
def W1QueryCosts : Prop :=
  ∀ (o : Counts) (x : ℤ) (reject : Counts → ℕ → Bool) (idx : ℕ),
    (runTests reject idx (candidates o x)).trace.length ≤
      (o.total+1)*(if x = 0 then 2 else 1)

/-- Literal Algorithm 5.3 stops its j scan after the first feasible line. -/
def w1LiteralBase (o : Counts) (x : ℤ) : Option (ℕ × Counts) :=
  ((List.range (o.total+1)).filterMap fun j => (firstOnLine o x j).map (fun v => (j,v))).head?

/-- Deterministic support of the vectors visited by the literal missing-loop schedule. -/
def w1LiteralVisited (o : Counts) : List Counts :=
  (candidateNumerators o).reverse.flatMap fun x =>
    match w1LiteralBase o x with
    | none => []
    | some (_,v) => v :: (reuseLine o v).map (reuseVector v)

/-- Fresh draws charged by the literal first-feasible-line schedule. -/
def w1LiteralDrawCount (o : Counts) (K : ℕ) : ℕ :=
  ((candidateNumerators o).map fun x =>
    if (w1LiteralBase o x).isSome then K else 0).sum

/-- Reuse updates charged by the literal schedule. -/
def w1LiteralUpdateCount (o : Counts) (K : ℕ) : ℕ :=
  ((candidateNumerators o).map fun x =>
    match w1LiteralBase o x with
    | none => 0
    | some (_,v) => K*(reuseLine o v).length).sum

/-- The arithmetic charge allows all n+1 possible line checks per effect. -/
def w1LiteralOperations (o : Counts) (K : ℕ) (c₀ c₁ c₂ : ℝ) : ℝ :=
  c₀*(o.total+1)^2+2*c₁*o.total*w1LiteralDrawCount o K+
    2*c₂*w1LiteralUpdateCount o K

/-- The literal unbalanced schedule also obeys the uniform O(K n³) charge. -/
def W1T18LiteralBound : Prop :=
  ∀ (o : Counts) (K : ℕ) (c₀ c₁ c₂ : ℝ),
    (0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂) → 1 ≤ o.total → 1 ≤ K →
    w1LiteralDrawCount o K ≤ generalDrawCount o K ∧
    w1LiteralUpdateCount o K ≤ generalUpdateCount o K ∧
    w1LiteralOperations o K c₀ c₁ c₂ ≤ generalOperations o K c₀ c₁ c₂ ∧
    w1LiteralOperations o K c₀ c₁ c₂ ≤ 4*(c₀+2*(c₁+c₂))*K*(o.total : ℝ)^3

/-- Finite operation and draw arithmetic in corrected Remark 5.7. -/
def W1T18Finite : Prop :=
  ∀ (n K t : ℕ) (c O : ℝ), 0 ≤ c →
    (t : ℝ) ≤ 4*(n : ℝ)*logTwo n → O ≤ (t : ℝ)*K*(c*n) →
    (t : ℝ)*K ≤ 4*K*n*logTwo n ∧
    O ≤ 4*c*K*(n : ℝ)^2*logTwo n ∧
    (4*(n : ℝ)*logTwo n)*K*(c*n) = 4*c*K*(n : ℝ)^2*logTwo n

/-- Assignment draws and the fixed-tolerance form of (1.6). -/
def W1T18Rates : Prop :=
  (∀ (ε : ℝ), 0 < ε → ∀ (tests : ℕ → ℕ),
    (∀ᶠ n in Filter.atTop, (tests n : ℝ) ≤ 4*(n : ℝ)*logTwo n) →
    (fun n => (tests n : ℝ)*recommendedK ε n) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ)*(Real.log n)^2)) ∧
  (∀ (ε c : ℝ), 0 < ε → 0 ≤ c →
    balancedEnvelope ε c =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ)^2*(Real.log n)^2) ∧
    balancedEnvelope ε c =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ)^2*Real.log n/ε^2*
        Real.log ((n : ℝ)*Real.log n/ε)))

/-- Uniform unbalanced arithmetic cost bound, including every fixed positive K. -/
def W1T18General : Prop :=
  (∀ (o : Counts) (K : ℕ) (c₀ c₁ c₂ : ℝ),
    0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂ →
    generalDrawCount o K ≤ (o.total+1)^2*K ∧
    generalUpdateCount o K ≤ (o.total+1)^2*o.total*K ∧
    generalOperations o K c₀ c₁ c₂ ≤ generalEnvelope o.total K c₀ c₁ c₂ ∧
    (1 ≤ o.total → 1 ≤ K → generalOperations o K c₀ c₁ c₂ ≤
      4*(c₀+2*(c₁+c₂))*K*(o.total : ℝ)^3)) ∧
  (∀ (c₀ c₁ c₂ : ℝ), 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂ →
    ∀ (o : ℕ × ℕ → Counts), (∀ p, (o p).total = p.1) →
    (∀ᶠ p in Filter.atTop, 0 < (o p).a+(o p).b ∧ 0 < (o p).c+(o p).d) →
    (fun p : ℕ × ℕ => generalOperations (o p) p.2 c₀ c₁ c₂) =O[Filter.atTop]
      (fun p : ℕ × ℕ => (p.2 : ℝ)*(p.1 : ℝ)^3))

/-- The printed real budget is conservative, and so is its integer ceiling. -/
def W1T18Budgets : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 15 ≤ n → 0 < ε →
    Real.log (4*(n : ℝ)*logTwo n/ε)/(2*ε^2) ≤
      Real.log (4*(n : ℝ)*(Real.log n)^2/ε)/(2*ε^2) ∧
    recommendedK ε n ≤ ⌈Real.log (4*(n : ℝ)*(Real.log n)^2/ε)/(2*ε^2)⌉₊

/-- p. 13 (PDF p. 13), corrected Remark 5.7; compare pp. 4 and 9, (1.6), (4.9).
For fixed positive tolerance the balanced arithmetic cost is O(n² log² n), with the
stated finite operation and draw bounds, O(n log² n) draws, and the (1.6) envelope.
The general arithmetic cost is uniformly O(K n³). The dyadic full-shuffle family
has the positive-probability and expected quadratic lower bounds and exceeds every
linear-polylogarithmic expected bound. For n ≥ 15 the printed budget is conservative. -/
def T18WholeStatement : Prop :=
  T18Statement ∧ W1T18Finite ∧ W1T18Rates ∧ W1T18General ∧ W1T18LiteralBound ∧ W1T18Budgets ∧
  ∀ q : ℝ, ¬ (fun r : ℕ =>
    let n : ℕ := 2^r
    expectedUpperShuffleCost (1/2) (1/8) n (recommendedK (1/8) n) ⟨0,n/2,0,n/2⟩)
      =O[Filter.atTop] (fun r : ℕ =>
        let n : ℕ := 2^r
        (n : ℝ)*Real.rpow (Real.log n) q)

/-- The actual Algorithm 4.3 oracle, its initial segment, and both separate endpoint budgets. -/
def W1T32Oracle : Prop :=
  ∀ (o : Counts) (α : ℝ),
    (0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) → (0 < α ∧ α < 1) →
    (∀ (x : ℤ) (idx : ℕ),
      (runTests (fun v _ => decide ((pValue v o : ℝ) < α)) idx (candidates o x)).compatible = true ↔
        ∃ v, Possible o v ∧ v.effect = x ∧ α ≤ (pValue v o : ℝ)) ∧
    (∃ r : ℤ, 2*((o.a : ℤ)-o.c) ≤ r ∧
      r ≤ (o.a : ℤ)-o.c+(o.a+o.b) ∧ upper α o = (r : ℝ)/o.total ∧
      ∀ x : ℤ, 2*((o.a : ℤ)-o.c) ≤ x →
        ((∃ v, Possible o v ∧ v.effect = x ∧ α ≤ (pValue v o : ℝ)) ↔ x ≤ r)) ∧
    (exactUpperRun α o).value.map (fun x : ℤ => (x : ℝ)/o.total) = some (upper α o) ∧
    (exactUpperRun α (complementObserved o)).value.map (fun x : ℤ => -(x : ℝ)/o.total) =
      some (lower α o) ∧
    (exactUpperRun α o).trace.length ≤ testBudget o.total ∧
    (exactUpperRun α (complementObserved o)).trace.length ≤ testBudget o.total

/-- Exact agreement between the natural-number budget and the printed real floor. -/
def W1BudgetFloor : Prop :=
  ∀ n : ℕ, (testBudget n : ℤ) = (n+1)*⌊logTwo ((n : ℝ)+1)+3⌋

/-- p. 8 (PDF p. 8), Theorem 4.1; Appendix B.2, p. 21.
The corrected sentinel searches construct both exact balanced endpoints with at most
4 n log₂ n tests for n ≥ 15. The actual oracle is equivalent to existence of a
possible accepted table; on the upper search domain its accepted effects form the
initial segment ending at n U. Nonzero queries use at most n+1 tests, zero queries
at most 2(n+1), and each endpoint obeys D at every positive balanced size.
The standalone inequality 2D ≤ 4 n log₂ n holds for every integer n ≥ 15. -/
def T32WholeStatement : Prop :=
  T32Statement ∧ W1T32Oracle ∧ W1QueryCosts ∧ W1BudgetFloor ∧
    ∀ n : ℕ, 15 ≤ n → 2*(testBudget n : ℝ) ≤ 4*(n : ℝ)*logTwo n

/-- Instrumentation of the corrected recursion: every evaluated midpoint, in order. -/
def w1Midpoints (fuel : ℕ) (o : Counts) (reject : Counts → ℕ → Bool)
    (a b : ℤ) (idx : ℕ) : List ℤ :=
  if b ≤ a+1 then [] else
  match fuel with
  | 0 => []
  | t+1 =>
    let c := (a+b)/2
    let q := runTests reject idx (candidates o c)
    c :: w1Midpoints t o reject (if q.compatible then c else a)
      (if q.compatible then b else c) q.idx

def w1UpperMidpoints (o : Counts) (reject : Counts → ℕ → Bool) (idx : ℕ) : List ℤ :=
  w1Midpoints (o.total+3) o reject (2*((o.a : ℤ)-o.c)-1)
    ((o.a : ℤ)-o.c+(o.a+o.b)+1) idx

/-- Pathwise decomposition of D, with no premise on the decision function. -/
def W1T7Budget : Prop :=
  ∀ (o : Counts) (reject : Counts → ℕ → Bool) (idx : ℕ),
    (0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) →
    let qs := w1UpperMidpoints o reject idx
    (upperRun true o reject idx).value.isSome ∧
    (upperRun true o reject idx).trace.length ≤ testBudget o.total ∧
    qs.length ≤ ⌈logTwo ((o.total : ℝ)+2)⌉₊ ∧ qs.Nodup ∧ qs.count 0 ≤ 1 ∧
    (upperRun true o reject idx).trace.length ≤ (o.total+1)*(qs.length+qs.count 0) ∧
    (o.total+1)*(⌈logTwo ((o.total : ℝ)+2)⌉₊+1) ≤ testBudget o.total

abbrev W1Pool (n m K : ℕ) := Fin (2*testBudget n+1) → Fin K → Assignment n m

/-- The upper endpoint uses the first batches; the reflected lower endpoint starts
at the number of upper tests. False selects the upper endpoint; true the lower. -/
def w1Start {n m K : ℕ} (lo : Bool) (α ε : ℝ) (o : Counts) (p : W1Pool n m K) : ℕ :=
  if lo then (upperRun true o (approximateReject α ε o p)).trace.length else 0

def w1Endpoint {n m K : ℕ} (lo : Bool) (α ε : ℝ) (o : Counts) (p : W1Pool n m K) : EndpointResult :=
  upperRun true (if lo then complementObserved o else o)
    (approximateReject α ε (if lo then complementObserved o else o) p) (w1Start lo α ε o p)

/-- Raw preceding batches, a finite history finer than all earlier test decisions.
For the lower endpoint this includes the completed upper history. -/
def w1History {n m K : ℕ} (lo : Bool) (i : ℕ) (α ε : ℝ) (o : Counts)
    (p : W1Pool n m K) : List (Fin K → Assignment n m) :=
  (List.range (w1Start lo α ε o p+i)).map fun j =>
    p ⟨j % (2*testBudget n+1), Nat.mod_lt _ (by omega)⟩

def w1NextBatch {n m K : ℕ} (lo : Bool) (i : ℕ) (α ε : ℝ) (o : Counts)
    (p : W1Pool n m K) : Fin K → Assignment n m :=
  p ⟨(w1Start lo α ε o p+i) % (2*testBudget n+1), Nat.mod_lt _ (by omega)⟩

/-- The chosen table is absent exactly at an unreached test position. -/
def w1Selected {n m K : ℕ} (lo : Bool) (i : ℕ) (α ε : ℝ) (o : Counts)
    (p : W1Pool n m K) : Option Counts :=
  ((w1Endpoint lo α ε o p).trace[i]?).map Prod.fst

/-- A dangerous performed rejection or acceptance; unreached positions have no event. -/
def w1Error {n m K : ℕ} (lo badReject : Bool) (i : ℕ) (α ε : ℝ) (o : Counts)
    (p : W1Pool n m K) : Prop :=
  ∃ v, (w1Endpoint lo α ε o p).trace[i]? = some (v,badReject) ∧
    if badReject then α ≤ (pValue v (if lo then complementObserved o else o) : ℝ)
    else (pValue v (if lo then complementObserved o else o) : ℝ) < α-2*ε

/-- Conditional predictability, fresh iid current draws, and both one-test bounds.
The positive-mass guard is exactly what makes conditional probabilities defined. -/
def W1T7Conditional (lo : Bool) : Prop :=
  ∀ (n m K : ℕ) (o : Counts) (α ε : ℝ), o.total = n → o.a+o.b = m →
    (0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) → 0 < K →
    (0 < α ∧ α < 1) → (0 < ε ∧ ε < α) →
    ∀ (i : ℕ), i < testBudget n → ∀ h : List (Fin K → Assignment n m),
    0 < uniformProb (fun p : W1Pool n m K => w1History lo i α ε o p = h) →
    (∀ p q : W1Pool n m K,
      w1History lo i α ε o p = h → w1History lo i α ε o q = h →
      w1Start lo α ε o p = w1Start lo α ε o q ∧
      w1Selected lo i α ε o p = w1Selected lo i α ε o q) ∧
    (∀ b : Fin K → Assignment n m,
      uniformProb (fun p : W1Pool n m K =>
        w1History lo i α ε o p = h ∧ w1NextBatch lo i α ε o p = b) /
      uniformProb (fun p : W1Pool n m K => w1History lo i α ε o p = h) =
        1/(Fintype.card (Fin K → Assignment n m) : ℝ)) ∧
    ∀ badReject : Bool,
      uniformProb (fun p : W1Pool n m K =>
        w1History lo i α ε o p = h ∧ w1Error lo badReject i α ε o p) /
      uniformProb (fun p : W1Pool n m K => w1History lo i α ε o p = h) ≤
        Real.exp (-2*(K : ℝ)*ε^2)

/-- Each endpoint separately has dangerous-error probability at most D delta. -/
def W1T7Errors : Prop :=
  ∀ (n m K : ℕ) (o : Counts) (α ε : ℝ), o.total = n → o.a+o.b = m →
    (0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) → 0 < K →
    (0 < α ∧ α < 1) → (0 < ε ∧ ε < α) → ∀ lo badReject : Bool,
    uniformProb (fun p : W1Pool n m K =>
      ∃ i < testBudget n, w1Error lo badReject i α ε o p) ≤
        (testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2)

/-- Pathwise comparisons for both endpoint searches, with arbitrary decisions and starts. -/
def W1T7Comparisons : Prop :=
  ∀ (o : Counts) (α : ℝ) (reject : Counts → ℕ → Bool) (idx : ℕ),
    (0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) → (0 < α ∧ α < 1) →
    ((∀ v, (v,true) ∈ (upperRun true o reject idx).trace → (pValue v o : ℝ) < α) →
      ∃ x, (upperRun true o reject idx).value = some x ∧ upper α o ≤ (x : ℝ)/o.total) ∧
    ((∀ v, (v,false) ∈ (upperRun true o reject idx).trace → α ≤ (pValue v o : ℝ)) →
      ∃ x, (upperRun true o reject idx).value = some x ∧ (x : ℝ)/o.total ≤ upper α o) ∧
    ((∀ v, (v,true) ∈ (upperRun true (complementObserved o) reject idx).trace →
      (pValue v (complementObserved o) : ℝ) < α) →
      ∃ x, (upperRun true (complementObserved o) reject idx).value = some x ∧
        -(x : ℝ)/o.total ≤ lower α o) ∧
    ((∀ v, (v,false) ∈ (upperRun true (complementObserved o) reject idx).trace →
      α ≤ (pValue v (complementObserved o) : ℝ)) →
      ∃ x, (upperRun true (complementObserved o) reject idx).value = some x ∧
        lower α o ≤ -(x : ℝ)/o.total)

/-- Conditional-on-data interval inclusions, before averaging over randomization. -/
def W1T7ConditionalInclusions : Prop :=
  ∀ (n m K : ℕ) (o : Counts) (α ε : ℝ), o.total = n → o.a+o.b = m →
    (0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) → 0 < K →
    (0 < α ∧ α < 1) → (0 < ε ∧ ε < α) →
    uniformProb (fun p : W1Pool n m K => exactInterval α o ⊆ monteInterval true α ε o p) ≥
      1-2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2) ∧
    (0 < α-2*ε → uniformProb (fun p : W1Pool n m K =>
      monteInterval true α ε o p ⊆ exactInterval (α-2*ε) o) ≥
      1-2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2))

/-- Joint inclusion bounds for every fixed labeled potential-outcome table. -/
def W1T7Labeled : Prop :=
  ∀ (n m K : ℕ) (w : PotentialTable n) (α ε : ℝ), 0 < m → n = 2*m → 0 < K →
    (0 < α ∧ α < 1) → (0 < ε ∧ ε < α) →
    uniformProb (fun ω : Assignment n m × W1Pool n m K =>
      exactInterval α (w1Observed w ω.1.val) ⊆
        monteInterval true α ε (w1Observed w ω.1.val) ω.2) ≥
      1-2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2) ∧
    (0 < α-2*ε → uniformProb (fun ω : Assignment n m × W1Pool n m K =>
      monteInterval true α ε (w1Observed w ω.1.val) ω.2 ⊆
        exactInterval (α-2*ε) (w1Observed w ω.1.val)) ≥
      1-2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2))

/-- pp. 27–28 (PDF pp. 27–28), corrected Lemma B.15 and its corrected proof.
For every fixed binary table in a positive balanced design, fresh independent
Monte Carlo batches give each of the two stated interval inclusions with probability
at least 1−2D exp(−2K ε²), the second when α−2ε>0. Each endpoint obeys the
midpoint/zero-query decomposition of D. Given every positive-mass preceding history,
the performed indicator and selected table are fixed, the current batch is iid uniform,
and both one-test errors have probability at most exp(−2K ε²). Each endpoint's
bad-event probability is at most D exp(−2K ε²). Absence of the corresponding errors
gives all four deterministic upper/lower comparisons. The inclusion bounds hold
conditionally on the observed counts and jointly over randomization and the draws. -/
def T7WholeStatement : Prop :=
  T7Statement ∧ W1BudgetFloor ∧ W1QueryCosts ∧ W1T7Budget ∧
    W1T7Conditional false ∧ W1T7Conditional true ∧ W1T7Errors ∧
    W1T7Comparisons ∧ W1T7ConditionalInclusions ∧ W1T7Labeled

def w1Trace_exact : List (Counts × Bool) :=
  [
    (⟨1,9,0,20⟩,true),
    (⟨2,9,0,19⟩,false),
    (⟨1,12,0,17⟩,true),
    (⟨2,12,0,16⟩,true),
    (⟨3,12,0,15⟩,true),
    (⟨3,13,1,13⟩,true),
    (⟨3,14,2,11⟩,true),
    (⟨1,10,0,19⟩,true),
    (⟨2,10,0,18⟩,true),
    (⟨3,10,0,17⟩,false),
    (⟨1,11,0,18⟩,true),
    (⟨2,11,0,17⟩,true),
    (⟨3,11,0,16⟩,true),
    (⟨3,12,1,14⟩,true),
    (⟨3,13,2,12⟩,true),
    (⟨3,14,3,10⟩,true)]

def w1Trace_low : List (Counts × Bool) :=
  [
    (⟨1,9,0,20⟩,false),
    (⟨1,12,0,17⟩,true),
    (⟨2,12,0,16⟩,true),
    (⟨3,12,0,15⟩,true),
    (⟨3,13,1,13⟩,true),
    (⟨3,14,2,11⟩,true),
    (⟨1,10,0,19⟩,true),
    (⟨2,10,0,18⟩,true),
    (⟨3,10,0,17⟩,false),
    (⟨1,11,0,18⟩,true),
    (⟨2,11,0,17⟩,true),
    (⟨3,11,0,16⟩,true),
    (⟨3,12,1,14⟩,true),
    (⟨3,13,2,12⟩,true),
    (⟨3,14,3,10⟩,true)]

def w1Trace_A : List (Counts × Bool) :=
  [
    (⟨1,9,0,20⟩,false),
    (⟨1,12,0,17⟩,true),
    (⟨2,12,0,16⟩,true),
    (⟨3,12,0,15⟩,true),
    (⟨3,13,1,13⟩,true),
    (⟨3,14,2,11⟩,true),
    (⟨1,10,0,19⟩,true),
    (⟨2,10,0,18⟩,true),
    (⟨3,10,0,17⟩,true),
    (⟨3,11,1,15⟩,true),
    (⟨3,12,2,13⟩,true),
    (⟨3,13,3,11⟩,true),
    (⟨3,14,4,9⟩,true)]

def w1Trace_B : List (Counts × Bool) :=
  [
    (⟨1,9,0,20⟩,true),
    (⟨2,9,0,19⟩,false),
    (⟨1,12,0,17⟩,false),
    (⟨1,14,0,15⟩,false),
    (⟨1,15,0,14⟩,false),
    (⟨1,16,0,13⟩,false)]

def w1Trace_D : List (Counts × Bool) :=
  [
    (⟨1,9,0,20⟩,true),
    (⟨2,9,0,19⟩,true),
    (⟨3,9,0,18⟩,false),
    (⟨1,12,0,17⟩,false),
    (⟨1,14,0,15⟩,false),
    (⟨1,15,0,14⟩,false),
    (⟨1,16,0,13⟩,false)]

/-- All displayed candidate lists, not just the tested prefixes. -/
def W1T6Candidates : Prop :=
  candidates adaptiveData 9 =
    [⟨1,9,0,20⟩, ⟨2,9,0,19⟩, ⟨3,9,0,18⟩, ⟨3,10,1,16⟩, ⟨3,11,2,14⟩, ⟨3,12,3,12⟩, ⟨3,13,4,10⟩, ⟨3,14,5,8⟩] ∧
  candidates adaptiveData 10 =
    [⟨1,10,0,19⟩, ⟨2,10,0,18⟩, ⟨3,10,0,17⟩, ⟨3,11,1,15⟩, ⟨3,12,2,13⟩, ⟨3,13,3,11⟩, ⟨3,14,4,9⟩] ∧
  candidates adaptiveData 11 =
    [⟨1,11,0,18⟩, ⟨2,11,0,17⟩, ⟨3,11,0,16⟩, ⟨3,12,1,14⟩, ⟨3,13,2,12⟩, ⟨3,14,3,10⟩] ∧
  candidates adaptiveData 12 =
    [⟨1,12,0,17⟩, ⟨2,12,0,16⟩, ⟨3,12,0,15⟩, ⟨3,13,1,13⟩, ⟨3,14,2,11⟩] ∧
  candidates adaptiveData 14 =
    [⟨1,14,0,15⟩, ⟨2,14,0,14⟩, ⟨3,14,0,13⟩] ∧
  candidates adaptiveData 15 =
    [⟨1,15,0,14⟩, ⟨2,15,0,13⟩] ∧
  candidates adaptiveData 16 =
    [⟨1,16,0,13⟩]

/-- Every displayed individual exact rational p-value. -/
def W1T6PValues : Prop :=
  pValue ⟨1,9,0,20⟩ adaptiveData = 412/10005 ∧
  pValue ⟨2,9,0,19⟩ adaptiveData = 752/10005 ∧
  pValue ⟨3,9,0,18⟩ adaptiveData = 20042/190095 ∧
  pValue ⟨1,10,0,19⟩ adaptiveData = 349/20010 ∧
  pValue ⟨2,10,0,18⟩ adaptiveData = 6917/190095 ∧
  pValue ⟨3,10,0,17⟩ adaptiveData = 7143/126730 ∧
  pValue ⟨3,11,1,15⟩ adaptiveData = 347731/6463230 ∧
  pValue ⟨3,12,2,13⟩ adaptiveData = 3772099/77558760 ∧
  pValue ⟨3,13,3,11⟩ adaptiveData = 397403/9694845 ∧
  pValue ⟨3,14,4,9⟩ adaptiveData = 103/3306 ∧
  pValue ⟨1,11,0,18⟩ adaptiveData = 43/6555 ∧
  pValue ⟨2,11,0,17⟩ adaptiveData = 8921/570285 ∧
  pValue ⟨3,11,0,16⟩ adaptiveData = 29093/1077205 ∧
  pValue ⟨3,12,1,14⟩ adaptiveData = 79726/3231615 ∧
  pValue ⟨3,13,2,12⟩ adaptiveData = 401731/19389690 ∧
  pValue ⟨3,14,3,10⟩ adaptiveData = 2941/190095 ∧
  pValue ⟨1,12,0,17⟩ adaptiveData = 407/190095 ∧
  pValue ⟨2,12,0,16⟩ adaptiveData = 18854/3231615 ∧
  pValue ⟨3,12,0,15⟩ adaptiveData = 3847/340170 ∧
  pValue ⟨3,13,1,13⟩ adaptiveData = 248263/25852920 ∧
  pValue ⟨3,14,2,11⟩ adaptiveData = 23017/3231615 ∧
  pValue ⟨1,14,0,15⟩ adaptiveData = 9781/77558760 ∧
  pValue ⟨1,15,0,14⟩ adaptiveData = 743/38779380 ∧
  pValue ⟨1,16,0,13⟩ adaptiveData = 1/646323

/-- Full chronological tested-vector transcripts of the exact and three witness paths. -/
def W1T6Traces : Prop :=
  upperRun false adaptiveData (exactRejectQ (1/20) adaptiveData) = ⟨some 10,w1Trace_exact⟩ ∧
  upperRun false adaptiveData (exactRejectQ (1/25) adaptiveData) = ⟨some 10,w1Trace_low⟩ ∧
  upperRun false adaptiveData (fun _ i => decide (i ≠ 0)) = ⟨some 9,w1Trace_A⟩ ∧
  upperRun false adaptiveData (fun _ i => decide (i = 0)) = ⟨some 16,w1Trace_B⟩ ∧
  upperRun false adaptiveData (fun _ i => decide (i < 2)) = ⟨some 16,w1Trace_D⟩ ∧
  firstMismatch w1Trace_exact w1Trace_A = 0 ∧
  firstMismatch w1Trace_low w1Trace_B = 0 ∧
  firstMismatch w1Trace_exact w1Trace_D = 1

/-- The four actual events whose conditional probabilities are compared in clause E. -/
def w1T6Event (j : Fin 4) (pool : W1Pool 30 15 1) : Prop :=
  let b := upperRun false adaptiveData (approximateReject (1/20) (1/200) adaptiveData pool)
  match j.val with
  | 0 => ∃ x, b.value = some x ∧ x < 10
  | 1 => let J := firstMismatch w1Trace_exact b.trace
         J < w1Trace_exact.length ∧ b.trace[J]!.2 = true
  | 2 => ∃ x, b.value = some x ∧ 10 < x
  | _ => let J := firstMismatch w1Trace_low b.trace
         J < w1Trace_low.length ∧ b.trace[J]!.2 = false

/-- Strict half-last-place enclosures interpret the explicitly approximate decimals. -/
def W1T6Rounding : Prop :=
  ∀ j : Fin 4,
    |uniformProb (w1T6Event j) - (![0.86285,0.94885,0.03005,0.00380] : Fin 4 → ℝ) j| <
      0.000005

/-- The failed aggregate estimate, stated as the actual sum over exact trace indices. -/
def W1T6Aggregate : Prop :=
  let a := upperRun false adaptiveData (exactRejectQ (1/20) adaptiveData)
  let bad := fun (i : ℕ) (pool : W1Pool 30 15 5000) =>
    let b := upperRun false adaptiveData (approximateReject (1/20) (1/50) adaptiveData pool)
    i < b.trace.length ∧ b.trace[i]!.2 = true ∧ a.trace[i]!.2 = false
  (4693104776190294207 : ℝ)/5012394999999664375 ≤
    ∑ i ∈ Finset.range a.trace.length, uniformProb (bad i) ∧
  (a.trace.length : ℝ)*Real.exp (-2*(5000 : ℝ)*(1/50)^2) = 16*Real.exp (-4) ∧
  (a.trace.length : ℝ)*Real.exp (-2*(5000 : ℝ)*(1/50)^2) <
    ∑ i ∈ Finset.range a.trace.length, uniformProb (bad i)

/-- pp. 27–28 (PDF pp. 27–28), printed proof of Lemma B.15.
The printed intermediate event identities, the resulting two probability equalities,
and aggregate estimate are false: the stated n=30,m=15 data have positive probability,
candidate numerators −14,…,16 and printed search domain 2,…,16, and 896 distinct
possible count vectors. Both exact intervals are [−1/5,1/3]. The full candidate
lists, individual p-values, exact and A/B/D transcripts, positive path probabilities,
four rounded event probabilities and the K=5000 aggregate counterexample all hold.
These counterexamples concern the intermediate proof assertions. -/
def T6WholeStatement : Prop :=
  T6Statement ∧
  candidateNumerators adaptiveData = (List.range 31).map (fun k : ℕ => (k : ℤ)-14) ∧
  2*((adaptiveData.a : ℤ)-adaptiveData.c) = 2 ∧
  (adaptiveData.a : ℤ)-adaptiveData.c+(adaptiveData.a+adaptiveData.b) = 16 ∧
  (possibleTables adaptiveData).toFinset.card = 896 ∧
  W1T6Candidates ∧ W1T6PValues ∧ W1T6Traces ∧ W1T6Rounding ∧ W1T6Aggregate

/-- The literal confidence set, with the paper's actual correlated reuse draws. -/
def w1LiteralSet {n m K : ℕ} (α : ℝ) (θ : Counts → ℝ) (R : Counts → Counts → ℝ)
    (o : Counts)
    (initial : (Fin (n+1) × Fin (n+1)) → Fin K → Assignment n m)
    (seeds : (Fin (n+1) × Fin (n+1)) → Fin n → Fin K →
      (Fin n.factorial × Fin n.factorial)) : Set ℝ :=
  {t | ∃ ij : Fin (n+1) × Fin (n+1), ∃ v : Counts,
    w1LiteralBase o ((candidateNumerators o).reverse[ij.1.val]!) = some (ij.2.val,v) ∧
    ∃ k ≤ n, k ≤ v.a ∧ k ≤ v.d ∧ Possible o (reuseVector v k) ∧
      t = θ (reuseVector v k) ∧
      α < rankValue R o (reuseVector v k) (reusedSamples v (initial ij) (seeds ij) k)}

def w1T35Population : Counts := ⟨0,1,1,0⟩
def w1T35Theta (u : Counts) : ℝ := if u = w1T35Population then 1 else 0

/-- p. 13 (PDF p. 13), Theorem 5.5(1); Appendix C, p. 28; literal Algorithm 5.3.
The printed claim is false: take n=2,m=1, true counts (0,1,1,0), α=1/4,
any positive K, θ the indicator of that true vector, and R identically zero.
Every rank equals one. The two observations each have probability 1/2; the literal
schedule omits the possible true vector on the all-zero observation and includes it
on the all-one observation. Thus joint coverage is exactly 1/2 < 3/4. -/
def T35WholeStatement : Prop :=
  w1T35Population.total = 2 ∧
  Possible ⟨0,1,0,1⟩ w1T35Population ∧
  w1LiteralVisited ⟨0,1,0,1⟩ = [⟨0,1,0,1⟩,⟨0,0,0,2⟩,⟨0,0,1,1⟩] ∧
  w1LiteralVisited ⟨1,0,1,0⟩ = [⟨1,1,0,0⟩,⟨0,1,1,0⟩,⟨1,0,1,0⟩] ∧
  w1T35Population ∉ w1LiteralVisited ⟨0,1,0,1⟩ ∧
  (∀ (K : ℕ) (o v : Counts) (samples : Fin K → Counts),
    rankValue (fun _ _ => 0) o v samples = 1) ∧
  ∀ K : ℕ, 0 < K →
    uniformProb (fun ω : GeneralSpace 2 1 K => w1T35Theta w1T35Population ∈
      w1LiteralSet (1/4) w1T35Theta (fun _ _ => 0)
        (canonicalObserved w1T35Population ω.1.val) ω.2.1 ω.2.2) = 1/2 ∧
    uniformProb (fun ω : GeneralSpace 2 1 K => w1T35Theta w1T35Population ∈
      w1LiteralSet (1/4) w1T35Theta (fun _ _ => 0)
        (canonicalObserved w1T35Population ω.1.val) ω.2.1 ω.2.2) < 1-1/4

end
end SAP.P003b
