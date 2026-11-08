import Mathlib
import SAP.P003a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

/-- The effect lattice (2.10), with integer numerators and the observed population size. -/
def w1CandidateLattice (o : Counts) : Set ℝ :=
  {t | ∃ d ∈ candidateNumerators o, t = (d : ℝ) / o.total}

/-- An attained maximum; this formulation never assigns an extremum to an empty fiber. -/
def w1MaxP (o : Counts) (d : ℤ) (p : ℚ) : Prop :=
  (∀ v, Possible o v → v.effect = d → pValue v o ≤ p) ∧
  ∃ v, Possible o v ∧ v.effect = d ∧ pValue v o = p

/-- Footnote 9's maxima, in increasing effect-numerator order. -/
def w1FootnoteMaxima : List (ℤ × ℚ) :=
  [(-6,1/36),(-5,1/12),(-4,1/6),(-3,4/9),(-2,1/2),
   (-1,29/36),(0,1),(1,1),(2,2/3),(3,1/12)]

/-- The entire effect-minus-one fiber, in the order used in the corrected claim. -/
def w1FootnoteNegative : List Counts :=
  [⟨1,0,1,7⟩,⟨0,1,2,6⟩,⟨0,2,3,4⟩,⟨0,3,4,2⟩,⟨1,1,2,5⟩,⟨1,2,3,3⟩]

/-- P003-T21; p. 7 (PDF p. 7), footnote 9, corrected.
In the legal nine-unit, seven-treated experiment, the 42 possible vectors have the
ten stated attained maximum p-values. Exactly zero and one ninth are accepted;
the interval is [0,1/9] and excludes the observed one seventh. The complete
negative-effect fiber and both possible p-equals-one witnesses are certified. -/
def T21WholeStatement : Prop :=
  T21Statement ∧
  (let o : Counts := ⟨1,6,0,2⟩;
    o.total = 9 ∧ o.a+o.b = 7 ∧ 0 < o.a+o.b ∧ 0 < o.c+o.d ∧
    Fintype.card (Assignment 9 7) = 36 ∧
    candidateNumerators o = [-6,-5,-4,-3,-2,-1,0,1,2,3] ∧
    possibleTables o = (List.range 2).flatMap (fun i =>
      (List.range 7).flatMap fun j =>
        (List.range 3).map fun l => (⟨i,1-i+l,j,8-j-l⟩ : Counts)) ∧
    (possibleTables o).toFinset.card = 42 ∧
    (∀ dp ∈ w1FootnoteMaxima, w1MaxP o dp.1 dp.2) ∧
    ((possibleTables o).filter (fun v => v.effect = -1)).toFinset =
      w1FootnoteNegative.toFinset ∧
    w1FootnoteNegative.map (fun v => pValue v o) =
      [29/36,18/36,17/36,16/36,19/36,16/36] ∧
    accepted ((17/18 : ℚ) : ℝ) o = {0,1/9} ∧
    exactInterval ((17/18 : ℚ) : ℝ) o = Set.Icc 0 (1/9) ∧
    estimate o ∉ exactInterval ((17/18 : ℚ) : ℝ) o ∧
    (Possible o ⟨0,1,0,8⟩ ∧ pValue ⟨0,1,0,8⟩ o = 1 ∧ tauQ ⟨0,1,0,8⟩ = 1/9) ∧
    (Possible o ⟨1,0,0,8⟩ ∧ pValue ⟨1,0,0,8⟩ o = 1 ∧ tauQ ⟨1,0,0,8⟩ = 0))

/-- One call to a direct test (k=0) or a draw-reuse test (k>0). -/
structure W1Visit (n : ℕ) where
  slot : Fin (n+1) × Fin (n+1)
  base : Counts
  k : ℕ
  deriving DecidableEq, Repr

/-- Positive reuse indices only, with both subtraction bounds and possibility checked. -/
def w1ReuseLine (o v : Counts) : List ℕ :=
  ((List.range o.total).map (fun k => k+1)).filter fun k =>
    k ≤ v.a ∧ k ≤ v.d ∧ Possible o (reuseVector v k)

/-- All tests on a nonempty line: its minimum base followed by the possible reuse line. -/
def w1LineVisits (o : Counts) (i j : Fin (o.total+1)) : List (W1Visit o.total) :=
  match firstOnLine o ((candidateNumerators o).reverse[i.val]!) j.val with
  | none => []
  | some v => ⟨(i,j),v,0⟩ :: (w1ReuseLine o v).map (fun k => ⟨(i,j),v,k⟩)

/-- The literal reading used by the counterexample stops at the first feasible j. -/
def w1FirstLineVisits (o : Counts) (i : Fin (o.total+1)) :
    List (Fin (o.total+1)) → List (W1Visit o.total)
  | [] => []
  | j::js => if (w1LineVisits o i j).isEmpty then w1FirstLineVisits o i js
      else w1LineVisits o i j

/-- Descending effects, ascending j; the corrected continuation visits every j. -/
def w1Traversal (corrected : Bool) (o : Counts) : List (W1Visit o.total) :=
  (List.finRange (o.total+1)).flatMap fun i =>
    if corrected then (List.finRange (o.total+1)).flatMap (w1LineVisits o i)
    else w1FirstLineVisits o i (List.finRange (o.total+1))

/-- The exact count update (5.21)-(5.26); seed residues choose the two type groups. -/
def w1UpdateTreated (v q : Counts) (s₀ s₁ : ℕ) : Counts :=
  let c₀ := s₀ % v.d < v.d-q.d
  let c₁ := s₁ % v.a < v.a-q.a
  ⟨if c₁ then q.a else q.a-1, if c₁ then q.b else q.b+1,
   if c₀ then q.c else q.c+1, if c₀ then q.d else q.d-1⟩

/-- Actual correlated draw reuse, including the initial k=0 sample. -/
def w1ReusedSamples {n m K : ℕ} (v : Counts) (initial : Fin K → Assignment n m)
    (seeds : Fin n → Fin K → (Fin n.factorial × Fin n.factorial)) :
    ℕ → Fin K → Counts
  | 0, i => treatedCounts v (initial i).val
  | t+1, i =>
    let s := if h : t < n then seeds ⟨t,h⟩ i else
      (⟨0,Nat.factorial_pos n⟩,⟨0,Nat.factorial_pos n⟩)
    w1UpdateTreated (reuseVector v t) (w1ReusedSamples v initial seeds t i) s.1.val s.2.val

/-- The accumulated output of the finite traversal, using Algorithm 5.1's strict test. -/
noncomputable def w1GeneralOutput {m K : ℕ} (corrected : Bool) (α : ℝ)
    (θ : Counts → ℝ) (R : Counts → Counts → ℝ) (o : Counts)
    (initial : (Fin (o.total+1) × Fin (o.total+1)) → Fin K → Assignment o.total m)
    (seeds : (Fin (o.total+1) × Fin (o.total+1)) → Fin o.total → Fin K →
      (Fin o.total.factorial × Fin o.total.factorial)) : Set ℝ :=
  {t | ∃ s ∈ w1Traversal corrected o,
    t = θ (reuseVector s.base s.k) ∧
    α < rankValue R o (reuseVector s.base s.k)
      (w1ReusedSamples s.base (initial s.slot) (seeds s.slot) s.k)}

/-- The full declarative output, retaining the slot-specific initial draws and updates. -/
noncomputable def w1GeneralFormula {m K : ℕ} (α : ℝ)
    (θ : Counts → ℝ) (R : Counts → Counts → ℝ) (o : Counts)
    (initial : (Fin (o.total+1) × Fin (o.total+1)) → Fin K → Assignment o.total m)
    (seeds : (Fin (o.total+1) × Fin (o.total+1)) → Fin o.total → Fin K →
      (Fin o.total.factorial × Fin o.total.factorial)) : Set ℝ :=
  {t | ∃ ij : Fin (o.total+1) × Fin (o.total+1), ∃ v,
    firstOnLine o ((candidateNumerators o).reverse[ij.1.val]!) ij.2.val = some v ∧
    ∃ k ≤ o.total, k ≤ v.a ∧ k ≤ v.d ∧ Possible o (reuseVector v k) ∧
      t = θ (reuseVector v k) ∧
      α < rankValue R o (reuseVector v k)
        (w1ReusedSamples v (initial ij) (seeds ij) k)}

/-- A labeled two-unit realization; labels in the paper are one greater than Fin indices. -/
def w1OmittedTable : PotentialTable 2 := fun i =>
  if i.val = 0 then (false,true) else (true,false)

/-- P003-T22; pp. 11-12 (PDF pp. 11-12), Algorithm 5.3, corrected.
Continuing with the next j after every processed line gives a finite traversal
of exactly every possible vector, using its minimum base and valid reuse line.
The returned set uses the actual plus-one tests and correlated reuse updates.
For the two-unit example and the constant statistic, every test accepts:
the literal first-line reading returns {0,1}, while the correction returns
{0,1,2}. The omitted value two is realized by the stated labeled experiment. -/
def T22WholeStatement : Prop :=
  T22Statement ∧
  (∀ o u, (∃ s ∈ w1Traversal true o, reuseVector s.base s.k = u) ↔ Possible o u) ∧
  (∀ (m K : ℕ) (α : ℝ) (θ : Counts → ℝ) (R : Counts → Counts → ℝ) (o : Counts)
    (initial : (Fin (o.total+1) × Fin (o.total+1)) → Fin K → Assignment o.total m)
    (seeds : (Fin (o.total+1) × Fin (o.total+1)) → Fin o.total → Fin K →
      (Fin o.total.factorial × Fin o.total.factorial)),
    w1GeneralOutput true α θ R o initial seeds = w1GeneralFormula α θ R o initial seeds) ∧
  (let o : Counts := ⟨0,1,0,1⟩;
    firstOnLine o (-1) 0 = some ⟨0,0,1,1⟩ ∧
    firstOnLine o 1 0 = none ∧ firstOnLine o 1 1 = some ⟨0,1,0,1⟩ ∧
    w1ReuseLine o ⟨0,0,1,1⟩ = [] ∧ w1ReuseLine o ⟨0,0,0,2⟩ = [] ∧
    w1ReuseLine o ⟨0,1,0,1⟩ = [] ∧
    (∀ (K : ℕ) (α : ℝ) (hK : 0 < K) (hα : 0 < α ∧ α < 1)
      (initial : (Fin (o.total+1) × Fin (o.total+1)) → Fin K → Assignment o.total 1)
      (seeds : (Fin (o.total+1) × Fin (o.total+1)) → Fin o.total → Fin K →
        (Fin o.total.factorial × Fin o.total.factorial)),
      w1GeneralOutput false α (fun v => (v.b+v.c : ℕ)) (fun _ _ => 0) o initial seeds =
        {0,1} ∧
      w1GeneralOutput true α (fun v => (v.b+v.c : ℕ)) (fun _ _ => 0) o initial seeds =
        {0,1,2})) ∧
  (∀ (K : ℕ) (o v : Counts) (s : Fin K → Counts), rankValue (fun _ _ => 0) o v s = 1) ∧
  (let z : Finset (Fin 2) := {0};
    z.card = 1 ∧ tableCounts w1OmittedTable = ⟨0,1,1,0⟩ ∧
    unitOutcomes w1OmittedTable z = (fun _ => false) ∧
    unitObserved (unitOutcomes w1OmittedTable z) z = ⟨0,1,0,1⟩ ∧
    ((tableCounts w1OmittedTable).b + (tableCounts w1OmittedTable).c : ℕ) = 2)

end SAP.P003a
