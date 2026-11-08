import SAP.P003a.Defs.WholeW1.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

/-- The explicit population in the missing-data counterexample (paper labels 1,...,20). -/
def w1BadTable : PotentialTable 20 := fun i =>
  if i.val < 11 then (true,true) else if i.val < 14 then (false,true) else (false,false)

def w1CriticalAssignment : Assignment 20 3 := ⟨{11,12,13}, by decide⟩

def w1BadMissing (z : Finset (Fin 20)) : Finset (Fin 20) :=
  if z = w1CriticalAssignment.val then {0} else ∅

def w1BadOutcomes (z : Finset (Fin 20)) : Fin 20 → Bool := unitOutcomes w1BadTable z

/-- Equation (6.1): -1 denotes a missing outcome, and other entries are the observed bits. -/
def w1BadM (z : Finset (Fin 20)) (i : Fin 20) : ℤ :=
  if i ∈ w1BadMissing z then -1 else if w1BadOutcomes z i then 1 else 0

def w1BinaryCompletion {n : ℕ} (M : Fin n → ℤ) (y : Fin n → Bool) : Prop :=
  ∀ i, M i ≠ -1 → (if y i then (1 : ℤ) else 0) = M i

def w1UnitMinus {n : ℕ} (y : Fin n → Bool) (z r : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ r then !decide (i ∈ z) else y i

/-- The union in Appendix D over every labeled binary completion of M. -/
noncomputable def w1LabeledCompletionUnion {n : ℕ} (α : ℝ) (M : Fin n → ℤ)
    (z : Finset (Fin n)) : Set ℝ :=
  {t | ∃ y, w1BinaryCompletion M y ∧ t ∈ exactInterval α (unitObserved y z)}

/-- A row of the complete-data coverage diagnostic, with exact rational endpoints. -/
structure W1CoverageRow where
  o : Counts
  weight : ℕ
  lo : ℚ
  hi : ℚ
  covers : Bool
  deriving DecidableEq, Repr

def w1BadRows : List W1CoverageRow :=
  [⟨⟨0,3,11,6⟩,1,-7/10,-3/20,true⟩,
   ⟨⟨0,3,12,5⟩,18,-3/4,-3/10,false⟩,
   ⟨⟨0,3,13,4⟩,45,-4/5,-7/20,false⟩,
   ⟨⟨0,3,14,3⟩,20,-17/20,-2/5,false⟩,
   ⟨⟨1,2,11,6⟩,33,-11/20,1/20,true⟩,
   ⟨⟨1,2,12,5⟩,198,-3/5,0,true⟩,
   ⟨⟨1,2,13,4⟩,165,-13/20,-1/20,true⟩,
   ⟨⟨2,1,11,6⟩,165,-7/20,1/4,true⟩,
   ⟨⟨2,1,12,5⟩,330,-2/5,1/5,true⟩,
   ⟨⟨3,0,11,6⟩,165,-1/10,2/5,false⟩]

/-- Labeled realization, and the precise transport of its missing mask to count states. -/
def w1BadRealization : Prop :=
  tableCounts w1BadTable = badPopulation ∧ tableTau w1BadTable = -3/20 ∧
  Fintype.card (Assignment 20 3) = 1140 ∧
  (∀ z : Assignment 20 3,
    unitObserved (w1BadOutcomes z.val) z.val = canonicalObserved badPopulation z.val ∧
    (∀ i, w1BadTable i = canonicalPair badPopulation i.val) ∧
    (w1BadMissing z.val = {0} ↔ z = w1CriticalAssignment) ∧
    (w1BadMissing z.val = ∅ ↔ z ≠ w1CriticalAssignment) ∧
    w1BinaryCompletion (w1BadM z.val) (w1BadOutcomes z.val)) ∧
  (let z := w1CriticalAssignment.val;
    0 ∉ z ∧ w1BadOutcomes z 0 = true ∧ w1BadM z 0 = -1 ∧
    unitObserved (w1BadOutcomes z) z = ⟨0,3,11,6⟩ ∧
    w1UnitMinus (w1BadOutcomes z) z (w1BadMissing z) = w1BadOutcomes z ∧
    unitObserved (unitPlus (w1BadOutcomes z) z (w1BadMissing z)) z = ⟨0,3,10,7⟩) ∧
  (∀ E : Counts → Prop,
    uniformProb (fun z : Assignment 20 3 => E (canonicalObserved badPopulation z.val)) =
      designProb badPopulation 3 (fun q => E (observed badPopulation q))) ∧
  (∀ z : Assignment 20 3,
    (Finset.univ.filter fun i => i ∈ w1BadMissing z.val ∧ i ∈ z.val ∧ w1BadOutcomes z.val i = true).card =
      (badMask (treatedCounts badPopulation z.val)).a ∧
    (Finset.univ.filter fun i => i ∈ w1BadMissing z.val ∧ i ∈ z.val ∧ w1BadOutcomes z.val i = false).card =
      (badMask (treatedCounts badPopulation z.val)).b ∧
    (Finset.univ.filter fun i => i ∈ w1BadMissing z.val ∧ i ∉ z.val ∧ w1BadOutcomes z.val i = true).card =
      (badMask (treatedCounts badPopulation z.val)).c ∧
    (Finset.univ.filter fun i => i ∈ w1BadMissing z.val ∧ i ∉ z.val ∧ w1BadOutcomes z.val i = false).card =
      (badMask (treatedCounts badPopulation z.val)).d)

/-- The real critical intervals and the explicit failed inclusion and tail inequality. -/
def w1BadCritical : Prop :=
  (let α : ℝ := (109/500 : ℚ);
    exactInterval α ⟨0,3,11,6⟩ = Set.Icc (-7/10) (-3/20) ∧
    exactInterval α ⟨0,3,10,7⟩ = Set.Icc (-13/20) (-1/5) ∧
    (accepted α ⟨0,3,11,6⟩).Nonempty ∧ (accepted α ⟨0,3,10,7⟩).Nonempty ∧
    missingInterval α ⟨0,3,11,6⟩ ⟨0,0,1,0⟩ = Set.Icc (-7/10) (-1/5) ∧
    (let z := w1CriticalAssignment.val;
      (-3/20 : ℝ) ∈ exactInterval α (unitObserved (w1BadOutcomes z) z) ∧
      exactInterval α (unitObserved (w1BadOutcomes z) z) ⊆
        w1LabeledCompletionUnion α (w1BadM z) z ∧
      (-3/20 : ℝ) ∈ w1LabeledCompletionUnion α (w1BadM z) z ∧
      (-3/20 : ℝ) ∉ missingInterval α ⟨0,3,11,6⟩ ⟨0,0,1,0⟩) ∧
    max (upper α ⟨0,3,10,7⟩) (estimate ⟨0,3,10,7⟩) < (-3/20 : ℝ) ∧
    uniformProb (fun q : Assignment 20 3 =>
      |tableEstimator w1BadTable q.val-(-3/20)| ≥
        |outcomeEstimator (w1BadOutcomes w1CriticalAssignment.val) w1CriticalAssignment.val-(-3/20)|) =
      (83/380 : ℝ) ∧
    uniformProb (fun q : Assignment 20 3 =>
      |tableEstimator w1BadTable q.val-(-3/20)| ≥
        |outcomeEstimator (unitPlus (w1BadOutcomes w1CriticalAssignment.val)
          w1CriticalAssignment.val (w1BadMissing w1CriticalAssignment.val))
          w1CriticalAssignment.val-(-3/20)|) = (83/380 : ℝ))

/-- The ten groups, their labeled multiplicities, real intervals and coverage bits. -/
def w1BadDiagnostics : Prop :=
  (w1BadRows.map W1CoverageRow.o).Nodup ∧
  (∀ z : Assignment 20 3, ∃ r ∈ w1BadRows,
    unitObserved (w1BadOutcomes z.val) z.val = r.o) ∧
  (∀ r ∈ w1BadRows,
    (Finset.univ.filter fun z : Assignment 20 3 =>
      unitObserved (w1BadOutcomes z.val) z.val = r.o).card = r.weight ∧
    intervalQ (109/500) r.o = some (r.lo,r.hi) ∧
    exactInterval ((109/500 : ℚ) : ℝ) r.o = Set.Icc (r.lo : ℝ) (r.hi : ℝ) ∧
    estimate r.o ∈ exactInterval ((109/500 : ℚ) : ℝ) r.o ∧
    ((-3/20 : ℝ) ∈ exactInterval ((109/500 : ℚ) : ℝ) r.o ↔ r.covers = true))

/-- Actual labeled coverage and the equality of intervals off the one exceptional assignment. -/
def w1BadCoverageFacts : Prop :=
  (Finset.univ.filter fun z : Assignment 20 3 => w1BadMissing z.val = ∅).card = 1139 ∧
  (∀ z : Assignment 20 3, z ≠ w1CriticalAssignment →
    missingInterval ((109/500 : ℚ) : ℝ)
        (unitObserved (w1BadOutcomes z.val) z.val) ⟨0,0,0,0⟩ =
      exactInterval ((109/500 : ℚ) : ℝ) (unitObserved (w1BadOutcomes z.val) z.val)) ∧
  uniformProb (fun z : Assignment 20 3 =>
    (-3/20 : ℝ) ∈ exactInterval ((109/500 : ℚ) : ℝ)
      (unitObserved (w1BadOutcomes z.val) z.val)) = (892/1140 : ℝ) ∧
  uniformProb (fun z : Assignment 20 3 =>
    (-3/20 : ℝ) ∈ missingInterval ((109/500 : ℚ) : ℝ)
      (unitObserved (w1BadOutcomes z.val) z.val) (badMask (treatedCounts badPopulation z.val))) =
    (297/380 : ℝ)

/-- P003-T1; Section 6, pp. 13-14 (PDF pp. 13-14); Appendix D, p. 29.
The printed claim is false: the specified binary twenty-unit population,
three-treated uniform design and assignment-dependent single missing entry
have imputation coverage 297/380, below 1-109/500 by 1/2375. The labeled
critical assignment, its two completions and real intervals refute (D.3);
both actual tails in (D.7) are 83/380, above alpha despite (D.5). Among tables
possible for the upper completion with effect at least -3/20, the maximum
p-value is 248/1140, attained at (8,0,3,9) and (9,0,3,8).
All ten complete-data groups, their multiplicities, intervals and coverage
bits are explicit; the other 1139 assignments retain the complete interval,
whose overall coverage is 892/1140. -/
def T1WholeStatement : Prop :=
  T1Statement ∧ w1BadRealization ∧ w1BadCritical ∧
  (∀ v, Possible ⟨0,3,10,7⟩ v → (-3/20 : ℚ) ≤ tauQ v →
    pValue v ⟨0,3,10,7⟩ ≤ 248/1140 ∧
    (pValue v ⟨0,3,10,7⟩ = 248/1140 ↔ v = ⟨8,0,3,9⟩ ∨ v = ⟨9,0,3,8⟩)) ∧
  (Possible ⟨0,3,10,7⟩ ⟨8,0,3,9⟩ ∧ tauQ ⟨8,0,3,9⟩ = -3/20 ∧
    pValue ⟨8,0,3,9⟩ ⟨0,3,10,7⟩ = 248/1140 ∧
    Possible ⟨0,3,10,7⟩ ⟨9,0,3,8⟩ ∧ tauQ ⟨9,0,3,8⟩ = -3/20 ∧
    pValue ⟨9,0,3,8⟩ ⟨0,3,10,7⟩ = 248/1140 ∧ (248/1140 : ℚ) < 109/500) ∧
  w1BadDiagnostics ∧ w1BadCoverageFacts ∧
  (33+198+165+165+330 : ℕ) = 891 ∧
  (891/1140 : ℚ) = 297/380 ∧ (249/1140 : ℚ) = 83/380 ∧
  (1-(109/500 : ℚ))-(297/380 : ℚ) = 1/2375

end SAP.P003a
