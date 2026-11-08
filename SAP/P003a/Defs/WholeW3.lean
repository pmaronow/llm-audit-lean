import Mathlib
import SAP.P003a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

/-- Exact probability mass at a physical, rational estimator value. -/
noncomputable def wholeEstimatorMass (v : Counts) (m : ℕ) (x : ℚ) : ℝ :=
  designProb v m (fun q => estimateQ (observed v q) = x)

/-- Two equiprobable values; coincident values give a point mass. -/
noncomputable def wholeTwoPointMass (a b x : ℚ) : ℝ :=
  (if x = a then 1/2 else 0) + (if x = b then 1/2 else 0)

/-- All seven discordant two-subject populations and their two estimator values. -/
def wholeBaseRows : List (Counts × ℚ × ℚ) :=
  [(⟨1,1,0,0⟩,0,1), (⟨0,1,0,1⟩,0,1),
   (⟨1,0,1,0⟩,-1,0), (⟨0,0,1,1⟩,-1,0),
   (⟨0,2,0,0⟩,1,1), (⟨0,0,2,0⟩,-1,-1), (⟨0,1,1,0⟩,0,0)]

/-- The four-subject sampling laws attached to the printed-proof witnesses.
The last row is the residual population, rather than the six-subject population. -/
def wholeWitnessRows : List (Counts × ℚ × ℚ) :=
  [(⟨0,4,0,0⟩,1,1), (⟨1,3,0,0⟩,1/2,1),
   (⟨1,2,1,0⟩,0,1/2), (⟨0,3,0,1⟩,1/2,1)]

def wholeRemovals10 : List Counts :=
  [⟨1,1,0,0⟩,⟨0,2,0,0⟩,⟨0,1,1,0⟩,⟨0,1,0,1⟩]

def wholeRemovals01 : List Counts :=
  [⟨1,0,1,0⟩,⟨0,1,1,0⟩,⟨0,0,2,0⟩,⟨0,0,1,1⟩]

def wholeCountsLE (a v : Counts) : Prop :=
  a.a ≤ v.a ∧ a.b ≤ v.b ∧ a.c ≤ v.c ∧ a.d ≤ v.d

/-- Natural subtraction is used only after coordinatewise feasibility is established. -/
def wholeCountsSub (v a : Counts) : Counts :=
  ⟨v.a-a.a,v.b-a.b,v.c-a.c,v.d-a.d⟩

/-- The cases actually printed in the induction paragraph, including its doubled c. -/
def wholePrintedInductionCases (v : Counts) : Prop :=
  (v.b = 1 ∧ v.c = 0) ∨ (v.b = 0 ∧ v.c = 1) ∨ v.c+v.c = 2 ∨
    (2 < v.c+v.c ∧ ((2 ≤ v.b ∧ 1 ≤ v.c) ∨ (1 ≤ v.b ∧ 2 ≤ v.c)))

/-- P003-T15; p. 25 (PDF p. 25).
For every positive balanced design with a discordant unit, mT has an SD mass on the
integers, equivalently T is SD on the lattice with spacing 1/m. The seven admissible
two-subject populations have the stated constant or consecutive-two-point laws.
The cases with one or two discordant units satisfy the same conclusion. Each removal
in (B.45) or (B.46) removes two subjects and at most two discordant units; when there
are at least three discordant units, one discordant count is at least two and every
feasible listed residual is a positive balanced design with an SD estimator law.
The four printed-proof gap witnesses have the stated arithmetic and complete sampling
laws, including zero probability away from their listed values. -/
def T15WholeStatement : Prop :=
  (∀ (v : Counts) (m : ℕ), 0 < m → v.total = 2*m → 1 ≤ v.b+v.c →
    IsSD (scaledEstimatorMass v m)) ∧
  ((∀ v : Counts, v.total = 2 → 1 ≤ v.b+v.c →
      ∃ r ∈ wholeBaseRows, r.1 = v) ∧
    (∀ r ∈ wholeBaseRows, ∀ x : ℚ,
      wholeEstimatorMass r.1 1 x = wholeTwoPointMass r.2.1 r.2.2 x)) ∧
  (∀ (v : Counts) (m : ℕ), 0 < m → v.total = 2*m →
    (v.b+v.c = 1 ∨ v.b+v.c = 2) → IsSD (scaledEstimatorMass v m)) ∧
  (∀ a : Counts, a ∈ wholeRemovals10 ∨ a ∈ wholeRemovals01 →
    a.total = 2 ∧ a.b+a.c ≤ 2) ∧
  (∀ (v : Counts) (m : ℕ), 0 < m → v.total = 2*m → 3 ≤ v.b+v.c →
    (2 ≤ v.b ∨ 2 ≤ v.c) ∧
    ∀ a : Counts, (a ∈ wholeRemovals10 ∨ a ∈ wholeRemovals01) →
      wholeCountsLE a v →
      let u := wholeCountsSub v a;
      u.total = 2*(m-1) ∧ 1 ≤ m-1 ∧ v.b+v.c-2 ≤ u.b+u.c ∧
        1 ≤ u.b+u.c ∧ IsSD (scaledEstimatorMass u (m-1))) ∧
  ((∀ v ∈ ([⟨0,4,0,0⟩,⟨1,3,0,0⟩] : List Counts),
      v.total = 4 ∧ 1 ≤ v.b+v.c ∧ min v.b v.c = 0 ∧
        ¬ wholePrintedInductionCases v) ∧
    (⟨1,2,1,0⟩ : Counts).c+(⟨1,2,1,0⟩ : Counts).c = 2 ∧
    (⟨1,2,1,0⟩ : Counts).b+(⟨1,2,1,0⟩ : Counts).c = 3 ∧
    wholeCountsLE ⟨0,1,1,0⟩ ⟨0,4,1,1⟩ ∧
    wholeCountsSub ⟨0,4,1,1⟩ ⟨0,1,1,0⟩ = ⟨0,3,0,1⟩ ∧
    min (wholeCountsSub ⟨0,4,1,1⟩ ⟨0,1,1,0⟩).b
      (wholeCountsSub ⟨0,4,1,1⟩ ⟨0,1,1,0⟩).c = 0) ∧
  (∀ r ∈ wholeWitnessRows,
    (∀ x : ℚ, wholeEstimatorMass r.1 2 x = wholeTwoPointMass r.2.1 r.2.2 x) ∧
    IsSD (scaledEstimatorMass r.1 2))

/-- Partners and remaining treatment sets retain the original labels. -/
abbrev WholePartner (n : ℕ) (i : Fin n) := {j : Fin n // j ≠ i}

abbrev WholeRemaining (n : ℕ) (i j : Fin n) := {k : Fin n // k ≠ i ∧ k ≠ j}

abbrev WholeResidualAssignment (n m : ℕ) (i j : Fin n) :=
  {s : Finset (Fin n) // s.card = m-1 ∧ i ∉ s ∧ j ∉ s}

/-- Uniform probability on this finite dependent sum is the partner sampler's source.
Its conditional product law is asserted in the whole statement, not assumed. -/
abbrev WholePairSource (n m : ℕ) (i : Fin n) :=
  (j : WholePartner n i) × (Bool × WholeResidualAssignment n m i j.val)

def wholePairSample {n m : ℕ} {i : Fin n} (ω : WholePairSource n m i) :
    Finset (Fin n) :=
  insert (if ω.2.1 then i else ω.1.val) ω.2.2.val

/-- A rectangular event in the conditional source for a specified partner. -/
def wholePairRectangle {n m : ℕ} {i : Fin n} (j : WholePartner n i)
    (E : Bool → Prop) (F : WholeResidualAssignment n m i j.val → Prop)
    (ω : WholePairSource n m i) : Prop :=
  ∃ (b : Bool) (r : WholeResidualAssignment n m i j.val),
    E b ∧ F r ∧ ω = ⟨j,(b,r)⟩

def wholeSignedTerm {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n))
    (i : Fin n) : ℝ := if i ∈ z then bit (w i).1 else -bit (w i).2

noncomputable def wholeResidualContribution {n : ℕ} (w : PotentialTable n)
    (z : Finset (Fin n)) (m : ℕ) (i j : Fin n) : ℝ :=
  (∑ k ∈ (Finset.univ.erase i).erase j, wholeSignedTerm w z k)/(m : ℝ)

def wholeRestrictedTable {n : ℕ} (w : PotentialTable n) {i j : Fin n}
    (e : Fin (n-2) ≃ WholeRemaining n i j) : PotentialTable (n-2) :=
  fun k => w (e k).val

def wholeRestrictedAssignment {n : ℕ} (z : Finset (Fin n)) {i j : Fin n}
    (e : Fin (n-2) ≃ WholeRemaining n i j) : Finset (Fin (n-2)) :=
  Finset.univ.filter fun k => (e k).val ∈ z

def wholePrintedPair (w₁ w₂ : Bool × Bool) (b : Bool) : ℤ :=
  if b then (if w₁.1 then 1 else 0) + (if w₂.2 then 1 else 0)
  else (if w₂.1 then 1 else 0) + (if w₁.2 then 1 else 0)

/-- An actual probability law, including coincident atoms and zero mass elsewhere. -/
def WholeFairLaw (f : Bool → ℤ) (a b : ℤ) : Prop :=
  ∀ x : ℤ, uniformProb (fun z : Bool => f z = x) =
    (if x = a then 1/2 else 0) + (if x = b then 1/2 else 0)

/-- Corrected and printed laws, in the order of the six cases on p. 24. -/
def WholePairLaws : Prop :=
  WholeFairLaw (pairContribution (true,false) (true,true)) 0 1 ∧
  WholeFairLaw (pairContribution (true,false) (true,false)) 1 1 ∧
  WholeFairLaw (pairContribution (true,false) (false,true)) 0 0 ∧
  WholeFairLaw (pairContribution (true,false) (false,false)) 1 0 ∧
  WholeFairLaw (pairContribution (true,true) (true,true)) 0 0 ∧
  WholeFairLaw (pairContribution (true,true) (false,false)) 1 (-1) ∧
  WholeFairLaw (wholePrintedPair (true,false) (true,true)) 2 1 ∧
  WholeFairLaw (wholePrintedPair (true,false) (true,false)) 1 1 ∧
  WholeFairLaw (wholePrintedPair (true,false) (false,true)) 2 0 ∧
  WholeFairLaw (wholePrintedPair (true,false) (false,false)) 1 0 ∧
  WholeFairLaw (wholePrintedPair (true,true) (true,true)) 2 2 ∧
  WholeFairLaw (wholePrintedPair (true,true) (false,false)) 1 1

/-- P003-T16; p. 24 (PDF p. 24).
In a positive balanced experiment the estimator is the signed sum divided by m.
Choose a partner uniformly from the other labels, a fair orientation, and independently
a uniform size-(m-1) treatment subset of the remaining labels. This construction gives
the uniform size-m assignment law; its conditional product law is explicit. The pair
contribution to mT is the corrected signed pair expression, and T is that expression
divided by m plus the remaining signed sum divided by m. Every ordering of the remaining
labels gives (B.51); for m>1 it is (m-1)/m times their estimator, and for m=1 it is zero.
The six corrected pair laws and the six different printed plus-sign laws hold under
the same fair orientations, conditional on the chosen partner, relabeled as subject 2. -/
def T16WholeStatement : Prop :=
  (∀ (n m : ℕ), 0 < m → n = 2*m → ∀ (w : PotentialTable n) (z : Assignment n m),
    tableEstimator w z.val = (∑ k, wholeSignedTerm w z.val k)/(m : ℝ)) ∧
  (∀ (n m : ℕ), 0 < m → n = 2*m → ∀ i : Fin n,
    Nonempty (WholePairSource n m i) ∧
    (∀ j : WholePartner n i,
      Nonempty (Fin (n-2) ≃ WholeRemaining n i j.val) ∧
      Nonempty (WholeResidualAssignment n m i j.val)) ∧
    (∀ ω : WholePairSource n m i, (wholePairSample ω).card = m) ∧
    (∀ E : Finset (Fin n) → Prop,
      uniformProb (fun ω : WholePairSource n m i => E (wholePairSample ω)) =
        uniformProb (fun z : Assignment n m => E z.val)) ∧
    (∀ (j : WholePartner n i) (E : Bool → Prop)
      (F : WholeResidualAssignment n m i j.val → Prop),
      uniformProb (wholePairRectangle j E F) =
        (1 / ((n-1 : ℕ) : ℝ)) * uniformProb E * uniformProb F)) ∧
  (∀ (n m : ℕ), 0 < m → n = 2*m →
    ∀ (w : PotentialTable n) (z : Assignment n m) (i : Fin n) (j : WholePartner n i),
    (i ∈ z.val ↔ j.val ∉ z.val) →
    tableEstimator w z.val =
      (pairContribution (w i) (w j.val) (decide (i ∈ z.val)) : ℝ)/(m : ℝ) +
        wholeResidualContribution w z.val m i j.val ∧
    (m = 1 → wholeResidualContribution w z.val m i j.val = 0) ∧
    (∀ e : Fin (n-2) ≃ WholeRemaining n i j.val,
      (wholeRestrictedAssignment z.val e).card = m-1 ∧
      wholeResidualContribution w z.val m i j.val =
        (∑ k : Fin (n-2), wholeSignedTerm (wholeRestrictedTable w e)
          (wholeRestrictedAssignment z.val e) k)/(m : ℝ) ∧
      (1 < m → wholeResidualContribution w z.val m i j.val =
        ((m-1 : ℕ) : ℝ)/(m : ℝ) *
          tableEstimator (wholeRestrictedTable w e) (wholeRestrictedAssignment z.val e)))) ∧
  WholePairLaws

/-- The unsimplified binary within-arm sum of squared residuals (5.10), (5.11). -/
noncomputable def wholeBinaryQ (a b : ℕ) : ℝ :=
  (a : ℝ)*((a : ℝ)/((a : ℝ)+b)-1)^2 +
    (b : ℝ)*((a : ℝ)/((a : ℝ)+b))^2

noncomputable def wholePrintedVariance (o : Counts) : ℝ :=
  wholeBinaryQ o.a o.b / ((o.a : ℝ)+o.b)^2 +
    wholeBinaryQ o.c o.d / ((o.c : ℝ)+o.d)^2

/-- The statistic with one C fixed for every observed, fresh, or reused input. -/
noncomputable def wholePrintedStudentized (C : ℝ) (o v : Counts) : ℝ :=
  if Real.sqrt (wholePrintedVariance o) = 0 then C
  else (estimate o-tau v)/Real.sqrt (wholePrintedVariance o)

/-- The literal plus-one formula on observed count vectors, rather than treated states.
No independence is assumed when this is used simply to describe reused evaluations. -/
noncomputable def wholeObservedRank {K : ℕ} (C : ℝ) (o v : Counts)
    (os : Fin K → Counts) : ℝ :=
  (1+∑ i, if |studentized C (os i) v| ≥ |studentized C o v| then (1 : ℝ) else 0)/(K+1)

def wholeZeroTable : PotentialTable 5 := fun _ => (false,false)

def wholeOneControlTable : PotentialTable 5 :=
  fun i => if i = 0 then (false,true) else (false,false)

/-- P003-T17; p. 11 (PDF p. 11); footnote 13 on the same page.
For two positive observed arms, the printed Q expressions simplify to ab/(a+b) and
cd/(c+d), and the printed variance equals the nonnegative binary variance formula.
Its standard error vanishes exactly when both within-arm products vanish. Fixing one
real C before testing defines the same real statistic on every observed, fresh, and
reused input. The all-zero five-subject population has ten zero-variance assignments;
the population with one (0,1) subject has the stated four versus six assignments,
observations, numerator 1/5, and other variance 2/27. Under every fixed null table the
plus-one Monte Carlo rank satisfies P(S≤alpha)≤alpha. In the second population with
the zero observation, the exact tail probability is 1 for C=0 and 2/5 for C=10^6. -/
def T17WholeStatement : Prop :=
  (∀ o : Counts, 0 < o.a+o.b → 0 < o.c+o.d →
    wholeBinaryQ o.a o.b = (o.a : ℝ)*o.b/((o.a : ℝ)+o.b) ∧
    wholeBinaryQ o.c o.d = (o.c : ℝ)*o.d/((o.c : ℝ)+o.d) ∧
    wholePrintedVariance o = varianceEstimate o ∧ 0 ≤ varianceEstimate o ∧
    (standardError o = 0 ↔ o.a*o.b = 0 ∧ o.c*o.d = 0)) ∧
  (∀ (C : ℝ) (o v : Counts), 0 < o.a+o.b → 0 < o.c+o.d →
    wholePrintedStudentized C o v = studentized C o v ∧
    (standardError o = 0 → studentized C o v = C) ∧
    (0 < standardError o → studentized C o v = (estimate o-tau v)/standardError o)) ∧
  (∀ (C : ℝ) (K : ℕ) (o v : Counts) (samples : Fin K → Counts),
    rankValue (studentized C) o v samples =
      wholeObservedRank C o v (fun i => observed v (samples i))) ∧
  (Fintype.card (Assignment 5 2) = 10 ∧
    tableCounts wholeZeroTable = ⟨0,0,0,5⟩ ∧ tableTau wholeZeroTable = 0 ∧
    tau ⟨0,0,0,5⟩ = 0 ∧
    (∀ z : Assignment 5 2, unitObserved (unitOutcomes wholeZeroTable z.val) z.val =
      ⟨0,2,0,3⟩ ∧ tableEstimator wholeZeroTable z.val = 0) ∧
    estimate ⟨0,2,0,3⟩ = 0 ∧ varianceEstimate ⟨0,2,0,3⟩ = 0 ∧
    standardError ⟨0,2,0,3⟩ = 0 ∧
    (∀ C : ℝ, studentized C ⟨0,2,0,3⟩ ⟨0,0,0,5⟩ = C)) ∧
  (tableCounts wholeOneControlTable = ⟨0,0,1,4⟩ ∧
    tableTau wholeOneControlTable = -1/5 ∧ tau ⟨0,0,1,4⟩ = -1/5 ∧
    (Finset.univ.filter fun z : Assignment 5 2 => (0 : Fin 5) ∈ z.val).card = 4 ∧
    (Finset.univ.filter fun z : Assignment 5 2 => (0 : Fin 5) ∉ z.val).card = 6 ∧
    (∀ z : Assignment 5 2,
      ((0 : Fin 5) ∈ z.val →
        unitObserved (unitOutcomes wholeOneControlTable z.val) z.val = ⟨0,2,0,3⟩) ∧
      ((0 : Fin 5) ∉ z.val →
        unitObserved (unitOutcomes wholeOneControlTable z.val) z.val = ⟨0,2,1,2⟩)) ∧
    standardError ⟨0,2,0,3⟩ = 0 ∧
    estimate ⟨0,2,0,3⟩ - tau ⟨0,0,1,4⟩ = 1/5 ∧
    estimate ⟨0,2,1,2⟩ = -1/3 ∧ varianceEstimate ⟨0,2,1,2⟩ = 2/27) ∧
  (∀ (n m K : ℕ) (w : PotentialTable n) (C α : ℝ),
    0 < m → m < n → 0 < K → 0 ≤ α → α ≤ 1 →
    uniformProb (fun zs : Fin (K+1) → Assignment n m =>
      wholeObservedRank C
        (unitObserved (unitOutcomes w (zs 0).val) (zs 0).val) (tableCounts w)
        (fun i => unitObserved (unitOutcomes w (zs i.succ).val) (zs i.succ).val) ≤ α)
      ≤ α) ∧
  (designProb ⟨0,0,1,4⟩ 2 (fun q =>
      |studentized 0 (observed ⟨0,0,1,4⟩ q) ⟨0,0,1,4⟩| ≥
        |studentized 0 ⟨0,2,0,3⟩ ⟨0,0,1,4⟩|) = 1 ∧
    designProb ⟨0,0,1,4⟩ 2 (fun q =>
      |studentized (10^6) (observed ⟨0,0,1,4⟩ q) ⟨0,0,1,4⟩| ≥
        |studentized (10^6) ⟨0,2,0,3⟩ ⟨0,0,1,4⟩|) = 2/5)

end SAP.P003a
