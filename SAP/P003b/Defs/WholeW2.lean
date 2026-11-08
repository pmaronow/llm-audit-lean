import Mathlib
import SAP.P003b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section

/-- The size of a fixed covariate stratum; zero sizes are permitted. -/
def wholeStratumSize {n : ℕ} (X : Fin n → Bool) (s : Bool) : ℕ :=
  (Finset.univ.filter fun i => X i = s).card

/-- Counts on a specified set of labels, in the order 11,10,01,00. -/
def wholeCountsOn {n : ℕ} (A : Finset (Fin n)) (w : PotentialTable n) : Counts :=
  ⟨(A.filter fun i => w i = (true,true)).card,
   (A.filter fun i => w i = (true,false)).card,
   (A.filter fun i => w i = (false,true)).card,
   (A.filter fun i => w i = (false,false)).card⟩

/-- Actual eight counts of a labeled table, with stratum zero first. -/
def wholeStratumCounts {n : ℕ} (X : Fin n → Bool) (w : PotentialTable n) : Counts × Counts :=
  (wholeCountsOn (Finset.univ.filter fun i => X i = false) w,
   wholeCountsOn (Finset.univ.filter fun i => X i = true) w)

def wholeStratumImage {n : ℕ} (X : Fin n → Bool) : Finset (Counts × Counts) :=
  Finset.univ.image (wholeStratumCounts X)

/-- Eight nonnegative coordinates with just the total restriction. -/
def wholeTotalEight (n : ℕ) : Finset (Counts × Counts) :=
  (Finset.range (n+1)).biUnion fun r => stratifiedCounts r (n-r)

/-- Coefficient rows of the two stratum equations in real eight-coordinate space. -/
def wholeStratumRow (s : Bool) : ((Bool × Bool) × Bool) → ℝ :=
  fun cell => if cell.2 = s then 1 else 0

/-- P003-T19; p. 17 (PDF p. 17), Section 8 and corrected footnote 16.
For fixed binary covariates, actual table counts have exactly the two independent
stratum-total restrictions. Their number is the product of the two four-cell
composition counts, at most (n+3)^6/36 and uniformly O(n^6), hence O(n^7).
With only a total restriction the eight-cell count is choose(n+7,7), the stated
convolution, and O(n^7); without covariates it is choose(n+3,3) and O(n^3).
For the fixed 2+2 split of four labels there are 256 tables, 100 realized count
vectors and 330 total-only vectors; (3,0,0,0;1,0,0,0) is not realizable. -/
def T19WholeStatement : Prop :=
  LinearIndependent ℝ wholeStratumRow ∧
  (∀ cell : (Bool × Bool) × Bool, wholeStratumRow false cell + wholeStratumRow true cell = 1) ∧
  (∀ (n : ℕ) (X : Fin n → Bool),
    wholeStratumSize X false + wholeStratumSize X true = n ∧
    (∀ w : PotentialTable n,
      (wholeStratumCounts X w).1.total = wholeStratumSize X false ∧
      (wholeStratumCounts X w).2.total = wholeStratumSize X true ∧
      (wholeStratumCounts X w).1.total + (wholeStratumCounts X w).2.total = n) ∧
    wholeStratumImage X = stratifiedCounts (wholeStratumSize X false) (wholeStratumSize X true) ∧
    (wholeStratumImage X).card =
      (wholeStratumSize X false+3).choose 3 * (wholeStratumSize X true+3).choose 3 ∧
    ((wholeStratumImage X).card : ℝ) ≤ ((n : ℝ)+3)^6/36 ∧
    (Finset.univ.image (tableCounts (n := n))) = allCounts n ∧
    (allCounts n).card = (n+3).choose 3 ∧
    Fintype.card (PotentialTable n) = 4^n) ∧
  (∀ n : ℕ,
    (∀ v : Counts × Counts, v ∈ wholeTotalEight n ↔ v.1.total+v.2.total = n) ∧
    (wholeTotalEight n).card = (n+7).choose 7 ∧
    (n+7).choose 7 = ∑ r ∈ Finset.range (n+1), (r+3).choose 3 * (n-r+3).choose 3) ∧
  (∀ (N₀ N₁ : ℕ → ℕ) (_hN : ∀ n, N₀ n+N₁ n = n),
    (fun n => ((stratifiedCounts (N₀ n) (N₁ n)).card : ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^6) ∧
    (fun n => ((stratifiedCounts (N₀ n) (N₁ n)).card : ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^7)) ∧
  ((fun n => ((wholeTotalEight n).card : ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^7)) ∧
  ((fun n => ((allCounts n).card : ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^3)) ∧
  (∀ (X : Fin 4 → Bool), wholeStratumSize X false = 2 → wholeStratumSize X true = 2 →
    Fintype.card (PotentialTable 4) = 256 ∧ (wholeStratumImage X).card = 100 ∧
    (wholeTotalEight 4).card = 330 ∧
    (⟨3,0,0,0⟩,⟨1,0,0,0⟩) ∈ wholeTotalEight 4 ∧
    ¬ ∃ w : PotentialTable 4, wholeStratumCounts X w = (⟨3,0,0,0⟩,⟨1,0,0,0⟩))

/-- Corrected possible-table J, represented by its count vectors. -/
def wholeJ (α : ℝ) (o : Counts) : Set ℝ :=
  {t | t ∈ candidateLattice o ∧ ∃ v : Counts,
    Possible o v ∧ tau v = t ∧ α ≤ (pValue v o : ℝ)}

/-- Printed B.11 omits possibility, while keeping the population size fixed. -/
def wholePrintedJ (α : ℝ) (o : Counts) : Set ℝ :=
  {t | t ∈ candidateLattice o ∧ ∃ v : Counts,
    v.total = o.total ∧ tau v = t ∧ α ≤ (pValue v o : ℝ)}

def wholeCPlus (o : Counts) : ℝ :=
  ((o.a : ℝ)-o.c-(o.a+o.b : ℕ)+o.total)/o.total

def wholeT25Data : Counts := ⟨0,2,0,2⟩

/-- All five attainable maximal p-values, indexed by the effect numerator. -/
def wholeT25Maxima : Prop :=
  ∀ e : ℤ, e ∈ [-2,-1,0,1,2] →
    let p : ℚ := if e = -2 ∨ e = 2 then 1/3 else 1
    (∀ v : Counts, Possible wholeT25Data v → v.effect = e → pValue v wholeT25Data ≤ p) ∧
    (∃ v : Counts, Possible wholeT25Data v ∧ v.effect = e ∧ pValue v wholeT25Data = p)

/-- P003-T25; p. 21 (PDF p. 21), corrected (B.11)-(B.12).
For every design the possible accepted effects J equal K and lie in the
interval hull and candidate lattice. Under balance J is exactly the lattice
part of the interval, and the upper-half identity holds with the same lattice
intersection. For n=4,m=2,o=(0,2,0,2),alpha=1/2, the candidate set has five
points, the possible maxima are 1/3,1,1,1,1/3, J has three points and the
interval is [-1/4,1/4]. The two impossible endpoint vectors have p=2/3;
the only possible negative endpoint vector has p=1/3. The printed set is
the full candidate set, including both points outside the interval, whereas
1/8 lies in the real interval and outside the lattice. -/
def T25WholeStatement : Prop :=
  (∀ (o : Counts) (α : ℝ),
    0 < o.a+o.b → 0 < o.c+o.d → 0 < α ∧ α < 1 →
    wholeJ α o = (↑(accepted α o) : Set ℝ) ∧
    wholeJ α o ⊆ exactInterval α o ∩ candidateLattice o) ∧
  (∀ (o : Counts) (α : ℝ),
    0 < o.a+o.b ∧ o.a+o.b = o.c+o.d → 0 < α ∧ α < 1 →
    wholeJ α o = exactInterval α o ∩ candidateLattice o ∧
    (Set.Icc (estimate o) (wholeCPlus o) ∩ wholeJ α o) =
      Set.Icc (estimate o) (upper α o) ∩ candidateLattice o ∧
    (accepted α o).Nonempty ∧ lower α o ≤ estimate o ∧ estimate o ≤ upper α o ∧
    upper α o ≤ wholeCPlus o ∧
    wholeCPlus o ∈ candidateLattice o ∧
    (∀ t ∈ candidateLattice o, t ≤ wholeCPlus o)) ∧
  (candidateLattice wholeT25Data = ({-1/2,-1/4,0,1/4,1/2} : Set ℝ)) ∧
  (tauQ ⟨1,0,2,1⟩ = -1/2 ∧ pValue ⟨1,0,2,1⟩ wholeT25Data = 2/3 ∧
    ¬ Possible wholeT25Data ⟨1,0,2,1⟩) ∧
  (tauQ ⟨1,2,0,1⟩ = 1/2 ∧ pValue ⟨1,2,0,1⟩ wholeT25Data = 2/3 ∧
    ¬ Possible wholeT25Data ⟨1,2,0,1⟩) ∧
  (∀ v : Counts, Possible wholeT25Data v → tauQ v = -1/2 → v = ⟨0,0,2,2⟩) ∧
  (Possible wholeT25Data ⟨0,0,2,2⟩ ∧ tauQ ⟨0,0,2,2⟩ = -1/2 ∧
    pValue ⟨0,0,2,2⟩ wholeT25Data = 1/3) ∧
  wholeT25Maxima ∧
  (wholeJ (1/2) wholeT25Data = ({-1/4,0,1/4} : Set ℝ)) ∧
  (exactInterval (1/2) wholeT25Data = Set.Icc (-1/4) (1/4)) ∧
  (lower (1/2) wholeT25Data = -1/4 ∧ upper (1/2) wholeT25Data = 1/4) ∧
  (wholePrintedJ (1/2) wholeT25Data = candidateLattice wholeT25Data) ∧
  ((-1/2 : ℝ) ∉ exactInterval (1/2) wholeT25Data ∧
    (1/2 : ℝ) ∉ exactInterval (1/2) wholeT25Data) ∧
  ((1/8 : ℝ) ∈ exactInterval (1/2) wholeT25Data ∧
    (1/8 : ℝ) ∉ candidateLattice wholeT25Data)

/-- Binary coordinates of a treated set. -/
def wholeAssignmentBits {n m : ℕ} (z : Assignment n m) : Fin n → Bool :=
  fun i => decide (i ∈ z.val)

abbrev wholeBinaryAssignments (n m : ℕ) :=
  {z : Fin n → Bool // (∑ i, if z i then 1 else 0) = m}

/-- Signed coordinates avoid truncated subtraction in the line identity. -/
def wholeSignedLine (n j b x : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (j-b,b,b-x,n-j-b+x)

def wholeT20Table (swapped : Bool) : PotentialTable 2 :=
  fun i => if (i.val = 0) = (!swapped = true) then (true,true) else (false,false)

def wholeT20Assignment : Finset (Fin 2) := {0}

/-- P003-T20; pp. 5,12,20,21,26,18 (PDF pages agree).
Binary assignment coordinates correspond bijectively to treated sets and
preserve their uniform law. The legal reuse update is (-1,1,1,-1), the four
B.8 comparisons use n01, and the signed line uses j=u11+u10 and
k=u10-v10. At its feasible minimum k is nonnegative and is positive off
the selected vector; in the balanced discordant case the quoted p-value
comparison follows. The printed index fails at (0,2,0,2). Evenness of
a+2+d implies d congruent to a modulo two. Equal table counts give equal
estimator distributions, but the two swapped tables (11,00) and (00,11)
give estimates 1 and -1 at the same assignment. -/
def T20WholeStatement : Prop :=
  (∀ n m : ℕ, 0 < m ∧ m < n → ∃ e : Assignment n m ≃ wholeBinaryAssignments n m,
    (∀ z, (e z).val = wholeAssignmentBits z) ∧
    (∀ E : wholeBinaryAssignments n m → Prop,
      uniformProb (fun z : Assignment n m => E (e z)) = uniformProb E)) ∧
  T20Statement ∧
  (∀ (n n₁₁ n₁₀ n₀₁ j b x : ℤ),
    (j-b-n₀₁ ≤ j-b ↔ 0 ≤ n₀₁) ∧
    (j-b-n₀₁ ≤ n₁₁ ↔ j-n₁₁-n₀₁ ≤ b) ∧
    (j-b-n₀₁ ≤ j-x-n₀₁ ↔ x ≤ b) ∧
    (j-b-n₀₁ ≤ n-b-n₁₀-n₀₁ ↔ j+n₁₀ ≤ n)) ∧
  (∀ (o u v : Counts), Possible o u →
    firstOnLine o u.effect (u.a+u.b) = some v →
    let k : ℤ := (u.b : ℤ)-v.b
    0 ≤ k ∧ (u ≠ v → 0 < k) ∧
    wholeSignedLine o.total (u.a+u.b) v.b u.effect =
      ((u.a : ℤ)+k,(u.b : ℤ)-k,(u.c : ℤ)-k,(u.d : ℤ)+k)) ∧
  (∀ (o u v : Counts) (α : ℝ),
    0 < o.a+o.b ∧ o.a+o.b = o.c+o.d → Possible o u →
    firstOnLine o u.effect (u.a+u.b) = some v → 1 ≤ v.b+v.c →
    pValue u o ≤ pValue v o ∧ ((pValue v o : ℝ) < α → (pValue u o : ℝ) < α)) ∧
  (∀ b k : ℤ, wholeSignedLine 4 0 b 2 ≠ (k,2-k,-k,2+k)) ∧
  (tableCounts (wholeT20Table false) = ⟨1,0,0,1⟩ ∧
    tableCounts (wholeT20Table true) = ⟨1,0,0,1⟩ ∧
    wholeT20Assignment.card = 1 ∧
    tableEstimator (wholeT20Table false) wholeT20Assignment = 1 ∧
    tableEstimator (wholeT20Table true) wholeT20Assignment = -1)

/-- Observed counts of arbitrary binary data on fixed labels. -/
def wholeObservedCounts {n : ℕ} (Y : Fin n → Bool) (z : Finset (Fin n)) : Counts :=
  ⟨(Finset.univ.filter fun i => i ∈ z ∧ Y i = true).card,
   (Finset.univ.filter fun i => i ∈ z ∧ Y i = false).card,
   (Finset.univ.filter fun i => i ∉ z ∧ Y i = true).card,
   (Finset.univ.filter fun i => i ∉ z ∧ Y i = false).card⟩

def wholeAgrees {n : ℕ} (w : PotentialTable n) (Y : Fin n → Bool)
    (z : Finset (Fin n)) : Prop :=
  ∀ i, (if i ∈ z then (w i).1 else (w i).2) = Y i

/-- Explicit discordant imputation of every missing potential outcome. -/
def wholeBalancedWitness {n : ℕ} (Y : Fin n → Bool)
    (z : Finset (Fin n)) : PotentialTable n :=
  fun i => if i ∈ z then (Y i, !Y i) else (!Y i, Y i)

def wholeBalancedVector (o : Counts) : Counts := ⟨0,o.a+o.d,o.b+o.c,0⟩

/-- P003-T30; p. 7 (PDF p. 7); Appendix A.1, pp. 18-19.
In a positive balanced design the possible vector (0,n11+n00,n10+n01,0)
has effect equal to the observed Neyman estimate and exact p-value one.
The explicit table obtained by imputing the complement of each observed
outcome is possible and has exactly these counts, effect and p-value.
Thus the estimate belongs to K and I, K is nonempty, and its genuine
endpoints satisfy L <= T <= U. -/
def T30WholeStatement : Prop :=
  (∀ (o : Counts) (α : ℝ),
    0 < o.a+o.b ∧ o.a+o.b = o.c+o.d → 0 < α ∧ α < 1 →
    Possible o (wholeBalancedVector o) ∧ tau (wholeBalancedVector o) = estimate o ∧
    pValue (wholeBalancedVector o) o = 1 ∧
    estimate o ∈ accepted α o ∧ estimate o ∈ exactInterval α o ∧
    (accepted α o).Nonempty ∧ lower α o ≤ estimate o ∧ estimate o ≤ upper α o) ∧
  (∀ (m : ℕ) (Y : Fin (2*m) → Bool) (z : Assignment (2*m) m) (α : ℝ),
    0 < m → 0 < α ∧ α < 1 →
    let o := wholeObservedCounts Y z.val
    let w := wholeBalancedWitness Y z.val
    o.total = 2*m ∧ o.a+o.b = m ∧ o.c+o.d = m ∧
    wholeAgrees w Y z.val ∧ tableCounts w = wholeBalancedVector o ∧
    tableTau w = tau (wholeBalancedVector o) ∧ tableTau w = estimate o ∧
    tableEstimator w z.val = estimate o ∧
    uniformProb (fun z' : Assignment (2*m) m =>
      |tableEstimator w z'.val-tableTau w| ≥ |estimate o-tableTau w|) = 1 ∧
    pValue (tableCounts w) o = 1 ∧
    estimate o ∈ accepted α o ∧ estimate o ∈ exactInterval α o ∧
    (accepted α o).Nonempty ∧ lower α o ≤ estimate o ∧ estimate o ≤ upper α o)

/-- B.2-B.3 use signed arithmetic, including for negative candidate effects. -/
def wholeLineLower (o : Counts) (x : ℤ) (j : ℕ) : ℤ :=
  max (max 0 x) (max ((j : ℤ)-o.a-o.c) ((o.a : ℤ)+o.c+x-j))

def wholeLineUpper (o : Counts) (x : ℤ) (j : ℕ) : ℤ :=
  min (min (j : ℤ) ((o.a : ℤ)+o.d))
    (min ((o.b : ℤ)+o.c+x) ((o.total : ℤ)+x-j))

def wholeLineGuards (o : Counts) (x : ℤ) (j : ℕ) : Prop :=
  x+o.c ≤ (j : ℤ) ∧ (o.a : ℤ) ≤ j ∧
  (j : ℤ)+o.b ≤ o.total ∧ (j : ℤ) ≤ (o.a : ℤ)+x+o.b+o.c

instance wholeLineGuardsDecidable (o : Counts) (x : ℤ) (j : ℕ) :
    Decidable (wholeLineGuards o x j) := by
  unfold wholeLineGuards
  infer_instance

/-- Constant-size arithmetic implementation of Step 2(b). -/
def wholeFastBase (o : Counts) (x : ℤ) (j : ℕ) : Option Counts :=
  if wholeLineGuards o x j ∧ wholeLineLower o x j ≤ wholeLineUpper o x j then
    some (lineVector o.total j (wholeLineLower o x j).toNat x)
  else none

/-- All feasible bases, or just the first feasible j as in the literal text. -/
def wholeCostBases (full : Bool) (o : Counts) (x : ℤ) : List (ℕ × Counts) :=
  let vs := (List.range (o.total+1)).filterMap fun j =>
    (wholeFastBase o x j).map fun v => (j,v)
  if full then vs else vs.take 1

/-- Reuse steps are generated directly from the feasible B.3 interval. -/
def wholeCostReuse (o : Counts) (x : ℤ) (j : ℕ) (v : Counts) : List ℕ :=
  (List.range ((wholeLineUpper o x j).toNat-v.b)).map (fun k => k+1)

def wholeCostDraws (full : Bool) (o : Counts) (K : ℕ) : ℕ :=
  ((candidateNumerators o).map fun x => (wholeCostBases full o x).length*K).sum

def wholeCostUpdates (full : Bool) (o : Counts) (K : ℕ) : ℕ :=
  ((candidateNumerators o).map fun x =>
    ((wholeCostBases full o x).map fun jv =>
      K*(wholeCostReuse o x jv.1 jv.2).length).sum).sum

/-- Paper arithmetic charges: constant-size selection/bookkeeping per slot,
linear fresh draw and initial scan, constant reuse and indicator evaluation.
Constant-time evaluations of the fixed estimand/statistic and list insertion
are included in the coefficients. These are charges, not bit complexity. -/
def wholeCostOperations (full : Bool) (o : Counts) (K : ℕ) (c₀ c₁ c₂ : ℝ) : ℝ :=
  c₀*(o.total+1)^2 + 2*c₁*o.total*wholeCostDraws full o K +
    2*c₂*wholeCostUpdates full o K

/-- P003-T36; p. 13 (PDF p. 13), Theorem 5.5(2); Appendix C, p. 28.
Algorithm 5.3 has arithmetic cost O(K n^3) under the paper's constant-cost
estimand/statistic and linear-cost fresh-draw model. The B.2-B.3 selector
implements its feasible minimum with constant-size arithmetic, and its reuse
interval enumerates exactly the legal updates. Both the literal first-feasible-j
loop and the full-j loop have at most (n+1)^2 K draws and (n+1)^2 n K updates.
Their nonnegative charged costs lie below the explicit envelope and a single
constant times K n^3, uniformly for positive n,K. The order bound holds jointly
and along every eventually positive K(n), including fixed positive K. -/
def T36WholeStatement : Prop :=
  (∀ (o : Counts) (x : ℤ) (j : ℕ), wholeFastBase o x j = firstOnLine o x j) ∧
  (∀ (o v : Counts) (x : ℤ) (j : ℕ), firstOnLine o x j = some v →
    wholeCostReuse o x j v = reuseLine o v) ∧
  (∀ (full : Bool) (o : Counts) (K : ℕ) (c₀ c₁ c₂ : ℝ),
    0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂ →
    wholeCostDraws full o K ≤ (o.total+1)^2*K ∧
    wholeCostUpdates full o K ≤ (o.total+1)^2*o.total*K ∧
    0 ≤ wholeCostOperations full o K c₀ c₁ c₂ ∧
    wholeCostOperations full o K c₀ c₁ c₂ ≤ generalEnvelope o.total K c₀ c₁ c₂ ∧
    (1 ≤ o.total → 1 ≤ K → wholeCostOperations full o K c₀ c₁ c₂ ≤
      4*(c₀+2*(c₁+c₂))*K*(o.total : ℝ)^3)) ∧
  (∀ (full : Bool) (c₀ c₁ c₂ : ℝ), 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂ →
    (∀ (o : ℕ × ℕ → Counts), (∀ p, (o p).total = p.1) →
      (fun p : ℕ × ℕ => wholeCostOperations full (o p) p.2 c₀ c₁ c₂)
        =O[Filter.atTop] (fun p : ℕ × ℕ => (p.2 : ℝ)*(p.1 : ℝ)^3)) ∧
    (∀ (o : ℕ → Counts) (K : ℕ → ℕ), (∀ n, (o n).total = n) →
      (∀ᶠ n in Filter.atTop, 1 ≤ K n) →
      (fun n => wholeCostOperations full (o n) (K n) c₀ c₁ c₂)
        =O[Filter.atTop] (fun n : ℕ => (K n : ℝ)*(n : ℝ)^3)))

end
end SAP.P003b
