import SAP.P003a.Defs.WholeW1.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

/-- One outer effect query, with its chronological first table-test index. -/
structure W1EffectQuery where
  x : ℤ
  start : ℕ
  rejected : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Search output with both outer queries and the original table-test trace. -/
structure W1EffectResult where
  value : Option ℤ
  queries : List W1EffectQuery
  tests : List (Counts × Bool)
  deriving DecidableEq, Repr

/-- Corrected T5 search with stateful compatibility blocks, instrumented without extra queries. -/
def w1EffectSearch (fuel : ℕ) (o : Counts) (reject : Counts → ℕ → Bool)
    (a b : ℤ) (idx : ℕ) : W1EffectResult :=
  if b ≤ a+1 then ⟨some a,[],[]⟩ else
  match fuel with
  | 0 => ⟨none,[],[]⟩
  | t+1 =>
    let c := (a+b)/2
    let q := runTests reject idx (candidates o c)
    let r := w1EffectSearch t o reject
      (if q.compatible then c else a) (if q.compatible then b else c) q.idx
    ⟨r.value, ⟨c,idx,!q.compatible⟩ :: r.queries, q.trace ++ r.tests⟩

/-- The two upper-search bounds in a balanced design. -/
def w1UpperBounds (o : Counts) : ℤ × ℤ :=
  (2*((o.a : ℤ)-o.c), (o.a : ℤ)-o.c+(o.a+o.b))

def w1EffectUpperRun (o : Counts) (reject : Counts → ℕ → Bool) : W1EffectResult :=
  w1EffectSearch (o.total+3) o reject
    ((w1UpperBounds o).1-1) ((w1UpperBounds o).2+1) 0

def w1TestBudget (n : ℕ) : ℕ := (n+1)*(Nat.log2 (n+1)+3)

/-- Pool slots are chronological; the theorem below proves that valid runs never wrap. -/
def w1Batch {n m K : ℕ}
    (pool : Fin (2*w1TestBudget n+1) → Fin K → Assignment n m) (idx : ℕ)
    (i : Fin K) : Finset (Fin n) :=
  (pool ⟨idx % (2*w1TestBudget n+1), Nat.mod_lt _ (by omega)⟩ i).val

def w1MonteMean {n K : ℕ} (v o : Counts) (draws : Fin K → Finset (Fin n)) : ℚ :=
  (∑ i, if (deviationNumerator v (canonicalObserved v (draws i)) (o.a+o.b)).natAbs ≥
    (deviationNumerator v o (o.a+o.b)).natAbs then (1 : ℚ) else 0)/(K : ℚ)

noncomputable def w1ApproxReject {n m K : ℕ} (α ε : ℝ) (o : Counts)
    (pool : Fin (2*w1TestBudget n+1) → Fin K → Assignment n m)
    (v : Counts) (idx : ℕ) : Bool :=
  decide ((w1MonteMean v o (w1Batch pool idx) : ℝ)+ε < α)

/-- P003-T23; p. 13 (PDF p. 13), Remark 5.6, corrected.
A rejected query in the corrected T5 search forces the returned numerator and
every later query strictly below it, for arbitrary decisions. This applies
pointwise to Algorithm 4.5's chronological fresh Monte Carlo batches and whole
compatibility blocks. The exact balanced endpoint exists on the effect lattice.
Returning at least that endpoint requires accepting every queried effect at or
below it, with no accuracy or monotonicity assumption on Monte Carlo decisions. -/
def T23WholeStatement : Prop :=
  T23Statement ∧
  (∀ (o : Counts) (K : ℕ) (α ε : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (hK : 0 < K) (hα : 0 < α ∧ α < 1) (hε : 0 ≤ ε ∧ ε < α)
    (pool : Fin (2*w1TestBudget o.total+1) → Fin K → Assignment o.total (o.a+o.b)),
    let reject := w1ApproxReject α ε o pool;
    let s := w1EffectUpperRun o reject;
    ∃ A r : ℤ, s.value = some A ∧
      (upperRun true o reject).value = some A ∧
      s.tests = (upperRun true o reject).trace ∧
      (accepted α o).Nonempty ∧ upper α o = (r : ℝ)/o.total ∧
      (∀ q ∈ s.queries,
        q.rejected = !(runTests reject q.start (candidates o q.x)).compatible) ∧
      (∀ i, i < s.tests.length →
        i < 2*w1TestBudget o.total+1 ∧
        (s.tests[i]!).2 = reject (s.tests[i]!).1 i) ∧
      (∀ q ∈ s.queries, q.rejected = true → (A : ℝ)/o.total < (q.x : ℝ)/o.total) ∧
      (∀ i j, i < j → j < s.queries.length → (s.queries[i]!).rejected = true →
        (s.queries[j]!).x < (s.queries[i]!).x) ∧
      ((r : ℝ)/o.total ≤ (A : ℝ)/o.total →
        ∀ q ∈ s.queries, (q.x : ℝ)/o.total ≤ upper α o → q.rejected = false))

/-- Literal printed B.1 with chronological queries and the final bracket. -/
structure W1PrintedResult where
  value : Option ℤ
  queries : List ℤ
  bracket : ℤ × ℤ
  deriving DecidableEq, Repr

def w1PrintedRun (fuel : ℕ) (k₁ k₂ : ℤ) (f : ℤ → Bool) (a b : ℤ) : W1PrintedResult :=
  match fuel with
  | 0 => ⟨none,[],(a,b)⟩
  | t+1 =>
    let c := (a+b)/2
    let s := searchStep f a b
    if s.2 = s.1+1 then
      if s.1 > k₁ ∧ s.2 < k₂ then ⟨some s.1,[c],s⟩
      else if s.1 = k₁ then ⟨some (if f k₁ then k₁-1 else k₁),[c,k₁],s⟩
      else if s.2 = k₂ then ⟨some (if f k₂ then k₂-1 else k₂),[c,k₂],s⟩
      else ⟨none,[c],s⟩
    else
      let r := w1PrintedRun t k₁ k₂ f s.1 s.2
      ⟨r.value,c::r.queries,r.bracket⟩

/-- P003-T4; p. 20 (PDF p. 20); Algorithm 4.3, p. 8; proof, p. 21.
The printed claim is false: on [1,2] the literal search queries [1,1] and
returns the wrong all-accept threshold, while all-reject repeats query one
forever, exceeding the printed three-evaluation budget. In the legal balanced
sixteen-unit example its upper endpoint is 14/16 instead of 15/16. The lattice,
first tests, 144 possible vectors, 12870 assignments and two-atom estimator law
are explicit. Three further balanced inputs violate the printed search domain. -/
def T4WholeStatement : Prop :=
  T4Statement ∧
  w1PrintedRun 1 1 2 (fun _ => false) 1 2 = ⟨some 1,[1,1],(1,2)⟩ ∧
  (∀ fuel, w1PrintedRun (fuel+1) 1 2 (fun _ => true) 1 2 =
    ⟨none,List.replicate (fuel+1) 1,(1,1)⟩) ∧
  (⌊logTwo 2+2⌋ : ℤ) = 3 ∧
  (let o : Counts := ⟨7,1,0,8⟩;
    o.total = 16 ∧ o.a+o.b = 8 ∧ o.c+o.d = 8 ∧
    candidateNumerators o = [-1,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] ∧
    w1UpperBounds o = (14,15) ∧ (0 : ℤ) < 14 ∧ (14 : ℤ) < 15 ∧
    (possibleTables o).toFinset.card = 144 ∧ Fintype.card (Assignment 16 8) = 12870 ∧
    firstOnLine o 14 14 = some ⟨0,14,0,2⟩ ∧ firstOnLine o 15 15 = some ⟨0,15,0,1⟩ ∧
    (∀ j < 14, firstOnLine o 14 j = none) ∧
    (∀ j < 15, firstOnLine o 15 j = none) ∧
    (candidates o 14).head? = some ⟨0,14,0,2⟩ ∧
    (candidates o 15).head? = some ⟨0,15,0,1⟩ ∧
    (runTests (exactRejectQ (1/20) o) 0 (candidates o 14)).compatible = true ∧
    (runTests (exactRejectQ (1/20) o) 0 (candidates o 15)).compatible = true ∧
    tauQ ⟨0,14,0,2⟩ = 14/16 ∧ tauQ ⟨0,15,0,1⟩ = 15/16 ∧
    exactInterval ((1/20 : ℚ) : ℝ) o = Set.Icc (1/2) (15/16) ∧
    upper ((1/20 : ℚ) : ℝ) o = 15/16 ∧
    w1PrintedRun 1 14 15
      (fun x => !(runTests (exactRejectQ (1/20) o) 0 (candidates o x)).compatible)
      14 15 = ⟨some 14,[14,14],(14,15)⟩ ∧
    (14/16 : ℝ) ≠ upper ((1/20 : ℚ) : ℝ) o) ∧
  (let w : PotentialTable 16 := fun i => canonicalPair ⟨0,15,0,1⟩ i.val;
    tableCounts w = ⟨0,15,0,1⟩ ∧ tableTau w = 15/16 ∧
    (∀ z : Assignment 16 8, tableEstimator w z.val = 7/8 ∨ tableEstimator w z.val = 1) ∧
    (Finset.univ.filter fun z : Assignment 16 8 => tableEstimator w z.val = 7/8).card = 6435 ∧
    (Finset.univ.filter fun z : Assignment 16 8 => tableEstimator w z.val = 1).card = 6435 ∧
    |(7/8 : ℝ)-15/16| = 1/16 ∧ |(1 : ℝ)-15/16| = 1/16 ∧
    |estimate ⟨7,1,0,8⟩-15/16| = 1/16) ∧
  (∀ od ∈ ([((⟨0,8,1,7⟩ : Counts),(-2,7)),(⟨0,8,0,8⟩,(0,8)),
      (⟨8,0,0,8⟩,(16,16))] : List (Counts × (ℤ × ℤ))),
    od.1.total = 16 ∧ od.1.a+od.1.b = 8 ∧ od.1.c+od.1.d = 8 ∧
    w1UpperBounds od.1 = od.2 ∧ ¬ (0 < od.2.1 ∧ od.2.1 < od.2.2))

end SAP.P003a
