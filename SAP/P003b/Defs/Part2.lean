import SAP.P003b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section

def canonicalPair (v : Counts) (i : ℕ) : Bool × Bool :=
  if i < v.a then (true,true)
  else if i < v.a+v.b then (true,false)
  else if i < v.a+v.b+v.c then (false,true) else (false,false)

def canonicalObserved {n : ℕ} (v : Counts) (z : Finset (Fin n)) : Counts :=
  ⟨(Finset.univ.filter fun i => i ∈ z ∧ (canonicalPair v i.val).1 = true).card,
   (Finset.univ.filter fun i => i ∈ z ∧ (canonicalPair v i.val).1 = false).card,
   (Finset.univ.filter fun i => i ∉ z ∧ (canonicalPair v i.val).2 = true).card,
   (Finset.univ.filter fun i => i ∉ z ∧ (canonicalPair v i.val).2 = false).card⟩

def candidates (o : Counts) (x : ℤ) : List Counts :=
  (List.range (o.total+1)).flatMap fun j =>
    match firstOnLine o x j with
    | none => []
    | some v =>
      if v.b = 0 ∧ v.c = 0 ∧ 1 ≤ v.a ∧ 1 ≤ v.d ∧
          Possible o ⟨v.a-1,1,1,v.d-1⟩ then [v,⟨v.a-1,1,1,v.d-1⟩] else [v]

structure QueryResult where
  compatible : Bool
  idx : ℕ
  trace : List (Counts × Bool)
  deriving Repr


def runTests (reject : Counts → ℕ → Bool) (idx : ℕ) : List Counts → QueryResult
  | [] => ⟨false,idx,[]⟩
  | v::vs =>
    if reject v idx then
      let r := runTests reject (idx+1) vs
      ⟨r.compatible,r.idx,(v,true)::r.trace⟩
    else ⟨true,idx+1,[(v,false)]⟩

structure EndpointResult where
  value : Option ℤ
  trace : List (Counts × Bool)
  deriving DecidableEq, Repr


def adaptiveSearch (fuel : ℕ) (corrected : Bool) (o : Counts)
    (k₁ k₂ : ℤ) (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) : EndpointResult :=
  if corrected ∧ b ≤ a+1 then ⟨some a,[]⟩ else
  match fuel with
  | 0 => ⟨none,[]⟩
  | t+1 =>
    let c := (a+b)/2
    let q := runTests reject idx (candidates o c)
    let a' := if q.compatible then c else a
    let b' := if q.compatible then b else c
    if ¬corrected ∧ b' = a'+1 then
      if a' > k₁ ∧ b' < k₂ then ⟨some a',q.trace⟩
      else if a' = k₁ then
        let e := runTests reject q.idx (candidates o k₁)
        ⟨some (if e.compatible then k₁ else k₁-1),q.trace++e.trace⟩
      else if b' = k₂ then
        let e := runTests reject q.idx (candidates o k₂)
        ⟨some (if e.compatible then k₂ else k₂-1),q.trace++e.trace⟩
      else ⟨none,q.trace⟩
    else
      let r := adaptiveSearch t corrected o k₁ k₂ reject a' b' q.idx
      ⟨r.value,q.trace++r.trace⟩

def upperRun (corrected : Bool) (o : Counts) (reject : Counts → ℕ → Bool)
    (idx : ℕ := 0) : EndpointResult :=
  let k₁ := 2*((o.a : ℤ)-o.c)
  let k₂ := (o.a : ℤ)-o.c+(o.a+o.b)
  adaptiveSearch (o.total+3) corrected o k₁ k₂ reject
    (if corrected then k₁-1 else k₁) (if corrected then k₂+1 else k₂) idx

def complementObserved (o : Counts) : Counts := ⟨o.b,o.a,o.d,o.c⟩

def exactRejectQ (α : ℚ) (o v : Counts) (_idx : ℕ) : Bool := !(levelAccepted α v o)

noncomputable def exactUpperRun (α : ℝ) (o : Counts) : EndpointResult :=
  upperRun true o (fun v _ => decide ((pValue v o : ℝ) < α))

def monteMean {n K : ℕ} (v o : Counts) (draws : Fin K → Finset (Fin n)) : ℚ :=
  (∑ i, if (deviationNumerator v (canonicalObserved v (draws i)) (o.a+o.b)).natAbs ≥
    (deviationNumerator v o (o.a+o.b)).natAbs then (1 : ℚ) else 0)/(K : ℚ)

def testBudget (n : ℕ) : ℕ := (n+1)*(Nat.log2 (n+1)+3)

abbrev MonteSpace (n m K : ℕ) :=
  Assignment n m × (Fin (2*testBudget n+1) → Fin K → Assignment n m)

noncomputable def uniformProb {Ω : Type*} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ)/Fintype.card Ω

def batch {n m K : ℕ} (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m)
    (idx : ℕ) (i : Fin K) : Finset (Fin n) :=
  (pool ⟨idx % (2*testBudget n+1), Nat.mod_lt _ (by omega)⟩ i).val

noncomputable def approximateReject {n m K : ℕ} (α ε : ℝ) (o : Counts)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m)
    (v : Counts) (idx : ℕ) : Bool :=
  decide ((monteMean v o (batch pool idx) : ℝ)+ε < α)

noncomputable def monteEndpoints {n m K : ℕ} (corrected : Bool) (α ε : ℝ)
    (o : Counts) (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m) :
    EndpointResult × EndpointResult :=
  let hi := upperRun corrected o (approximateReject α ε o pool)
  let lo := upperRun corrected (complementObserved o)
    (approximateReject α ε (complementObserved o) pool) hi.trace.length
  (lo,hi)

noncomputable def monteInterval {n m K : ℕ} (corrected : Bool) (α ε : ℝ)
    (o : Counts) (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m) : Set ℝ :=
  let e := monteEndpoints corrected α ε o pool
  match e.1.value, e.2.value with
  | some lo, some hi => Set.Icc (-(lo : ℝ)/o.total) ((hi : ℝ)/o.total)
  | _, _ => ∅

def traceProbabilityQ (o : Counts) (trace : List (Counts × Bool)) : ℚ :=
  (trace.map fun t => if t.2 then 1-pValue t.1 o else pValue t.1 o).prod

def adaptiveData : Counts := ⟨2,13,1,14⟩

def firstMismatch (a b : List (Counts × Bool)) : ℕ :=
  match (a.zip b).findIdx? (fun p => p.1.2 != p.2.2) with
  | some i => i
  | none => a.length

noncomputable def upperShuffleCost {n K : ℕ} (α ε : ℝ) (o : Counts)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n (n/2)) : ℕ :=
  (upperRun true o (approximateReject α ε o pool)).trace.length*K*(n-1)

noncomputable def expectedUpperShuffleCost (α ε : ℝ) (n K : ℕ) (o : Counts) : ℝ :=
  (∑ pool : Fin (2*testBudget n+1) → Fin K → Assignment n (n/2),
    (upperShuffleCost α ε o pool : ℝ)) /
      Fintype.card (Fin (2*testBudget n+1) → Fin K → Assignment n (n/2))

end
end SAP.P003b
