import SAP.P003a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The ordered compatibility tests and upper search implement the paper's printed
boundary rule when corrected is false. Failed fuel returns none. These definitions
are used to state the executed balanced counterexample in T4, not a new correctness claim. -/

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

def candidates (o : Counts) (x : ℤ) : List Counts :=
  (List.range (o.total+1)).flatMap fun j =>
    match firstOnLine o x j with
    | none => []
    | some v =>
      if v.b = 0 ∧ v.c = 0 ∧ 1 ≤ v.a ∧ 1 ≤ v.d ∧
          Possible o ⟨v.a-1,1,1,v.d-1⟩ then [v,⟨v.a-1,1,1,v.d-1⟩] else [v]

/-- The result and trace of one compatibility query; true trace entries reject. -/
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

/-- An endpoint and its table-test trace; none records fuel exhaustion. -/
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

def exactRejectQ (α : ℚ) (o v : Counts) (_idx : ℕ) : Bool := !(levelAccepted α v o)

end SAP.P003a
