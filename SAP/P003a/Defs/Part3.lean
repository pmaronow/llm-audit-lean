import SAP.P003a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The literal printed and corrected sentinel searches. True means rejection. The
recursive fuel makes executions total; each theorem specifies the fuel it uses. The
minimum-base and reuse definitions represent the corrected exhaustive scan over effect
numerators and all possible values of the treatment-outcome total. -/

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

def searchStep (f : ℤ → Bool) (a b : ℤ) : ℤ × ℤ :=
  let c := (a+b)/2
  if f c then (a,c) else (c,b)

def printedReturn (k₁ k₂ a b : ℤ) (f : ℤ → Bool) : Option ℤ :=
  if b = a+1 then
    if a > k₁ ∧ b < k₂ then some a
    else if a = k₁ then some (if f k₁ then k₁-1 else k₁)
    else if b = k₂ then some (if f k₂ then k₂-1 else k₂)
    else none
  else none

def printedSearch (fuel : ℕ) (k₁ k₂ : ℤ) (f : ℤ → Bool) (a b : ℤ) : Option ℤ :=
  match fuel with
  | 0 => none
  | t+1 =>
    let s := searchStep f a b
    match printedReturn k₁ k₂ s.1 s.2 f with
    | some r => some r
    | none => printedSearch t k₁ k₂ f s.1 s.2

/-- Corrected integer search; returns the endpoint and the list of evaluated indices. -/
def sentinelSearch (fuel : ℕ) (f : ℤ → Bool) (a b : ℤ) : ℤ × List ℤ :=
  match fuel with
  | 0 => (a,[])
  | t+1 =>
    if b ≤ a+1 then (a,[]) else
      let c := (a+b)/2
      let next := if f c then sentinelSearch t f a c else sentinelSearch t f c b
      (next.1, c :: next.2)

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

def candidateNumerators (o : Counts) : List ℤ :=
  (List.range (o.total+1)).map fun k : ℕ =>
    (o.a : ℤ)-(o.c : ℤ)-((o.a+o.b : ℕ) : ℤ)+(k : ℤ)

def lineGroup (o : Counts) (x : ℤ) (j : ℕ) : List Counts :=
  (possibleTables o).filter fun v => v.effect = x ∧ v.a+v.b = j

def minimumB : List Counts → Option Counts
  | [] => none
  | v::vs => match minimumB vs with
    | none => some v
    | some u => some (if v.b ≤ u.b then v else u)

def firstOnLine (o : Counts) (x : ℤ) (j : ℕ) : Option Counts :=
  minimumB (lineGroup o x j)

def reuseVector (v : Counts) (k : ℕ) : Counts := ⟨v.a-k,v.b+k,v.c+k,v.d-k⟩

end SAP.P003a
