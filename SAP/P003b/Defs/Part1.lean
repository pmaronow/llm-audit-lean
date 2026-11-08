import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section

/-- Four nonnegative counts, in the order (11,10,01,00). -/
@[ext] structure Counts where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq, Repr, Inhabited

def Counts.total (v : Counts) : ℕ := v.a + v.b + v.c + v.d

def Counts.effect (v : Counts) : ℤ := (v.b : ℤ) - v.c

def tauQ (v : Counts) : ℚ := (v.effect : ℚ) / v.total

def tau (v : Counts) : ℝ := (tauQ v : ℝ)

def estimateQ (o : Counts) : ℚ := (o.a : ℚ) / (o.a + o.b) -
  (o.c : ℚ) / (o.c + o.d)

def estimate (o : Counts) : ℝ := (estimateQ o : ℝ)

def randomStates (v : Counts) (m : ℕ) : List Counts :=
  (List.range (min v.a m + 1)).flatMap fun a =>
  (List.range (min v.b (m-a) + 1)).flatMap fun b =>
  (List.range (min v.c (m-a-b) + 1)).filterMap fun c =>
    let d := m-a-b-c
    if d ≤ v.d then some ⟨a,b,c,d⟩ else none

def binomial (n k : ℕ) : ℕ := Nat.fast_choose n k

def multiplicity (v q : Counts) : ℕ :=
  binomial v.a q.a * binomial v.b q.b * binomial v.c q.c * binomial v.d q.d

def observed (v q : Counts) : Counts :=
  ⟨q.a+q.b, q.c+q.d, v.a-q.a+v.c-q.c, v.b-q.b+v.d-q.d⟩

noncomputable def designProb (v : Counts) (m : ℕ) (event : Counts → Prop) : ℝ :=
  ((randomStates v m).map fun q =>
    if event q then (multiplicity v q : ℝ) else 0).sum / v.total.choose m

noncomputable def designMean (v : Counts) (m : ℕ) (f : Counts → ℝ) : ℝ :=
  ((randomStates v m).map fun q => (multiplicity v q : ℝ) * f q).sum /
    v.total.choose m

def deviationNumerator (v o : Counts) (m : ℕ) : ℤ :=
  (v.total : ℤ) * (((v.total : ℤ)-m) * o.a - (m : ℤ) * o.c) -
  (m : ℤ) * ((v.total : ℤ)-m) * v.effect

def tailCount (v o : Counts) : ℕ :=
  let m := o.a+o.b
  ((randomStates v m).map fun q =>
    if (deviationNumerator v (observed v q) m).natAbs ≥
        (deviationNumerator v o m).natAbs then multiplicity v q else 0).sum

def pValue (v o : Counts) : ℚ := (tailCount v o : ℚ) / binomial v.total (o.a+o.b)

def levelAccepted (α : ℚ) (v o : Counts) : Bool :=
  let D := binomial v.total (o.a+o.b)
  if D = 0 then decide (α ≤ 0) else
    decide (α.num*(D : ℤ) ≤ (tailCount v o : ℤ)*(α.den : ℤ))

def possibleTables (o : Counts) : List Counts :=
  (List.range (o.a+1)).flatMap fun i =>
  (List.range (o.b+1)).flatMap fun j =>
  (List.range (o.c+1)).flatMap fun k =>
  (List.range (o.d+1)).map fun l =>
    ⟨i+k, o.a-i+l, o.c-k+j, o.b+o.d-j-l⟩

def Possible (o v : Counts) : Prop := v ∈ possibleTables o

instance possibleDecidable (o v : Counts) : Decidable (Possible o v) :=
  inferInstanceAs (Decidable (v ∈ possibleTables o))

noncomputable def accepted (α : ℝ) (o : Counts) : Finset ℝ := by
  classical
  exact ((possibleTables o).filter fun v => α ≤ (pValue v o : ℝ)).toFinset.image tau

noncomputable def exactInterval (α : ℝ) (o : Counts) : Set ℝ :=
  {t | ∃ l ∈ accepted α o, ∃ u ∈ accepted α o, l ≤ t ∧ t ≤ u}

noncomputable def lower (α : ℝ) (o : Counts) : ℝ := sInf (↑(accepted α o) : Set ℝ)

noncomputable def upper (α : ℝ) (o : Counts) : ℝ := sSup (↑(accepted α o) : Set ℝ)

def acceptedEffectsQ (α : ℚ) (o : Counts) : List ℤ :=
  ((possibleTables o).dedup.filter fun v => levelAccepted α v o).map Counts.effect

def intervalQ (α : ℚ) (o : Counts) : Option (ℚ × ℚ) :=
  match acceptedEffectsQ α o with
  | [] => none
  | d :: ds => some ((ds.foldl min d : ℚ) / o.total,
                     (ds.foldl max d : ℚ) / o.total)

abbrev PotentialTable (n : ℕ) := Fin n → Bool × Bool

def bit (b : Bool) : ℝ := if b then 1 else 0

def tableCounts {n : ℕ} (w : PotentialTable n) : Counts :=
  ⟨(Finset.univ.filter fun i => w i = (true,true)).card,
   (Finset.univ.filter fun i => w i = (true,false)).card,
   (Finset.univ.filter fun i => w i = (false,true)).card,
   (Finset.univ.filter fun i => w i = (false,false)).card⟩

noncomputable def tableTau {n : ℕ} (w : PotentialTable n) : ℝ :=
  (∑ i, (bit (w i).1 - bit (w i).2)) / n

noncomputable def tableEstimator {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) : ℝ :=
  (∑ i, if i ∈ z then bit (w i).1 else 0) / z.card -
    (∑ i, if i ∈ z then 0 else bit (w i).2) / (n-z.card)

def candidateNumerators (o : Counts) : List ℤ :=
  (List.range (o.total+1)).map fun k : ℕ =>
    (o.a : ℤ)-(o.c : ℤ)-((o.a+o.b : ℕ) : ℤ)+(k : ℤ)

def candidateLattice (o : Counts) : Set ℝ :=
  {t | ∃ d ∈ candidateNumerators o, t = (d : ℝ)/o.total}

def lineVector (n : ℕ) (j b : ℕ) (x : ℤ) : Counts :=
  ⟨j-b,b,((b : ℤ)-x).toNat,((n : ℤ)-j-b+x).toNat⟩

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

abbrev Assignment (n m : ℕ) := {z : Finset (Fin n) // z.card = m}

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

def searchStep (f : ℤ → Bool) (a b : ℤ) : ℤ × ℤ :=
  let c := (a+b)/2
  if f c then (a,c) else (c,b)

def printedExecution (fuel : ℕ) (k₁ k₂ : ℤ) (f : ℤ → Bool)
    (a b : ℤ) : Option (ℤ × ℕ) :=
  match fuel with
  | 0 => none
  | t+1 =>
    let s := searchStep f a b
    if s.2 = s.1+1 then
      if s.1 > k₁ ∧ s.2 < k₂ then some (s.1,1)
      else if s.1 = k₁ then some ((if f k₁ then k₁-1 else k₁),2)
      else if s.2 = k₂ then some ((if f k₂ then k₂-1 else k₂),2)
      else none
    else (printedExecution t k₁ k₂ f s.1 s.2).map fun p => (p.1,p.2+1)

end
end SAP.P003b
