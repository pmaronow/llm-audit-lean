import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Complete randomization and exact inversion. A state records the treated counts of each
potential-outcome type. Its weight is the product of the four binomial coefficients, so
the weighted sums represent the uniform law on labeled assignments. The exact interval
is the existential closed hull of accepted effects and is empty when none are accepted. -/

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

/-- Four binary-outcome cell counts, in order (11, 10, 01, 00).
For potential outcomes the indices are (treatment, control); for observations they are (assignment, outcome). -/
@[ext] structure Counts where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Population size, or observed sample size, obtained by summing all four cells. -/
def Counts.total (v : Counts) : ℕ := v.a + v.b + v.c + v.d

/-- The signed discordant-count difference; subtraction is in the integers. -/
def Counts.effect (v : Counts) : ℤ := (v.b : ℤ) - v.c

/-- Exact rational population effect; theorem hypotheses exclude an empty population. -/
def tauQ (v : Counts) : ℚ := (v.effect : ℚ) / v.total

/-- The same population effect as a real number. -/
def tau (v : Counts) : ℝ := (tauQ v : ℝ)

/-- Exact treated-minus-control observed means; valid experiments have two positive arms. -/
def estimateQ (o : Counts) : ℚ := (o.a : ℚ) / (o.a + o.b) -
  (o.c : ℚ) / (o.c + o.d)

/-- The same observed difference in means as a real number. -/
def estimate (o : Counts) : ℝ := (estimateQ o : ℝ)

/-- All admissible treated type-count states, with exactly m treated units. -/
def randomStates (v : Counts) (m : ℕ) : List Counts :=
  (List.range (min v.a m + 1)).flatMap fun a =>
  (List.range (min v.b (m-a) + 1)).flatMap fun b =>
  (List.range (min v.c (m-a-b) + 1)).filterMap fun c =>
    let d := m-a-b-c
    if d ≤ v.d then some ⟨a,b,c,d⟩ else none

/-- Mathlib's computational binomial coefficient, equal to Nat.choose. -/
def binomial (n k : ℕ) : ℕ := Nat.fast_choose n k

/-- The number of labeled assignments inducing the treated type counts. -/
def multiplicity (v q : Counts) : ℕ :=
  binomial v.a q.a * binomial v.b q.b * binomial v.c q.c * binomial v.d q.d

/-- Observed assignment/outcome cell counts induced by a population and treated state. -/
def observed (v q : Counts) : Counts :=
  ⟨q.a+q.b, q.c+q.d, v.a-q.a+v.c-q.c, v.b-q.b+v.d-q.d⟩

/-- The exact weighted complete-randomization probability of an event. -/
noncomputable def designProb (v : Counts) (m : ℕ) (event : Counts → Prop) : ℝ :=
  ((randomStates v m).map fun q =>
    if event q then (multiplicity v q : ℝ) else 0).sum / v.total.choose m

/-- Integer numerator after clearing the common positive deviation denominator. -/
def deviationNumerator (v o : Counts) (m : ℕ) : ℤ :=
  (v.total : ℤ) * (((v.total : ℤ)-m) * o.a - (m : ℤ) * o.c) -
  (m : ℤ) * ((v.total : ℤ)-m) * v.effect

def tailCount (v o : Counts) : ℕ :=
  let m := o.a+o.b
  ((randomStates v m).map fun q =>
    if (deviationNumerator v (observed v q) m).natAbs ≥
        (deviationNumerator v o m).natAbs then multiplicity v q else 0).sum

/-- Exact rational two-sided randomization p-value, including ties. -/
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

/-- A count vector can be completed to the given observed data. -/
def Possible (o v : Counts) : Prop := v ∈ possibleTables o

instance possibleDecidable (o v : Counts) : Decidable (Possible o v) :=
  inferInstanceAs (Decidable (v ∈ possibleTables o))

/-- The finite set of effects of possible tables whose p-values are at least alpha. -/
noncomputable def accepted (α : ℝ) (o : Counts) : Finset ℝ := by
  classical
  exact ((possibleTables o).filter fun v => α ≤ (pValue v o : ℝ)).toFinset.image tau

/-- Closed interval hull of accepted effects; the hull of an empty set is empty. -/
noncomputable def exactInterval (α : ℝ) (o : Counts) : Set ℝ :=
  {t | ∃ l ∈ accepted α o, ∃ u ∈ accepted α o, l ≤ t ∧ t ≤ u}

/-- Lower accepted-effect endpoint, used only when existence is ensured by the hypotheses. -/
noncomputable def lower (α : ℝ) (o : Counts) : ℝ := sInf (↑(accepted α o) : Set ℝ)

/-- Upper accepted-effect endpoint, used only when existence is ensured by the hypotheses. -/
noncomputable def upper (α : ℝ) (o : Counts) : ℝ := sSup (↑(accepted α o) : Set ℝ)

def acceptedEffectsQ (α : ℚ) (o : Counts) : List ℤ :=
  ((possibleTables o).dedup.filter fun v => levelAccepted α v o).map Counts.effect

/-- Exact rational inversion endpoints; none means the accepted set is empty. -/
def intervalQ (α : ℚ) (o : Counts) : Option (ℚ × ℚ) :=
  match acceptedEffectsQ α o with
  | [] => none
  | d :: ds => some ((ds.foldl min d : ℚ) / o.total,
                     (ds.foldl max d : ℚ) / o.total)

end SAP.P003a
