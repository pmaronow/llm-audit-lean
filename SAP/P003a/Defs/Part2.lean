import SAP.P003a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Missingness is represented by missing counts in each observed cell. A joint law has
nonnegative masses and the prescribed complete-randomization marginal, with arbitrary
dependence between randomization and missingness. Completions enumerate distinct observed
count vectors, not labeled binary completions. Rational examples compute exact endpoints. -/

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

def missingMasks (o : Counts) : List Counts :=
  (List.range (o.a+1)).flatMap fun a =>
  (List.range (o.b+1)).flatMap fun b =>
  (List.range (o.c+1)).flatMap fun c =>
  (List.range (o.d+1)).map fun d => ⟨a,b,c,d⟩

def plusCompletion (o r : Counts) : Counts :=
  ⟨o.a+r.b, o.b-r.b, o.c-r.c, o.d+r.c⟩

def minusCompletion (o r : Counts) : Counts :=
  ⟨o.a-r.a, o.b+r.a, o.c+r.d, o.d-r.d⟩

def completions (o r : Counts) : List Counts :=
  (List.range (r.a+r.b+1)).flatMap fun t =>
  (List.range (r.c+r.d+1)).map fun c =>
    ⟨o.a-r.a+t, o.b-r.b+(r.a+r.b-t),
      o.c-r.c+c, o.d-r.d+(r.c+r.d-c)⟩

/-- Printed two-completion interval, with guarded endpoints for empty accepted sets. -/
noncomputable def missingInterval (α : ℝ) (o r : Counts) : Set ℝ :=
  let lo := minusCompletion o r
  let hi := plusCompletion o r
  Set.Icc (if (accepted α lo).Nonempty then min (lower α lo) (estimate lo)
           else estimate lo)
          (if (accepted α hi).Nonempty then max (upper α hi) (estimate hi)
           else estimate hi)

/-- Union of exact inversion intervals over all count completions. -/
noncomputable def completionUnion (α : ℝ) (o r : Counts) : Set ℝ :=
  {t | ∃ c ∈ completions o r, t ∈ exactInterval α c}

/-- Closed interval hull of the completion union, empty if the union is empty. -/
noncomputable def completionHull (α : ℝ) (o r : Counts) : Set ℝ :=
  {t | ∃ l ∈ completionUnion α o r, ∃ u ∈ completionUnion α o r, l ≤ t ∧ t ≤ u}

/-- An arbitrary joint law with nonnegative mass and the complete-randomization marginal. -/
def IsMissingLaw (v : Counts) (m : ℕ) (μ : Counts → Counts → ℝ) : Prop :=
  (∀ q ∈ randomStates v m, ∀ r ∈ missingMasks (observed v q), 0 ≤ μ q r) ∧
  (∀ q ∈ randomStates v m,
    ((missingMasks (observed v q)).map (μ q)).sum =
      (multiplicity v q : ℝ) / v.total.choose m)

/-- Joint probability under a law of randomization and missingness. -/
noncomputable def missingProb (v : Counts) (m : ℕ) (μ : Counts → Counts → ℝ)
    (E : Counts → Counts → Prop) : ℝ :=
  ((randomStates v m).map fun q =>
    ((missingMasks (observed v q)).map fun r => if E q r then μ q r else 0).sum).sum

def missingIntervalQ (α : ℚ) (o r : Counts) : ℚ × ℚ :=
  let lo := minusCompletion o r
  let hi := plusCompletion o r
  (match intervalQ α lo with
    | none => estimateQ lo
    | some (l,_) => min l (estimateQ lo),
   match intervalQ α hi with
    | none => estimateQ hi
    | some (_,u) => max u (estimateQ hi))

/-- Counterexample population with potential-outcome counts (11, 0, 3, 6). -/
def badPopulation : Counts := ⟨11,0,3,6⟩

/-- One missing control success only when all three (0,1) units are treated. -/
def badMask (q : Counts) : Counts :=
  if q = ⟨0,0,3,0⟩ then ⟨0,0,1,0⟩ else ⟨0,0,0,0⟩

/-- Exact coverage of the printed missing-data interval in the counterexample. -/
def badCoverage : ℚ :=
  ((randomStates badPopulation 3).map fun q =>
    let I := missingIntervalQ (109/500) (observed badPopulation q) (badMask q)
    if I.1 ≤ tauQ badPopulation ∧ tauQ badPopulation ≤ I.2
    then multiplicity badPopulation q else 0).sum / (1140 : ℚ)

def completionHullQ (α : ℚ) (o r : Counts) : Option (ℚ × ℚ) :=
  match (completions o r).filterMap (intervalQ α) with
  | [] => none
  | I::Is => some (Is.foldl (fun l J => min l J.1) I.1,
                  Is.foldl (fun u J => max u J.2) I.2)

/-- Exact coverage of the repaired completion hull in the same counterexample. -/
def badHullCoverage : ℚ :=
  ((randomStates badPopulation 3).map fun q =>
    match completionHullQ (109/500) (observed badPopulation q) (badMask q) with
    | none => 0
    | some (l,u) => if l ≤ tauQ badPopulation ∧ tauQ badPopulation ≤ u
        then multiplicity badPopulation q else 0).sum / (1140 : ℚ)

end SAP.P003a
