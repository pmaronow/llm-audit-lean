import SAP.P030.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P030
open scoped BigOperators
noncomputable section

/-- Five-unit counterexample: fixed units 1, 2, 3, and one of units 4, 5 treated. -/
def fiveX : Fin 5 → ℝ := ![0, 4, 8, -1, -2]
def fiveS : FixedIndicator 5 := ![true, true, true, false, false]
def fiveY (i : Fin 5) (_z : Assignment 5) : ℝ := (![0, 1, 2, 0, 0] : Fin 5 → ℝ) i
def fiveAssignment (a : Fin 2) : Assignment 5 := fun i => decide (i.val = a.val + 3)
def fiveΩ : Finset (Assignment 5) := Finset.univ.image fiveAssignment
def fiveFixed (i : Fin 3) : Fin 5 := ⟨i.val, by omega⟩
def fiveOutcomes : Fin 3 → ℝ := fun i => fiveY (fiveFixed i) (fiveAssignment 0)
def fiveDistances (a : Fin 2) : Fin 3 → ℝ :=
  fun i => nearestDistance fiveX fiveS (fiveAssignment a) (fiveFixed i)
def fiveStatistic (a : Fin 2) : ℝ := spearman (fiveDistances a) fiveOutcomes

/-- Ten-unit design: positions 1 through 10; fixed units 1, 8, 9, 10. -/
def tenX (i : Fin 10) : ℝ := (i.val : ℝ) + 1
def tenS (i : Fin 10) : Bool := decide (i.val = 0 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9)
def tenAssignment (j : Fin 10) : Assignment 10 := fun i => decide (i = j)
def tenΩ : Finset (Assignment 10) := Finset.univ.image tenAssignment
def tenYnull (i : Fin 10) (_z : Assignment 10) : ℝ :=
  (![1,2,2,2,2,3,2,3,2,1] : Fin 10 → ℝ) i
def tenFixed : Fin 4 → Fin 10 := ![0,7,8,9]
def tableTreatment (r : Fin 6) : Fin 10 := ⟨r.val + 1, by omega⟩
def tableΩ : Finset (Assignment 10) :=
  Finset.univ.image (fun r => tenAssignment (tableTreatment r))
def tableY : Fin 4 → ℝ := fun i => tenYnull (tenFixed i) (tenAssignment 6)
def tableDistances (r : Fin 6) : Fin 4 → ℝ :=
  fun i => nearestDistance tenX tenS (tenAssignment (tableTreatment r)) (tenFixed i)
def tableRho (r : Fin 6) : ℝ := spearman (tableDistances r) tableY
def tableValues : Fin 6 → ℝ :=
  ![-1 / Real.sqrt 90, -1 / Real.sqrt 90, -1 / Real.sqrt 90,
    -5/6, -3 / Real.sqrt 10, -3 / Real.sqrt 10]

/-- The actual illustrative outcome model, separate from the constant null schedule. -/
def tenPsi (i : Fin 10) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun j => |tenX i - tenX j| = 1)).card : ℝ)
def tenTheta (i : Fin 10) (z : Assignment 10) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun j => z j = true ∧ |tenX i - tenX j| = 1)).card : ℝ)
def tenYexample (i : Fin 10) (z : Assignment 10) : ℝ := tenPsi i + tenTheta i z
def tenG (y : {i // tenS i = true} → ℝ) (z : Assignment 10) : ℝ :=
  spearman (fun i : Fin 4 => nearestDistance tenX tenS z (tenFixed i))
    (fun i : Fin 4 => y ⟨tenFixed i, by fin_cases i <;> norm_num [tenS, tenFixed]⟩)

/-- The printed universal two-tailed assertion, which T4 negates. -/
def PrintedTwoTailedExactness : Prop :=
  ∀ (N : ℕ) (Ω : AssignmentSet N) (S : FixedIndicator N) (a : Assignment N),
    (conditionalAssignments Ω S a).Nonempty →
    ∀ (Y : PotentialOutcomes N)
      (g : ({i // S i = true} → ℝ) → Assignment N → ℝ), NoInterference Ω Y →
    ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      uniformProbability (conditionalAssignments Ω S a) (fun z => printedReject α
        (uniformProbability (conditionalAssignments Ω S a)
          (fun w => referenceStatistic S Y g z w ≤ statistic S Y g z))) ≤ α

end
end SAP.P030
