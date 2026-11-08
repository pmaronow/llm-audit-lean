import SAP.P042.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

/-- The two unconditional variance readings of the printed pooling guidance fail. -/
def T5Statement : Prop :=
  (¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ℕ), 0 < J → ∀ (D : Fin J → Ω → ℝ),
    (∀ j, MemLp (D j) 2 μ) → (∀ j, 0 < variance (D j) μ) →
    variance (pooled (normalizedWeight (fun j => variance (D j) μ)) D) μ =
      (totalWeight (fun j => variance (D j) μ))⁻¹) ∧
  (¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (N A : Finset ι),
    N.Nonempty → A.Nonempty → Disjoint N A →
    ∀ (D : ι → Ω → ℝ), (∀ j, MemLp (D j) 2 μ) → (∀ j, 0 < variance (D j) μ) →
    let v := fun j => variance (D j) μ
    variance (fun ω => pooled (subsetWeight N v) D ω-pooled (subsetWeight A v) D ω) μ =
      (∑ j ∈ N, (v j)⁻¹)⁻¹ + (∑ j ∈ A, (v j)⁻¹)⁻¹)

/-- Balance, ITT and CACE under uniform complete randomization, with fixed
outcomes and one-sided contact affecting only the subject's own outcome. -/
def T6Statement : Prop :=
  (∀ (N m : ℕ), 2 ≤ N → 1 ≤ m → m ≤ N-1 → ∀ (Y : Fin N → Bool → ℝ),
    (∀ t : Bool,
      finiteExpectation (completeAssignments N m)
        (fun S => assignedTreatmentMean m S (fun i => Y i t)) =
          populationMean (fun i => Y i t) ∧
      finiteExpectation (completeAssignments N m)
        (fun S => assignedControlMean m S (fun i => Y i t)) =
          populationMean (fun i => Y i t)) ∧
    finiteExpectation (completeAssignments N m)
      (fun S => assignedTreatmentMean m S (assignedOutcome S Y) -
        assignedControlMean m S (assignedOutcome S Y)) =
      populationMean (fun i => Y i true-Y i false) ∧
    (∀ (c : Fin N → Bool), 0 < complierCount c →
      let S := completeAssignments N m
      let diff := fun s => assignedTreatmentMean m s (contactedOutcome s Y c) -
        assignedControlMean m s (contactedOutcome s Y c)
      assignmentEffect Y c = complierShare c*complierEffect Y c ∧
      finiteExpectation S diff = assignmentEffect Y c ∧
      finiteExpectation S (fun s => assignedContactRate m s c) = complierShare c ∧
      0 < finiteExpectation S (fun s => assignedContactRate m s c) ∧
      complierEffect Y c = finiteExpectation S diff /
        finiteExpectation S (fun s => assignedContactRate m s c))) ∧
  (((94:ℝ)/10-70/10)/(1/2) = 48/10)

end
end SAP.P042
