import SAP.P029a.Bridge.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace SAP.P029a.Bridge

open SAP.P029a Set
open scoped BigOperators Classical

noncomputable section

/-- Instantiate the existing minimum theorem and substitute the cell totals. -/
theorem freeCellFit_of_totals {I C : Type*} [Fintype I] [Fintype C]
    (cell : I → C) (D : I → Bool) (w : I → ℝ) (S F : C → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hS : ∀ c, successWeightTotal cell D w c = S c)
    (hF : ∀ c, failureWeightTotal cell D w c = F c)
    (hpS : ∀ c, 0 < S c) (hpF : ∀ c, 0 < F c) :
    IsUniqueFreeCellFit cell D w (fun c => S c / (S c + F c)) := by
  have hs : ∀ c, 0 < successWeightTotal cell D w c := fun c => by rw [hS]; exact hpS c
  have hf : ∀ c, 0 < failureWeightTotal cell D w c := fun c => by rw [hF]; exact hpF c
  have h := proveFreeCellUniqueMinimum cell D w hw hs hf
  simpa only [IsUniqueFreeCellFit, hS, hF] using h

theorem treated_weighted_fit :
    IsUniqueFreeCellFit Prod.fst treatedReceipt treatedWeight specifiedWeightedScores := by
  let S : Bool → ℝ := fun x => if x then 27 else 9
  let F : Bool → ℝ := fun x => if x then 1 else 3
  have hs : ∀ x, successWeightTotal Prod.fst treatedReceipt treatedWeight x = S x := by
    intro x
    cases x <;> norm_num [successWeightTotal, treatedReceipt, treatedWeight,
      receiptDependentWeight, weightWitnessResponse, weightWitnessAssignment,
      PotentialResponse.receivedTreatment, S, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have hf : ∀ x, failureWeightTotal Prod.fst treatedReceipt treatedWeight x = F x := by
    intro x
    cases x <;> norm_num [failureWeightTotal, treatedReceipt, treatedWeight,
      receiptDependentWeight, weightWitnessResponse, weightWitnessAssignment,
      PotentialResponse.receivedTreatment, F, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have hw : ∀ i, 0 ≤ treatedWeight i := by
    intro i
    unfold treatedWeight receiptDependentWeight
    split <;> norm_num
  have heq : (fun x => S x / (S x + F x)) = specifiedWeightedScores := by
    funext x
    cases x <;> norm_num [S, F, specifiedWeightedScores]
  have h := freeCellFit_of_totals Prod.fst treatedReceipt treatedWeight S F hw hs hf
    (by intro x; cases x <;> norm_num [S]) (by intro x; cases x <;> norm_num [F])
  simpa only [heq] using h

theorem treated_perturbed_fit (t : ℝ) (ht : 0 < t) :
    IsUniqueFreeCellFit Prod.fst treatedReceipt (treatedPerturbationWeight t)
      (specifiedPerturbedScores t) := by
  let S : Bool → ℝ := fun x => if x then 3 else 1
  let F : Bool → ℝ := fun x => if x then 1 else 2+t
  have hs : ∀ x, successWeightTotal Prod.fst treatedReceipt (treatedPerturbationWeight t) x = S x := by
    intro x
    cases x <;> simp only [successWeightTotal, Fintype.sum_prod_type,
      Fintype.sum_bool, Fin.sum_univ_succ]
    all_goals norm_num [treatedReceipt, treatedPerturbationWeight,
      perturbedRecordWeight, weightWitnessResponse, PotentialResponse.receivedTreatment, S]
  have hf : ∀ x, failureWeightTotal Prod.fst treatedReceipt (treatedPerturbationWeight t) x = F x := by
    intro x
    cases x <;> simp only [failureWeightTotal, Fintype.sum_prod_type,
      Fintype.sum_bool, Fin.sum_univ_succ]
    all_goals norm_num [treatedReceipt, treatedPerturbationWeight,
      perturbedRecordWeight, weightWitnessResponse, PotentialResponse.receivedTreatment, F] <;> ring
  have hw : ∀ i, 0 ≤ treatedPerturbationWeight t i := by
    intro i
    unfold treatedPerturbationWeight perturbedRecordWeight
    split
    · exact ht.le
    · norm_num
  have heq : (fun x => S x / (S x + F x)) = specifiedPerturbedScores t := by
    funext x
    cases x
    · dsimp [S, F, specifiedPerturbedScores]
      congr 1 <;> ring
    · norm_num [S, F, specifiedPerturbedScores]
  have h := freeCellFit_of_totals Prod.fst treatedReceipt (treatedPerturbationWeight t)
    S F hw hs hf (by intro x; cases x <;> norm_num [S])
    (by intro x; cases x <;> dsimp [F] <;> linarith)
  simpa only [heq] using h

theorem two_sided_weighted_fit :
    IsUniqueFreeCellFit Prod.fst twoSidedReceipt twoSidedObservationWeight specifiedWeightedRates := by
  let S : Bool × Bool → ℝ := fun x => if x.2 then (if x.1 then 27 else 18) else 9
  let F : Bool × Bool → ℝ := fun x => if x.2 then (if x.1 then 1 else 2) else 3
  have hs : ∀ x, successWeightTotal Prod.fst twoSidedReceipt twoSidedObservationWeight x = S x := by
    rintro ⟨x,z⟩
    cases x <;> cases z <;>
      norm_num [successWeightTotal, twoSidedReceipt, twoSidedObservationWeight,
        twoSidedSuccessCount, S, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have hf : ∀ x, failureWeightTotal Prod.fst twoSidedReceipt twoSidedObservationWeight x = F x := by
    rintro ⟨x,z⟩
    cases x <;> cases z <;>
      norm_num [failureWeightTotal, twoSidedReceipt, twoSidedObservationWeight,
        twoSidedSuccessCount, F, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have hw : ∀ i, 0 ≤ twoSidedObservationWeight i := by
    intro i
    unfold twoSidedObservationWeight
    split <;> norm_num
  have heq : (fun x => S x / (S x + F x)) = specifiedWeightedRates := by
    funext i
    rcases i with ⟨x,z⟩
    cases x <;> cases z <;> norm_num [S, F, specifiedWeightedRates]
  have h := freeCellFit_of_totals Prod.fst twoSidedReceipt twoSidedObservationWeight
    S F hw hs hf
    (by rintro ⟨x,z⟩; cases x <;> cases z <;> norm_num [S])
    (by rintro ⟨x,z⟩; cases x <;> cases z <;> norm_num [F])
  simpa only [heq] using h

theorem proveConcreteFreeCellFits : ConcreteFreeCellFits := by
  exact ⟨treated_weighted_fit, treated_perturbed_fit, two_sided_weighted_fit⟩

end
end SAP.P029a.Bridge
