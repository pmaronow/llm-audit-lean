import AronowAudit.P029.Wave1.PackageWeightedFitBlueprint
import AronowAudit.P029.Wave1.PackageWeightedFit.N1

namespace AronowAudit.P029.Wave1.PackageWeightedFit

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- The feasible weighted cell optimum strictly improves on the package optimum. -/
theorem n3_proof : N3 := by
  intro q hq
  let cell : Obs → Bool × Bool := fun i => (i.1, i.2.1)
  have hS : ∀ c : Bool × Bool,
      cellSuccessWeight cell obsD obsW c = 9 * (twoSidedSuccesses c : ℝ) := by
    rintro ⟨x, z⟩
    cases x <;> cases z <;>
      norm_num [cellSuccessWeight, cell, obsW, obsD, twoSidedSuccesses,
        Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  have hF : ∀ c : Bool × Bool,
      cellFailureWeight cell obsD obsW c = 4 - (twoSidedSuccesses c : ℝ) := by
    rintro ⟨x, z⟩
    cases x <;> cases z <;>
      norm_num [cellFailureWeight, cell, obsW, obsD, twoSidedSuccesses,
        Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  have hSpos : ∀ c : Bool × Bool, 0 < cellSuccessWeight cell obsD obsW c := by
    intro c
    rw [hS c]
    rcases c with ⟨x, z⟩
    cases x <;> cases z <;> norm_num [twoSidedSuccesses]
  have hFpos : ∀ c : Bool × Bool, 0 < cellFailureWeight cell obsD obsW c := by
    intro c
    rw [hF c]
    rcases c with ⟨x, z⟩
    cases x <;> cases z <;> norm_num [twoSidedSuccesses]
  have hhat : ∀ c : Bool × Bool,
      cellSuccessWeight cell obsD obsW c /
        (cellSuccessWeight cell obsD obsW c + cellFailureWeight cell obsD obsW c) =
        weightedCells c := by
    intro c
    rw [hS c, hF c]
    rcases c with ⟨x, z⟩
    cases x <;> cases z <;> norm_num [twoSidedSuccesses, weightedCells]
  have hsat := saturated_weighted_objective_minimum cell obsD obsW
    (fun i => (n1_proof.2 i).le) hSpos hFpos
  dsimp only at hsat
  simp only [hhat] at hsat
  let qw : Theta := ⟨weightedCells, two_sided_weight_counterexample.2.1⟩
  have hqint : ∀ c : Bool × Bool, q.val c ∈ Set.Ioo (0 : ℝ) 1 := by
    rintro ⟨x, z⟩
    obtain ⟨h0, h01, h1⟩ := q.property x
    cases z with
    | false => exact ⟨h0, lt_trans h01 h1⟩
    | true => exact ⟨lt_trans h0 h01, h1⟩
  have hopt := hsat.2 q.val hqint
  have hne : q.val ≠ weightedCells := by
    intro heq
    have h00 := congrFun (hq.symm.trans heq) (false, false)
    norm_num [packageCells, weightedCells] at h00
  have hle : weightedObjective (lik qw) obsW ≤ weightedObjective (lik q) obsW := by
    simpa only [weightedObjective, lik, qw, cell] using hopt.1
  have hstrict : weightedObjective (lik qw) obsW < weightedObjective (lik q) obsW := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hne
    apply hopt.2.mp
    simpa only [weightedObjective, lik, qw, cell] using heq
  intro hbad
  exact (not_lt_of_ge (hbad qw)) hstrict

end

end AronowAudit.P029.Wave1.PackageWeightedFit
