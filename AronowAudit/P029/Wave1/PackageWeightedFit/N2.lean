import AronowAudit.P029.Wave1.PackageWeightedFitBlueprint
import AronowAudit.P029.Wave1.PackageWeightedFit.N1

namespace AronowAudit.P029.Wave1.PackageWeightedFit

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- The inside-log objective has the unit-weight cell optimum. -/
theorem n2_proof : N2 := by
  intro q hq
  apply (inside_log_minimizers lik obsW n1_proof.1 n1_proof.2 q).2
  let cell : Obs → Bool × Bool := fun i => (i.1, i.2.1)
  have hS : ∀ c : Bool × Bool,
      cellSuccessWeight cell obsD (fun _ : Obs => (1 : ℝ)) c =
        (twoSidedSuccesses c : ℝ) := by
    rintro ⟨x, z⟩
    cases x <;> cases z <;>
      simp only [cellSuccessWeight, Fintype.sum_prod_type,
        Fintype.sum_bool, Fin.sum_univ_succ] <;>
      norm_num [cell, obsD, twoSidedSuccesses]
  have hF : ∀ c : Bool × Bool,
      cellFailureWeight cell obsD (fun _ : Obs => (1 : ℝ)) c =
        4 - (twoSidedSuccesses c : ℝ) := by
    rintro ⟨x, z⟩
    cases x <;> cases z <;>
      simp only [cellFailureWeight, Fintype.sum_prod_type,
        Fintype.sum_bool, Fin.sum_univ_succ] <;>
      norm_num [cell, obsD, twoSidedSuccesses]
  have hSpos : ∀ c : Bool × Bool,
      0 < cellSuccessWeight cell obsD (fun _ : Obs => (1 : ℝ)) c := by
    intro c
    rw [hS c]
    rcases c with ⟨x, z⟩
    cases x <;> cases z <;> norm_num [twoSidedSuccesses]
  have hFpos : ∀ c : Bool × Bool,
      0 < cellFailureWeight cell obsD (fun _ : Obs => (1 : ℝ)) c := by
    intro c
    rw [hF c]
    rcases c with ⟨x, z⟩
    cases x <;> cases z <;> norm_num [twoSidedSuccesses]
  have hhat : ∀ c : Bool × Bool,
      cellSuccessWeight cell obsD (fun _ : Obs => (1 : ℝ)) c /
        (cellSuccessWeight cell obsD (fun _ : Obs => (1 : ℝ)) c +
          cellFailureWeight cell obsD (fun _ : Obs => (1 : ℝ)) c) =
        packageCells c := by
    intro c
    rw [hS c, hF c]
    rcases c with ⟨x, z⟩
    cases x <;> cases z <;> norm_num [twoSidedSuccesses, packageCells]
  have hsat := saturated_weighted_objective_minimum cell obsD
    (fun _ : Obs => (1 : ℝ)) (fun _ => by norm_num) hSpos hFpos
  -- Expose the theorem's local qhat, then replace its four coordinates.
  dsimp only at hsat
  simp only [hhat] at hsat
  change ∀ t : Theta,
    weightedObjective (lik q) (fun _ => 1) ≤ weightedObjective (lik t) (fun _ => 1)
  intro t
  have ht : ∀ c : Bool × Bool, t.val c ∈ Set.Ioo (0 : ℝ) 1 := by
    rintro ⟨x, z⟩
    obtain ⟨h0, h01, h1⟩ := t.property x
    cases z with
    | false => exact ⟨h0, lt_trans h01 h1⟩
    | true => exact ⟨lt_trans h0 h01, h1⟩
  simpa only [weightedObjective, lik, hq, cell] using (hsat.2 t.val ht).1

end

end AronowAudit.P029.Wave1.PackageWeightedFit
