import AronowAudit.P045.Wave1.MissingTiesBias.N3

/-! The measured-d00 ratio, with outcomes determined by the true graph (node N4). -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.MissingTiesBias

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

/-- This bound holds for every mask, not just masks of size at most two.
It is stronger than the bound eight needed for the no-exposure weights. -/
lemma measuredDegree_le_six (R : Finset (Fin 10 × Fin 10)) (i : Fin 10) :
    measuredDegree R i ≤ 6 := by
  exact le_trans (deleted_degree_loss_bound R i).2
    (zero_deletion_hajek_counterexample.2.2.1 i).2

lemma obsT28_of_mem_d00 (R : Finset (Fin 10 × Fin 10)) (t i : Fin 10)
    (hi : i ∈ univ \ insert t (univ.filter (fun j => deletedAdj R t j = true))) :
    obsT28 i (unitAssignment t) =
      biasBaseline i * (1 + (if printedAdj t i then (1/4 : ℝ) else 0)) := by
  have hnot : i ∉ insert t (univ.filter (fun j => deletedAdj R t j = true)) :=
    (Finset.mem_sdiff.mp hi).2
  have hit : i ≠ t := by
    intro heq
    apply hnot
    simp [heq]
  have hsym : printedNetwork.adj i t = printedAdj t i :=
    printedNetwork.symmetric i t
  change yT28 i (exposure printedNetwork.adj (unitAssignment t) i) = _
  rw [exposure_unit, if_neg hit, hsym]
  cases hA : printedAdj t i <;> norm_num [hA, yT28]

/-- The d00 cell excludes `t`; its true exposure records whether its tie to `t` was lost. -/
theorem n4_proof : N4 := by
  classical
  intro hN2 R t hC
  let C : Finset (Fin 10) :=
    univ \ insert t (univ.filter (fun i => deletedAdj R t i = true))
  have hq : ∀ i ∈ C, 0 < 9 - (measuredDegree R i : ℝ) := by
    intro i _
    have hupper : (measuredDegree R i : ℝ) ≤ 6 := by
      exact_mod_cast measuredDegree_le_six R i
    linarith
  have hformula := hajekObserved_eq_some_of_cell
    (crMass 10 1) (exposure (deleteNetwork printedNetwork R)) obsT28 .d00
    (unitAssignment t) C (fun i => 9 - (measuredDegree R i : ℝ))
    (fun i => measured_d00_iff_mem R t i)
    (fun i _ => (hN2 R i).2) hq hC
  have hnum :
      (∑ i ∈ C, obsT28 i (unitAssignment t) / (9 - (measuredDegree R i : ℝ))) =
      ∑ i ∈ C, biasBaseline i * (1 + (if printedAdj t i then (1/4 : ℝ) else 0)) /
        (9 - (measuredDegree R i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [obsT28_of_mem_d00 R t i hi]
  simpa only [hnum] using hformula

end

end AronowAudit.P045.Wave1.MissingTiesBias
