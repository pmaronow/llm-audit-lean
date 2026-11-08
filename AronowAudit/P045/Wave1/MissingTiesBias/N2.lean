import AronowAudit.P045.Wave1.MissingTiesBias.N1

/-! Exposure cells and their exact single-treated probabilities (node N2).
The auxiliary statements apply to every mask, including non-edge entries. -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.MissingTiesBias

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

lemma deleteNetwork_printed (R : Finset (Fin 10 × Fin 10)) :
    deleteNetwork printedNetwork R = deletedAdj R := rfl

lemma deletedAdj_symmetric (R : Finset (Fin 10 × Fin 10)) (i j : Fin 10) :
    deletedAdj R i j = deletedAdj R j i := by
  change (printedNetwork.adj i j && decide ((i,j) ∉ R ∧ (j,i) ∉ R)) =
    (printedNetwork.adj j i && decide ((j,i) ∉ R ∧ (i,j) ∉ R))
  rw [printedNetwork.symmetric i j]
  simp only [Bool.decide_and, Bool.and_comm]

lemma deletedAdj_loopless (R : Finset (Fin 10 × Fin 10)) (i : Fin 10) :
    deletedAdj R i i = false := by
  change (printedNetwork.adj i i && _) = false
  rw [printedNetwork.loopless i]
  rfl

lemma deletedAdj_true_printed (R : Finset (Fin 10 × Fin 10)) (i j : Fin 10)
    (h : deletedAdj R i j = true) : printedAdj i j = true := by
  unfold deletedAdj at h
  cases hA : printedAdj i j <;> simp_all

/-- Under a unit assignment the only possible treated peer is `t`. -/
lemma exposure_unit (A : Fin 10 → Fin 10 → Bool) (t i : Fin 10) :
    exposure A (unitAssignment t) i =
      if i = t then (if A i t then .d11 else .d10)
      else (if A i t then .d01 else .d00) := by
  simp [exposure, unitAssignment]

lemma exposure_unit_d01_iff (R : Finset (Fin 10 × Fin 10)) (t i : Fin 10) :
    exposure (deleteNetwork printedNetwork R) (unitAssignment t) i = .d01 ↔
      deletedAdj R i t = true := by
  rw [deleteNetwork_printed, exposure_unit]
  by_cases hit : i = t
  · subst i
    simp [deletedAdj_loopless]
  · cases hA : deletedAdj R i t <;> simp [hit, hA]

lemma exposure_unit_d00_iff (R : Finset (Fin 10 × Fin 10)) (t i : Fin 10) :
    exposure (deleteNetwork printedNetwork R) (unitAssignment t) i = .d00 ↔
      t ≠ i ∧ deletedAdj R i t = false := by
  rw [deleteNetwork_printed, exposure_unit]
  by_cases hit : i = t
  · subst i
    simp [deletedAdj_loopless]
  · cases hA : deletedAdj R i t <;> simp [hit, Ne.symm hit, hA]

lemma measured_d01_iff_mem (R : Finset (Fin 10 × Fin 10)) (t i : Fin 10) :
    exposure (deleteNetwork printedNetwork R) (unitAssignment t) i = .d01 ↔
      i ∈ univ.filter (fun j => deletedAdj R t j = true) := by
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    deletedAdj_symmetric R i t] using exposure_unit_d01_iff R t i

lemma measured_d00_iff_mem (R : Finset (Fin 10 × Fin 10)) (t i : Fin 10) :
    exposure (deleteNetwork printedNetwork R) (unitAssignment t) i = .d00 ↔
      i ∈ univ \ insert t (univ.filter (fun j => deletedAdj R t j = true)) := by
  rw [exposure_unit_d00_iff]
  by_cases hit : i = t
  · subst i
    simp
  · cases hA : deletedAdj R t i <;>
      simp [hit, Ne.symm hit, deletedAdj_symmetric R i t, hA]

/-- Count possible treated neighbours and possible treated non-neighbours. -/
theorem n2_proof : N2 := by
  classical
  intro R i
  constructor
  · unfold exposureProb prob
    rw [n1_proof.1]
    simp_rw [exposure_unit_d01_iff]
    simp only [mean, Fintype.card_fin, Finset.sum_boole, measuredDegree, Nat.cast_ofNat]
  · let B : Finset (Fin 10) := univ.filter (fun t => deletedAdj R i t = true)
    let C : Finset (Fin 10) := (univ.erase i) \ B
    have hsub : B ⊆ (univ : Finset (Fin 10)).erase i := by
      intro t ht
      have hA : deletedAdj R i t = true := (Finset.mem_filter.mp ht).2
      have hti : t ≠ i := by
        intro heq
        subst t
        rw [deletedAdj_loopless] at hA
        cases hA
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact hti
    have hC : univ.filter (fun t => t ≠ i ∧ deletedAdj R i t = false) = C := by
      ext t
      cases hA : deletedAdj R i t <;> simp [B, C, hA]
    have hcardNat : C.card + measuredDegree R i = 9 := by
      simpa [C, B, measuredDegree] using Finset.card_sdiff_add_card_eq_card hsub
    have hcardReal : (C.card : ℝ) = 9 - (measuredDegree R i : ℝ) := by
      have hc : (C.card : ℝ) + (measuredDegree R i : ℝ) = 9 := by
        exact_mod_cast hcardNat
      linarith
    unfold exposureProb prob
    rw [n1_proof.1]
    simp_rw [exposure_unit_d00_iff]
    simp only [mean, Fintype.card_fin, Finset.sum_boole, Nat.cast_ofNat]
    rw [hC, hcardReal]

end

end AronowAudit.P045.Wave1.MissingTiesBias
