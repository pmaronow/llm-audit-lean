import AronowAudit.P045.Wave1.MissingTiesBias.N2

/-! A positive-cell Hajek calculation and the measured-d01 formula (node N3). -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.MissingTiesBias

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

/-- If a realized cell has probabilities `q i / 10`, its common factor ten
cancels. Positivity is proved before evaluating the Option-valued ratio.
This helper also serves N4; it does not assume either node's conclusion. -/
lemma hajekObserved_eq_some_of_cell
    (p : Assignment 10 → ℝ) (D : Assignment 10 → Fin 10 → Exposure)
    (Y : Fin 10 → Assignment 10 → ℝ) (d : Exposure) (z : Assignment 10)
    (S : Finset (Fin 10)) (q : Fin 10 → ℝ)
    (hcell : ∀ i, D z i = d ↔ i ∈ S)
    (hprob : ∀ i ∈ S, exposureProb p D i d = q i / 10)
    (hq : ∀ i ∈ S, 0 < q i) (hS : S.Nonempty) :
    hajekObserved p D Y d z =
      some ((∑ i ∈ S, Y i z / q i) / (∑ i ∈ S, 1 / q i)) := by
  classical
  let W : ℝ := ∑ i ∈ S, 1 / q i
  let V : ℝ := ∑ i ∈ S, Y i z / q i
  have hW : 0 < W := by
    exact Finset.sum_pos (fun i hi => one_div_pos.mpr (hq i hi)) hS
  have hden :
      (∑ i, if D z i = d then 1 / exposureProb p D i d else 0) = 10 * W := by
    calc
      _ = ∑ i ∈ S, 1 / exposureProb p D i d := by
        simp_rw [hcell]
        exact Finset.sum_ite_mem_eq S (fun i => 1 / exposureProb p D i d)
      _ = ∑ i ∈ S, 10 * (1 / q i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hprob i hi]
        field_simp [ne_of_gt (hq i hi)] <;> ring
      _ = 10 * W := by
        simp only [W, Finset.mul_sum]
  have hnum : htObserved p D Y d z = 10 * V := by
    unfold htObserved
    calc
      _ = ∑ i ∈ S, Y i z / exposureProb p D i d := by
        simp_rw [hcell]
        exact Finset.sum_ite_mem_eq S (fun i => Y i z / exposureProb p D i d)
      _ = ∑ i ∈ S, 10 * (Y i z / q i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hprob i hi]
        field_simp [ne_of_gt (hq i hi)] <;> ring
      _ = 10 * V := by
        simp only [V, Finset.mul_sum]
  have hden_ne : (10 : ℝ) * W ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) hW)
  simp only [hajekObserved, hden, hnum, if_neg hden_ne]
  congr 1
  exact mul_div_mul_left V W (by norm_num : (10 : ℝ) ≠ 0)

lemma measuredDegree_pos_of_mem_d01 (R : Finset (Fin 10 × Fin 10)) (t i : Fin 10)
    (hi : i ∈ univ.filter (fun j => deletedAdj R t j = true)) :
    0 < (measuredDegree R i : ℝ) := by
  have hti : deletedAdj R t i = true := (Finset.mem_filter.mp hi).2
  have hit : deletedAdj R i t = true := (deletedAdj_symmetric R i t).trans hti
  have htmem : t ∈ univ.filter (fun j => deletedAdj R i j = true) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ t, hit⟩
  have hcard : 0 < measuredDegree R i := Finset.card_pos.mpr ⟨t, htmem⟩
  exact_mod_cast hcard

lemma obsT28_of_mem_d01 (R : Finset (Fin 10 × Fin 10)) (t i : Fin 10)
    (hi : i ∈ univ.filter (fun j => deletedAdj R t j = true)) :
    obsT28 i (unitAssignment t) = (5 / 4 : ℝ) * biasBaseline i := by
  have hti : deletedAdj R t i = true := (Finset.mem_filter.mp hi).2
  have hit : i ≠ t := by
    intro heq
    subst i
    rw [deletedAdj_loopless] at hti
    cases hti
  have htrue : printedNetwork.adj i t = true := by
    exact deletedAdj_true_printed R i t ((deletedAdj_symmetric R i t).trans hti)
  have hexp : exposure printedNetwork.adj (unitAssignment t) i = .d01 := by
    rw [exposure_unit]
    simp [hit, htrue]
  change yT28 i (exposure printedNetwork.adj (unitAssignment t) i) = _
  rw [hexp]
  simp only [yT28]
  ring

/-- A measured neighbour is a true neighbour, with observed outcome `(5/4)b_i`. -/
theorem n3_proof : N3 := by
  classical
  intro hN2 R t hS
  let S : Finset (Fin 10) := univ.filter (fun i => deletedAdj R t i = true)
  have hq : ∀ i ∈ S, 0 < (measuredDegree R i : ℝ) := by
    intro i hi
    exact measuredDegree_pos_of_mem_d01 R t i hi
  have hformula := hajekObserved_eq_some_of_cell
    (crMass 10 1) (exposure (deleteNetwork printedNetwork R)) obsT28 .d01
    (unitAssignment t) S (fun i => (measuredDegree R i : ℝ))
    (fun i => measured_d01_iff_mem R t i)
    (fun i _ => (hN2 R i).1) hq hS
  have hnum : (∑ i ∈ S, obsT28 i (unitAssignment t) / (measuredDegree R i : ℝ)) =
      ∑ i ∈ S, ((5/4)*biasBaseline i) / (measuredDegree R i : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [obsT28_of_mem_d01 R t i hi]
  simpa only [hnum] using hformula

end

end AronowAudit.P045.Wave1.MissingTiesBias
