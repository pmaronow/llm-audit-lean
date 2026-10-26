import AronowAudit.P047.Wave1.ImpossibilityBlueprint

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

theorem n11_proof : N11 := by
  classical
  intro s1 M n
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => uniform01
  have hU (i : Fin n) (k : Fin (M + 1)) :
      μ.real {w | cellLabel M (w i) = k} = 1 / (M + 1 : ℝ) := by
    change (μ {w | cellLabel M (w i) = k}).toReal = _
    have hS : MeasurableSet {x : ℝ | cellLabel M x = k} :=
      (measurable_cellLabel M) (measurableSet_singleton k)
    have hset : {w : Fin n → ℝ | cellLabel M (w i) = k} =
        (fun f : Fin n → ℝ => f i) ⁻¹' {x : ℝ | cellLabel M x = k} := rfl
    have hmap : μ.map (fun f : Fin n → ℝ => f i) = uniform01 :=
      (measurePreserving_eval (fun _ : Fin n => uniform01) i).map_eq
    rw [hset, ← Measure.map_apply (measurable_pi_apply i) hS, hmap, s1 M k,
      ENNReal.toReal_ofReal (by positivity)]
  have hind : iIndepFun (fun i : Fin n => fun w : Fin n → ℝ => cellLabel M (w i)) μ :=
    iIndepFun_pi (μ := fun _ : Fin n => uniform01)
      (X := fun _ : Fin n => cellLabel M) (fun _ => (measurable_cellLabel M).aemeasurable)
  have hpair (i j : Fin n) (hij : i ≠ j) :
      μ.real {w | cellLabel M (w i) = cellLabel M (w j)} = 1 / (M + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      uniform_labels_pair_collision (P := μ) (M := M + 1) (by omega)
        (fun w => cellLabel M (w i)) (fun w => cellLabel M (w j))
        ((measurable_cellLabel M).comp (measurable_pi_apply i))
        ((measurable_cellLabel M).comp (measurable_pi_apply j))
        (hind.indepFun hij) (fun k => by rw [hU i k]; norm_num)
        (fun k => by rw [hU j k]; norm_num)
  -- The union-bound lemma is indexed by naturals. Outside the first n indices,
  -- assign distinct deterministic labels larger than every genuine cell label.
  let label : ℕ → (Fin n → ℝ) → ℕ := fun i w =>
    if hi : i < n then (cellLabel M (w ⟨i, hi⟩)).val else M + 1 + i
  have hp (i j : ℕ) (hij : i < j) :
      μ.real {w | label i w = label j w} ≤ 1 / (M + 1 : ℝ) := by
    by_cases hi : i < n
    · by_cases hj : j < n
      · have he : {w | label i w = label j w} =
            {w | cellLabel M (w ⟨i, hi⟩) = cellLabel M (w ⟨j, hj⟩)} := by
          ext w
          simp only [label, dif_pos hi, dif_pos hj, Fin.val_inj]
        rw [he, hpair ⟨i, hi⟩ ⟨j, hj⟩
          (by intro h; exact absurd (Fin.mk.inj_iff.mp h) (ne_of_lt hij))]
      · have he : {w | label i w = label j w} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro w hw
          change label i w = label j w at hw
          simp only [label, dif_pos hi, dif_neg hj] at hw
          have hb := (cellLabel M (w ⟨i, hi⟩)).isLt
          omega
        rw [he]
        simpa only [measureReal_empty] using (by positivity : (0 : ℝ) ≤ 1 / (M + 1 : ℝ))
    · have hj : ¬j < n := by omega
      have he : {w | label i w = label j w} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro w hw
        change label i w = label j w at hw
        simp only [label, dif_neg hi, dif_neg hj] at hw
        omega
      rw [he]
      simpa only [measureReal_empty] using (by positivity : (0 : ℝ) ≤ 1 / (M + 1 : ℝ))
  have hcollision := collision_union_bound (P := μ) label
    (by positivity : (0 : ℝ) < (M + 1 : ℝ)) hp n
  have hevent : {w : Fin n → ℝ | ¬ Function.Injective (fun i => cellLabel M (w i))} =
      {w | ∃ i j : ℕ, i < j ∧ j < n ∧ label i w = label j w} := by
    ext w
    constructor
    · intro hbad
      obtain ⟨i, j, heq, hne⟩ : ∃ i j : Fin n,
          cellLabel M (w i) = cellLabel M (w j) ∧ i ≠ j := by
        simpa only [Set.mem_setOf_eq, Function.Injective, not_forall, not_imp, exists_prop,
          ne_eq] using hbad
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact ⟨i.val, j.val, hij, j.isLt, by
          simpa only [label, dif_pos i.isLt, dif_pos j.isLt] using congrArg Fin.val heq⟩
      · exact ⟨j.val, i.val, hji, i.isLt, by
          simpa only [label, dif_pos i.isLt, dif_pos j.isLt] using congrArg Fin.val heq.symm⟩
    · rintro ⟨i, j, hij, hj, heq⟩ hinj
      have hi : i < n := lt_trans hij hj
      have hc : cellLabel M (w ⟨i, hi⟩) = cellLabel M (w ⟨j, hj⟩) := by
        apply Fin.ext
        simpa only [label, dif_pos hi, dif_pos hj] using heq
      have hv := Fin.mk.inj_iff.mp (hinj hc)
      omega
  change μ.real _ ≤ _
  rw [hevent]
  exact hcollision

end

end AronowAudit.P047.Wave1.Impossibility
